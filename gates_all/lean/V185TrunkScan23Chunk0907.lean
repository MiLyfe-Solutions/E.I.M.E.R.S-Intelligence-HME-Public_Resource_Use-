import V185TrunkScan23Chunk0906

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5367981 : List Nat := [1, 5, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_5367981 : Nat := 118140960795 + 5367981 * 2 ^ 59
def prefixEnd_5367981 : Nat := 4983230072969 + 3 ^ 40 * 5367981 * 2
def baseEnd_5367981 : Nat := 918784799067555827783537

theorem tailTrace_5367981 : CollatzResearch.WordTrace tailWord_5367981 prefixEnd_5367981 918784799067555827783537 := by
  unfold tailWord_5367981
  simp only [CollatzResearch.WordTrace]
  refine ⟨195786351565729090011471797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130524234377152726674314531 195786351565729090011471797)
  ·
    refine ⟨18354970459287102188575481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195786351565729090011471797 18354970459287102188575481)
    ·
      refine ⟨13766227844465326641431611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18354970459287102188575481 13766227844465326641431611)
      ·
        refine ⟨20649341766697989962147417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13766227844465326641431611 20649341766697989962147417)
        ·
          refine ⟨15487006325023492471610563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20649341766697989962147417 15487006325023492471610563)
          ·
            refine ⟨23230509487535238707415845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15487006325023492471610563 23230509487535238707415845)
            ·
              refine ⟨4355720528912857257640471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23230509487535238707415845 4355720528912857257640471)
              ·
                refine ⟨6533580793369285886460707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4355720528912857257640471 6533580793369285886460707)
                ·
                  refine ⟨9800371190053928829691061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6533580793369285886460707 9800371190053928829691061)
                  ·
                    refine ⟨918784799067555827783537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9800371190053928829691061 918784799067555827783537)
                    ·
                      rfl

theorem cell23_5367981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_5367981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367981 prefixEnd_5367981 := by exact prefixLift 5367981
  have htrace : WordTrace (prefixWord ++ tailWord_5367981) baseStart_5367981 baseEnd_5367981 := by
    simpa [prefixWord, tailWord_5367981, baseEnd_5367981] using wordTrace_append hprefix tailTrace_5367981
  have hstable : (prefixWord ++ tailWord_5367981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367981).length < 2 ^ (prefixWord ++ tailWord_5367981).sum := by decide
  have hdescent : baseEnd_5367981 < baseStart_5367981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367994 : List Nat := [3, 1, 1, 1, 2, 2, 5, 2, 2, 4]
def baseStart_5367994 : Nat := 118140960795 + 5367994 * 2 ^ 59
def prefixEnd_5367994 : Nat := 4983230072969 + 3 ^ 40 * 5367994 * 2
def baseEnd_5367994 : Nat := 918787024150391977496017

theorem tailTrace_5367994 : CollatzResearch.WordTrace tailWord_5367994 prefixEnd_5367994 918787024150391977496017 := by
  unfold tailWord_5367994
  simp only [CollatzResearch.WordTrace]
  refine ⟨48946706428670498307923759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130524550476454662154463357 48946706428670498307923759)
  ·
    refine ⟨73420059643005747461885639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48946706428670498307923759 73420059643005747461885639)
    ·
      refine ⟨110130089464508621192828459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73420059643005747461885639 110130089464508621192828459)
      ·
        refine ⟨165195134196762931789242689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110130089464508621192828459 165195134196762931789242689)
        ·
          refine ⟨123896350647572198841932017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165195134196762931789242689 123896350647572198841932017)
          ·
            refine ⟨92922262985679149131449013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123896350647572198841932017 92922262985679149131449013)
            ·
              refine ⟨8711462154907420231073345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92922262985679149131449013 8711462154907420231073345)
              ·
                refine ⟨6533596616180565173305009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8711462154907420231073345 6533596616180565173305009)
                ·
                  refine ⟨4900197462135423879978757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6533596616180565173305009 4900197462135423879978757)
                  ·
                    refine ⟨918787024150391977496017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4900197462135423879978757 918787024150391977496017)
                    ·
                      rfl

theorem cell23_5367994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_5367994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367994 prefixEnd_5367994 := by exact prefixLift 5367994
  have htrace : WordTrace (prefixWord ++ tailWord_5367994) baseStart_5367994 baseEnd_5367994 := by
    simpa [prefixWord, tailWord_5367994, baseEnd_5367994] using wordTrace_append hprefix tailTrace_5367994
  have hstable : (prefixWord ++ tailWord_5367994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367994).length < 2 ^ (prefixWord ++ tailWord_5367994).sum := by decide
  have hdescent : baseEnd_5367994 < baseStart_5367994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368004 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_5368004 : Nat := 118140960795 + 5368004 * 2 ^ 59
def prefixEnd_5368004 : Nat := 4983230072969 + 3 ^ 40 * 5368004 * 2
def baseEnd_5368004 : Nat := 2756366207257720893363005

theorem tailTrace_5368004 : CollatzResearch.WordTrace tailWord_5368004 prefixEnd_5368004 2756366207257720893363005 := by
  unfold tailWord_5368004
  simp only [CollatzResearch.WordTrace]
  refine ⟨97893595222322882469779533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130524793629763843293039377 97893595222322882469779533)
  ·
    refine ⟨36710098208371080926167325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97893595222322882469779533 36710098208371080926167325)
    ·
      refine ⟨13766286828139155347312747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36710098208371080926167325 13766286828139155347312747)
      ·
        refine ⟨20649430242208733020969121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13766286828139155347312747 20649430242208733020969121)
        ·
          refine ⟨15487072681656549765726841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20649430242208733020969121 15487072681656549765726841)
          ·
            refine ⟨11615304511242412324295131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15487072681656549765726841 11615304511242412324295131)
            ·
              refine ⟨17422956766863618486442697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11615304511242412324295131 17422956766863618486442697)
              ·
                refine ⟨13067217575147713864832023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17422956766863618486442697 13067217575147713864832023)
                ·
                  refine ⟨19600826362721570797248035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13067217575147713864832023 19600826362721570797248035)
                  ·
                    refine ⟨29401239544082356195872053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19600826362721570797248035 29401239544082356195872053)
                    ·
                      refine ⟨2756366207257720893363005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29401239544082356195872053 2756366207257720893363005)
                      ·
                        rfl

theorem cell23_5368004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_5368004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368004 prefixEnd_5368004 := by exact prefixLift 5368004
  have htrace : WordTrace (prefixWord ++ tailWord_5368004) baseStart_5368004 baseEnd_5368004 := by
    simpa [prefixWord, tailWord_5368004, baseEnd_5368004] using wordTrace_append hprefix tailTrace_5368004
  have hstable : (prefixWord ++ tailWord_5368004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368004).length < 2 ^ (prefixWord ++ tailWord_5368004).sum := by decide
  have hdescent : baseEnd_5368004 < baseStart_5368004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368014 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_5368014 : Nat := 118140960795 + 5368014 * 2 ^ 59
def prefixEnd_5368014 : Nat := 4983230072969 + 3 ^ 40 * 5368014 * 2
def baseEnd_5368014 : Nat := 2756371342064265854237959

theorem tailTrace_5368014 : CollatzResearch.WordTrace tailWord_5368014 prefixEnd_5368014 2756371342064265854237959 := by
  unfold tailWord_5368014
  simp only [CollatzResearch.WordTrace]
  refine ⟨24473444396826192080927887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130525036783073024431615397 24473444396826192080927887)
  ·
    refine ⟨36710166595239288121391831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24473444396826192080927887 36710166595239288121391831)
    ·
      refine ⟨55065249892858932182087747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36710166595239288121391831 55065249892858932182087747)
      ·
        refine ⟨82597874839288398273131621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55065249892858932182087747 82597874839288398273131621)
        ·
          refine ⟨15487101532366574676212179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82597874839288398273131621 15487101532366574676212179)
          ·
            refine ⟨23230652298549862014318269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15487101532366574676212179 23230652298549862014318269)
            ·
              refine ⟨8711494611956198255369351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23230652298549862014318269 8711494611956198255369351)
              ·
                refine ⟨13067241917934297383054027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8711494611956198255369351 13067241917934297383054027)
                ·
                  refine ⟨19600862876901446074581041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13067241917934297383054027 19600862876901446074581041)
                  ·
                    refine ⟨14700647157676084555935781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19600862876901446074581041 14700647157676084555935781)
                    ·
                      refine ⟨2756371342064265854237959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14700647157676084555935781 2756371342064265854237959)
                      ·
                        rfl

theorem cell23_5368014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_5368014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368014 prefixEnd_5368014 := by exact prefixLift 5368014
  have htrace : WordTrace (prefixWord ++ tailWord_5368014) baseStart_5368014 baseEnd_5368014 := by
    simpa [prefixWord, tailWord_5368014, baseEnd_5368014] using wordTrace_append hprefix tailTrace_5368014
  have hstable : (prefixWord ++ tailWord_5368014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368014).length < 2 ^ (prefixWord ++ tailWord_5368014).sum := by decide
  have hdescent : baseEnd_5368014 < baseStart_5368014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368024 : List Nat := [2, 1, 2, 2, 4, 3, 2, 7]
def baseStart_5368024 : Nat := 118140960795 + 5368024 * 2 ^ 59
def prefixEnd_5368024 : Nat := 4983230072969 + 3 ^ 40 * 5368024 * 2
def baseEnd_5368024 : Nat := 102088017661881882041219

theorem tailTrace_5368024 : CollatzResearch.WordTrace tailWord_5368024 prefixEnd_5368024 102088017661881882041219 := by
  unfold tailWord_5368024
  simp only [CollatzResearch.WordTrace]
  refine ⟨97893959952286654177643563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130525279936382205570191417 97893959952286654177643563)
  ·
    refine ⟨146840939928429981266465345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97893959952286654177643563 146840939928429981266465345)
    ·
      refine ⟨110130704946322485949849009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146840939928429981266465345 110130704946322485949849009)
      ·
        refine ⟨82598028709741864462386757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110130704946322485949849009 82598028709741864462386757)
        ·
          refine ⟨15487130383076599586697517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82598028709741864462386757 15487130383076599586697517)
          ·
            refine ⟨5807673893653724845011569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15487130383076599586697517 5807673893653724845011569)
            ·
              refine ⟨4355755420240293633758677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5807673893653724845011569 4355755420240293633758677)
              ·
                refine ⟨102088017661881882041219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4355755420240293633758677 102088017661881882041219)
                ·
                  rfl

theorem cell23_5368024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 7].length) (baseStart_5368024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368024 prefixEnd_5368024 := by exact prefixLift 5368024
  have htrace : WordTrace (prefixWord ++ tailWord_5368024) baseStart_5368024 baseEnd_5368024 := by
    simpa [prefixWord, tailWord_5368024, baseEnd_5368024] using wordTrace_append hprefix tailTrace_5368024
  have hstable : (prefixWord ++ tailWord_5368024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368024).length < 2 ^ (prefixWord ++ tailWord_5368024).sum := by decide
  have hdescent : baseEnd_5368024 < baseStart_5368024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368068 : List Nat := [2, 3, 2, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_5368068 : Nat := 118140960795 + 5368068 * 2 ^ 59
def prefixEnd_5368068 : Nat := 4983230072969 + 3 ^ 40 * 5368068 * 2
def baseEnd_5368068 : Nat := 2756399070019608642962711

theorem tailTrace_5368068 : CollatzResearch.WordTrace tailWord_5368068 prefixEnd_5368068 2756399070019608642962711 := by
  unfold tailWord_5368068
  simp only [CollatzResearch.WordTrace]
  refine ⟨97894762358206951934944429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130526349810942602579925905 97894762358206951934944429)
  ·
    refine ⟨36710535884327606975604161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97894762358206951934944429 36710535884327606975604161)
    ·
      refine ⟨27532901913245705231703121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36710535884327606975604161 27532901913245705231703121)
      ·
        refine ⟨20649676434934278923777341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27532901913245705231703121 20649676434934278923777341)
        ·
          refine ⟨7743628663100354596416503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20649676434934278923777341 7743628663100354596416503)
          ·
            refine ⟨11615442994650531894624755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7743628663100354596416503 11615442994650531894624755)
            ·
              refine ⟨17423164491975797841937133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11615442994650531894624755 17423164491975797841937133)
              ·
                refine ⟨6533686684490924190726425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17423164491975797841937133 6533686684490924190726425)
                ·
                  refine ⟨4900265013368193143044819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6533686684490924190726425 4900265013368193143044819)
                  ·
                    refine ⟨7350397520052289714567229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4900265013368193143044819 7350397520052289714567229)
                    ·
                      refine ⟨2756399070019608642962711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7350397520052289714567229 2756399070019608642962711)
                      ·
                        rfl

theorem cell23_5368068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_5368068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368068 prefixEnd_5368068 := by exact prefixLift 5368068
  have htrace : WordTrace (prefixWord ++ tailWord_5368068) baseStart_5368068 baseEnd_5368068 := by
    simpa [prefixWord, tailWord_5368068, baseEnd_5368068] using wordTrace_append hprefix tailTrace_5368068
  have hstable : (prefixWord ++ tailWord_5368068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368068).length < 2 ^ (prefixWord ++ tailWord_5368068).sum := by decide
  have hdescent : baseEnd_5368068 < baseStart_5368068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368103 : List Nat := [1, 1, 8, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_5368103 : Nat := 118140960795 + 5368103 * 2 ^ 59
def prefixEnd_5368103 : Nat := 4983230072969 + 3 ^ 40 * 5368103 * 2
def baseEnd_5368103 : Nat := 2756417041842516006025051

theorem tailTrace_5368103 : CollatzResearch.WordTrace tailWord_5368103 prefixEnd_5368103 2756417041842516006025051 := by
  unfold tailWord_5368103
  simp only [CollatzResearch.WordTrace]
  refine ⟨195790801271287104847412963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130527200847524736564941975 195790801271287104847412963)
  ·
    refine ⟨293686201906930657271119445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195790801271287104847412963 293686201906930657271119445)
    ·
      refine ⟨3441635178596843639895931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 293686201906930657271119445 3441635178596843639895931)
      ·
        refine ⟨5162452767895265459843897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3441635178596843639895931 5162452767895265459843897)
        ·
          refine ⟨3871839575921449094882923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5162452767895265459843897 3871839575921449094882923)
          ·
            refine ⟨5807759363882173642324385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3871839575921449094882923 5807759363882173642324385)
            ·
              refine ⟨4355819522911630231743289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5807759363882173642324385 4355819522911630231743289)
              ·
                refine ⟨3266864642183722673807467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4355819522911630231743289 3266864642183722673807467)
                ·
                  refine ⟨4900296963275584010711201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3266864642183722673807467 4900296963275584010711201)
                  ·
                    refine ⟨3675222722456688008033401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4900296963275584010711201 3675222722456688008033401)
                    ·
                      refine ⟨2756417041842516006025051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3675222722456688008033401 2756417041842516006025051)
                      ·
                        rfl

theorem cell23_5368103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_5368103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368103 prefixEnd_5368103 := by exact prefixLift 5368103
  have htrace : WordTrace (prefixWord ++ tailWord_5368103) baseStart_5368103 baseEnd_5368103 := by
    simpa [prefixWord, tailWord_5368103, baseEnd_5368103] using wordTrace_append hprefix tailTrace_5368103
  have hstable : (prefixWord ++ tailWord_5368103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368103).length < 2 ^ (prefixWord ++ tailWord_5368103).sum := by decide
  have hdescent : baseEnd_5368103 < baseStart_5368103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368124 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_5368124 : Nat := 118140960795 + 5368124 * 2 ^ 59
def prefixEnd_5368124 : Nat := 4983230072969 + 3 ^ 40 * 5368124 * 2
def baseEnd_5368124 : Nat := 2756427824936260423862453

theorem tailTrace_5368124 : CollatzResearch.WordTrace tailWord_5368124 prefixEnd_5368124 2756427824936260423862453 := by
  unfold tailWord_5368124
  simp only [CollatzResearch.WordTrace]
  refine ⟨97895783602105512716963713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130527711469474016955951617 97895783602105512716963713)
  ·
    refine ⟨73421837701579134537722785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97895783602105512716963713 73421837701579134537722785)
    ·
      refine ⟨55066378276184350903292089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73421837701579134537722785 55066378276184350903292089)
      ·
        refine ⟨41299783707138263177469067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55066378276184350903292089 41299783707138263177469067)
        ·
          refine ⟨61949675560707394766203601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41299783707138263177469067 61949675560707394766203601)
          ·
            refine ⟨46462256670530546074652701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61949675560707394766203601 46462256670530546074652701)
            ·
              refine ⟨17423346251448954777994763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46462256670530546074652701 17423346251448954777994763)
              ·
                refine ⟨26135019377173432166992145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17423346251448954777994763 26135019377173432166992145)
                ·
                  refine ⟨19601264532880074125244109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26135019377173432166992145 19601264532880074125244109)
                  ·
                    refine ⟨7350474199830027796966541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19601264532880074125244109 7350474199830027796966541)
                    ·
                      refine ⟨2756427824936260423862453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7350474199830027796966541 2756427824936260423862453)
                      ·
                        rfl

theorem cell23_5368124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_5368124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368124 prefixEnd_5368124 := by exact prefixLift 5368124
  have htrace : WordTrace (prefixWord ++ tailWord_5368124) baseStart_5368124 baseEnd_5368124 := by
    simpa [prefixWord, tailWord_5368124, baseEnd_5368124] using wordTrace_append hprefix tailTrace_5368124
  have hstable : (prefixWord ++ tailWord_5368124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368124).length < 2 ^ (prefixWord ++ tailWord_5368124).sum := by decide
  have hdescent : baseEnd_5368124 < baseStart_5368124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368127 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 1, 7]
def baseStart_5368127 : Nat := 118140960795 + 5368127 * 2 ^ 59
def prefixEnd_5368127 : Nat := 4983230072969 + 3 ^ 40 * 5368127 * 2
def baseEnd_5368127 : Nat := 918809788459407970708313

theorem tailTrace_5368127 : CollatzResearch.WordTrace tailWord_5368127 prefixEnd_5368127 918809788459407970708313 := by
  unfold tailWord_5368127
  simp only [CollatzResearch.WordTrace]
  refine ⟨195791676623200156946286635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130527784415466771297524423 195791676623200156946286635)
  ·
    refine ⟨293687514934800235419429953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195791676623200156946286635 293687514934800235419429953)
    ·
      refine ⟨220265636201100176564572465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293687514934800235419429953 220265636201100176564572465)
      ·
        refine ⟨165199227150825132423429349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220265636201100176564572465 165199227150825132423429349)
        ·
          refine ⟨30974855090779712329393003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165199227150825132423429349 30974855090779712329393003)
          ·
            refine ⟨46462282636169568494089505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30974855090779712329393003 46462282636169568494089505)
            ·
              refine ⟨34846711977127176370567129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46462282636169568494089505 34846711977127176370567129)
              ·
                refine ⟨26135033982845382277925347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34846711977127176370567129 26135033982845382277925347)
                ·
                  refine ⟨39202550974268073416888021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26135033982845382277925347 39202550974268073416888021)
                  ·
                    refine ⟨918809788459407970708313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39202550974268073416888021 918809788459407970708313)
                    ·
                      rfl

theorem cell23_5368127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 7].length) (baseStart_5368127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368127 prefixEnd_5368127 := by exact prefixLift 5368127
  have htrace : WordTrace (prefixWord ++ tailWord_5368127) baseStart_5368127 baseEnd_5368127 := by
    simpa [prefixWord, tailWord_5368127, baseEnd_5368127] using wordTrace_append hprefix tailTrace_5368127
  have hstable : (prefixWord ++ tailWord_5368127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368127).length < 2 ^ (prefixWord ++ tailWord_5368127).sum := by decide
  have hdescent : baseEnd_5368127 < baseStart_5368127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368144 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 2, 5]
def baseStart_5368144 : Nat := 118140960795 + 5368144 * 2 ^ 59
def prefixEnd_5368144 : Nat := 4983230072969 + 3 ^ 40 * 5368144 * 2
def baseEnd_5368144 : Nat := 918812698183116781870787

theorem tailTrace_5368144 : CollatzResearch.WordTrace tailWord_5368144 prefixEnd_5368144 918812698183116781870787 := by
  unfold tailWord_5368144
  simp only [CollatzResearch.WordTrace]
  refine ⟨97896148332069284424827743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130528197776092379233103657 97896148332069284424827743)
  ·
    refine ⟨146844222498103926637241615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97896148332069284424827743 146844222498103926637241615)
    ·
      refine ⟨220266333747155889955862423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146844222498103926637241615 220266333747155889955862423)
      ·
        refine ⟨330399500620733834933793635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220266333747155889955862423 330399500620733834933793635)
        ·
          refine ⟨495599250931100752400690453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330399500620733834933793635 495599250931100752400690453)
          ·
            refine ⟨23231214887395347768782365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 495599250931100752400690453 23231214887395347768782365)
            ·
              refine ⟨8711705582773255413293387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23231214887395347768782365 8711705582773255413293387)
              ·
                refine ⟨13067558374159883119940081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8711705582773255413293387 13067558374159883119940081)
                ·
                  refine ⟨9800668780619912339955061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13067558374159883119940081 9800668780619912339955061)
                  ·
                    refine ⟨918812698183116781870787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9800668780619912339955061 918812698183116781870787)
                    ·
                      rfl

theorem cell23_5368144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 2, 5].length) (baseStart_5368144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368144 prefixEnd_5368144 := by exact prefixLift 5368144
  have htrace : WordTrace (prefixWord ++ tailWord_5368144) baseStart_5368144 baseEnd_5368144 := by
    simpa [prefixWord, tailWord_5368144, baseEnd_5368144] using wordTrace_append hprefix tailTrace_5368144
  have hstable : (prefixWord ++ tailWord_5368144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368144).length < 2 ^ (prefixWord ++ tailWord_5368144).sum := by decide
  have hdescent : baseEnd_5368144 < baseStart_5368144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368164 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_5368164 : Nat := 118140960795 + 5368164 * 2 ^ 59
def prefixEnd_5368164 : Nat := 4983230072969 + 3 ^ 40 * 5368164 * 2
def baseEnd_5368164 : Nat := 2756448364162440267362269

theorem tailTrace_5368164 : CollatzResearch.WordTrace tailWord_5368164 prefixEnd_5368164 2756448364162440267362269 := by
  unfold tailWord_5368164
  simp only [CollatzResearch.WordTrace]
  refine ⟨97896513062033056132691773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130528684082710741510255697 97896513062033056132691773)
  ·
    refine ⟨36711192398262396049759415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97896513062033056132691773 36711192398262396049759415)
    ·
      refine ⟨55066788597393594074639123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36711192398262396049759415 55066788597393594074639123)
      ·
        refine ⟨82600182896090391111958685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55066788597393594074639123 82600182896090391111958685)
        ·
          refine ⟨30975068586033896666984507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82600182896090391111958685 30975068586033896666984507)
          ·
            refine ⟨46462602879050845000476761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30975068586033896666984507 46462602879050845000476761)
            ·
              refine ⟨34846952159288133750357571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46462602879050845000476761 34846952159288133750357571)
              ·
                refine ⟨52270428238932200625536357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34846952159288133750357571 52270428238932200625536357)
                ·
                  refine ⟨9800705294799787617288067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52270428238932200625536357 9800705294799787617288067)
                  ·
                    refine ⟨14701057942199681425932101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9800705294799787617288067 14701057942199681425932101)
                    ·
                      refine ⟨2756448364162440267362269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14701057942199681425932101 2756448364162440267362269)
                      ·
                        rfl

theorem cell23_5368164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_5368164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368164 prefixEnd_5368164 := by exact prefixLift 5368164
  have htrace : WordTrace (prefixWord ++ tailWord_5368164) baseStart_5368164 baseEnd_5368164 := by
    simpa [prefixWord, tailWord_5368164, baseEnd_5368164] using wordTrace_append hprefix tailTrace_5368164
  have hstable : (prefixWord ++ tailWord_5368164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368164).length < 2 ^ (prefixWord ++ tailWord_5368164).sum := by decide
  have hdescent : baseEnd_5368164 < baseStart_5368164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368177 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_5368177 : Nat := 118140960795 + 5368177 * 2 ^ 59
def prefixEnd_5368177 : Nat := 4983230072969 + 3 ^ 40 * 5368177 * 2
def baseEnd_5368177 : Nat := 2756455039410948716499709

theorem tailTrace_5368177 : CollatzResearch.WordTrace tailWord_5368177 prefixEnd_5368177 2756455039410948716499709 := by
  unfold tailWord_5368177
  simp only [CollatzResearch.WordTrace]
  refine ⟨195793500273019015485606785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130529000182012676990404523 195793500273019015485606785)
  ·
    refine ⟨146845125204764261614205089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195793500273019015485606785 146845125204764261614205089)
    ·
      refine ⟨110133843903573196210653817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146845125204764261614205089 110133843903573196210653817)
      ·
        refine ⟨82600382927679897157990363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110133843903573196210653817 82600382927679897157990363)
        ·
          refine ⟨123900574391519845736985545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82600382927679897157990363 123900574391519845736985545)
          ·
            refine ⟨92925430793639884302739159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123900574391519845736985545 92925430793639884302739159)
            ·
              refine ⟨139388146190459826454108739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92925430793639884302739159 139388146190459826454108739)
              ·
                refine ⟨209082219285689739681163109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139388146190459826454108739 209082219285689739681163109)
                ·
                  refine ⟨39202916116066826190218083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209082219285689739681163109 39202916116066826190218083)
                  ·
                    refine ⟨58804374174100239285327125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39202916116066826190218083 58804374174100239285327125)
                    ·
                      refine ⟨2756455039410948716499709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58804374174100239285327125 2756455039410948716499709)
                      ·
                        rfl

theorem cell23_5368177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_5368177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368177 prefixEnd_5368177 := by exact prefixLift 5368177
  have htrace : WordTrace (prefixWord ++ tailWord_5368177) baseStart_5368177 baseEnd_5368177 := by
    simpa [prefixWord, tailWord_5368177, baseEnd_5368177] using wordTrace_append hprefix tailTrace_5368177
  have hstable : (prefixWord ++ tailWord_5368177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368177).length < 2 ^ (prefixWord ++ tailWord_5368177).sum := by decide
  have hdescent : baseEnd_5368177 < baseStart_5368177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368225 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 3, 4]
def baseStart_5368225 : Nat := 118140960795 + 5368225 * 2 ^ 59
def prefixEnd_5368225 : Nat := 4983230072969 + 3 ^ 40 * 5368225 * 2
def baseEnd_5368225 : Nat := 918826562160788176233163

theorem tailTrace_5368225 : CollatzResearch.WordTrace tailWord_5368225 prefixEnd_5368225 918826562160788176233163 := by
  unfold tailWord_5368225
  simp only [CollatzResearch.WordTrace]
  refine ⟨195795250976845119683354129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130530167317896746455569419 195795250976845119683354129)
  ·
    refine ⟨146846438232633839762515597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195795250976845119683354129 146846438232633839762515597)
    ·
      refine ⟨55067414337237689910943349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146846438232633839762515597 55067414337237689910943349)
      ·
        refine ⟨5162570094116033429150939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55067414337237689910943349 5162570094116033429150939)
        ·
          refine ⟨7743855141174050143726409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5162570094116033429150939 7743855141174050143726409)
          ·
            refine ⟨5807891355880537607794807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7743855141174050143726409 5807891355880537607794807)
            ·
              refine ⟨8711837033820806411692211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5807891355880537607794807 8711837033820806411692211)
              ·
                refine ⟨13067755550731209617538317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8711837033820806411692211 13067755550731209617538317)
                ·
                  refine ⟨4900408331524203606576869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13067755550731209617538317 4900408331524203606576869)
                  ·
                    refine ⟨918826562160788176233163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4900408331524203606576869 918826562160788176233163)
                    ·
                      rfl

theorem cell23_5368225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_5368225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368225 prefixEnd_5368225 := by exact prefixLift 5368225
  have htrace : WordTrace (prefixWord ++ tailWord_5368225) baseStart_5368225 baseEnd_5368225 := by
    simpa [prefixWord, tailWord_5368225, baseEnd_5368225] using wordTrace_append hprefix tailTrace_5368225
  have hstable : (prefixWord ++ tailWord_5368225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368225).length < 2 ^ (prefixWord ++ tailWord_5368225).sum := by decide
  have hdescent : baseEnd_5368225 < baseStart_5368225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368264 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 3, 6]
def baseStart_5368264 : Nat := 118140960795 + 5368264 * 2 ^ 59
def prefixEnd_5368264 : Nat := 4983230072969 + 3 ^ 40 * 5368264 * 2
def baseEnd_5368264 : Nat := 918833237409296625370603

theorem tailTrace_5368264 : CollatzResearch.WordTrace tailWord_5368264 prefixEnd_5368264 918833237409296625370603 := by
  unfold tailWord_5368264
  simp only [CollatzResearch.WordTrace]
  refine ⟨97898336711851914672011923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130531115615802552896015897 97898336711851914672011923)
  ·
    refine ⟨146847505067777872008017885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97898336711851914672011923 146847505067777872008017885)
    ·
      refine ⟨55067814400416702003006707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146847505067777872008017885 55067814400416702003006707)
      ·
        refine ⟨82601721600625053004510061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55067814400416702003006707 82601721600625053004510061)
        ·
          refine ⟨30975645600234394876691273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82601721600625053004510061 30975645600234394876691273)
          ·
            refine ⟨23231734200175796157518455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30975645600234394876691273 23231734200175796157518455)
            ·
              refine ⟨34847601300263694236277683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23231734200175796157518455 34847601300263694236277683)
              ·
                refine ⟨52271401950395541354416525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34847601300263694236277683 52271401950395541354416525)
                ·
                  refine ⟨19601775731398328007906197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52271401950395541354416525 19601775731398328007906197)
                  ·
                    refine ⟨918833237409296625370603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19601775731398328007906197 918833237409296625370603)
                    ·
                      rfl

theorem cell23_5368264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_5368264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368264 prefixEnd_5368264 := by exact prefixLift 5368264
  have htrace : WordTrace (prefixWord ++ tailWord_5368264) baseStart_5368264 baseEnd_5368264 := by
    simpa [prefixWord, tailWord_5368264, baseEnd_5368264] using wordTrace_append hprefix tailTrace_5368264
  have hstable : (prefixWord ++ tailWord_5368264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368264).length < 2 ^ (prefixWord ++ tailWord_5368264).sum := by decide
  have hdescent : baseEnd_5368264 < baseStart_5368264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368288 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 3, 2, 2]
def baseStart_5368288 : Nat := 118140960795 + 5368288 * 2 ^ 59
def prefixEnd_5368288 : Nat := 4983230072969 + 3 ^ 40 * 5368288 * 2
def baseEnd_5368288 : Nat := 2756512035763597782211699

theorem tailTrace_5368288 : CollatzResearch.WordTrace tailWord_5368288 prefixEnd_5368288 2756512035763597782211699 := by
  unfold tailWord_5368288
  simp only [CollatzResearch.WordTrace]
  refine ⟨97898774387808440721448759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130531699183744587628598345 97898774387808440721448759)
  ·
    refine ⟨146848161581712661082173139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97898774387808440721448759 146848161581712661082173139)
    ·
      refine ⟨220272242372568991623259709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146848161581712661082173139 220272242372568991623259709)
      ·
        refine ⟨82602090889713371858722391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220272242372568991623259709 82602090889713371858722391)
        ·
          refine ⟨123903136334570057788083587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82602090889713371858722391 123903136334570057788083587)
          ·
            refine ⟨185854704501855086682125381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123903136334570057788083587 185854704501855086682125381)
            ·
              refine ⟨34847757094097828752898509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185854704501855086682125381 34847757094097828752898509)
              ·
                refine ⟨13067908910286685782336941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34847757094097828752898509 13067908910286685782336941)
                ·
                  refine ⟨4900465841357507168376353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13067908910286685782336941 4900465841357507168376353)
                  ·
                    refine ⟨3675349381018130376282265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4900465841357507168376353 3675349381018130376282265)
                    ·
                      refine ⟨2756512035763597782211699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3675349381018130376282265 2756512035763597782211699)
                      ·
                        rfl

theorem cell23_5368288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_5368288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368288 prefixEnd_5368288 := by exact prefixLift 5368288
  have htrace : WordTrace (prefixWord ++ tailWord_5368288) baseStart_5368288 baseEnd_5368288 := by
    simpa [prefixWord, tailWord_5368288, baseEnd_5368288] using wordTrace_append hprefix tailTrace_5368288
  have hstable : (prefixWord ++ tailWord_5368288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368288).length < 2 ^ (prefixWord ++ tailWord_5368288).sum := by decide
  have hdescent : baseEnd_5368288 < baseStart_5368288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368298 : List Nat := [3, 1, 3, 1, 3, 1, 2, 3, 2, 4]
def baseStart_5368298 : Nat := 118140960795 + 5368298 * 2 ^ 59
def prefixEnd_5368298 : Nat := 4983230072969 + 3 ^ 40 * 5368298 * 2
def baseEnd_5368298 : Nat := 918839056856714247695551

theorem tailTrace_5368298 : CollatzResearch.WordTrace tailWord_5368298 prefixEnd_5368298 918839056856714247695551 := by
  unfold tailWord_5368298
  simp only [CollatzResearch.WordTrace]
  refine ⟨48949478376395163287690387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130531942337053768767174365 48949478376395163287690387)
  ·
    refine ⟨73424217564592744931535581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48949478376395163287690387 73424217564592744931535581)
    ·
      refine ⟨27534081586722279349325843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73424217564592744931535581 27534081586722279349325843)
      ·
        refine ⟨41301122380083419023988765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27534081586722279349325843 41301122380083419023988765)
        ·
          refine ⟨15487920892531282133995787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41301122380083419023988765 15487920892531282133995787)
          ·
            refine ⟨23231881338796923200993681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15487920892531282133995787 23231881338796923200993681)
            ·
              refine ⟨17423911004097692400745261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23231881338796923200993681 17423911004097692400745261)
              ·
                refine ⟨6533966626536634650279473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17423911004097692400745261 6533966626536634650279473)
                ·
                  refine ⟨4900474969902475987709605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6533966626536634650279473 4900474969902475987709605)
                  ·
                    refine ⟨918839056856714247695551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4900474969902475987709605 918839056856714247695551)
                    ·
                      rfl

theorem cell23_5368298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_5368298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368298 prefixEnd_5368298 := by exact prefixLift 5368298
  have htrace : WordTrace (prefixWord ++ tailWord_5368298) baseStart_5368298 baseEnd_5368298 := by
    simpa [prefixWord, tailWord_5368298, baseEnd_5368298] using wordTrace_append hprefix tailTrace_5368298
  have hstable : (prefixWord ++ tailWord_5368298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368298).length < 2 ^ (prefixWord ++ tailWord_5368298).sum := by decide
  have hdescent : baseEnd_5368298 < baseStart_5368298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368309 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_5368309 : Nat := 118140960795 + 5368309 * 2 ^ 59
def prefixEnd_5368309 : Nat := 4983230072969 + 3 ^ 40 * 5368309 * 2
def baseEnd_5368309 : Nat := 2756522818857342200049103

theorem tailTrace_5368309 : CollatzResearch.WordTrace tailWord_5368309 prefixEnd_5368309 2756522818857342200049103 := by
  unfold tailWord_5368309
  simp only [CollatzResearch.WordTrace]
  refine ⟨195798314708540802029411981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130532209805693868019607987 195798314708540802029411981)
  ·
    refine ⟨73424368015702800761029493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195798314708540802029411981 73424368015702800761029493)
    ·
      refine ⟨6883534501472137571346515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73424368015702800761029493 6883534501472137571346515)
      ·
        refine ⟨10325301752208206357019773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6883534501472137571346515 10325301752208206357019773)
        ·
          refine ⟨3871988157078077383882415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10325301752208206357019773 3871988157078077383882415)
          ·
            refine ⟨5807982235617116075823623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3871988157078077383882415 5807982235617116075823623)
            ·
              refine ⟨8711973353425674113735435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5807982235617116075823623 8711973353425674113735435)
              ·
                refine ⟨13067960030138511170603153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8711973353425674113735435 13067960030138511170603153)
                ·
                  refine ⟨9800970022603883377952365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13067960030138511170603153 9800970022603883377952365)
                  ·
                    refine ⟨3675363758476456266732137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9800970022603883377952365 3675363758476456266732137)
                    ·
                      refine ⟨2756522818857342200049103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3675363758476456266732137 2756522818857342200049103)
                      ·
                        rfl

theorem cell23_5368309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_5368309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368309 prefixEnd_5368309 := by exact prefixLift 5368309
  have htrace : WordTrace (prefixWord ++ tailWord_5368309) baseStart_5368309 baseEnd_5368309 := by
    simpa [prefixWord, tailWord_5368309, baseEnd_5368309] using wordTrace_append hprefix tailTrace_5368309
  have hstable : (prefixWord ++ tailWord_5368309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368309).length < 2 ^ (prefixWord ++ tailWord_5368309).sum := by decide
  have hdescent : baseEnd_5368309 < baseStart_5368309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368364 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_5368364 : Nat := 118140960795 + 5368364 * 2 ^ 59
def prefixEnd_5368364 : Nat := 4983230072969 + 3 ^ 40 * 5368364 * 2
def baseEnd_5368364 : Nat := 2756551060293339484861349

theorem tailTrace_5368364 : CollatzResearch.WordTrace tailWord_5368364 prefixEnd_5368364 2756551060293339484861349 := by
  unfold tailWord_5368364
  simp only [CollatzResearch.WordTrace]
  refine ⟨97900160361670773211332073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130533547148894364281776097 97900160361670773211332073)
  ·
    refine ⟨73425120271253079908499055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97900160361670773211332073 73425120271253079908499055)
    ·
      refine ⟨110137680406879619862748583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73425120271253079908499055 110137680406879619862748583)
      ·
        refine ⟨165206520610319429794122875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110137680406879619862748583 165206520610319429794122875)
        ·
          refine ⟨247809780915479144691184313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165206520610319429794122875 247809780915479144691184313)
          ·
            refine ⟨185857335686609358518388235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247809780915479144691184313 185857335686609358518388235)
            ·
              refine ⟨278786003529914037777582353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185857335686609358518388235 278786003529914037777582353)
              ·
                refine ⟨209089502647435528333186765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278786003529914037777582353 209089502647435528333186765)
                ·
                  refine ⟨78408563492788323124945037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209089502647435528333186765 78408563492788323124945037)
                  ·
                    refine ⟨29403211309795621171854389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78408563492788323124945037 29403211309795621171854389)
                    ·
                      refine ⟨2756551060293339484861349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29403211309795621171854389 2756551060293339484861349)
                      ·
                        rfl

theorem cell23_5368364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_5368364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368364 prefixEnd_5368364 := by exact prefixLift 5368364
  have htrace : WordTrace (prefixWord ++ tailWord_5368364) baseStart_5368364 baseEnd_5368364 := by
    simpa [prefixWord, tailWord_5368364, baseEnd_5368364] using wordTrace_append hprefix tailTrace_5368364
  have hstable : (prefixWord ++ tailWord_5368364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368364).length < 2 ^ (prefixWord ++ tailWord_5368364).sum := by decide
  have hdescent : baseEnd_5368364 < baseStart_5368364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368381 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_5368381 : Nat := 118140960795 + 5368381 * 2 ^ 59
def prefixEnd_5368381 : Nat := 4983230072969 + 3 ^ 40 * 5368381 * 2
def baseEnd_5368381 : Nat := 2756559789464465918348771

theorem tailTrace_5368381 : CollatzResearch.WordTrace tailWord_5368381 prefixEnd_5368381 2756559789464465918348771 := by
  unfold tailWord_5368381
  simp only [CollatzResearch.WordTrace]
  refine ⟨195800940764279958326032997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130533960509519972217355331 195800940764279958326032997)
  ·
    refine ⟨36712676393302492186131187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195800940764279958326032997 36712676393302492186131187)
    ·
      refine ⟨55069014589953738279196781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36712676393302492186131187 55069014589953738279196781)
      ·
        refine ⟨20650880471232651854698793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55069014589953738279196781 20650880471232651854698793)
        ·
          refine ⟨15488160353424488891024095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20650880471232651854698793 15488160353424488891024095)
          ·
            refine ⟨23232240530136733336536143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15488160353424488891024095 23232240530136733336536143)
            ·
              refine ⟨34848360795205100004804215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23232240530136733336536143 34848360795205100004804215)
              ·
                refine ⟨52272541192807650007206323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34848360795205100004804215 52272541192807650007206323)
                ·
                  refine ⟨78408811789211475010809485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52272541192807650007206323 78408811789211475010809485)
                  ·
                    refine ⟨29403304420954303129053557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78408811789211475010809485 29403304420954303129053557)
                    ·
                      refine ⟨2756559789464465918348771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29403304420954303129053557 2756559789464465918348771)
                      ·
                        rfl

theorem cell23_5368381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_5368381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368381 prefixEnd_5368381 := by exact prefixLift 5368381
  have htrace : WordTrace (prefixWord ++ tailWord_5368381) baseStart_5368381 baseEnd_5368381 := by
    simpa [prefixWord, tailWord_5368381, baseEnd_5368381] using wordTrace_append hprefix tailTrace_5368381
  have hstable : (prefixWord ++ tailWord_5368381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368381).length < 2 ^ (prefixWord ++ tailWord_5368381).sum := by decide
  have hdescent : baseEnd_5368381 < baseStart_5368381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368384 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 9]
def baseStart_5368384 : Nat := 118140960795 + 5368384 * 2 ^ 59
def prefixEnd_5368384 : Nat := 4983230072969 + 3 ^ 40 * 5368384 * 2
def baseEnd_5368384 : Nat := 306284592211825489623473

theorem tailTrace_5368384 : CollatzResearch.WordTrace tailWord_5368384 prefixEnd_5368384 306284592211825489623473 := by
  unfold tailWord_5368384
  simp only [CollatzResearch.WordTrace]
  refine ⟨97900525091634544919196103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130534033455512726558928137 97900525091634544919196103)
  ·
    refine ⟨146850787637451817378794155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97900525091634544919196103 146850787637451817378794155)
    ·
      refine ⟨220276181456177726068191233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146850787637451817378794155 220276181456177726068191233)
      ·
        refine ⟨165207136092133294551143425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220276181456177726068191233 165207136092133294551143425)
        ·
          refine ⟨123905352069099970913357569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165207136092133294551143425 123905352069099970913357569)
          ·
            refine ⟨92929014051824978185018177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123905352069099970913357569 92929014051824978185018177)
            ·
              refine ⟨69696760538868733638763633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92929014051824978185018177 69696760538868733638763633)
              ·
                refine ⟨52272570404151550229072725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69696760538868733638763633 52272570404151550229072725)
                ·
                  refine ⟨306284592211825489623473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52272570404151550229072725 306284592211825489623473)
                  ·
                    rfl

theorem cell23_5368384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 9].length) (baseStart_5368384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368384 prefixEnd_5368384 := by exact prefixLift 5368384
  have htrace : WordTrace (prefixWord ++ tailWord_5368384) baseStart_5368384 baseEnd_5368384 := by
    simpa [prefixWord, tailWord_5368384, baseEnd_5368384] using wordTrace_append hprefix tailTrace_5368384
  have hstable : (prefixWord ++ tailWord_5368384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368384).length < 2 ^ (prefixWord ++ tailWord_5368384).sum := by decide
  have hdescent : baseEnd_5368384 < baseStart_5368384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368401 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 7]
def baseStart_5368401 : Nat := 118140960795 + 5368401 * 2 ^ 59
def prefixEnd_5368401 : Nat := 4983230072969 + 3 ^ 40 * 5368401 * 2
def baseEnd_5368401 : Nat := 306285562119728426677631

theorem tailTrace_5368401 : CollatzResearch.WordTrace tailWord_5368401 prefixEnd_5368401 306285562119728426677631 := by
  unfold tailWord_5368401
  simp only [CollatzResearch.WordTrace]
  refine ⟨195801670224207501741761057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130534446816138334494507371 195801670224207501741761057)
  ·
    refine ⟨146851252668155626306320793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195801670224207501741761057 146851252668155626306320793)
    ·
      refine ⟨110138439501116719729740595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146851252668155626306320793 110138439501116719729740595)
      ·
        refine ⟨165207659251675079594610893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110138439501116719729740595 165207659251675079594610893)
        ·
          refine ⟨61952872219378154847979085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165207659251675079594610893 61952872219378154847979085)
          ·
            refine ⟨23232327082266808067992157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61952872219378154847979085 23232327082266808067992157)
            ·
              refine ⟨8712122655850053025497059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23232327082266808067992157 8712122655850053025497059)
              ·
                refine ⟨13068183983775079538245589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8712122655850053025497059 13068183983775079538245589)
                ·
                  refine ⟨306285562119728426677631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13068183983775079538245589 306285562119728426677631)
                  ·
                    rfl

theorem cell23_5368401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 7].length) (baseStart_5368401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368401 prefixEnd_5368401 := by exact prefixLift 5368401
  have htrace : WordTrace (prefixWord ++ tailWord_5368401) baseStart_5368401 baseEnd_5368401 := by
    simpa [prefixWord, tailWord_5368401, baseEnd_5368401] using wordTrace_append hprefix tailTrace_5368401
  have hstable : (prefixWord ++ tailWord_5368401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368401).length < 2 ^ (prefixWord ++ tailWord_5368401).sum := by decide
  have hdescent : baseEnd_5368401 < baseStart_5368401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368431 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 2, 5]
def baseStart_5368431 : Nat := 118140960795 + 5368431 * 2 ^ 59
def prefixEnd_5368431 : Nat := 4983230072969 + 3 ^ 40 * 5368431 * 2
def baseEnd_5368431 : Nat := 918861821165730240907847

theorem tailTrace_5368431 : CollatzResearch.WordTrace tailWord_5368431 prefixEnd_5368431 918861821165730240907847 := by
  unfold tailWord_5368431
  simp only [CollatzResearch.WordTrace]
  refine ⟨195802764414098816865353147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130535176276065877910235431 195802764414098816865353147)
  ·
    refine ⟨293704146621148225298029721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195802764414098816865353147 293704146621148225298029721)
    ·
      refine ⟨220278109965861168973522291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293704146621148225298029721 220278109965861168973522291)
      ·
        refine ⟨330417164948791753460283437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220278109965861168973522291 330417164948791753460283437)
        ·
          refine ⟨123906436855796907547606289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330417164948791753460283437 123906436855796907547606289)
          ·
            refine ⟨92929827641847680660704717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123906436855796907547606289 92929827641847680660704717)
            ·
              refine ⟨34848685365692880247764269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92929827641847680660704717 34848685365692880247764269)
              ·
                refine ⟨13068257012134830092911601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34848685365692880247764269 13068257012134830092911601)
                ·
                  refine ⟨9801192759101122569683701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13068257012134830092911601 9801192759101122569683701)
                  ·
                    refine ⟨918861821165730240907847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9801192759101122569683701 918861821165730240907847)
                    ·
                      rfl

theorem cell23_5368431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 5].length) (baseStart_5368431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368431 prefixEnd_5368431 := by exact prefixLift 5368431
  have htrace : WordTrace (prefixWord ++ tailWord_5368431) baseStart_5368431 baseEnd_5368431 := by
    simpa [prefixWord, tailWord_5368431, baseEnd_5368431] using wordTrace_append hprefix tailTrace_5368431
  have hstable : (prefixWord ++ tailWord_5368431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368431).length < 2 ^ (prefixWord ++ tailWord_5368431).sum := by decide
  have hdescent : baseEnd_5368431 < baseStart_5368431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368441 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 5]
def baseStart_5368441 : Nat := 118140960795 + 5368441 * 2 ^ 59
def prefixEnd_5368441 : Nat := 4983230072969 + 3 ^ 40 * 5368441 * 2
def baseEnd_5368441 : Nat := 2756590598303735683598495

theorem tailTrace_5368441 : CollatzResearch.WordTrace tailWord_5368441 prefixEnd_5368441 2756590598303735683598495 := by
  unfold tailWord_5368441
  simp only [CollatzResearch.WordTrace]
  refine ⟨195803129144062588573217177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130535419429375059048811451 195803129144062588573217177)
  ·
    refine ⟨146852346858046941429912883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195803129144062588573217177 146852346858046941429912883)
    ·
      refine ⟨220278520287070412144869325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146852346858046941429912883 220278520287070412144869325)
      ·
        refine ⟨82604445107651404554325997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220278520287070412144869325 82604445107651404554325997)
        ·
          refine ⟨30976666915369276707872249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82604445107651404554325997 30976666915369276707872249)
          ·
            refine ⟨23232500186526957530904187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30976666915369276707872249 23232500186526957530904187)
            ·
              refine ⟨34848750279790436296356281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23232500186526957530904187 34848750279790436296356281)
              ·
                refine ⟨26136562709842827222267211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34848750279790436296356281 26136562709842827222267211)
                ·
                  refine ⟨39204844064764240833400817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26136562709842827222267211 39204844064764240833400817)
                  ·
                    refine ⟨29403633048573180625050613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39204844064764240833400817 29403633048573180625050613)
                    ·
                      refine ⟨2756590598303735683598495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29403633048573180625050613 2756590598303735683598495)
                      ·
                        rfl

theorem cell23_5368441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_5368441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368441 prefixEnd_5368441 := by exact prefixLift 5368441
  have htrace : WordTrace (prefixWord ++ tailWord_5368441) baseStart_5368441 baseEnd_5368441 := by
    simpa [prefixWord, tailWord_5368441, baseEnd_5368441] using wordTrace_append hprefix tailTrace_5368441
  have hstable : (prefixWord ++ tailWord_5368441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368441).length < 2 ^ (prefixWord ++ tailWord_5368441).sum := by decide
  have hdescent : baseEnd_5368441 < baseStart_5368441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368452 : List Nat := [2, 3, 2, 1, 3, 3, 2, 2, 5]
def baseStart_5368452 : Nat := 118140960795 + 5368452 * 2 ^ 59
def prefixEnd_5368452 : Nat := 4983230072969 + 3 ^ 40 * 5368452 * 2
def baseEnd_5368452 : Nat := 306288471843437237840105

theorem tailTrace_5368452 : CollatzResearch.WordTrace tailWord_5368452 prefixEnd_5368452 306288471843437237840105 := by
  unfold tailWord_5368452
  simp only [CollatzResearch.WordTrace]
  refine ⟨97901765173511368725933805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130535686898015158301245073 97901765173511368725933805)
  ·
    refine ⟨36713161940066763272225177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97901765173511368725933805 36713161940066763272225177)
    ·
      refine ⟨27534871455050072454168883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36713161940066763272225177 27534871455050072454168883)
      ·
        refine ⟨41302307182575108681253325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27534871455050072454168883 41302307182575108681253325)
        ·
          refine ⟨15488365193465665755469997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41302307182575108681253325 15488365193465665755469997)
          ·
            refine ⟨5808136947549624658301249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15488365193465665755469997 5808136947549624658301249)
            ·
              refine ⟨4356102710662218493725937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5808136947549624658301249 4356102710662218493725937)
              ·
                refine ⟨3267077032996663870294453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4356102710662218493725937 3267077032996663870294453)
                ·
                  refine ⟨306288471843437237840105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3267077032996663870294453 306288471843437237840105)
                  ·
                    rfl

theorem cell23_5368452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_5368452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368452 prefixEnd_5368452 := by exact prefixLift 5368452
  have htrace : WordTrace (prefixWord ++ tailWord_5368452) baseStart_5368452 baseEnd_5368452 := by
    simpa [prefixWord, tailWord_5368452, baseEnd_5368452] using wordTrace_append hprefix tailTrace_5368452
  have hstable : (prefixWord ++ tailWord_5368452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368452).length < 2 ^ (prefixWord ++ tailWord_5368452).sum := by decide
  have hdescent : baseEnd_5368452 < baseStart_5368452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368495 : List Nat := [1, 1, 2, 1, 2, 5, 1, 5, 1, 4]
def baseStart_5368495 : Nat := 118140960795 + 5368495 * 2 ^ 59
def prefixEnd_5368495 : Nat := 4983230072969 + 3 ^ 40 * 5368495 * 2
def baseEnd_5368495 : Nat := 918872775419692824107749

theorem tailTrace_5368495 : CollatzResearch.WordTrace tailWord_5368495 prefixEnd_5368495 918872775419692824107749 := by
  unfold tailWord_5368495
  simp only [CollatzResearch.WordTrace]
  refine ⟨195805098685866955795682939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130536732457244637197121959 195805098685866955795682939)
  ·
    refine ⟨293707648028800433693524409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195805098685866955795682939 293707648028800433693524409)
    ·
      refine ⟨220280736021600325270143307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293707648028800433693524409 220280736021600325270143307)
      ·
        refine ⟨330421104032400487905214961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220280736021600325270143307 330421104032400487905214961)
        ·
          refine ⟨247815828024300365928911221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330421104032400487905214961 247815828024300365928911221)
          ·
            refine ⟨23232733877278159305835427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 247815828024300365928911221 23232733877278159305835427)
            ·
              refine ⟨34849100815917238958753141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23232733877278159305835427 34849100815917238958753141)
              ·
                refine ⟨3267103201492241152383107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34849100815917238958753141 3267103201492241152383107)
                ·
                  refine ⟨4900654802238361728574661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267103201492241152383107 4900654802238361728574661)
                  ·
                    refine ⟨918872775419692824107749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4900654802238361728574661 918872775419692824107749)
                    ·
                      rfl

theorem cell23_5368495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 1, 4].length) (baseStart_5368495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368495 prefixEnd_5368495 := by exact prefixLift 5368495
  have htrace : WordTrace (prefixWord ++ tailWord_5368495) baseStart_5368495 baseEnd_5368495 := by
    simpa [prefixWord, tailWord_5368495, baseEnd_5368495] using wordTrace_append hprefix tailTrace_5368495
  have hstable : (prefixWord ++ tailWord_5368495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368495).length < 2 ^ (prefixWord ++ tailWord_5368495).sum := by decide
  have hdescent : baseEnd_5368495 < baseStart_5368495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368511 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 6]
def baseStart_5368511 : Nat := 118140960795 + 5368511 * 2 ^ 59
def prefixEnd_5368511 : Nat := 4983230072969 + 3 ^ 40 * 5368511 * 2
def baseEnd_5368511 : Nat := 2756626541949550409723173

theorem tailTrace_5368511 : CollatzResearch.WordTrace tailWord_5368511 prefixEnd_5368511 2756626541949550409723173 := by
  unfold tailWord_5368511
  simp only [CollatzResearch.WordTrace]
  refine ⟨195805682253808990528265387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130537121502539327018843591 195805682253808990528265387)
  ·
    refine ⟨293708523380713485792398081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195805682253808990528265387 293708523380713485792398081)
    ·
      refine ⟨220281392535535114344298561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293708523380713485792398081 220281392535535114344298561)
      ·
        refine ⟨165211044401651335758223921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220281392535535114344298561 165211044401651335758223921)
        ·
          refine ⟨123908283301238501818667941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165211044401651335758223921 123908283301238501818667941)
          ·
            refine ⟨23232803118982219091000239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123908283301238501818667941 23232803118982219091000239)
            ·
              refine ⟨34849204678473328636500359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23232803118982219091000239 34849204678473328636500359)
              ·
                refine ⟨52273807017709992954750539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34849204678473328636500359 52273807017709992954750539)
                ·
                  refine ⟨78410710526564989432125809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52273807017709992954750539 78410710526564989432125809)
                  ·
                    refine ⟨58808032894923742074094357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78410710526564989432125809 58808032894923742074094357)
                    ·
                      refine ⟨2756626541949550409723173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58808032894923742074094357 2756626541949550409723173)
                      ·
                        rfl

theorem cell23_5368511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_5368511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368511 prefixEnd_5368511 := by exact prefixLift 5368511
  have htrace : WordTrace (prefixWord ++ tailWord_5368511) baseStart_5368511 baseEnd_5368511 := by
    simpa [prefixWord, tailWord_5368511, baseEnd_5368511] using wordTrace_append hprefix tailTrace_5368511
  have hstable : (prefixWord ++ tailWord_5368511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368511).length < 2 ^ (prefixWord ++ tailWord_5368511).sum := by decide
  have hdescent : baseEnd_5368511 < baseStart_5368511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368535 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 3, 1, 3]
def baseStart_5368535 : Nat := 118140960795 + 5368535 * 2 ^ 59
def prefixEnd_5368535 : Nat := 4983230072969 + 3 ^ 40 * 5368535 * 2
def baseEnd_5368535 : Nat := 2756638865485258315823063

theorem tailTrace_5368535 : CollatzResearch.WordTrace tailWord_5368535 prefixEnd_5368535 2756638865485258315823063 := by
  unfold tailWord_5368535
  simp only [CollatzResearch.WordTrace]
  refine ⟨195806557605722042627139059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130537705070481361751426039 195806557605722042627139059)
  ·
    refine ⟨293709836408583063940708589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195806557605722042627139059 293709836408583063940708589)
    ·
      refine ⟨110141188653218648977765721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293709836408583063940708589 110141188653218648977765721)
      ·
        refine ⟨82605891489913986733324291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110141188653218648977765721 82605891489913986733324291)
        ·
          refine ⟨123908837234870980099986437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82605891489913986733324291 123908837234870980099986437)
          ·
            refine ⟨23232906981538308768747457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123908837234870980099986437 23232906981538308768747457)
            ·
              refine ⟨17424680236153731576560593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23232906981538308768747457 17424680236153731576560593)
              ·
                refine ⟨13068510177115298682420445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17424680236153731576560593 13068510177115298682420445)
                ·
                  refine ⟨4900691316418237005907667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13068510177115298682420445 4900691316418237005907667)
                  ·
                    refine ⟨7351036974627355508861501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4900691316418237005907667 7351036974627355508861501)
                    ·
                      refine ⟨2756638865485258315823063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7351036974627355508861501 2756638865485258315823063)
                      ·
                        rfl

theorem cell23_5368535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_5368535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368535 prefixEnd_5368535 := by exact prefixLift 5368535
  have htrace : WordTrace (prefixWord ++ tailWord_5368535) baseStart_5368535 baseEnd_5368535 := by
    simpa [prefixWord, tailWord_5368535, baseEnd_5368535] using wordTrace_append hprefix tailTrace_5368535
  have hstable : (prefixWord ++ tailWord_5368535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368535).length < 2 ^ (prefixWord ++ tailWord_5368535).sum := by decide
  have hdescent : baseEnd_5368535 < baseStart_5368535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368545 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 1, 5, 2]
def baseStart_5368545 : Nat := 118140960795 + 5368545 * 2 ^ 59
def prefixEnd_5368545 : Nat := 4983230072969 + 3 ^ 40 * 5368545 * 2
def baseEnd_5368545 : Nat := 2756644000291803276698017

theorem tailTrace_5368545 : CollatzResearch.WordTrace tailWord_5368545 prefixEnd_5368545 2756644000291803276698017 := by
  unfold tailWord_5368545
  simp only [CollatzResearch.WordTrace]
  refine ⟨195806922335685814335003089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130537948223790542890002059 195806922335685814335003089)
  ·
    refine ⟨146855191751764360751252317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195806922335685814335003089 146855191751764360751252317)
    ·
      refine ⟨55070696906911635281719619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146855191751764360751252317 55070696906911635281719619)
      ·
        refine ⟨82606045360367452922579429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55070696906911635281719619 82606045360367452922579429)
        ·
          refine ⟨15488633505068897422983643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82606045360367452922579429 15488633505068897422983643)
          ·
            refine ⟨23232950257603346134475465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15488633505068897422983643 23232950257603346134475465)
            ·
              refine ⟨17424712693202509600856599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23232950257603346134475465 17424712693202509600856599)
              ·
                refine ⟨26137069039803764401284899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17424712693202509600856599 26137069039803764401284899)
                ·
                  refine ⟨39205603559705646601927349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26137069039803764401284899 39205603559705646601927349)
                  ·
                    refine ⟨3675525333722404368930689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39205603559705646601927349 3675525333722404368930689)
                    ·
                      refine ⟨2756644000291803276698017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3675525333722404368930689 2756644000291803276698017)
                      ·
                        rfl

theorem cell23_5368545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_5368545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368545 prefixEnd_5368545 := by exact prefixLift 5368545
  have htrace : WordTrace (prefixWord ++ tailWord_5368545) baseStart_5368545 baseEnd_5368545 := by
    simpa [prefixWord, tailWord_5368545, baseEnd_5368545] using wordTrace_append hprefix tailTrace_5368545
  have hstable : (prefixWord ++ tailWord_5368545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368545).length < 2 ^ (prefixWord ++ tailWord_5368545).sum := by decide
  have hdescent : baseEnd_5368545 < baseStart_5368545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368562 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 2, 3, 2]
def baseStart_5368562 : Nat := 118140960795 + 5368562 * 2 ^ 59
def prefixEnd_5368562 : Nat := 4983230072969 + 3 ^ 40 * 5368562 * 2
def baseEnd_5368562 : Nat := 2756652729462929710185439

theorem tailTrace_5368562 : CollatzResearch.WordTrace tailWord_5368562 prefixEnd_5368562 2756652729462929710185439 := by
  unfold tailWord_5368562
  simp only [CollatzResearch.WordTrace]
  refine ⟨48951885594156056559592985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130538361584416150825581293 48951885594156056559592985)
  ·
    refine ⟨36713914195617042419694739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48951885594156056559592985 36713914195617042419694739)
    ·
      refine ⟨55070871293425563629542109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36713914195617042419694739 55070871293425563629542109)
      ·
        refine ⟨20651576735034586361078291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55070871293425563629542109 20651576735034586361078291)
        ·
          refine ⟨30977365102551879541617437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20651576735034586361078291 30977365102551879541617437)
          ·
            refine ⟨11616511913456954828106539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30977365102551879541617437 11616511913456954828106539)
            ·
              refine ⟨17424767870185432242159809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11616511913456954828106539 17424767870185432242159809)
              ·
                refine ⟨13068575902639074181619857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17424767870185432242159809 13068575902639074181619857)
                ·
                  refine ⟨9801431926979305636214893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13068575902639074181619857 9801431926979305636214893)
                  ·
                    refine ⟨3675536972617239613580585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9801431926979305636214893 3675536972617239613580585)
                    ·
                      refine ⟨2756652729462929710185439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3675536972617239613580585 2756652729462929710185439)
                      ·
                        rfl

theorem cell23_5368562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_5368562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368562 prefixEnd_5368562 := by exact prefixLift 5368562
  have htrace : WordTrace (prefixWord ++ tailWord_5368562) baseStart_5368562 baseEnd_5368562 := by
    simpa [prefixWord, tailWord_5368562, baseEnd_5368562] using wordTrace_append hprefix tailTrace_5368562
  have hstable : (prefixWord ++ tailWord_5368562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368562).length < 2 ^ (prefixWord ++ tailWord_5368562).sum := by decide
  have hdescent : baseEnd_5368562 < baseStart_5368562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368568 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 4, 4]
def baseStart_5368568 : Nat := 118140960795 + 5368568 * 2 ^ 59
def prefixEnd_5368568 : Nat := 4983230072969 + 3 ^ 40 * 5368568 * 2
def baseEnd_5368568 : Nat := 918885270115618895570137

theorem tailTrace_5368568 : CollatzResearch.WordTrace tailWord_5368568 prefixEnd_5368568 918885270115618895570137 := by
  unfold tailWord_5368568
  simp only [CollatzResearch.WordTrace]
  refine ⟨97903880607301244631545179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130538507476401659508726905 97903880607301244631545179)
  ·
    refine ⟨146855820910951866947317769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97903880607301244631545179 146855820910951866947317769)
    ·
      refine ⟨110141865683213900210488327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146855820910951866947317769 110141865683213900210488327)
      ·
        refine ⟨165212798524820850315732491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110141865683213900210488327 165212798524820850315732491)
        ·
          refine ⟨247819197787231275473598737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165212798524820850315732491 247819197787231275473598737)
          ·
            refine ⟨185864398340423456605199053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247819197787231275473598737 185864398340423456605199053)
            ·
              refine ⟨69699149377658796226949645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185864398340423456605199053 69699149377658796226949645)
              ·
                refine ⟨26137181016622048585106117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69699149377658796226949645 26137181016622048585106117)
                ·
                  refine ⟨4900721440616634109707397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26137181016622048585106117 4900721440616634109707397)
                  ·
                    refine ⟨918885270115618895570137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4900721440616634109707397 918885270115618895570137)
                    ·
                      rfl

theorem cell23_5368568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 4, 4].length) (baseStart_5368568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368568 prefixEnd_5368568 := by exact prefixLift 5368568
  have htrace : WordTrace (prefixWord ++ tailWord_5368568) baseStart_5368568 baseEnd_5368568 := by
    simpa [prefixWord, tailWord_5368568, baseEnd_5368568] using wordTrace_append hprefix tailTrace_5368568
  have hstable : (prefixWord ++ tailWord_5368568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368568).length < 2 ^ (prefixWord ++ tailWord_5368568).sum := by decide
  have hdescent : baseEnd_5368568 < baseStart_5368568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368588 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 1, 2, 4]
def baseStart_5368588 : Nat := 118140960795 + 5368588 * 2 ^ 59
def prefixEnd_5368588 : Nat := 4983230072969 + 3 ^ 40 * 5368588 * 2
def baseEnd_5368588 : Nat := 2756666079959946608460319

theorem tailTrace_5368588 : CollatzResearch.WordTrace tailWord_5368588 prefixEnd_5368588 2756666079959946608460319 := by
  unfold tailWord_5368588
  simp only [CollatzResearch.WordTrace]
  refine ⟨97904245337265016339409209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130538993783020021785878945 97904245337265016339409209)
  ·
    refine ⟨73428184002948762254556907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97904245337265016339409209 73428184002948762254556907)
    ·
      refine ⟨110142276004423143381835361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73428184002948762254556907 110142276004423143381835361)
      ·
        refine ⟨82606707003317357536376521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110142276004423143381835361 82606707003317357536376521)
        ·
          refine ⟨61955030252488018152282391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82606707003317357536376521 61955030252488018152282391)
          ·
            refine ⟨92932545378732027228423587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61955030252488018152282391 92932545378732027228423587)
            ·
              refine ⟨139398818068098040842635381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92932545378732027228423587 139398818068098040842635381)
              ·
                refine ⟨13068639193884191328997067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139398818068098040842635381 13068639193884191328997067)
                ·
                  refine ⟨19602958790826286993495601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13068639193884191328997067 19602958790826286993495601)
                  ·
                    refine ⟨14702219093119715245121701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19602958790826286993495601 14702219093119715245121701)
                    ·
                      refine ⟨2756666079959946608460319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14702219093119715245121701 2756666079959946608460319)
                      ·
                        rfl

theorem cell23_5368588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_5368588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368588 prefixEnd_5368588 := by exact prefixLift 5368588
  have htrace : WordTrace (prefixWord ++ tailWord_5368588) baseStart_5368588 baseEnd_5368588 := by
    simpa [prefixWord, tailWord_5368588, baseEnd_5368588] using wordTrace_append hprefix tailTrace_5368588
  have hstable : (prefixWord ++ tailWord_5368588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368588).length < 2 ^ (prefixWord ++ tailWord_5368588).sum := by decide
  have hdescent : baseEnd_5368588 < baseStart_5368588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368609 : List Nat := [1, 2, 3, 2, 1, 2, 2, 5, 1, 2, 2]
def baseStart_5368609 : Nat := 118140960795 + 5368609 * 2 ^ 59
def prefixEnd_5368609 : Nat := 4983230072969 + 3 ^ 40 * 5368609 * 2
def baseEnd_5368609 : Nat := 2756676863053691026297723

theorem tailTrace_5368609 : CollatzResearch.WordTrace tailWord_5368609 prefixEnd_5368609 2756676863053691026297723 := by
  unfold tailWord_5368609
  simp only [CollatzResearch.WordTrace]
  refine ⟨195809256607453953265332881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130539504404969302176888587 195809256607453953265332881)
  ·
    refine ⟨146856942455590464948999661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195809256607453953265332881 146856942455590464948999661)
    ·
      refine ⟨55071353420846424355874873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146856942455590464948999661 55071353420846424355874873)
      ·
        refine ⟨41303515065634818266906155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55071353420846424355874873 41303515065634818266906155)
        ·
          refine ⟨61955272598452227400359233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41303515065634818266906155 61955272598452227400359233)
          ·
            refine ⟨46466454448839170550269425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61955272598452227400359233 46466454448839170550269425)
            ·
              refine ⟨34849840836629377912702069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46466454448839170550269425 34849840836629377912702069)
              ·
                refine ⟨3267172578434004179315819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34849840836629377912702069 3267172578434004179315819)
                ·
                  refine ⟨4900758867651006268973729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267172578434004179315819 4900758867651006268973729)
                  ·
                    refine ⟨3675569150738254701730297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4900758867651006268973729 3675569150738254701730297)
                    ·
                      refine ⟨2756676863053691026297723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3675569150738254701730297 2756676863053691026297723)
                      ·
                        rfl

theorem cell23_5368609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_5368609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368609 prefixEnd_5368609 := by exact prefixLift 5368609
  have htrace : WordTrace (prefixWord ++ tailWord_5368609) baseStart_5368609 baseEnd_5368609 := by
    simpa [prefixWord, tailWord_5368609, baseEnd_5368609] using wordTrace_append hprefix tailTrace_5368609
  have hstable : (prefixWord ++ tailWord_5368609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368609).length < 2 ^ (prefixWord ++ tailWord_5368609).sum := by decide
  have hdescent : baseEnd_5368609 < baseStart_5368609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368612 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 1, 1, 5]
def baseStart_5368612 : Nat := 118140960795 + 5368612 * 2 ^ 59
def prefixEnd_5368612 : Nat := 4983230072969 + 3 ^ 40 * 5368612 * 2
def baseEnd_5368612 : Nat := 2756678403495654514560209

theorem tailTrace_5368612 : CollatzResearch.WordTrace tailWord_5368612 prefixEnd_5368612 2756678403495654514560209 := by
  unfold tailWord_5368612
  simp only [CollatzResearch.WordTrace]
  refine ⟨97904683013221542388846045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130539577350962056518461393 97904683013221542388846045)
  ·
    refine ⟨36714256129958078395817267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97904683013221542388846045 36714256129958078395817267)
    ·
      refine ⟨55071384194937117593725901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36714256129958078395817267 55071384194937117593725901)
      ·
        refine ⟨20651769073101419097647213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55071384194937117593725901 20651769073101419097647213)
        ·
          refine ⟨7744413402413032161617705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20651769073101419097647213 7744413402413032161617705)
          ·
            refine ⟨5808310051809774121213279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7744413402413032161617705 5808310051809774121213279)
            ·
              refine ⟨8712465077714661181819919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5808310051809774121213279 8712465077714661181819919)
              ·
                refine ⟨13068697616571991772729879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8712465077714661181819919 13068697616571991772729879)
                ·
                  refine ⟨19603046424857987659094819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13068697616571991772729879 19603046424857987659094819)
                  ·
                    refine ⟨29404569637286981488642229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19603046424857987659094819 29404569637286981488642229)
                    ·
                      refine ⟨2756678403495654514560209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29404569637286981488642229 2756678403495654514560209)
                      ·
                        rfl

theorem cell23_5368612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_5368612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368612 prefixEnd_5368612 := by exact prefixLift 5368612
  have htrace : WordTrace (prefixWord ++ tailWord_5368612) baseStart_5368612 baseEnd_5368612 := by
    simpa [prefixWord, tailWord_5368612, baseEnd_5368612] using wordTrace_append hprefix tailTrace_5368612
  have hstable : (prefixWord ++ tailWord_5368612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368612).length < 2 ^ (prefixWord ++ tailWord_5368612).sum := by decide
  have hdescent : baseEnd_5368612 < baseStart_5368612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368648 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_5368648 : Nat := 118140960795 + 5368648 * 2 ^ 59
def prefixEnd_5368648 : Nat := 4983230072969 + 3 ^ 40 * 5368648 * 2
def baseEnd_5368648 : Nat := 2756696888799216373710043

theorem tailTrace_5368648 : CollatzResearch.WordTrace tailWord_5368648 prefixEnd_5368648 2756696888799216373710043 := by
  unfold tailWord_5368648
  simp only [CollatzResearch.WordTrace]
  refine ⟨97905339527156331463001299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130540452702875108617335065 97905339527156331463001299)
  ·
    refine ⟨146858009290734497194501949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97905339527156331463001299 146858009290734497194501949)
    ·
      refine ⟨55071753484025436447938231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146858009290734497194501949 55071753484025436447938231)
      ·
        refine ⟨82607630226038154671907347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55071753484025436447938231 82607630226038154671907347)
        ·
          refine ⟨123911445339057232007861021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82607630226038154671907347 123911445339057232007861021)
          ·
            refine ⟨46466792002146462002947883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123911445339057232007861021 46466792002146462002947883)
            ·
              refine ⟨69700188003219693004421825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46466792002146462002947883 69700188003219693004421825)
              ·
                refine ⟨52275141002414769753316369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69700188003219693004421825 52275141002414769753316369)
                ·
                  refine ⟨39206355751811077314987277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52275141002414769753316369 39206355751811077314987277)
                  ·
                    refine ⟨14702383406929153993120229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39206355751811077314987277 14702383406929153993120229)
                    ·
                      refine ⟨2756696888799216373710043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14702383406929153993120229 2756696888799216373710043)
                      ·
                        rfl

theorem cell23_5368648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_5368648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368648 prefixEnd_5368648 := by exact prefixLift 5368648
  have htrace : WordTrace (prefixWord ++ tailWord_5368648) baseStart_5368648 baseEnd_5368648 := by
    simpa [prefixWord, tailWord_5368648, baseEnd_5368648] using wordTrace_append hprefix tailTrace_5368648
  have hstable : (prefixWord ++ tailWord_5368648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368648).length < 2 ^ (prefixWord ++ tailWord_5368648).sum := by decide
  have hdescent : baseEnd_5368648 < baseStart_5368648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368652 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 3, 3, 2]
def baseStart_5368652 : Nat := 118140960795 + 5368652 * 2 ^ 59
def prefixEnd_5368652 : Nat := 4983230072969 + 3 ^ 40 * 5368652 * 2
def baseEnd_5368652 : Nat := 2756698942721834358060025

theorem tailTrace_5368652 : CollatzResearch.WordTrace tailWord_5368652 prefixEnd_5368652 2756698942721834358060025 := by
  unfold tailWord_5368652
  simp only [CollatzResearch.WordTrace]
  refine ⟨97905412473149085804574105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130540549964198781072765473 97905412473149085804574105)
  ·
    refine ⟨73429059354861814353430579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97905412473149085804574105 73429059354861814353430579)
    ·
      refine ⟨110143589032292721530145869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73429059354861814353430579 110143589032292721530145869)
      ·
        refine ⟨41303845887109770573804701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110143589032292721530145869 41303845887109770573804701)
        ·
          refine ⟨15488942207666163965176763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41303845887109770573804701 15488942207666163965176763)
          ·
            refine ⟨23233413311499245947765145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15488942207666163965176763 23233413311499245947765145)
            ·
              refine ⟨17425059983624434460823859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23233413311499245947765145 17425059983624434460823859)
              ·
                refine ⟨26137589975436651691235789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17425059983624434460823859 26137589975436651691235789)
                ·
                  refine ⟨9801596240788744384213421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26137589975436651691235789 9801596240788744384213421)
                  ·
                    refine ⟨3675598590295779144080033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9801596240788744384213421 3675598590295779144080033)
                    ·
                      refine ⟨2756698942721834358060025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3675598590295779144080033 2756698942721834358060025)
                      ·
                        rfl

theorem cell23_5368652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_5368652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368652 prefixEnd_5368652 := by exact prefixLift 5368652
  have htrace : WordTrace (prefixWord ++ tailWord_5368652) baseStart_5368652 baseEnd_5368652 := by
    simpa [prefixWord, tailWord_5368652, baseEnd_5368652] using wordTrace_append hprefix tailTrace_5368652
  have hstable : (prefixWord ++ tailWord_5368652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368652).length < 2 ^ (prefixWord ++ tailWord_5368652).sum := by decide
  have hdescent : baseEnd_5368652 < baseStart_5368652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368658 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_5368658 : Nat := 118140960795 + 5368658 * 2 ^ 59
def prefixEnd_5368658 : Nat := 4983230072969 + 3 ^ 40 * 5368658 * 2
def baseEnd_5368658 : Nat := 918900674535253778194999

theorem tailTrace_5368658 : CollatzResearch.WordTrace tailWord_5368658 prefixEnd_5368658 918900674535253778194999 := by
  unfold tailWord_5368658
  simp only [CollatzResearch.WordTrace]
  refine ⟨48952760946069108658466657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130540695856184289755911085 48952760946069108658466657)
  ·
    refine ⟨36714570709551831493849993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48952760946069108658466657 36714570709551831493849993)
    ·
      refine ⟨27535928032163873620387495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36714570709551831493849993 27535928032163873620387495)
      ·
        refine ⟨41303892048245810430581243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27535928032163873620387495 41303892048245810430581243)
        ·
          refine ⟨61955838072368715645871865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41303892048245810430581243 61955838072368715645871865)
          ·
            refine ⟨46466878554276536734403899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61955838072368715645871865 46466878554276536734403899)
            ·
              refine ⟨69700317831414805101605849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46466878554276536734403899 69700317831414805101605849)
              ·
                refine ⟨52275238373561103826204387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69700317831414805101605849 52275238373561103826204387)
                ·
                  refine ⟨78412857560341655739306581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52275238373561103826204387 78412857560341655739306581)
                  ·
                    refine ⟨918900674535253778194999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78412857560341655739306581 918900674535253778194999)
                    ·
                      rfl

theorem cell23_5368658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_5368658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368658 prefixEnd_5368658 := by exact prefixLift 5368658
  have htrace : WordTrace (prefixWord ++ tailWord_5368658) baseStart_5368658 baseEnd_5368658 := by
    simpa [prefixWord, tailWord_5368658, baseEnd_5368658] using wordTrace_append hprefix tailTrace_5368658
  have hstable : (prefixWord ++ tailWord_5368658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368658).length < 2 ^ (prefixWord ++ tailWord_5368658).sum := by decide
  have hdescent : baseEnd_5368658 < baseStart_5368658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368688 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 7]
def baseStart_5368688 : Nat := 118140960795 + 5368688 * 2 ^ 59
def prefixEnd_5368688 : Nat := 4983230072969 + 3 ^ 40 * 5368688 * 2
def baseEnd_5368688 : Nat := 306301936447266246356651

theorem tailTrace_5368688 : CollatzResearch.WordTrace tailWord_5368688 prefixEnd_5368688 306301936447266246356651 := by
  unfold tailWord_5368688
  simp only [CollatzResearch.WordTrace]
  refine ⟨97906068987083874878729359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130541425316111833171639145 97906068987083874878729359)
  ·
    refine ⟨146859103480625812318094039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97906068987083874878729359 146859103480625812318094039)
    ·
      refine ⟨220288655220938718477141059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146859103480625812318094039 220288655220938718477141059)
      ·
        refine ⟨330432982831408077715711589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220288655220938718477141059 330432982831408077715711589)
        ·
          refine ⟨61956184280889014571695923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 330432982831408077715711589 61956184280889014571695923)
          ·
            refine ⟨92934276421333521857543885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61956184280889014571695923 92934276421333521857543885)
            ·
              refine ⟨34850353658000070696578957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92934276421333521857543885 34850353658000070696578957)
              ·
                refine ⟨13068882621750026511217109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34850353658000070696578957 13068882621750026511217109)
                ·
                  refine ⟨306301936447266246356651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13068882621750026511217109 306301936447266246356651)
                  ·
                    rfl

theorem cell23_5368688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 7].length) (baseStart_5368688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368688 prefixEnd_5368688 := by exact prefixLift 5368688
  have htrace : WordTrace (prefixWord ++ tailWord_5368688) baseStart_5368688 baseEnd_5368688 := by
    simpa [prefixWord, tailWord_5368688, baseEnd_5368688] using wordTrace_append hprefix tailTrace_5368688
  have hstable : (prefixWord ++ tailWord_5368688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368688).length < 2 ^ (prefixWord ++ tailWord_5368688).sum := by decide
  have hdescent : baseEnd_5368688 < baseStart_5368688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368735 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 4, 5]
def baseStart_5368735 : Nat := 118140960795 + 5368735 * 2 ^ 59
def prefixEnd_5368735 : Nat := 4983230072969 + 3 ^ 40 * 5368735 * 2
def baseEnd_5368735 : Nat := 918913853872052511107381

theorem tailTrace_5368735 : CollatzResearch.WordTrace tailWord_5368735 prefixEnd_5368735 918913853872052511107381 := by
  unfold tailWord_5368735
  simp only [CollatzResearch.WordTrace]
  refine ⟨195813852204997476784419659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130542568136664984522946439 195813852204997476784419659)
  ·
    refine ⟨293720778307496215176629489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195813852204997476784419659 293720778307496215176629489)
    ·
      refine ⟨220290583730622161382472117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293720778307496215176629489 220290583730622161382472117)
      ·
        refine ⟨20652242224745827629606761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 220290583730622161382472117 20652242224745827629606761)
        ·
          refine ⟨15489181668559370722205071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20652242224745827629606761 15489181668559370722205071)
          ·
            refine ⟨23233772502839056083307607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15489181668559370722205071 23233772502839056083307607)
            ·
              refine ⟨34850658754258584124961411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23233772502839056083307607 34850658754258584124961411)
              ·
                refine ⟨52275988131387876187442117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34850658754258584124961411 52275988131387876187442117)
                ·
                  refine ⟨9801747774635226785145397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52275988131387876187442117 9801747774635226785145397)
                  ·
                    refine ⟨918913853872052511107381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9801747774635226785145397 918913853872052511107381)
                    ·
                      rfl

theorem cell23_5368735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 5].length) (baseStart_5368735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368735 prefixEnd_5368735 := by exact prefixLift 5368735
  have htrace : WordTrace (prefixWord ++ tailWord_5368735) baseStart_5368735 baseEnd_5368735 := by
    simpa [prefixWord, tailWord_5368735, baseEnd_5368735] using wordTrace_append hprefix tailTrace_5368735
  have hstable : (prefixWord ++ tailWord_5368735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368735).length < 2 ^ (prefixWord ++ tailWord_5368735).sum := by decide
  have hdescent : baseEnd_5368735 < baseStart_5368735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368775 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_5368775 : Nat := 118140960795 + 5368775 * 2 ^ 59
def prefixEnd_5368775 : Nat := 4983230072969 + 3 ^ 40 * 5368775 * 2
def baseEnd_5368775 : Nat := 2756762100842337376821959

theorem tailTrace_5368775 : CollatzResearch.WordTrace tailWord_5368775 prefixEnd_5368775 2756762100842337376821959 := by
  unfold tailWord_5368775
  simp only [CollatzResearch.WordTrace]
  refine ⟨195815311124852563615875779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130543540749901709077250519 195815311124852563615875779)
  ·
    refine ⟨293722966687278845423813669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195815311124852563615875779 293722966687278845423813669)
    ·
      refine ⟨55073056253864783516965063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 293722966687278845423813669 55073056253864783516965063)
      ·
        refine ⟨82609584380797175275447595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55073056253864783516965063 82609584380797175275447595)
        ·
          refine ⟨123914376571195762913171393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82609584380797175275447595 123914376571195762913171393)
          ·
            refine ⟨92935782428396822184878545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123914376571195762913171393 92935782428396822184878545)
            ·
              refine ⟨69701836821297616638658909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92935782428396822184878545 69701836821297616638658909)
              ·
                refine ⟨26138188807986606239497091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69701836821297616638658909 26138188807986606239497091)
                ·
                  refine ⟨39207283211979909359245637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26138188807986606239497091 39207283211979909359245637)
                  ·
                    refine ⟨7351365602246233004858557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39207283211979909359245637 7351365602246233004858557)
                    ·
                      refine ⟨2756762100842337376821959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7351365602246233004858557 2756762100842337376821959)
                      ·
                        rfl

theorem cell23_5368775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_5368775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368775 prefixEnd_5368775 := by exact prefixLift 5368775
  have htrace : WordTrace (prefixWord ++ tailWord_5368775) baseStart_5368775 baseEnd_5368775 := by
    simpa [prefixWord, tailWord_5368775, baseEnd_5368775] using wordTrace_append hprefix tailTrace_5368775
  have hstable : (prefixWord ++ tailWord_5368775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368775).length < 2 ^ (prefixWord ++ tailWord_5368775).sum := by decide
  have hdescent : baseEnd_5368775 < baseStart_5368775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368792 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 2, 2, 3]
def baseStart_5368792 : Nat := 118140960795 + 5368792 * 2 ^ 59
def prefixEnd_5368792 : Nat := 4983230072969 + 3 ^ 40 * 5368792 * 2
def baseEnd_5368792 : Nat := 2756770830013463810309381

theorem tailTrace_5368792 : CollatzResearch.WordTrace tailWord_5368792 prefixEnd_5368792 2756770830013463810309381 := by
  unfold tailWord_5368792
  simp only [CollatzResearch.WordTrace]
  refine ⟨97907965582895487759622315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130543954110527317012829753 97907965582895487759622315)
  ·
    refine ⟨146861948374343231639433473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97907965582895487759622315 146861948374343231639433473)
    ·
      refine ⟨110146461280757423729575105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146861948374343231639433473 110146461280757423729575105)
      ·
        refine ⟨82609845960568067797181329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110146461280757423729575105 82609845960568067797181329)
        ·
          refine ⟨61957384470426050847885997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82609845960568067797181329 61957384470426050847885997)
          ·
            refine ⟨23234019176409769067957249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61957384470426050847885997 23234019176409769067957249)
            ·
              refine ⟨17425514382307326800967937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23234019176409769067957249 17425514382307326800967937)
              ·
                refine ⟨13069135786730495100725953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17425514382307326800967937 13069135786730495100725953)
                ·
                  refine ⟨9801851840047871325544465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13069135786730495100725953 9801851840047871325544465)
                  ·
                    refine ⟨7351388880035903494158349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9801851840047871325544465 7351388880035903494158349)
                    ·
                      refine ⟨2756770830013463810309381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7351388880035903494158349 2756770830013463810309381)
                      ·
                        rfl

theorem cell23_5368792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_5368792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368792 prefixEnd_5368792 := by exact prefixLift 5368792
  have htrace : WordTrace (prefixWord ++ tailWord_5368792) baseStart_5368792 baseEnd_5368792 := by
    simpa [prefixWord, tailWord_5368792, baseEnd_5368792] using wordTrace_append hprefix tailTrace_5368792
  have hstable : (prefixWord ++ tailWord_5368792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368792).length < 2 ^ (prefixWord ++ tailWord_5368792).sum := by decide
  have hdescent : baseEnd_5368792 < baseStart_5368792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368820 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_5368820 : Nat := 118140960795 + 5368820 * 2 ^ 59
def prefixEnd_5368820 : Nat := 4983230072969 + 3 ^ 40 * 5368820 * 2
def baseEnd_5368820 : Nat := 918928402490596566919751

theorem tailTrace_5368820 : CollatzResearch.WordTrace tailWord_5368820 prefixEnd_5368820 918928402490596566919751 := by
  unfold tailWord_5368820
  simp only [CollatzResearch.WordTrace]
  refine ⟨97908476204844768150631957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130544634939793024200842609 97908476204844768150631957)
  ·
    refine ⟨4589459822102098507060873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 97908476204844768150631957 4589459822102098507060873)
    ·
      refine ⟨3442094866576573880295655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4589459822102098507060873 3442094866576573880295655)
      ·
        refine ⟨5163142299864860820443483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3442094866576573880295655 5163142299864860820443483)
        ·
          refine ⟨7744713449797291230665225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5163142299864860820443483 7744713449797291230665225)
          ·
            refine ⟨5808535087347968422998919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7744713449797291230665225 5808535087347968422998919)
            ·
              refine ⟨8712802631021952634498379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5808535087347968422998919 8712802631021952634498379)
              ·
                refine ⟨13069203946532928951747569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8712802631021952634498379 13069203946532928951747569)
                ·
                  refine ⟨9801902959899696713810677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13069203946532928951747569 9801902959899696713810677)
                  ·
                    refine ⟨918928402490596566919751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9801902959899696713810677 918928402490596566919751)
                    ·
                      rfl

theorem cell23_5368820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_5368820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368820 prefixEnd_5368820 := by exact prefixLift 5368820
  have htrace : WordTrace (prefixWord ++ tailWord_5368820) baseStart_5368820 baseEnd_5368820 := by
    simpa [prefixWord, tailWord_5368820, baseEnd_5368820] using wordTrace_append hprefix tailTrace_5368820
  have hstable : (prefixWord ++ tailWord_5368820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368820).length < 2 ^ (prefixWord ++ tailWord_5368820).sum := by decide
  have hdescent : baseEnd_5368820 < baseStart_5368820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368825 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 3, 5]
def baseStart_5368825 : Nat := 118140960795 + 5368825 * 2 ^ 59
def prefixEnd_5368825 : Nat := 4983230072969 + 3 ^ 40 * 5368825 * 2
def baseEnd_5368825 : Nat := 918929258291687393732243

theorem tailTrace_5368825 : CollatzResearch.WordTrace tailWord_5368825 prefixEnd_5368825 918929258291687393732243 := by
  unfold tailWord_5368825
  simp only [CollatzResearch.WordTrace]
  refine ⟨195817134774671422155195929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130544756516447614770130619 195817134774671422155195929)
  ·
    refine ⟨146862851081003566616396947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195817134774671422155195929 146862851081003566616396947)
    ·
      refine ⟨220294276621505349924595421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146862851081003566616396947 220294276621505349924595421)
      ·
        refine ⟨82610353733064506221723283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220294276621505349924595421 82610353733064506221723283)
        ·
          refine ⟨123915530599596759332584925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82610353733064506221723283 123915530599596759332584925)
          ·
            refine ⟨46468323974848784749719347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123915530599596759332584925 46468323974848784749719347)
            ·
              refine ⟨69702485962273177124579021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46468323974848784749719347 69702485962273177124579021)
              ·
                refine ⟨26138432235852441421717133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69702485962273177124579021 26138432235852441421717133)
                ·
                  refine ⟨9801912088444665533143925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26138432235852441421717133 9801912088444665533143925)
                  ·
                    refine ⟨918929258291687393732243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9801912088444665533143925 918929258291687393732243)
                    ·
                      rfl

theorem cell23_5368825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 5].length) (baseStart_5368825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368825 prefixEnd_5368825 := by exact prefixLift 5368825
  have htrace : WordTrace (prefixWord ++ tailWord_5368825) baseStart_5368825 baseEnd_5368825 := by
    simpa [prefixWord, tailWord_5368825, baseEnd_5368825] using wordTrace_append hprefix tailTrace_5368825
  have hstable : (prefixWord ++ tailWord_5368825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368825).length < 2 ^ (prefixWord ++ tailWord_5368825).sum := by decide
  have hdescent : baseEnd_5368825 < baseStart_5368825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368856 : List Nat := [2, 1, 2, 3, 2, 2, 2, 4, 1, 1, 3]
def baseStart_5368856 : Nat := 118140960795 + 5368856 * 2 ^ 59
def prefixEnd_5368856 : Nat := 4983230072969 + 3 ^ 40 * 5368856 * 2
def baseEnd_5368856 : Nat := 2756803692775351559909087

theorem tailTrace_5368856 : CollatzResearch.WordTrace tailWord_5368856 prefixEnd_5368856 2756803692775351559909087 := by
  unfold tailWord_5368856
  simp only [CollatzResearch.WordTrace]
  refine ⟨97909132718779557224787211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130545510291706076299716281 97909132718779557224787211)
  ·
    refine ⟨146863699078169335837180817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97909132718779557224787211 146863699078169335837180817)
    ·
      refine ⟨110147774308627001877885613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146863699078169335837180817 110147774308627001877885613)
      ·
        refine ⟨41305415365735125704207105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110147774308627001877885613 41305415365735125704207105)
        ·
          refine ⟨30979061524301344278155329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41305415365735125704207105 30979061524301344278155329)
          ·
            refine ⟨23234296143226008208616497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30979061524301344278155329 23234296143226008208616497)
            ·
              refine ⟨17425722107419506156462373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23234296143226008208616497 17425722107419506156462373)
              ·
                refine ⟨3267322895141157404336695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17425722107419506156462373 3267322895141157404336695)
                ·
                  refine ⟨4900984342711736106505043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267322895141157404336695 4900984342711736106505043)
                  ·
                    refine ⟨7351476514067604159757565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4900984342711736106505043 7351476514067604159757565)
                    ·
                      refine ⟨2756803692775351559909087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7351476514067604159757565 2756803692775351559909087)
                      ·
                        rfl

theorem cell23_5368856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_5368856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368856 prefixEnd_5368856 := by exact prefixLift 5368856
  have htrace : WordTrace (prefixWord ++ tailWord_5368856) baseStart_5368856 baseEnd_5368856 := by
    simpa [prefixWord, tailWord_5368856, baseEnd_5368856] using wordTrace_append hprefix tailTrace_5368856
  have hstable : (prefixWord ++ tailWord_5368856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368856).length < 2 ^ (prefixWord ++ tailWord_5368856).sum := by decide
  have hdescent : baseEnd_5368856 < baseStart_5368856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368875 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 6]
def baseStart_5368875 : Nat := 118140960795 + 5368875 * 2 ^ 59
def prefixEnd_5368875 : Nat := 4983230072969 + 3 ^ 40 * 5368875 * 2
def baseEnd_5368875 : Nat := 2756813448907786985571499

theorem tailTrace_5368875 : CollatzResearch.WordTrace tailWord_5368875 prefixEnd_5368875 2756813448907786985571499 := by
  unfold tailWord_5368875
  simp only [CollatzResearch.WordTrace]
  refine ⟨195818958424490280694516079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130545972282993520463010719 195818958424490280694516079)
  ·
    refine ⟨293728437636735421041774119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195818958424490280694516079 293728437636735421041774119)
    ·
      refine ⟨440592656455103131562661179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293728437636735421041774119 440592656455103131562661179)
      ·
        refine ⟨660888984682654697343991769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440592656455103131562661179 660888984682654697343991769)
        ·
          refine ⟨495666738511991023007993827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 660888984682654697343991769 495666738511991023007993827)
          ·
            refine ⟨743500107767986534511990741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495666738511991023007993827 743500107767986534511990741)
            ·
              refine ⟨17425783775812184402624783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 743500107767986534511990741 17425783775812184402624783)
              ·
                refine ⟨26138675663718276603937175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17425783775812184402624783 26138675663718276603937175)
                ·
                  refine ⟨39208013495577414905905763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26138675663718276603937175 39208013495577414905905763)
                  ·
                    refine ⟨58812020243366122358858645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39208013495577414905905763 58812020243366122358858645)
                    ·
                      refine ⟨2756813448907786985571499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58812020243366122358858645 2756813448907786985571499)
                      ·
                        rfl

theorem cell23_5368875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 6].length) (baseStart_5368875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368875 prefixEnd_5368875 := by exact prefixLift 5368875
  have htrace : WordTrace (prefixWord ++ tailWord_5368875) baseStart_5368875 baseEnd_5368875 := by
    simpa [prefixWord, tailWord_5368875, baseEnd_5368875] using wordTrace_append hprefix tailTrace_5368875
  have hstable : (prefixWord ++ tailWord_5368875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368875).length < 2 ^ (prefixWord ++ tailWord_5368875).sum := by decide
  have hdescent : baseEnd_5368875 < baseStart_5368875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368926 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_5368926 : Nat := 118140960795 + 5368926 * 2 ^ 59
def prefixEnd_5368926 : Nat := 4983230072969 + 3 ^ 40 * 5368926 * 2
def baseEnd_5368926 : Nat := 2756839636421166286033765

theorem tailTrace_5368926 : CollatzResearch.WordTrace tailWord_5368926 prefixEnd_5368926 2756839636421166286033765 := by
  unfold tailWord_5368926
  simp only [CollatzResearch.WordTrace]
  refine ⟨24477602318413189550577829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130547212364870344269748421 24477602318413189550577829)
  ·
    refine ⟨4589550434702473040733343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24477602318413189550577829 4589550434702473040733343)
    ·
      refine ⟨6884325652053709561100015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4589550434702473040733343 6884325652053709561100015)
      ·
        refine ⟨10326488478080564341650023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6884325652053709561100015 10326488478080564341650023)
        ·
          refine ⟨15489732717120846512475035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10326488478080564341650023 15489732717120846512475035)
          ·
            refine ⟨23234599075681269768712553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15489732717120846512475035 23234599075681269768712553)
            ·
              refine ⟨17425949306760952326534415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23234599075681269768712553 17425949306760952326534415)
              ·
                refine ⟨26138923960141428489801623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17425949306760952326534415 26138923960141428489801623)
                ·
                  refine ⟨39208385940212142734702435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26138923960141428489801623 39208385940212142734702435)
                  ·
                    refine ⟨58812578910318214102053653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39208385940212142734702435 58812578910318214102053653)
                    ·
                      refine ⟨2756839636421166286033765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58812578910318214102053653 2756839636421166286033765)
                      ·
                        rfl

theorem cell23_5368926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_5368926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368926 prefixEnd_5368926 := by exact prefixLift 5368926
  have htrace : WordTrace (prefixWord ++ tailWord_5368926) baseStart_5368926 baseEnd_5368926 := by
    simpa [prefixWord, tailWord_5368926, baseEnd_5368926] using wordTrace_append hprefix tailTrace_5368926
  have hstable : (prefixWord ++ tailWord_5368926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368926).length < 2 ^ (prefixWord ++ tailWord_5368926).sum := by decide
  have hdescent : baseEnd_5368926 < baseStart_5368926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368945 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 3, 8]
def baseStart_5368945 : Nat := 118140960795 + 5368945 * 2 ^ 59
def prefixEnd_5368945 : Nat := 4983230072969 + 3 ^ 40 * 5368945 * 2
def baseEnd_5368945 : Nat := 918949797517867237232059

theorem tailTrace_5368945 : CollatzResearch.WordTrace tailWord_5368945 prefixEnd_5368945 918949797517867237232059 := by
  unfold tailWord_5368945
  simp only [CollatzResearch.WordTrace]
  refine ⟨195821511534236682649564289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130547674356157788433042859 195821511534236682649564289)
  ·
    refine ⟨146866133650677511987173217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195821511534236682649564289 146866133650677511987173217)
    ·
      refine ⟨110149600238008133990379913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146866133650677511987173217 110149600238008133990379913)
      ·
        refine ⟨82612200178506100492784935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110149600238008133990379913 82612200178506100492784935)
        ·
          refine ⟨123918300267759150739177403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82612200178506100492784935 123918300267759150739177403)
          ·
            refine ⟨185877450401638726108766105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123918300267759150739177403 185877450401638726108766105)
            ·
              refine ⟨139408087801229044581574579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185877450401638726108766105 139408087801229044581574579)
              ·
                refine ⟨209112131701843566872361869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139408087801229044581574579 209112131701843566872361869)
                ·
                  refine ⟨78417049388191337577135701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209112131701843566872361869 78417049388191337577135701)
                  ·
                    refine ⟨918949797517867237232059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78417049388191337577135701 918949797517867237232059)
                    ·
                      rfl

theorem cell23_5368945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_5368945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368945 prefixEnd_5368945 := by exact prefixLift 5368945
  have htrace : WordTrace (prefixWord ++ tailWord_5368945) baseStart_5368945 baseEnd_5368945 := by
    simpa [prefixWord, tailWord_5368945, baseEnd_5368945] using wordTrace_append hprefix tailTrace_5368945
  have hstable : (prefixWord ++ tailWord_5368945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368945).length < 2 ^ (prefixWord ++ tailWord_5368945).sum := by decide
  have hdescent : baseEnd_5368945 < baseStart_5368945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368986 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2]
def baseStart_5368986 : Nat := 118140960795 + 5368986 * 2 ^ 59
def prefixEnd_5368986 : Nat := 4983230072969 + 3 ^ 40 * 5368986 * 2
def baseEnd_5368986 : Nat := 2756870445260436051283489

theorem tailTrace_5368986 : CollatzResearch.WordTrace tailWord_5368986 prefixEnd_5368986 2756870445260436051283489 := by
  unfold tailWord_5368986
  simp only [CollatzResearch.WordTrace]
  refine ⟨48955751731772036662951703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130548671284725431101204541 48955751731772036662951703)
  ·
    refine ⟨73433627597658054994427555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48955751731772036662951703 73433627597658054994427555)
    ·
      refine ⟨110150441396487082491641333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73433627597658054994427555 110150441396487082491641333)
      ·
        refine ⟨10326603880920663983591375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110150441396487082491641333 10326603880920663983591375)
        ·
          refine ⟨15489905821380995975387063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10326603880920663983591375 15489905821380995975387063)
          ·
            refine ⟨23234858732071493963080595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15489905821380995975387063 23234858732071493963080595)
            ·
              refine ⟨34852288098107240944620893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23234858732071493963080595 34852288098107240944620893)
              ·
                refine ⟨13069608036790215354232835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34852288098107240944620893 13069608036790215354232835)
                ·
                  refine ⟨19604412055185323031349253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13069608036790215354232835 19604412055185323031349253)
                  ·
                    refine ⟨3675827260347248068377985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19604412055185323031349253 3675827260347248068377985)
                    ·
                      refine ⟨2756870445260436051283489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3675827260347248068377985 2756870445260436051283489)
                      ·
                        rfl

theorem cell23_5368986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_5368986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368986 prefixEnd_5368986 := by exact prefixLift 5368986
  have htrace : WordTrace (prefixWord ++ tailWord_5368986) baseStart_5368986 baseEnd_5368986 := by
    simpa [prefixWord, tailWord_5368986, baseEnd_5368986] using wordTrace_append hprefix tailTrace_5368986
  have hstable : (prefixWord ++ tailWord_5368986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368986).length < 2 ^ (prefixWord ++ tailWord_5368986).sum := by decide
  have hdescent : baseEnd_5368986 < baseStart_5368986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5368992 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 7]
def baseStart_5368992 : Nat := 118140960795 + 5368992 * 2 ^ 59
def prefixEnd_5368992 : Nat := 4983230072969 + 3 ^ 40 * 5368992 * 2
def baseEnd_5368992 : Nat := 306319280682707003089829

theorem tailTrace_5368992 : CollatzResearch.WordTrace tailWord_5368992 prefixEnd_5368992 306319280682707003089829 := by
  unfold tailWord_5368992
  simp only [CollatzResearch.WordTrace]
  refine ⟨97911612882533204838262615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130548817176710939784350153 97911612882533204838262615)
  ·
    refine ⟨146867419323799807257393923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97911612882533204838262615 146867419323799807257393923)
    ·
      refine ⟨220301128985699710886090885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146867419323799807257393923 220301128985699710886090885)
      ·
        refine ⟨41306461684818695791142041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220301128985699710886090885 41306461684818695791142041)
        ·
          refine ⟨30979846263614021843356531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41306461684818695791142041 30979846263614021843356531)
          ·
            refine ⟨46469769395421032765034797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30979846263614021843356531 46469769395421032765034797)
            ·
              refine ⟨17426163523282887286888049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46469769395421032765034797 17426163523282887286888049)
              ·
                refine ⟨13069622642462165465166037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17426163523282887286888049 13069622642462165465166037)
                ·
                  refine ⟨306319280682707003089829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13069622642462165465166037 306319280682707003089829)
                  ·
                    rfl

theorem cell23_5368992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 7].length) (baseStart_5368992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5368992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5368992 prefixEnd_5368992 := by exact prefixLift 5368992
  have htrace : WordTrace (prefixWord ++ tailWord_5368992) baseStart_5368992 baseEnd_5368992 := by
    simpa [prefixWord, tailWord_5368992, baseEnd_5368992] using wordTrace_append hprefix tailTrace_5368992
  have hstable : (prefixWord ++ tailWord_5368992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5368992).length < 2 ^ (prefixWord ++ tailWord_5368992).sum := by decide
  have hdescent : baseEnd_5368992 < baseStart_5368992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5368992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369014 : List Nat := [5, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_5369014 : Nat := 118140960795 + 5369014 * 2 ^ 59
def prefixEnd_5369014 : Nat := 4983230072969 + 3 ^ 40 * 5369014 * 2
def baseEnd_5369014 : Nat := 2756884822718761941733361

theorem tailTrace_5369014 : CollatzResearch.WordTrace tailWord_5369014 prefixEnd_5369014 2756884822718761941733361 := by
  unfold tailWord_5369014
  simp only [CollatzResearch.WordTrace]
  refine ⟨12239001760686669214614131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130549352113991138289217397 12239001760686669214614131)
  ·
    refine ⟨18358502641030003821921197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12239001760686669214614131 18358502641030003821921197)
    ·
      refine ⟨6884438490386251433220449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18358502641030003821921197 6884438490386251433220449)
      ·
        refine ⟨5163328867789688574915337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6884438490386251433220449 5163328867789688574915337)
        ·
          refine ⟨3872496650842266431186503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5163328867789688574915337 3872496650842266431186503)
          ·
            refine ⟨5808744976263399646779755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3872496650842266431186503 5808744976263399646779755)
            ·
              refine ⟨8713117464395099470169633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5808744976263399646779755 8713117464395099470169633)
              ·
                refine ⟨6534838098296324602627225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8713117464395099470169633 6534838098296324602627225)
                ·
                  refine ⟨4901128573722243451970419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6534838098296324602627225 4901128573722243451970419)
                  ·
                    refine ⟨7351692860583365177955629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4901128573722243451970419 7351692860583365177955629)
                    ·
                      refine ⟨2756884822718761941733361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7351692860583365177955629 2756884822718761941733361)
                      ·
                        rfl

theorem cell23_5369014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_5369014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369014 prefixEnd_5369014 := by exact prefixLift 5369014
  have htrace : WordTrace (prefixWord ++ tailWord_5369014) baseStart_5369014 baseEnd_5369014 := by
    simpa [prefixWord, tailWord_5369014, baseEnd_5369014] using wordTrace_append hprefix tailTrace_5369014
  have hstable : (prefixWord ++ tailWord_5369014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369014).length < 2 ^ (prefixWord ++ tailWord_5369014).sum := by decide
  have hdescent : baseEnd_5369014 < baseStart_5369014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369020 : List Nat := [2, 2, 2, 3, 2, 3, 1, 2, 2, 2, 2]
def baseStart_5369020 : Nat := 118140960795 + 5369020 * 2 ^ 59
def prefixEnd_5369020 : Nat := 4983230072969 + 3 ^ 40 * 5369020 * 2
def baseEnd_5369020 : Nat := 2756887903602688918258333

theorem tailTrace_5369020 : CollatzResearch.WordTrace tailWord_5369020 prefixEnd_5369020 2756887903602688918258333 := by
  unfold tailWord_5369020
  simp only [CollatzResearch.WordTrace]
  refine ⟨97912123504482485229272257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130549498005976646972363009 97912123504482485229272257)
  ·
    refine ⟨73434092628361863921954193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97912123504482485229272257 73434092628361863921954193)
    ·
      refine ⟨55075569471271397941465645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73434092628361863921954193 55075569471271397941465645)
      ·
        refine ⟨20653338551726774228049617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55075569471271397941465645 20653338551726774228049617)
        ·
          refine ⟨15490003913795080671037213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20653338551726774228049617 15490003913795080671037213)
          ·
            refine ⟨5808751467673155251638955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15490003913795080671037213 5808751467673155251638955)
            ·
              refine ⟨8713127201509732877458433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5808751467673155251638955 8713127201509732877458433)
              ·
                refine ⟨6534845401132299658093825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8713127201509732877458433 6534845401132299658093825)
                ·
                  refine ⟨4901134050849224743570369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6534845401132299658093825 4901134050849224743570369)
                  ·
                    refine ⟨3675850538136918557677777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4901134050849224743570369 3675850538136918557677777)
                    ·
                      refine ⟨2756887903602688918258333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3675850538136918557677777 2756887903602688918258333)
                      ·
                        rfl

theorem cell23_5369020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_5369020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369020 prefixEnd_5369020 := by exact prefixLift 5369020
  have htrace : WordTrace (prefixWord ++ tailWord_5369020) baseStart_5369020 baseEnd_5369020 := by
    simpa [prefixWord, tailWord_5369020, baseEnd_5369020] using wordTrace_append hprefix tailTrace_5369020
  have hstable : (prefixWord ++ tailWord_5369020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369020).length < 2 ^ (prefixWord ++ tailWord_5369020).sum := by decide
  have hdescent : baseEnd_5369020 < baseStart_5369020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369032 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_5369032 : Nat := 118140960795 + 5369032 * 2 ^ 59
def prefixEnd_5369032 : Nat := 4983230072969 + 3 ^ 40 * 5369032 * 2
def baseEnd_5369032 : Nat := 2756894065370542871308277

theorem tailTrace_5369032 : CollatzResearch.WordTrace tailWord_5369032 prefixEnd_5369032 2756894065370542871308277 := by
  unfold tailWord_5369032
  simp only [CollatzResearch.WordTrace]
  refine ⟨97912342342460748253990675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130549789789947664338654233 97912342342460748253990675)
  ·
    refine ⟨146868513513691122380986013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97912342342460748253990675 146868513513691122380986013)
    ·
      refine ⟨55075692567634170892869755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146868513513691122380986013 55075692567634170892869755)
      ·
        refine ⟨82613538851451256339304633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55075692567634170892869755 82613538851451256339304633)
        ·
          refine ⟨61960154138588442254478475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82613538851451256339304633 61960154138588442254478475)
          ·
            refine ⟨92940231207882663381717713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61960154138588442254478475 92940231207882663381717713)
            ·
              refine ⟨69705173405911997536288285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92940231207882663381717713 69705173405911997536288285)
              ·
                refine ⟨26139440027216999076108107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69705173405911997536288285 26139440027216999076108107)
                ·
                  refine ⟨39209160040825498614162161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26139440027216999076108107 39209160040825498614162161)
                  ·
                    refine ⟨29406870030619123960621621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39209160040825498614162161 29406870030619123960621621)
                    ·
                      refine ⟨2756894065370542871308277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29406870030619123960621621 2756894065370542871308277)
                      ·
                        rfl

theorem cell23_5369032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_5369032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369032 prefixEnd_5369032 := by exact prefixLift 5369032
  have htrace : WordTrace (prefixWord ++ tailWord_5369032) baseStart_5369032 baseEnd_5369032 := by
    simpa [prefixWord, tailWord_5369032, baseEnd_5369032] using wordTrace_append hprefix tailTrace_5369032
  have hstable : (prefixWord ++ tailWord_5369032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369032).length < 2 ^ (prefixWord ++ tailWord_5369032).sum := by decide
  have hdescent : baseEnd_5369032 < baseStart_5369032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369037 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_5369037 : Nat := 118140960795 + 5369037 * 2 ^ 59
def prefixEnd_5369037 : Nat := 4983230072969 + 3 ^ 40 * 5369037 * 2
def baseEnd_5369037 : Nat := 2756896632773815351745755

theorem tailTrace_5369037 : CollatzResearch.WordTrace tailWord_5369037 prefixEnd_5369037 2756896632773815351745755 := by
  unfold tailWord_5369037
  simp only [CollatzResearch.WordTrace]
  refine ⟨195824867049903382361913365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130549911366602254907942243 195824867049903382361913365)
  ·
    refine ⟨9179290642964221048214689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 195824867049903382361913365 9179290642964221048214689)
    ·
      refine ⟨6884467982223165786161017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9179290642964221048214689 6884467982223165786161017)
      ·
        refine ⟨5163350986667374339620763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6884467982223165786161017 5163350986667374339620763)
        ·
          refine ⟨7745026480001061509431145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5163350986667374339620763 7745026480001061509431145)
          ·
            refine ⟨5808769860000796132073359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7745026480001061509431145 5808769860000796132073359)
            ·
              refine ⟨8713154790001194198110039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5808769860000796132073359 8713154790001194198110039)
              ·
                refine ⟨13069732185001791297165059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8713154790001194198110039 13069732185001791297165059)
                ·
                  refine ⟨19604598277502686945747589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13069732185001791297165059 19604598277502686945747589)
                  ·
                    refine ⟨3675862177031753802327673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19604598277502686945747589 3675862177031753802327673)
                    ·
                      refine ⟨2756896632773815351745755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3675862177031753802327673 2756896632773815351745755)
                      ·
                        rfl

theorem cell23_5369037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_5369037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369037 prefixEnd_5369037 := by exact prefixLift 5369037
  have htrace : WordTrace (prefixWord ++ tailWord_5369037) baseStart_5369037 baseEnd_5369037 := by
    simpa [prefixWord, tailWord_5369037, baseEnd_5369037] using wordTrace_append hprefix tailTrace_5369037
  have hstable : (prefixWord ++ tailWord_5369037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369037).length < 2 ^ (prefixWord ++ tailWord_5369037).sum := by decide
  have hdescent : baseEnd_5369037 < baseStart_5369037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369079 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 3]
def baseStart_5369079 : Nat := 118140960795 + 5369079 * 2 ^ 59
def prefixEnd_5369079 : Nat := 4983230072969 + 3 ^ 40 * 5369079 * 2
def baseEnd_5369079 : Nat := 2756918198961304187420561

theorem tailTrace_5369079 : CollatzResearch.WordTrace tailWord_5369079 prefixEnd_5369079 2756918198961304187420561 := by
  unfold tailWord_5369079
  simp only [CollatzResearch.WordTrace]
  refine ⟨195826398915751223534942291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130550932610500815689961527 195826398915751223534942291)
  ·
    refine ⟨293739598373626835302413437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195826398915751223534942291 293739598373626835302413437)
    ·
      refine ⟨110152349390110063238405039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293739598373626835302413437 110152349390110063238405039)
      ·
        refine ⟨165228524085165094857607559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110152349390110063238405039 165228524085165094857607559)
        ·
          refine ⟨247842786127747642286411339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165228524085165094857607559 247842786127747642286411339)
          ·
            refine ⟨371764179191621463429617009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247842786127747642286411339 371764179191621463429617009)
            ·
              refine ⟨278823134393716097572212757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371764179191621463429617009 278823134393716097572212757)
              ·
                refine ⟨13069834424705442073697473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 278823134393716097572212757 13069834424705442073697473)
                ·
                  refine ⟨9802375818529081555273105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13069834424705442073697473 9802375818529081555273105)
                  ·
                    refine ⟨7351781863896811166454829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9802375818529081555273105 7351781863896811166454829)
                    ·
                      refine ⟨2756918198961304187420561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7351781863896811166454829 2756918198961304187420561)
                      ·
                        rfl

theorem cell23_5369079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_5369079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369079 prefixEnd_5369079 := by exact prefixLift 5369079
  have htrace : WordTrace (prefixWord ++ tailWord_5369079) baseStart_5369079 baseEnd_5369079 := by
    simpa [prefixWord, tailWord_5369079, baseEnd_5369079] using wordTrace_append hprefix tailTrace_5369079
  have hstable : (prefixWord ++ tailWord_5369079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369079).length < 2 ^ (prefixWord ++ tailWord_5369079).sum := by decide
  have hdescent : baseEnd_5369079 < baseStart_5369079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369082 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 8]
def baseStart_5369082 : Nat := 118140960795 + 5369082 * 2 ^ 59
def prefixEnd_5369082 : Nat := 4983230072969 + 3 ^ 40 * 5369082 * 2
def baseEnd_5369082 : Nat := 306324415489251963964783

theorem tailTrace_5369082 : CollatzResearch.WordTrace tailWord_5369082 prefixEnd_5369082 306324415489251963964783 := by
  unfold tailWord_5369082
  simp only [CollatzResearch.WordTrace]
  refine ⟨48956627083685088761825375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130551005556493570031534333 48956627083685088761825375)
  ·
    refine ⟨73434940625527633142738063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48956627083685088761825375 73434940625527633142738063)
    ·
      refine ⟨110152410938291449714107095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73434940625527633142738063 110152410938291449714107095)
      ·
        refine ⟨165228616407437174571160643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110152410938291449714107095 165228616407437174571160643)
        ·
          refine ⟨247842924611155761856740965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165228616407437174571160643 247842924611155761856740965)
          ·
            refine ⟨46470548364591705348138931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247842924611155761856740965 46470548364591705348138931)
            ·
              refine ⟨69705822546887558022208397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46470548364591705348138931 69705822546887558022208397)
              ·
                refine ⟨26139683455082834258328149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69705822546887558022208397 26139683455082834258328149)
                ·
                  refine ⟨306324415489251963964783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26139683455082834258328149 306324415489251963964783)
                  ·
                    rfl

theorem cell23_5369082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_5369082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369082 prefixEnd_5369082 := by exact prefixLift 5369082
  have htrace : WordTrace (prefixWord ++ tailWord_5369082) baseStart_5369082 baseEnd_5369082 := by
    simpa [prefixWord, tailWord_5369082, baseEnd_5369082] using wordTrace_append hprefix tailTrace_5369082
  have hstable : (prefixWord ++ tailWord_5369082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369082).length < 2 ^ (prefixWord ++ tailWord_5369082).sum := by decide
  have hdescent : baseEnd_5369082 < baseStart_5369082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369099 : List Nat := [1, 1, 1, 1, 5, 4, 1, 3, 6]
def baseStart_5369099 : Nat := 118140960795 + 5369099 * 2 ^ 59
def prefixEnd_5369099 : Nat := 4983230072969 + 3 ^ 40 * 5369099 * 2
def baseEnd_5369099 : Nat := 306325385397154901018941

theorem tailTrace_5369099 : CollatzResearch.WordTrace tailWord_5369099 prefixEnd_5369099 306325385397154901018941 := by
  unfold tailWord_5369099
  simp only [CollatzResearch.WordTrace]
  refine ⟨195827128375678766950670351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130551418917119177967113567 195827128375678766950670351)
  ·
    refine ⟨293740692563518150426005527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195827128375678766950670351 293740692563518150426005527)
    ·
      refine ⟨440611038845277225639008291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293740692563518150426005527 440611038845277225639008291)
      ·
        refine ⟨660916558267915838458512437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440611038845277225639008291 660916558267915838458512437)
        ·
          refine ⟨61960927337617109855485541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 660916558267915838458512437 61960927337617109855485541)
          ·
            refine ⟨11617673875803208097903539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61960927337617109855485541 11617673875803208097903539)
            ·
              refine ⟨17426510813704812146855309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11617673875803208097903539 17426510813704812146855309)
              ·
                refine ⟨6534941555139304555070741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17426510813704812146855309 6534941555139304555070741)
                ·
                  refine ⟨306325385397154901018941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6534941555139304555070741 306325385397154901018941)
                  ·
                    rfl

theorem cell23_5369099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 6].length) (baseStart_5369099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369099 prefixEnd_5369099 := by exact prefixLift 5369099
  have htrace : WordTrace (prefixWord ++ tailWord_5369099) baseStart_5369099 baseEnd_5369099 := by
    simpa [prefixWord, tailWord_5369099, baseEnd_5369099] using wordTrace_append hprefix tailTrace_5369099
  have hstable : (prefixWord ++ tailWord_5369099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369099).length < 2 ^ (prefixWord ++ tailWord_5369099).sum := by decide
  have hdescent : baseEnd_5369099 < baseStart_5369099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369133 : List Nat := [1, 5, 3, 1, 1, 2, 2, 2, 6]
def baseStart_5369133 : Nat := 118140960795 + 5369133 * 2 ^ 59
def prefixEnd_5369133 : Nat := 4983230072969 + 3 ^ 40 * 5369133 * 2
def baseEnd_5369133 : Nat := 306327325212960775127257

theorem tailTrace_5369133 : CollatzResearch.WordTrace tailWord_5369133 prefixEnd_5369133 306327325212960775127257 := by
  unfold tailWord_5369133
  simp only [CollatzResearch.WordTrace]
  refine ⟨195828368457555590757408053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130552245638370393838272035 195828368457555590757408053)
  ·
    refine ⟨18358909542895836633507005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195828368457555590757408053 18358909542895836633507005)
    ·
      refine ⟨6884591078585938737565127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18358909542895836633507005 6884591078585938737565127)
      ·
        refine ⟨10326886617878908106347691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6884591078585938737565127 10326886617878908106347691)
        ·
          refine ⟨15490329926818362159521537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10326886617878908106347691 15490329926818362159521537)
          ·
            refine ⟨11617747445113771619641153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15490329926818362159521537 11617747445113771619641153)
            ·
              refine ⟨8713310583835328714730865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11617747445113771619641153 8713310583835328714730865)
              ·
                refine ⟨6534982937876496536048149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8713310583835328714730865 6534982937876496536048149)
                ·
                  refine ⟨306327325212960775127257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6534982937876496536048149 306327325212960775127257)
                  ·
                    rfl

theorem cell23_5369133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_5369133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369133 prefixEnd_5369133 := by exact prefixLift 5369133
  have htrace : WordTrace (prefixWord ++ tailWord_5369133) baseStart_5369133 baseEnd_5369133 := by
    simpa [prefixWord, tailWord_5369133, baseEnd_5369133] using wordTrace_append hprefix tailTrace_5369133
  have hstable : (prefixWord ++ tailWord_5369133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369133).length < 2 ^ (prefixWord ++ tailWord_5369133).sum := by decide
  have hdescent : baseEnd_5369133 < baseStart_5369133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369136 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 2, 3, 2]
def baseStart_5369136 : Nat := 118140960795 + 5369136 * 2 ^ 59
def prefixEnd_5369136 : Nat := 4983230072969 + 3 ^ 40 * 5369136 * 2
def baseEnd_5369136 : Nat := 2756947467358610464407799

theorem tailTrace_5369136 : CollatzResearch.WordTrace tailWord_5369136 prefixEnd_5369136 2756947467358610464407799 := by
  unfold tailWord_5369136
  simp only [CollatzResearch.WordTrace]
  refine ⟨97914238938272361134883631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130552318584363148179844841 97914238938272361134883631)
  ·
    refine ⟨146871358407408541702325447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97914238938272361134883631 146871358407408541702325447)
    ·
      refine ⟨220307037611112812553488171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146871358407408541702325447 220307037611112812553488171)
      ·
        refine ⟨330460556416669218830232257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220307037611112812553488171 330460556416669218830232257)
        ·
          refine ⟨247845417312501914122674193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330460556416669218830232257 247845417312501914122674193)
          ·
            refine ⟨185884062984376435592005645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247845417312501914122674193 185884062984376435592005645)
            ·
              refine ⟨69706523619141163347002117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185884062984376435592005645 69706523619141163347002117)
              ·
                refine ⟨13069973178588968127562897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69706523619141163347002117 13069973178588968127562897)
                ·
                  refine ⟨9802479883941726095672173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13069973178588968127562897 9802479883941726095672173)
                  ·
                    refine ⟨3675929956478147285877065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9802479883941726095672173 3675929956478147285877065)
                    ·
                      refine ⟨2756947467358610464407799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3675929956478147285877065 2756947467358610464407799)
                      ·
                        rfl

theorem cell23_5369136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 2, 3, 2].length) (baseStart_5369136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369136 prefixEnd_5369136 := by exact prefixLift 5369136
  have htrace : WordTrace (prefixWord ++ tailWord_5369136) baseStart_5369136 baseEnd_5369136 := by
    simpa [prefixWord, tailWord_5369136, baseEnd_5369136] using wordTrace_append hprefix tailTrace_5369136
  have hstable : (prefixWord ++ tailWord_5369136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369136).length < 2 ^ (prefixWord ++ tailWord_5369136).sum := by decide
  have hdescent : baseEnd_5369136 < baseStart_5369136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369159 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 1, 6]
def baseStart_5369159 : Nat := 118140960795 + 5369159 * 2 ^ 59
def prefixEnd_5369159 : Nat := 4983230072969 + 3 ^ 40 * 5369159 * 2
def baseEnd_5369159 : Nat := 918986425804554624806731

theorem tailTrace_5369159 : CollatzResearch.WordTrace tailWord_5369159 prefixEnd_5369159 918986425804554624806731 := by
  unfold tailWord_5369159
  simp only [CollatzResearch.WordTrace]
  refine ⟨195829316755461397197854531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130552877836974264798569687 195829316755461397197854531)
  ·
    refine ⟨293743975133192095796781797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195829316755461397197854531 293743975133192095796781797)
    ·
      refine ⟨55076995337473517961896587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 293743975133192095796781797 55076995337473517961896587)
      ·
        refine ⟨82615493006210276942844881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55076995337473517961896587 82615493006210276942844881)
        ·
          refine ⟨61961619754657707707133661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82615493006210276942844881 61961619754657707707133661)
          ·
            refine ⟨23235607407996640390175123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61961619754657707707133661 23235607407996640390175123)
            ·
              refine ⟨34853411111994960585262685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23235607407996640390175123 34853411111994960585262685)
              ·
                refine ⟨13070029166998110219473507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34853411111994960585262685 13070029166998110219473507)
                ·
                  refine ⟨19605043750497165329210261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13070029166998110219473507 19605043750497165329210261)
                  ·
                    refine ⟨918986425804554624806731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19605043750497165329210261 918986425804554624806731)
                    ·
                      rfl

theorem cell23_5369159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_5369159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369159 prefixEnd_5369159 := by exact prefixLift 5369159
  have htrace : WordTrace (prefixWord ++ tailWord_5369159) baseStart_5369159 baseEnd_5369159 := by
    simpa [prefixWord, tailWord_5369159, baseEnd_5369159] using wordTrace_append hprefix tailTrace_5369159
  have hstable : (prefixWord ++ tailWord_5369159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369159).length < 2 ^ (prefixWord ++ tailWord_5369159).sum := by decide
  have hdescent : baseEnd_5369159 < baseStart_5369159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369166 : List Nat := [4, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4]
def baseStart_5369166 : Nat := 118140960795 + 5369166 * 2 ^ 59
def prefixEnd_5369166 : Nat := 4983230072969 + 3 ^ 40 * 5369166 * 2
def baseEnd_5369166 : Nat := 2756962871778245347032661

theorem tailTrace_5369166 : CollatzResearch.WordTrace tailWord_5369166 prefixEnd_5369166 2756962871778245347032661 := by
  unfold tailWord_5369166
  simp only [CollatzResearch.WordTrace]
  refine ⟨24478696508304504674169919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130553048044290691595572901 24478696508304504674169919)
  ·
    refine ⟨36718044762456757011254879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24478696508304504674169919 36718044762456757011254879)
    ·
      refine ⟨55077067143685135516882319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36718044762456757011254879 55077067143685135516882319)
      ·
        refine ⟨82615600715527703275323479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55077067143685135516882319 82615600715527703275323479)
        ·
          refine ⟨123923401073291554912985219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82615600715527703275323479 123923401073291554912985219)
          ·
            refine ⟨185885101609937332369477829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123923401073291554912985219 185885101609937332369477829)
            ·
              refine ⟨34853456551863249819277093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185885101609937332369477829 34853456551863249819277093)
              ·
                refine ⟨6535023103474359341114455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34853456551863249819277093 6535023103474359341114455)
                ·
                  refine ⟨9802534655211539011671683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6535023103474359341114455 9802534655211539011671683)
                  ·
                    refine ⟨14703801982817308517507525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9802534655211539011671683 14703801982817308517507525)
                    ·
                      refine ⟨2756962871778245347032661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14703801982817308517507525 2756962871778245347032661)
                      ·
                        rfl

theorem cell23_5369166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_5369166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369166 prefixEnd_5369166 := by exact prefixLift 5369166
  have htrace : WordTrace (prefixWord ++ tailWord_5369166) baseStart_5369166 baseEnd_5369166 := by
    simpa [prefixWord, tailWord_5369166, baseEnd_5369166] using wordTrace_append hprefix tailTrace_5369166
  have hstable : (prefixWord ++ tailWord_5369166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369166).length < 2 ^ (prefixWord ++ tailWord_5369166).sum := by decide
  have hdescent : baseEnd_5369166 < baseStart_5369166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369186 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_5369186 : Nat := 118140960795 + 5369186 * 2 ^ 59
def prefixEnd_5369186 : Nat := 4983230072969 + 3 ^ 40 * 5369186 * 2
def baseEnd_5369186 : Nat := 2756973141391335268782569

theorem tailTrace_5369186 : CollatzResearch.WordTrace tailWord_5369186 prefixEnd_5369186 2756973141391335268782569 := by
  unfold tailWord_5369186
  simp only [CollatzResearch.WordTrace]
  refine ⟨48957575381590895202271853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130553534350909053872724941 48957575381590895202271853)
  ·
    refine ⟨18359090768096585700851945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48957575381590895202271853 18359090768096585700851945)
    ·
      refine ⟨13769318076072439275638959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18359090768096585700851945 13769318076072439275638959)
      ·
        refine ⟨20653977114108658913458439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13769318076072439275638959 20653977114108658913458439)
        ·
          refine ⟨30980965671162988370187659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20653977114108658913458439 30980965671162988370187659)
          ·
            refine ⟨46471448506744482555281489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30980965671162988370187659 46471448506744482555281489)
            ·
              refine ⟨34853586380058361916461117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46471448506744482555281489 34853586380058361916461117)
              ·
                refine ⟨13070094892521885718672919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34853586380058361916461117 13070094892521885718672919)
                ·
                  refine ⟨19605142338782828578009379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13070094892521885718672919 19605142338782828578009379)
                  ·
                    refine ⟨29407713508174242867014069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19605142338782828578009379 29407713508174242867014069)
                    ·
                      refine ⟨2756973141391335268782569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29407713508174242867014069 2756973141391335268782569)
                      ·
                        rfl

theorem cell23_5369186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_5369186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369186 prefixEnd_5369186 := by exact prefixLift 5369186
  have htrace : WordTrace (prefixWord ++ tailWord_5369186) baseStart_5369186 baseEnd_5369186 := by
    simpa [prefixWord, tailWord_5369186, baseEnd_5369186] using wordTrace_append hprefix tailTrace_5369186
  have hstable : (prefixWord ++ tailWord_5369186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369186).length < 2 ^ (prefixWord ++ tailWord_5369186).sum := by decide
  have hdescent : baseEnd_5369186 < baseStart_5369186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369200 : List Nat := [2, 1, 1, 1, 4, 2, 1, 6, 1, 2, 2]
def baseStart_5369200 : Nat := 118140960795 + 5369200 * 2 ^ 59
def prefixEnd_5369200 : Nat := 4983230072969 + 3 ^ 40 * 5369200 * 2
def baseEnd_5369200 : Nat := 2756980330120498214007505

theorem tailTrace_5369200 : CollatzResearch.WordTrace tailWord_5369200 prefixEnd_5369200 2756980330120498214007505 := by
  unfold tailWord_5369200
  simp only [CollatzResearch.WordTrace]
  refine ⟨97915406074156430600048527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130553874765541907466731369 97915406074156430600048527)
  ·
    refine ⟨146873109111234645900072791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97915406074156430600048527 146873109111234645900072791)
    ·
      refine ⟨220309663666851968850109187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146873109111234645900072791 220309663666851968850109187)
      ·
        refine ⟨330464495500277953275163781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220309663666851968850109187 330464495500277953275163781)
        ·
          refine ⟨61962092906302116239093209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 330464495500277953275163781 61962092906302116239093209)
          ·
            refine ⟨46471569679726587179319907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61962092906302116239093209 46471569679726587179319907)
            ·
              refine ⟨69707354519589880768979861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46471569679726587179319907 69707354519589880768979861)
              ·
                refine ⟨3267532243105775661045931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69707354519589880768979861 3267532243105775661045931)
                ·
                  refine ⟨4901298364658663491568897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267532243105775661045931 4901298364658663491568897)
                  ·
                    refine ⟨3675973773493997618676673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4901298364658663491568897 3675973773493997618676673)
                    ·
                      refine ⟨2756980330120498214007505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3675973773493997618676673 2756980330120498214007505)
                      ·
                        rfl

theorem cell23_5369200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 1, 2, 2].length) (baseStart_5369200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369200 prefixEnd_5369200 := by exact prefixLift 5369200
  have htrace : WordTrace (prefixWord ++ tailWord_5369200) baseStart_5369200 baseEnd_5369200 := by
    simpa [prefixWord, tailWord_5369200, baseEnd_5369200] using wordTrace_append hprefix tailTrace_5369200
  have hstable : (prefixWord ++ tailWord_5369200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369200).length < 2 ^ (prefixWord ++ tailWord_5369200).sum := by decide
  have hdescent : baseEnd_5369200 < baseStart_5369200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369239 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_5369239 : Nat := 118140960795 + 5369239 * 2 ^ 59
def prefixEnd_5369239 : Nat := 4983230072969 + 3 ^ 40 * 5369239 * 2
def baseEnd_5369239 : Nat := 2757000355866023561419825

theorem tailTrace_5369239 : CollatzResearch.WordTrace tailWord_5369239 prefixEnd_5369239 2757000355866023561419825 := by
  unfold tailWord_5369239
  simp only [CollatzResearch.WordTrace]
  refine ⟨195832234595171570860766771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130554823063447713907177847 195832234595171570860766771)
  ·
    refine ⟨293748351892757356291150157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195832234595171570860766771 293748351892757356291150157)
    ·
      refine ⟨110155631959784008609181309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293748351892757356291150157 110155631959784008609181309)
      ·
        refine ⟨41308361984919003228442991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110155631959784008609181309 41308361984919003228442991)
        ·
          refine ⟨61962542977378504842664487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41308361984919003228442991 61962542977378504842664487)
          ·
            refine ⟨92943814466067757263996731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61962542977378504842664487 92943814466067757263996731)
            ·
              refine ⟨139415721699101635895995097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92943814466067757263996731 139415721699101635895995097)
              ·
                refine ⟨104561791274326226921996323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139415721699101635895995097 104561791274326226921996323)
                ·
                  refine ⟨156842686911489340382994485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104561791274326226921996323 156842686911489340382994485)
                  ·
                    refine ⟨14704001897952125660905733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 156842686911489340382994485 14704001897952125660905733)
                    ·
                      refine ⟨2757000355866023561419825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14704001897952125660905733 2757000355866023561419825)
                      ·
                        rfl

theorem cell23_5369239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_5369239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369239 prefixEnd_5369239 := by exact prefixLift 5369239
  have htrace : WordTrace (prefixWord ++ tailWord_5369239) baseStart_5369239 baseEnd_5369239 := by
    simpa [prefixWord, tailWord_5369239, baseEnd_5369239] using wordTrace_append hprefix tailTrace_5369239
  have hstable : (prefixWord ++ tailWord_5369239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369239).length < 2 ^ (prefixWord ++ tailWord_5369239).sum := by decide
  have hdescent : baseEnd_5369239 < baseStart_5369239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369279 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 7]
def baseStart_5369279 : Nat := 118140960795 + 5369279 * 2 ^ 59
def prefixEnd_5369279 : Nat := 4983230072969 + 3 ^ 40 * 5369279 * 2
def baseEnd_5369279 : Nat := 306335655010244822768849

theorem tailTrace_5369279 : CollatzResearch.WordTrace tailWord_5369279 prefixEnd_5369279 306335655010244822768849 := by
  unfold tailWord_5369279
  simp only [CollatzResearch.WordTrace]
  refine ⟨195833693515026657692222891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130555795676684438461481927 195833693515026657692222891)
  ·
    refine ⟨293750540272539986538334337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195833693515026657692222891 293750540272539986538334337)
    ·
      refine ⟨220312905204404989903750753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293750540272539986538334337 220312905204404989903750753)
      ·
        refine ⟨165234678903303742427813065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220312905204404989903750753 165234678903303742427813065)
        ·
          refine ⟨123926009177477806820859799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165234678903303742427813065 123926009177477806820859799)
          ·
            refine ⟨185889013766216710231289699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123926009177477806820859799 185889013766216710231289699)
            ·
              refine ⟨278833520649325065346934549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185889013766216710231289699 278833520649325065346934549)
              ·
                refine ⟨13070321280437112438137557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 278833520649325065346934549 13070321280437112438137557)
                ·
                  refine ⟨306335655010244822768849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13070321280437112438137557 306335655010244822768849)
                  ·
                    rfl

theorem cell23_5369279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 7].length) (baseStart_5369279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369279 prefixEnd_5369279 := by exact prefixLift 5369279
  have htrace : WordTrace (prefixWord ++ tailWord_5369279) baseStart_5369279 baseEnd_5369279 := by
    simpa [prefixWord, tailWord_5369279, baseEnd_5369279] using wordTrace_append hprefix tailTrace_5369279
  have hstable : (prefixWord ++ tailWord_5369279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369279).length < 2 ^ (prefixWord ++ tailWord_5369279).sum := by decide
  have hdescent : baseEnd_5369279 < baseStart_5369279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369313 : List Nat := [1, 2, 3, 1, 2, 4, 1, 4, 5]
def baseStart_5369313 : Nat := 118140960795 + 5369313 * 2 ^ 59
def prefixEnd_5369313 : Nat := 4983230072969 + 3 ^ 40 * 5369313 * 2
def baseEnd_5369313 : Nat := 306337594826050696877165

theorem tailTrace_5369313 : CollatzResearch.WordTrace tailWord_5369313 prefixEnd_5369313 306337594826050696877165 := by
  unfold tailWord_5369313
  simp only [CollatzResearch.WordTrace]
  refine ⟨195834933596903481498960593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130556622397935654332640395 195834933596903481498960593)
  ·
    refine ⟨146876200197677611124220445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195834933596903481498960593 146876200197677611124220445)
    ·
      refine ⟨55078575074129104171582667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146876200197677611124220445 55078575074129104171582667)
      ·
        refine ⟨82617862611193656257374001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55078575074129104171582667 82617862611193656257374001)
        ·
          refine ⟨61963396958395242193030501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82617862611193656257374001 61963396958395242193030501)
          ·
            refine ⟨11618136929699107911193219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61963396958395242193030501 11618136929699107911193219)
            ·
              refine ⟨17427205394548661866789829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11618136929699107911193219 17427205394548661866789829)
              ·
                refine ⟨3267601011477874100023093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17427205394548661866789829 3267601011477874100023093)
                ·
                  refine ⟨306337594826050696877165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3267601011477874100023093 306337594826050696877165)
                  ·
                    rfl

theorem cell23_5369313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 5].length) (baseStart_5369313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369313 prefixEnd_5369313 := by exact prefixLift 5369313
  have htrace : WordTrace (prefixWord ++ tailWord_5369313) baseStart_5369313 baseEnd_5369313 := by
    simpa [prefixWord, tailWord_5369313, baseEnd_5369313] using wordTrace_append hprefix tailTrace_5369313
  have hstable : (prefixWord ++ tailWord_5369313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369313).length < 2 ^ (prefixWord ++ tailWord_5369313).sum := by decide
  have hdescent : baseEnd_5369313 < baseStart_5369313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369326 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_5369326 : Nat := 118140960795 + 5369326 * 2 ^ 59
def prefixEnd_5369326 : Nat := 4983230072969 + 3 ^ 40 * 5369326 * 2
def baseEnd_5369326 : Nat := 919015009560988240343975

theorem tailTrace_5369326 : CollatzResearch.WordTrace tailWord_5369326 prefixEnd_5369326 919015009560988240343975 := by
  unfold tailWord_5369326
  simp only [CollatzResearch.WordTrace]
  refine ⟨24479425968232048089897979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130556938497237589812789221 24479425968232048089897979)
  ·
    refine ⟨36719138952348072134846969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24479425968232048089897979 36719138952348072134846969)
    ·
      refine ⟨27539354214261054101135227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36719138952348072134846969 27539354214261054101135227)
      ·
        refine ⟨41309031321391581151702841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27539354214261054101135227 41309031321391581151702841)
        ·
          refine ⟨30981773491043685863777131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41309031321391581151702841 30981773491043685863777131)
          ·
            refine ⟨46472660236565528795665697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30981773491043685863777131 46472660236565528795665697)
            ·
              refine ⟨34854495177424146596749273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46472660236565528795665697 34854495177424146596749273)
              ·
                refine ⟨26140871383068109947561955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34854495177424146596749273 26140871383068109947561955)
                ·
                  refine ⟨39211307074602164921342933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26140871383068109947561955 39211307074602164921342933)
                  ·
                    refine ⟨919015009560988240343975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39211307074602164921342933 919015009560988240343975)
                    ·
                      rfl

theorem cell23_5369326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_5369326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369326 prefixEnd_5369326 := by exact prefixLift 5369326
  have htrace : WordTrace (prefixWord ++ tailWord_5369326) baseStart_5369326 baseEnd_5369326 := by
    simpa [prefixWord, tailWord_5369326, baseEnd_5369326] using wordTrace_append hprefix tailTrace_5369326
  have hstable : (prefixWord ++ tailWord_5369326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369326).length < 2 ^ (prefixWord ++ tailWord_5369326).sum := by decide
  have hdescent : baseEnd_5369326 < baseStart_5369326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369339 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 2, 8]
def baseStart_5369339 : Nat := 118140960795 + 5369339 * 2 ^ 59
def prefixEnd_5369339 : Nat := 4983230072969 + 3 ^ 40 * 5369339 * 2
def baseEnd_5369339 : Nat := 919017234643824390056455

theorem tailTrace_5369339 : CollatzResearch.WordTrace tailWord_5369339 prefixEnd_5369339 919017234643824390056455 := by
  unfold tailWord_5369339
  simp only [CollatzResearch.WordTrace]
  refine ⟨195835881894809287939407071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130557254596539525292938047 195835881894809287939407071)
  ·
    refine ⟨293753822842213931909110607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195835881894809287939407071 293753822842213931909110607)
    ·
      refine ⟨440630734263320897863665911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293753822842213931909110607 440630734263320897863665911)
      ·
        refine ⟨660946101394981346795498867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440630734263320897863665911 660946101394981346795498867)
        ·
          refine ⟨991419152092472020193248301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660946101394981346795498867 991419152092472020193248301)
          ·
            refine ⟨371782182034677007572468113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 991419152092472020193248301 371782182034677007572468113)
            ·
              refine ⟨278836636526007755679351085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371782182034677007572468113 278836636526007755679351085)
              ·
                refine ⟨104563738697252908379756657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278836636526007755679351085 104563738697252908379756657)
                ·
                  refine ⟨78422804022939681284817493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104563738697252908379756657 78422804022939681284817493)
                  ·
                    refine ⟨919017234643824390056455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78422804022939681284817493 919017234643824390056455)
                    ·
                      rfl

theorem cell23_5369339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 8].length) (baseStart_5369339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369339 prefixEnd_5369339 := by exact prefixLift 5369339
  have htrace : WordTrace (prefixWord ++ tailWord_5369339) baseStart_5369339 baseEnd_5369339 := by
    simpa [prefixWord, tailWord_5369339, baseEnd_5369339] using wordTrace_append hprefix tailTrace_5369339
  have hstable : (prefixWord ++ tailWord_5369339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369339).length < 2 ^ (prefixWord ++ tailWord_5369339).sum := by decide
  have hdescent : baseEnd_5369339 < baseStart_5369339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369363 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 2, 4, 2]
def baseStart_5369363 : Nat := 118140960795 + 5369363 * 2 ^ 59
def prefixEnd_5369363 : Nat := 4983230072969 + 3 ^ 40 * 5369363 * 2
def baseEnd_5369363 : Nat := 2757064027467181076269255

theorem tailTrace_5369363 : CollatzResearch.WordTrace tailWord_5369363 prefixEnd_5369363 2757064027467181076269255 := by
  unfold tailWord_5369363
  simp only [CollatzResearch.WordTrace]
  refine ⟨195836757246722340038280743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130557838164481560025520495 195836757246722340038280743)
  ·
    refine ⟨293755135870083510057421115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195836757246722340038280743 293755135870083510057421115)
    ·
      refine ⟨440632703805125265086131673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293755135870083510057421115 440632703805125265086131673)
      ·
        refine ⟨330474527853843948814598755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440632703805125265086131673 330474527853843948814598755)
        ·
          refine ⟨495711791780765923221898133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330474527853843948814598755 495711791780765923221898133)
          ·
            refine ⟨23236490239723402651026475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 495711791780765923221898133 23236490239723402651026475)
            ·
              refine ⟨34854735359585103976539713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23236490239723402651026475 34854735359585103976539713)
              ·
                refine ⟨26141051519688827982404785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34854735359585103976539713 26141051519688827982404785)
                ·
                  refine ⟨19605788639766620986803589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26141051519688827982404785 19605788639766620986803589)
                  ·
                    refine ⟨3676085369956241435025673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19605788639766620986803589 3676085369956241435025673)
                    ·
                      refine ⟨2757064027467181076269255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3676085369956241435025673 2757064027467181076269255)
                      ·
                        rfl

theorem cell23_5369363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 4, 2].length) (baseStart_5369363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369363 prefixEnd_5369363 := by exact prefixLift 5369363
  have htrace : WordTrace (prefixWord ++ tailWord_5369363) baseStart_5369363 baseEnd_5369363 := by
    simpa [prefixWord, tailWord_5369363, baseEnd_5369363] using wordTrace_append hprefix tailTrace_5369363
  have hstable : (prefixWord ++ tailWord_5369363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369363).length < 2 ^ (prefixWord ++ tailWord_5369363).sum := by decide
  have hdescent : baseEnd_5369363 < baseStart_5369363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369390 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_5369390 : Nat := 118140960795 + 5369390 * 2 ^ 59
def prefixEnd_5369390 : Nat := 4983230072969 + 3 ^ 40 * 5369390 * 2
def baseEnd_5369390 : Nat := 919025963814950823543877

theorem tailTrace_5369390 : CollatzResearch.WordTrace tailWord_5369390 prefixEnd_5369390 919025963814950823543877 := by
  unfold tailWord_5369390
  simp only [CollatzResearch.WordTrace]
  refine ⟨24479717752203065456189203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130558494678416349099675749 24479717752203065456189203)
  ·
    refine ⟨36719576628304598184283805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24479717752203065456189203 36719576628304598184283805)
    ·
      refine ⟨13769841235614224319106427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36719576628304598184283805 13769841235614224319106427)
      ·
        refine ⟨20654761853421336478659641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13769841235614224319106427 20654761853421336478659641)
        ·
          refine ⟨15491071390066002358994731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20654761853421336478659641 15491071390066002358994731)
          ·
            refine ⟨23236607085099003538492097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15491071390066002358994731 23236607085099003538492097)
            ·
              refine ⟨17427455313824252653869073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23236607085099003538492097 17427455313824252653869073)
              ·
                refine ⟨13070591485368189490401805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17427455313824252653869073 13070591485368189490401805)
                ·
                  refine ⟨4901471807013071058900677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13070591485368189490401805 4901471807013071058900677)
                  ·
                    refine ⟨919025963814950823543877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4901471807013071058900677 919025963814950823543877)
                    ·
                      rfl

theorem cell23_5369390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_5369390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369390 prefixEnd_5369390 := by exact prefixLift 5369390
  have htrace : WordTrace (prefixWord ++ tailWord_5369390) baseStart_5369390 baseEnd_5369390 := by
    simpa [prefixWord, tailWord_5369390, baseEnd_5369390] using wordTrace_append hprefix tailTrace_5369390
  have hstable : (prefixWord ++ tailWord_5369390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369390).length < 2 ^ (prefixWord ++ tailWord_5369390).sum := by decide
  have hdescent : baseEnd_5369390 < baseStart_5369390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369407 : List Nat := [1, 1, 2, 2, 3, 5, 1, 3, 1, 4]
def baseStart_5369407 : Nat := 118140960795 + 5369407 * 2 ^ 59
def prefixEnd_5369407 : Nat := 4983230072969 + 3 ^ 40 * 5369407 * 2
def baseEnd_5369407 : Nat := 919028873538659634706351

theorem tailTrace_5369407 : CollatzResearch.WordTrace tailWord_5369407 prefixEnd_5369407 919028873538659634706351 := by
  unfold tailWord_5369407
  simp only [CollatzResearch.WordTrace]
  refine ⟨195838362058562935552882475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130558908039041957035254983 195838362058562935552882475)
  ·
    refine ⟨293757543087844403329323713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195838362058562935552882475 293757543087844403329323713)
    ·
      refine ⟨220318157315883302496992785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293757543087844403329323713 220318157315883302496992785)
      ·
        refine ⟨165238617986912476872744589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220318157315883302496992785 165238617986912476872744589)
        ·
          refine ⟨61964481745092178827279221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165238617986912476872744589 61964481745092178827279221)
          ·
            refine ⟨5809170163602391765057427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61964481745092178827279221 5809170163602391765057427)
            ·
              refine ⟨8713755245403587647586141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5809170163602391765057427 8713755245403587647586141)
              ·
                refine ⟨3267658217026345367844803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8713755245403587647586141 3267658217026345367844803)
                ·
                  refine ⟨4901487325539518051767205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267658217026345367844803 4901487325539518051767205)
                  ·
                    refine ⟨919028873538659634706351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4901487325539518051767205 919028873538659634706351)
                    ·
                      rfl

theorem cell23_5369407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 1, 4].length) (baseStart_5369407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369407 prefixEnd_5369407 := by exact prefixLift 5369407
  have htrace : WordTrace (prefixWord ++ tailWord_5369407) baseStart_5369407 baseEnd_5369407 := by
    simpa [prefixWord, tailWord_5369407, baseEnd_5369407] using wordTrace_append hprefix tailTrace_5369407
  have hstable : (prefixWord ++ tailWord_5369407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369407).length < 2 ^ (prefixWord ++ tailWord_5369407).sum := by decide
  have hdescent : baseEnd_5369407 < baseStart_5369407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369416 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 7, 5]
def baseStart_5369416 : Nat := 118140960795 + 5369416 * 2 ^ 59
def prefixEnd_5369416 : Nat := 4983230072969 + 3 ^ 40 * 5369416 * 2
def baseEnd_5369416 : Nat := 919030413980623122968837

theorem tailTrace_5369416 : CollatzResearch.WordTrace tailWord_5369416 prefixEnd_5369416 919030413980623122968837 := by
  unfold tailWord_5369416
  simp only [CollatzResearch.WordTrace]
  refine ⟨97919345157765165044980051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130559126877020220059973401 97919345157765165044980051)
  ·
    refine ⟨146879017736647747567470077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97919345157765165044980051 146879017736647747567470077)
    ·
      refine ⟨55079631651242905337801279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146879017736647747567470077 55079631651242905337801279)
      ·
        refine ⟨82619447476864358006701919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55079631651242905337801279 82619447476864358006701919)
        ·
          refine ⟨123929171215296537010052879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82619447476864358006701919 123929171215296537010052879)
          ·
            refine ⟨185893756822944805515079319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123929171215296537010052879 185893756822944805515079319)
            ·
              refine ⟨278840635234417208272618979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185893756822944805515079319 278840635234417208272618979)
              ·
                refine ⟨418260952851625812408928469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278840635234417208272618979 418260952851625812408928469)
                ·
                  refine ⟨9802991082459979978334261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 418260952851625812408928469 9802991082459979978334261)
                  ·
                    refine ⟨919030413980623122968837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9802991082459979978334261 919030413980623122968837)
                    ·
                      rfl

theorem cell23_5369416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_5369416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369416 prefixEnd_5369416 := by exact prefixLift 5369416
  have htrace : WordTrace (prefixWord ++ tailWord_5369416) baseStart_5369416 baseEnd_5369416 := by
    simpa [prefixWord, tailWord_5369416, baseEnd_5369416] using wordTrace_append hprefix tailTrace_5369416
  have hstable : (prefixWord ++ tailWord_5369416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369416).length < 2 ^ (prefixWord ++ tailWord_5369416).sum := by decide
  have hdescent : baseEnd_5369416 < baseStart_5369416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369437 : List Nat := [1, 4, 4, 2, 1, 1, 1, 3, 6]
def baseStart_5369437 : Nat := 118140960795 + 5369437 * 2 ^ 59
def prefixEnd_5369437 : Nat := 4983230072969 + 3 ^ 40 * 5369437 * 2
def baseEnd_5369437 : Nat := 306344669448401531860435

theorem tailTrace_5369437 : CollatzResearch.WordTrace tailWord_5369437 prefixEnd_5369437 306344669448401531860435 := by
  unfold tailWord_5369437
  simp only [CollatzResearch.WordTrace]
  refine ⟨195839456248454250676474565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130559637498969500450983043 195839456248454250676474565)
  ·
    refine ⟨36719898046585172001838981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195839456248454250676474565 36719898046585172001838981)
    ·
      refine ⟨6884980883734719750344809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36719898046585172001838981 6884980883734719750344809)
      ·
        refine ⟨5163735662801039812758607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6884980883734719750344809 5163735662801039812758607)
        ·
          refine ⟨7745603494201559719137911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5163735662801039812758607 7745603494201559719137911)
          ·
            refine ⟨11618405241302339578706867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7745603494201559719137911 11618405241302339578706867)
            ·
              refine ⟨17427607861953509368060301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11618405241302339578706867 17427607861953509368060301)
              ·
                refine ⟨6535352948232566013022613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17427607861953509368060301 6535352948232566013022613)
                ·
                  refine ⟨306344669448401531860435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6535352948232566013022613 306344669448401531860435)
                  ·
                    rfl

theorem cell23_5369437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_5369437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369437 prefixEnd_5369437 := by exact prefixLift 5369437
  have htrace : WordTrace (prefixWord ++ tailWord_5369437) baseStart_5369437 baseEnd_5369437 := by
    simpa [prefixWord, tailWord_5369437, baseEnd_5369437] using wordTrace_append hprefix tailTrace_5369437
  have hstable : (prefixWord ++ tailWord_5369437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369437).length < 2 ^ (prefixWord ++ tailWord_5369437).sum := by decide
  have hdescent : baseEnd_5369437 < baseStart_5369437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369450 : List Nat := [3, 1, 3, 2, 1, 2, 3, 2, 1, 5]
def baseStart_5369450 : Nat := 118140960795 + 5369450 * 2 ^ 59
def prefixEnd_5369450 : Nat := 4983230072969 + 3 ^ 40 * 5369450 * 2
def baseEnd_5369450 : Nat := 919036233428040745293785

theorem tailTrace_5369450 : CollatzResearch.WordTrace tailWord_5369450 prefixEnd_5369450 919036233428040745293785 := by
  unfold tailWord_5369450
  simp only [CollatzResearch.WordTrace]
  refine ⟨48959982599351788474174451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130559953598271435931131869 48959982599351788474174451)
  ·
    refine ⟨73439973899027682711261677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48959982599351788474174451 73439973899027682711261677)
    ·
      refine ⟨27539990212135381016723129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73439973899027682711261677 27539990212135381016723129)
      ·
        refine ⟨20654992659101535762542347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27539990212135381016723129 20654992659101535762542347)
        ·
          refine ⟨30982488988652303643813521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20654992659101535762542347 30982488988652303643813521)
          ·
            refine ⟨23236866741489227732860141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30982488988652303643813521 23236866741489227732860141)
            ·
              refine ⟨8713825028058460399822553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23236866741489227732860141 8713825028058460399822553)
              ·
                refine ⟨6535368771043845299866915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8713825028058460399822553 6535368771043845299866915)
                ·
                  refine ⟨9803053156565767949800373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6535368771043845299866915 9803053156565767949800373)
                  ·
                    refine ⟨919036233428040745293785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9803053156565767949800373 919036233428040745293785)
                    ·
                      rfl

theorem cell23_5369450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_5369450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369450 prefixEnd_5369450 := by exact prefixLift 5369450
  have htrace : WordTrace (prefixWord ++ tailWord_5369450) baseStart_5369450 baseEnd_5369450 := by
    simpa [prefixWord, tailWord_5369450, baseEnd_5369450] using wordTrace_append hprefix tailTrace_5369450
  have hstable : (prefixWord ++ tailWord_5369450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369450).length < 2 ^ (prefixWord ++ tailWord_5369450).sum := by decide
  have hdescent : baseEnd_5369450 < baseStart_5369450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369466 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_5369466 : Nat := 118140960795 + 5369466 * 2 ^ 59
def prefixEnd_5369466 : Nat := 4983230072969 + 3 ^ 40 * 5369466 * 2
def baseEnd_5369466 : Nat := 2757116915974594173281281

theorem tailTrace_5369466 : CollatzResearch.WordTrace tailWord_5369466 prefixEnd_5369466 2757116915974594173281281 := by
  unfold tailWord_5369466
  simp only [CollatzResearch.WordTrace]
  refine ⟨48960128491337297157320063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130560342643566125752853501 48960128491337297157320063)
  ·
    refine ⟨73440192737005945735980095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48960128491337297157320063 73440192737005945735980095)
    ·
      refine ⟨110160289105508918603970143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73440192737005945735980095 110160289105508918603970143)
      ·
        refine ⟨165240433658263377905955215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110160289105508918603970143 165240433658263377905955215)
        ·
          refine ⟨247860650487395066858932823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165240433658263377905955215 247860650487395066858932823)
          ·
            refine ⟨371790975731092600288399235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247860650487395066858932823 371790975731092600288399235)
            ·
              refine ⟨557686463596638900432598853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371790975731092600288399235 557686463596638900432598853)
              ·
                refine ⟨104566211924369793831112285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 557686463596638900432598853 104566211924369793831112285)
                ·
                  refine ⟨39212329471638672686667107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104566211924369793831112285 39212329471638672686667107)
                  ·
                    refine ⟨58818494207458009030000661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39212329471638672686667107 58818494207458009030000661)
                    ·
                      refine ⟨2757116915974594173281281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58818494207458009030000661 2757116915974594173281281)
                      ·
                        rfl

theorem cell23_5369466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_5369466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369466 prefixEnd_5369466 := by exact prefixLift 5369466
  have htrace : WordTrace (prefixWord ++ tailWord_5369466) baseStart_5369466 baseEnd_5369466 := by
    simpa [prefixWord, tailWord_5369466, baseEnd_5369466] using wordTrace_append hprefix tailTrace_5369466
  have hstable : (prefixWord ++ tailWord_5369466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369466).length < 2 ^ (prefixWord ++ tailWord_5369466).sum := by decide
  have hdescent : baseEnd_5369466 < baseStart_5369466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369476 : List Nat := [2, 3, 2, 1, 15]
def baseStart_5369476 : Nat := 118140960795 + 5369476 * 2 ^ 59
def prefixEnd_5369476 : Nat := 4983230072969 + 3 ^ 40 * 5369476 * 2
def baseEnd_5369476 : Nat := 3782060426311576315715

theorem tailTrace_5369476 : CollatzResearch.WordTrace tailWord_5369476 prefixEnd_5369476 3782060426311576315715 := by
  unfold tailWord_5369476
  simp only [CollatzResearch.WordTrace]
  refine ⟨97920439347656480168572141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130560585796875306891429521 97920439347656480168572141)
  ·
    refine ⟨36720164755371180063214553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97920439347656480168572141 36720164755371180063214553)
    ·
      refine ⟨27540123566528385047410915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36720164755371180063214553 27540123566528385047410915)
      ·
        refine ⟨41310185349792577571116373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27540123566528385047410915 41310185349792577571116373)
        ·
          refine ⟨3782060426311576315715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 41310185349792577571116373 3782060426311576315715)
          ·
            rfl

theorem cell23_5369476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 15].length) (baseStart_5369476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369476 prefixEnd_5369476 := by exact prefixLift 5369476
  have htrace : WordTrace (prefixWord ++ tailWord_5369476) baseStart_5369476 baseEnd_5369476 := by
    simpa [prefixWord, tailWord_5369476, baseEnd_5369476] using wordTrace_append hprefix tailTrace_5369476
  have hstable : (prefixWord ++ tailWord_5369476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369476).length < 2 ^ (prefixWord ++ tailWord_5369476).sum := by decide
  have hdescent : baseEnd_5369476 < baseStart_5369476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369553 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 2, 6]
def baseStart_5369553 : Nat := 118140960795 + 5369553 * 2 ^ 59
def prefixEnd_5369553 : Nat := 4983230072969 + 3 ^ 40 * 5369553 * 2
def baseEnd_5369553 : Nat := 919053862930511777631127

theorem tailTrace_5369553 : CollatzResearch.WordTrace tailWord_5369553 prefixEnd_5369553 919053862930511777631127 := by
  unfold tailWord_5369553
  simp only [CollatzResearch.WordTrace]
  refine ⟨195843687116034002487697313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130562458077356001658464875 195843687116034002487697313)
  ·
    refine ⟨146882765337025501865772985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195843687116034002487697313 146882765337025501865772985)
    ·
      refine ⟨110162074002769126399329739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146882765337025501865772985 110162074002769126399329739)
      ·
        refine ⟨165243111004153689598994609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110162074002769126399329739 165243111004153689598994609)
        ·
          refine ⟨123932333253115267199245957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165243111004153689598994609 123932333253115267199245957)
          ·
            refine ⟨23237312484959112599858617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123932333253115267199245957 23237312484959112599858617)
            ·
              refine ⟨17427984363719334449893963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23237312484959112599858617 17427984363719334449893963)
              ·
                refine ⟨26141976545579001674840945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17427984363719334449893963 26141976545579001674840945)
                ·
                  refine ⟨19606482409184251256130709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26141976545579001674840945 19606482409184251256130709)
                  ·
                    refine ⟨919053862930511777631127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19606482409184251256130709 919053862930511777631127)
                    ·
                      rfl

theorem cell23_5369553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_5369553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369553 prefixEnd_5369553 := by exact prefixLift 5369553
  have htrace : WordTrace (prefixWord ++ tailWord_5369553) baseStart_5369553 baseEnd_5369553 := by
    simpa [prefixWord, tailWord_5369553, baseEnd_5369553] using wordTrace_append hprefix tailTrace_5369553
  have hstable : (prefixWord ++ tailWord_5369553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369553).length < 2 ^ (prefixWord ++ tailWord_5369553).sum := by decide
  have hdescent : baseEnd_5369553 < baseStart_5369553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369640 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_5369640 : Nat := 118140960795 + 5369640 * 2 ^ 59
def prefixEnd_5369640 : Nat := 4983230072969 + 3 ^ 40 * 5369640 * 2
def baseEnd_5369640 : Nat := 2757206261608476492505481

theorem tailTrace_5369640 : CollatzResearch.WordTrace tailWord_5369640 prefixEnd_5369640 2757206261608476492505481 := by
  unfold tailWord_5369640
  simp only [CollatzResearch.WordTrace]
  refine ⟨97923430133359408173057187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130564573511145877564076249 97923430133359408173057187)
  ·
    refine ⟨146885145200039112259585781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97923430133359408173057187 146885145200039112259585781)
    ·
      refine ⟨13770482362503666774336167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146885145200039112259585781 13770482362503666774336167)
      ·
        refine ⟨20655723543755500161504251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13770482362503666774336167 20655723543755500161504251)
        ·
          refine ⟨30983585315633250242256377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20655723543755500161504251 30983585315633250242256377)
          ·
            refine ⟨23237688986724937681692283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30983585315633250242256377 23237688986724937681692283)
            ·
              refine ⟨34856533480087406522538425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23237688986724937681692283 34856533480087406522538425)
              ·
                refine ⟨26142400110065554891903819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34856533480087406522538425 26142400110065554891903819)
                ·
                  refine ⟨39213600165098332337855729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26142400110065554891903819 39213600165098332337855729)
                  ·
                    refine ⟨29410200123823749253391797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39213600165098332337855729 29410200123823749253391797)
                    ·
                      refine ⟨2757206261608476492505481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29410200123823749253391797 2757206261608476492505481)
                      ·
                        rfl

theorem cell23_5369640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_5369640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369640 prefixEnd_5369640 := by exact prefixLift 5369640
  have htrace : WordTrace (prefixWord ++ tailWord_5369640) baseStart_5369640 baseEnd_5369640 := by
    simpa [prefixWord, tailWord_5369640, baseEnd_5369640] using wordTrace_append hprefix tailTrace_5369640
  have hstable : (prefixWord ++ tailWord_5369640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369640).length < 2 ^ (prefixWord ++ tailWord_5369640).sum := by decide
  have hdescent : baseEnd_5369640 < baseStart_5369640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369651 : List Nat := [1, 1, 1, 2, 8, 1, 2, 2, 5]
def baseStart_5369651 : Nat := 118140960795 + 5369651 * 2 ^ 59
def prefixEnd_5369651 : Nat := 4983230072969 + 3 ^ 40 * 5369651 * 2
def baseEnd_5369651 : Nat := 306356878877297327718659

theorem tailTrace_5369651 : CollatzResearch.WordTrace tailWord_5369651 prefixEnd_5369651 306356878877297327718659 := by
  unfold tailWord_5369651
  simp only [CollatzResearch.WordTrace]
  refine ⟨195847261469678965224764807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130564840979785976816509871 195847261469678965224764807)
  ·
    refine ⟨293770892204518447837147211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195847261469678965224764807 293770892204518447837147211)
    ·
      refine ⟨440656338306777671755720817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293770892204518447837147211 440656338306777671755720817)
      ·
        refine ⟨330492253730083253816790613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440656338306777671755720817 330492253730083253816790613)
        ·
          refine ⟨3872956098399413130665515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 330492253730083253816790613 3872956098399413130665515)
          ·
            refine ⟨5809434147599119695998273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3872956098399413130665515 5809434147599119695998273)
            ·
              refine ⟨4357075610699339771998705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5809434147599119695998273 4357075610699339771998705)
              ·
                refine ⟨3267806708024504828999029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4357075610699339771998705 3267806708024504828999029)
                ·
                  refine ⟨306356878877297327718659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3267806708024504828999029 306356878877297327718659)
                  ·
                    rfl

theorem cell23_5369651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 5].length) (baseStart_5369651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369651 prefixEnd_5369651 := by exact prefixLift 5369651
  have htrace : WordTrace (prefixWord ++ tailWord_5369651) baseStart_5369651 baseEnd_5369651 := by
    simpa [prefixWord, tailWord_5369651, baseEnd_5369651] using wordTrace_append hprefix tailTrace_5369651
  have hstable : (prefixWord ++ tailWord_5369651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369651).length < 2 ^ (prefixWord ++ tailWord_5369651).sum := by decide
  have hdescent : baseEnd_5369651 < baseStart_5369651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369654 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_5369654 : Nat := 118140960795 + 5369654 * 2 ^ 59
def prefixEnd_5369654 : Nat := 4983230072969 + 3 ^ 40 * 5369654 * 2
def baseEnd_5369654 : Nat := 2757213450337639437730417

theorem tailTrace_5369654 : CollatzResearch.WordTrace tailWord_5369654 prefixEnd_5369654 2757213450337639437730417 := by
  unfold tailWord_5369654
  simp only [CollatzResearch.WordTrace]
  refine ⟨12240460680541756046070251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130564913925778731158082677 12240460680541756046070251)
  ·
    refine ⟨18360691020812634069105377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12240460680541756046070251 18360691020812634069105377)
    ·
      refine ⟨13770518265609475551829033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18360691020812634069105377 13770518265609475551829033)
      ·
        refine ⟨10327888699207106663871775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13770518265609475551829033 10327888699207106663871775)
        ·
          refine ⟨15491833048810659995807663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10327888699207106663871775 15491833048810659995807663)
          ·
            refine ⟨23237749573215989993711495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15491833048810659995807663 23237749573215989993711495)
            ·
              refine ⟨34856624359823984990567243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23237749573215989993711495 34856624359823984990567243)
              ·
                refine ⟨52284936539735977485850865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34856624359823984990567243 52284936539735977485850865)
                ·
                  refine ⟨39213702404801983114388149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52284936539735977485850865 39213702404801983114388149)
                  ·
                    refine ⟨3676284600450185916973889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39213702404801983114388149 3676284600450185916973889)
                    ·
                      refine ⟨2757213450337639437730417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3676284600450185916973889 2757213450337639437730417)
                      ·
                        rfl

theorem cell23_5369654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_5369654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369654 prefixEnd_5369654 := by exact prefixLift 5369654
  have htrace : WordTrace (prefixWord ++ tailWord_5369654) baseStart_5369654 baseEnd_5369654 := by
    simpa [prefixWord, tailWord_5369654, baseEnd_5369654] using wordTrace_append hprefix tailTrace_5369654
  have hstable : (prefixWord ++ tailWord_5369654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369654).length < 2 ^ (prefixWord ++ tailWord_5369654).sum := by decide
  have hdescent : baseEnd_5369654 < baseStart_5369654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369667 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 2, 4, 2]
def baseStart_5369667 : Nat := 118140960795 + 5369667 * 2 ^ 59
def prefixEnd_5369667 : Nat := 4983230072969 + 3 ^ 40 * 5369667 * 2
def baseEnd_5369667 : Nat := 2757220125586147886867857

theorem tailTrace_5369667 : CollatzResearch.WordTrace tailWord_5369667 prefixEnd_5369667 2757220125586147886867857 := by
  unfold tailWord_5369667
  simp only [CollatzResearch.WordTrace]
  refine ⟨195847845037620999957347255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130565230025080666638231503 195847845037620999957347255)
  ·
    refine ⟨293771767556431499936020883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195847845037620999957347255 293771767556431499936020883)
    ·
      refine ⟨440657651334647249904031325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293771767556431499936020883 440657651334647249904031325)
      ·
        refine ⟨165246619250492718714011747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 440657651334647249904031325 165246619250492718714011747)
        ·
          refine ⟨247869928875739078071017621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165246619250492718714011747 247869928875739078071017621)
          ·
            refine ⟨11618902916050269284578951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 247869928875739078071017621 11618902916050269284578951)
            ·
              refine ⟨17428354374075403926868427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11618902916050269284578951 17428354374075403926868427)
              ·
                refine ⟨26142531561113105890302641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17428354374075403926868427 26142531561113105890302641)
                ·
                  refine ⟨19606898670834829417726981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26142531561113105890302641 19606898670834829417726981)
                  ·
                    refine ⟨3676293500781530515823809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19606898670834829417726981 3676293500781530515823809)
                    ·
                      refine ⟨2757220125586147886867857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3676293500781530515823809 2757220125586147886867857)
                      ·
                        rfl

theorem cell23_5369667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 4, 2].length) (baseStart_5369667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369667 prefixEnd_5369667 := by exact prefixLift 5369667
  have htrace : WordTrace (prefixWord ++ tailWord_5369667) baseStart_5369667 baseEnd_5369667 := by
    simpa [prefixWord, tailWord_5369667, baseEnd_5369667] using wordTrace_append hprefix tailTrace_5369667
  have hstable : (prefixWord ++ tailWord_5369667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369667).length < 2 ^ (prefixWord ++ tailWord_5369667).sum := by decide
  have hdescent : baseEnd_5369667 < baseStart_5369667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369684 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_5369684 : Nat := 118140960795 + 5369684 * 2 ^ 59
def prefixEnd_5369684 : Nat := 4983230072969 + 3 ^ 40 * 5369684 * 2
def baseEnd_5369684 : Nat := 2757228854757274320355279

theorem tailTrace_5369684 : CollatzResearch.WordTrace tailWord_5369684 prefixEnd_5369684 2757228854757274320355279 := by
  unfold tailWord_5369684
  simp only [CollatzResearch.WordTrace]
  refine ⟨97924232539279705930358053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130565643385706274573810737 97924232539279705930358053)
  ·
    refine ⟨18360793601114944861942135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97924232539279705930358053 18360793601114944861942135)
    ·
      refine ⟨27541190401672417292913203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18360793601114944861942135 27541190401672417292913203)
      ·
        refine ⟨41311785602508625939369805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27541190401672417292913203 41311785602508625939369805)
        ·
          refine ⟨15491919600940734727263677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41311785602508625939369805 15491919600940734727263677)
          ·
            refine ⟨5809469850352775522723879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15491919600940734727263677 5809469850352775522723879)
            ·
              refine ⟨8714204775529163284085819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5809469850352775522723879 8714204775529163284085819)
              ·
                refine ⟨13071307163293744926128729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8714204775529163284085819 13071307163293744926128729)
                ·
                  refine ⟨9803480372470308694596547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13071307163293744926128729 9803480372470308694596547)
                  ·
                    refine ⟨14705220558705463041894821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9803480372470308694596547 14705220558705463041894821)
                    ·
                      refine ⟨2757228854757274320355279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14705220558705463041894821 2757228854757274320355279)
                      ·
                        rfl

theorem cell23_5369684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_5369684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369684 prefixEnd_5369684 := by exact prefixLift 5369684
  have htrace : WordTrace (prefixWord ++ tailWord_5369684) baseStart_5369684 baseEnd_5369684 := by
    simpa [prefixWord, tailWord_5369684, baseEnd_5369684] using wordTrace_append hprefix tailTrace_5369684
  have hstable : (prefixWord ++ tailWord_5369684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369684).length < 2 ^ (prefixWord ++ tailWord_5369684).sum := by decide
  have hdescent : baseEnd_5369684 < baseStart_5369684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369687 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 3]
def baseStart_5369687 : Nat := 118140960795 + 5369687 * 2 ^ 59
def prefixEnd_5369687 : Nat := 4983230072969 + 3 ^ 40 * 5369687 * 2
def baseEnd_5369687 : Nat := 2757230395199237808617765

theorem tailTrace_5369687 : CollatzResearch.WordTrace tailWord_5369687 prefixEnd_5369687 2757230395199237808617765 := by
  unfold tailWord_5369687
  simp only [CollatzResearch.WordTrace]
  refine ⟨195848574497548543373075315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130565716331699028915383543 195848574497548543373075315)
  ·
    refine ⟨293772861746322815059612973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195848574497548543373075315 293772861746322815059612973)
    ·
      refine ⟨110164823154871055647354865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293772861746322815059612973 110164823154871055647354865)
      ·
        refine ⟨82623617366153291735516149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110164823154871055647354865 82623617366153291735516149)
        ·
          refine ⟨7745964128076871100204639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82623617366153291735516149 7745964128076871100204639)
          ·
            refine ⟨11618946192115306650306959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7745964128076871100204639 11618946192115306650306959)
            ·
              refine ⟨17428419288172959975460439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11618946192115306650306959 17428419288172959975460439)
              ·
                refine ⟨26142628932259439963190659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17428419288172959975460439 26142628932259439963190659)
                ·
                  refine ⟨39213943398389159944785989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26142628932259439963190659 39213943398389159944785989)
                  ·
                    refine ⟨7352614387197967489647373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39213943398389159944785989 7352614387197967489647373)
                    ·
                      refine ⟨2757230395199237808617765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7352614387197967489647373 2757230395199237808617765)
                      ·
                        rfl

theorem cell23_5369687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_5369687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369687 prefixEnd_5369687 := by exact prefixLift 5369687
  have htrace : WordTrace (prefixWord ++ tailWord_5369687) baseStart_5369687 baseEnd_5369687 := by
    simpa [prefixWord, tailWord_5369687, baseEnd_5369687] using wordTrace_append hprefix tailTrace_5369687
  have hstable : (prefixWord ++ tailWord_5369687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369687).length < 2 ^ (prefixWord ++ tailWord_5369687).sum := by decide
  have hdescent : baseEnd_5369687 < baseStart_5369687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369737 : List Nat := [1, 2, 1, 1, 5, 1, 4, 2, 1, 5]
def baseStart_5369737 : Nat := 118140960795 + 5369737 * 2 ^ 59
def prefixEnd_5369737 : Nat := 4983230072969 + 3 ^ 40 * 5369737 * 2
def baseEnd_5369737 : Nat := 919085356410654204330845

theorem tailTrace_5369737 : CollatzResearch.WordTrace tailWord_5369737 prefixEnd_5369737 919085356410654204330845 := by
  unfold tailWord_5369737
  simp only [CollatzResearch.WordTrace]
  refine ⟨195850398147367401912395465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130566932098244934608263643 195850398147367401912395465)
  ·
    refine ⟨146887798610525551434296599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195850398147367401912395465 146887798610525551434296599)
    ·
      refine ⟨220331697915788327151444899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146887798610525551434296599 220331697915788327151444899)
      ·
        refine ⟨330497546873682490727167349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220331697915788327151444899 330497546873682490727167349)
        ·
          refine ⟨30984145019407733505671939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 330497546873682490727167349 30984145019407733505671939)
          ·
            refine ⟨46476217529111600258507909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30984145019407733505671939 46476217529111600258507909)
            ·
              refine ⟨8714290786708425048470233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46476217529111600258507909 8714290786708425048470233)
              ·
                refine ⟨6535718090031318786352675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8714290786708425048470233 6535718090031318786352675)
                ·
                  refine ⟨9803577135046978179529013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6535718090031318786352675 9803577135046978179529013)
                  ·
                    refine ⟨919085356410654204330845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9803577135046978179529013 919085356410654204330845)
                    ·
                      rfl

theorem cell23_5369737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 5].length) (baseStart_5369737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369737 prefixEnd_5369737 := by exact prefixLift 5369737
  have htrace : WordTrace (prefixWord ++ tailWord_5369737) baseStart_5369737 baseEnd_5369737 := by
    simpa [prefixWord, tailWord_5369737, baseEnd_5369737] using wordTrace_append hprefix tailTrace_5369737
  have hstable : (prefixWord ++ tailWord_5369737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369737).length < 2 ^ (prefixWord ++ tailWord_5369737).sum := by decide
  have hdescent : baseEnd_5369737 < baseStart_5369737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369751 : List Nat := [1, 1, 3, 3, 1, 3, 3, 3, 1, 1, 3]
def baseStart_5369751 : Nat := 118140960795 + 5369751 * 2 ^ 59
def prefixEnd_5369751 : Nat := 4983230072969 + 3 ^ 40 * 5369751 * 2
def baseEnd_5369751 : Nat := 2757263257961125558217471

theorem tailTrace_5369751 : CollatzResearch.WordTrace tailWord_5369751 prefixEnd_5369751 2757263257961125558217471 := by
  unfold tailWord_5369751
  simp only [CollatzResearch.WordTrace]
  refine ⟨195850908769316682303405107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130567272512877788202270071 195850908769316682303405107)
  ·
    refine ⟨293776363153975023455107661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195850908769316682303405107 293776363153975023455107661)
    ·
      refine ⟨110166136182740633795665373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293776363153975023455107661 110166136182740633795665373)
      ·
        refine ⟨41312301068527737673374515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110166136182740633795665373 41312301068527737673374515)
        ·
          refine ⟨61968451602791606510061773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41312301068527737673374515 61968451602791606510061773)
          ·
            refine ⟨23238169351046852441273165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61968451602791606510061773 23238169351046852441273165)
            ·
              refine ⟨8714313506642569665477437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23238169351046852441273165 8714313506642569665477437)
              ·
                refine ⟨3267867564990963624554039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8714313506642569665477437 3267867564990963624554039)
                ·
                  refine ⟨4901801347486445436831059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267867564990963624554039 4901801347486445436831059)
                  ·
                    refine ⟨7352702021229668155246589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4901801347486445436831059 7352702021229668155246589)
                    ·
                      refine ⟨2757263257961125558217471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7352702021229668155246589 2757263257961125558217471)
                      ·
                        rfl

theorem cell23_5369751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_5369751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369751 prefixEnd_5369751 := by exact prefixLift 5369751
  have htrace : WordTrace (prefixWord ++ tailWord_5369751) baseStart_5369751 baseEnd_5369751 := by
    simpa [prefixWord, tailWord_5369751, baseEnd_5369751] using wordTrace_append hprefix tailTrace_5369751
  have hstable : (prefixWord ++ tailWord_5369751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369751).length < 2 ^ (prefixWord ++ tailWord_5369751).sum := by decide
  have hdescent : baseEnd_5369751 < baseStart_5369751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369761 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 2, 3, 2]
def baseStart_5369761 : Nat := 118140960795 + 5369761 * 2 ^ 59
def prefixEnd_5369761 : Nat := 4983230072969 + 3 ^ 40 * 5369761 * 2
def baseEnd_5369761 : Nat := 2757268392767670519092425

theorem tailTrace_5369761 : CollatzResearch.WordTrace tailWord_5369761 prefixEnd_5369761 2757268392767670519092425 := by
  unfold tailWord_5369761
  simp only [CollatzResearch.WordTrace]
  refine ⟨195851273499280454011269137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130567515666186969340846091 195851273499280454011269137)
  ·
    refine ⟨146888455124460340508451853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195851273499280454011269137 146888455124460340508451853)
    ·
      refine ⟨55083170671672627690669445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146888455124460340508451853 55083170671672627690669445)
      ·
        refine ⟨10328094500938617692000521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55083170671672627690669445 10328094500938617692000521)
        ·
          refine ⟨7746070875703963269000391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10328094500938617692000521 7746070875703963269000391)
          ·
            refine ⟨11619106313555944903500587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7746070875703963269000391 11619106313555944903500587)
            ·
              refine ⟨17428659470333917355250881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11619106313555944903500587 17428659470333917355250881)
              ·
                refine ⟨13071494602750438016438161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17428659470333917355250881 13071494602750438016438161)
                ·
                  refine ⟨9803620952062828512328621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13071494602750438016438161 9803620952062828512328621)
                  ·
                    refine ⟨3676357857023560692123233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9803620952062828512328621 3676357857023560692123233)
                    ·
                      refine ⟨2757268392767670519092425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3676357857023560692123233 2757268392767670519092425)
                      ·
                        rfl

theorem cell23_5369761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_5369761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369761 prefixEnd_5369761 := by exact prefixLift 5369761
  have htrace : WordTrace (prefixWord ++ tailWord_5369761) baseStart_5369761 baseEnd_5369761 := by
    simpa [prefixWord, tailWord_5369761, baseEnd_5369761] using wordTrace_append hprefix tailTrace_5369761
  have hstable : (prefixWord ++ tailWord_5369761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369761).length < 2 ^ (prefixWord ++ tailWord_5369761).sum := by decide
  have hdescent : baseEnd_5369761 < baseStart_5369761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369777 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 1, 1, 5]
def baseStart_5369777 : Nat := 118140960795 + 5369777 * 2 ^ 59
def prefixEnd_5369777 : Nat := 4983230072969 + 3 ^ 40 * 5369777 * 2
def baseEnd_5369777 : Nat := 2757276608458142456492351

theorem tailTrace_5369777 : CollatzResearch.WordTrace tailWord_5369777 prefixEnd_5369777 2757276608458142456492351 := by
  unfold tailWord_5369777
  simp only [CollatzResearch.WordTrace]
  refine ⟨195851857067222488743851585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130567904711481659162567723 195851857067222488743851585)
  ·
    refine ⟨146888892800416866557888689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195851857067222488743851585 146888892800416866557888689)
    ·
      refine ⟨110166669600312649918416517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146888892800416866557888689 110166669600312649918416517)
      ·
        refine ⟨20656250550058621859703097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110166669600312649918416517 20656250550058621859703097)
        ·
          refine ⟨15492187912543966394777323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20656250550058621859703097 15492187912543966394777323)
          ·
            refine ⟨23238281868815949592165985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15492187912543966394777323 23238281868815949592165985)
            ·
              refine ⟨17428711401611962194124489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23238281868815949592165985 17428711401611962194124489)
              ·
                refine ⟨13071533551208971645593367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17428711401611962194124489 13071533551208971645593367)
                ·
                  refine ⟨19607300326813457468390051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13071533551208971645593367 19607300326813457468390051)
                  ·
                    refine ⟨29410950490220186202585077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19607300326813457468390051 29410950490220186202585077)
                    ·
                      refine ⟨2757276608458142456492351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29410950490220186202585077 2757276608458142456492351)
                      ·
                        rfl

theorem cell23_5369777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_5369777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369777 prefixEnd_5369777 := by exact prefixLift 5369777
  have htrace : WordTrace (prefixWord ++ tailWord_5369777) baseStart_5369777 baseEnd_5369777 := by
    simpa [prefixWord, tailWord_5369777, baseEnd_5369777] using wordTrace_append hprefix tailTrace_5369777
  have hstable : (prefixWord ++ tailWord_5369777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369777).length < 2 ^ (prefixWord ++ tailWord_5369777).sum := by decide
  have hdescent : baseEnd_5369777 < baseStart_5369777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369788 : List Nat := [2, 2, 2, 5, 2, 1, 1, 2, 1, 5]
def baseStart_5369788 : Nat := 118140960795 + 5369788 * 2 ^ 59
def prefixEnd_5369788 : Nat := 4983230072969 + 3 ^ 40 * 5369788 * 2
def baseEnd_5369788 : Nat := 919094085581780637818267

theorem tailTrace_5369788 : CollatzResearch.WordTrace tailWord_5369788 prefixEnd_5369788 919094085581780637818267 := by
  unfold tailWord_5369788
  simp only [CollatzResearch.WordTrace]
  refine ⟨97926129135091318811251009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130568172180121758415001345 97926129135091318811251009)
  ·
    refine ⟨73444596851318489108438257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97926129135091318811251009 73444596851318489108438257)
    ·
      refine ⟨55083447638488866831328693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73444596851318489108438257 55083447638488866831328693)
      ·
        refine ⟨5164073216108331265437065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55083447638488866831328693 5164073216108331265437065)
        ·
          refine ⟨3873054912081248449077799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5164073216108331265437065 3873054912081248449077799)
          ·
            refine ⟨5809582368121872673616699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3873054912081248449077799 5809582368121872673616699)
            ·
              refine ⟨8714373552182809010425049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5809582368121872673616699 8714373552182809010425049)
              ·
                refine ⟨6535780164137106757818787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8714373552182809010425049 6535780164137106757818787)
                ·
                  refine ⟨9803670246205660136728181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6535780164137106757818787 9803670246205660136728181)
                  ·
                    refine ⟨919094085581780637818267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9803670246205660136728181 919094085581780637818267)
                    ·
                      rfl

theorem cell23_5369788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_5369788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369788 prefixEnd_5369788 := by exact prefixLift 5369788
  have htrace : WordTrace (prefixWord ++ tailWord_5369788) baseStart_5369788 baseEnd_5369788 := by
    simpa [prefixWord, tailWord_5369788, baseEnd_5369788] using wordTrace_append hprefix tailTrace_5369788
  have hstable : (prefixWord ++ tailWord_5369788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369788).length < 2 ^ (prefixWord ++ tailWord_5369788).sum := by decide
  have hdescent : baseEnd_5369788 < baseStart_5369788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369807 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 3]
def baseStart_5369807 : Nat := 118140960795 + 5369807 * 2 ^ 59
def prefixEnd_5369807 : Nat := 4983230072969 + 3 ^ 40 * 5369807 * 2
def baseEnd_5369807 : Nat := 2757292012877777339117213

theorem tailTrace_5369807 : CollatzResearch.WordTrace tailWord_5369807 prefixEnd_5369807 2757292012877777339117213 := by
  unfold tailWord_5369807
  simp only [CollatzResearch.WordTrace]
  refine ⟨195852951257113803867443675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130568634171409202578295783 195852951257113803867443675)
  ·
    refine ⟨293779426885670705801165513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195852951257113803867443675 293779426885670705801165513)
    ·
      refine ⟨220334570164253029350874135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293779426885670705801165513 220334570164253029350874135)
      ·
        refine ⟨330501855246379544026311203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220334570164253029350874135 330501855246379544026311203)
        ·
          refine ⟨495752782869569316039466805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330501855246379544026311203 495752782869569316039466805)
          ·
            refine ⟨46476823394022123378700013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 495752782869569316039466805 46476823394022123378700013)
            ·
              refine ⟨17428808772758296267012505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46476823394022123378700013 17428808772758296267012505)
              ·
                refine ⟨13071606579568722200259379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17428808772758296267012505 13071606579568722200259379)
                ·
                  refine ⟨19607409869353083300389069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13071606579568722200259379 19607409869353083300389069)
                  ·
                    refine ⟨7352778701007406237645901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19607409869353083300389069 7352778701007406237645901)
                    ·
                      refine ⟨2757292012877777339117213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7352778701007406237645901 2757292012877777339117213)
                      ·
                        rfl

theorem cell23_5369807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 3].length) (baseStart_5369807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369807 prefixEnd_5369807 := by exact prefixLift 5369807
  have htrace : WordTrace (prefixWord ++ tailWord_5369807) baseStart_5369807 baseEnd_5369807 := by
    simpa [prefixWord, tailWord_5369807, baseEnd_5369807] using wordTrace_append hprefix tailTrace_5369807
  have hstable : (prefixWord ++ tailWord_5369807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369807).length < 2 ^ (prefixWord ++ tailWord_5369807).sum := by decide
  have hdescent : baseEnd_5369807 < baseStart_5369807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369814 : List Nat := [5, 2, 1, 1, 4, 10]
def baseStart_5369814 : Nat := 118140960795 + 5369814 * 2 ^ 59
def prefixEnd_5369814 : Nat := 4983230072969 + 3 ^ 40 * 5369814 * 2
def baseEnd_5369814 : Nat := 11346895503054974533867

theorem tailTrace_5369814 : CollatzResearch.WordTrace tailWord_5369814 prefixEnd_5369814 11346895503054974533867 := by
  unfold tailWord_5369814
  simp only [CollatzResearch.WordTrace]
  refine ⟨12240825410505527753934281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130568804378725629375298997 12240825410505527753934281)
  ·
    refine ⟨9180619057879145815450711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12240825410505527753934281 9180619057879145815450711)
    ·
      refine ⟨13770928586818718723176067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9180619057879145815450711 13770928586818718723176067)
      ·
        refine ⟨20656392880228078084764101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13770928586818718723176067 20656392880228078084764101)
        ·
          refine ⟨3873073665042764640893269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20656392880228078084764101 3873073665042764640893269)
          ·
            refine ⟨11346895503054974533867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3873073665042764640893269 11346895503054974533867)
            ·
              rfl

theorem cell23_5369814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 10].length) (baseStart_5369814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369814 prefixEnd_5369814 := by exact prefixLift 5369814
  have htrace : WordTrace (prefixWord ++ tailWord_5369814) baseStart_5369814 baseEnd_5369814 := by
    simpa [prefixWord, tailWord_5369814, baseEnd_5369814] using wordTrace_append hprefix tailTrace_5369814
  have hstable : (prefixWord ++ tailWord_5369814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369814).length < 2 ^ (prefixWord ++ tailWord_5369814).sum := by decide
  have hdescent : baseEnd_5369814 < baseStart_5369814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369834 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_5369834 : Nat := 118140960795 + 5369834 * 2 ^ 59
def prefixEnd_5369834 : Nat := 4983230072969 + 3 ^ 40 * 5369834 * 2
def baseEnd_5369834 : Nat := 2757305876855448733479589

theorem tailTrace_5369834 : CollatzResearch.WordTrace tailWord_5369834 prefixEnd_5369834 2757305876855448733479589 := by
  unfold tailWord_5369834
  simp only [CollatzResearch.WordTrace]
  refine ⟨48963484007003996869669139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130569290685343991652451037 48963484007003996869669139)
  ·
    refine ⟨73445226010505995304503709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48963484007003996869669139 73445226010505995304503709)
    ·
      refine ⟨27541959753939748239188891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73445226010505995304503709 27541959753939748239188891)
      ·
        refine ⟨41312939630909622358783337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27541959753939748239188891 41312939630909622358783337)
        ·
          refine ⟨30984704723182216769087503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41312939630909622358783337 30984704723182216769087503)
          ·
            refine ⟨46477057084773325153631255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30984704723182216769087503 46477057084773325153631255)
            ·
              refine ⟨69715585627159987730446883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46477057084773325153631255 69715585627159987730446883)
              ·
                refine ⟨104573378440739981595670325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69715585627159987730446883 104573378440739981595670325)
                ·
                  refine ⟨9803754228819373274594093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104573378440739981595670325 9803754228819373274594093)
                  ·
                    refine ⟨3676407835807264977972785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9803754228819373274594093 3676407835807264977972785)
                    ·
                      refine ⟨2757305876855448733479589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3676407835807264977972785 2757305876855448733479589)
                      ·
                        rfl

theorem cell23_5369834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_5369834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369834 prefixEnd_5369834 := by exact prefixLift 5369834
  have htrace : WordTrace (prefixWord ++ tailWord_5369834) baseStart_5369834 baseEnd_5369834 := by
    simpa [prefixWord, tailWord_5369834, baseEnd_5369834] using wordTrace_append hprefix tailTrace_5369834
  have hstable : (prefixWord ++ tailWord_5369834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369834).length < 2 ^ (prefixWord ++ tailWord_5369834).sum := by decide
  have hdescent : baseEnd_5369834 < baseStart_5369834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369840 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 1, 8]
def baseStart_5369840 : Nat := 118140960795 + 5369840 * 2 ^ 59
def prefixEnd_5369840 : Nat := 4983230072969 + 3 ^ 40 * 5369840 * 2
def baseEnd_5369840 : Nat := 919102985913125236668187

theorem tailTrace_5369840 : CollatzResearch.WordTrace tailWord_5369840 prefixEnd_5369840 919102985913125236668187 := by
  unfold tailWord_5369840
  simp only [CollatzResearch.WordTrace]
  refine ⟨97927077432997125251697487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130569436577329500335596649 97927077432997125251697487)
  ·
    refine ⟨146890616149495687877546231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97927077432997125251697487 146890616149495687877546231)
    ·
      refine ⟨220335924224243531816319347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146890616149495687877546231 220335924224243531816319347)
      ·
        refine ⟨330503886336365297724479021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220335924224243531816319347 330503886336365297724479021)
        ·
          refine ⟨123938957376136986646679633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330503886336365297724479021 123938957376136986646679633)
          ·
            refine ⟨92954218032102739985009725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123938957376136986646679633 92954218032102739985009725)
            ·
              refine ⟨34857831762038527494378647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92954218032102739985009725 34857831762038527494378647)
              ·
                refine ⟨52286747643057791241567971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34857831762038527494378647 52286747643057791241567971)
                ·
                  refine ⟨78430121464586686862351957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52286747643057791241567971 78430121464586686862351957)
                  ·
                    refine ⟨919102985913125236668187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78430121464586686862351957 919102985913125236668187)
                    ·
                      rfl

theorem cell23_5369840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_5369840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369840 prefixEnd_5369840 := by exact prefixLift 5369840
  have htrace : WordTrace (prefixWord ++ tailWord_5369840) baseStart_5369840 baseEnd_5369840 := by
    simpa [prefixWord, tailWord_5369840, baseEnd_5369840] using wordTrace_append hprefix tailTrace_5369840
  have hstable : (prefixWord ++ tailWord_5369840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369840).length < 2 ^ (prefixWord ++ tailWord_5369840).sum := by decide
  have hdescent : baseEnd_5369840 < baseStart_5369840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369862 : List Nat := [6, 2, 1, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_5369862 : Nat := 118140960795 + 5369862 * 2 ^ 59
def prefixEnd_5369862 : Nat := 4983230072969 + 3 ^ 40 * 5369862 * 2
def baseEnd_5369862 : Nat := 2757320254313774623929461

theorem tailTrace_5369862 : CollatzResearch.WordTrace tailWord_5369862 prefixEnd_5369862 2757320254313774623929461 := by
  unfold tailWord_5369862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6120467414747329633146745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130569971514609698840463893 6120467414747329633146745)
  ·
    refine ⟨4590350561060497224860059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6120467414747329633146745 4590350561060497224860059)
    ·
      refine ⟨6885525841590745837290089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4590350561060497224860059 6885525841590745837290089)
      ·
        refine ⟨5164144381193059377967567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6885525841590745837290089 5164144381193059377967567)
        ·
          refine ⟨7746216571789589066951351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5164144381193059377967567 7746216571789589066951351)
          ·
            refine ⟨11619324857684383600427027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7746216571789589066951351 11619324857684383600427027)
            ·
              refine ⟨17428987286526575400640541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11619324857684383600427027 17428987286526575400640541)
              ·
                refine ⟨6535870232447465775240203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17428987286526575400640541 6535870232447465775240203)
                ·
                  refine ⟨9803805348671198662860305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6535870232447465775240203 9803805348671198662860305)
                  ·
                    refine ⟨7352854011503398997145229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9803805348671198662860305 7352854011503398997145229)
                    ·
                      refine ⟨2757320254313774623929461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7352854011503398997145229 2757320254313774623929461)
                      ·
                        rfl

theorem cell23_5369862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_5369862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369862 prefixEnd_5369862 := by exact prefixLift 5369862
  have htrace : WordTrace (prefixWord ++ tailWord_5369862) baseStart_5369862 baseEnd_5369862 := by
    simpa [prefixWord, tailWord_5369862, baseEnd_5369862] using wordTrace_append hprefix tailTrace_5369862
  have hstable : (prefixWord ++ tailWord_5369862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369862).length < 2 ^ (prefixWord ++ tailWord_5369862).sum := by decide
  have hdescent : baseEnd_5369862 < baseStart_5369862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369864 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 1, 4, 2]
def baseStart_5369864 : Nat := 118140960795 + 5369864 * 2 ^ 59
def prefixEnd_5369864 : Nat := 4983230072969 + 3 ^ 40 * 5369864 * 2
def baseEnd_5369864 : Nat := 2757321281275083616104451

theorem tailTrace_5369864 : CollatzResearch.WordTrace tailWord_5369864 prefixEnd_5369864 2757321281275083616104451 := by
  unfold tailWord_5369864
  simp only [CollatzResearch.WordTrace]
  refine ⟨97927515108953651301134323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130570020145271535068179097 97927515108953651301134323)
  ·
    refine ⟨146891272663430476951701485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97927515108953651301134323 146891272663430476951701485)
    ·
      refine ⟨55084227248786428856888057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146891272663430476951701485 55084227248786428856888057)
      ·
        refine ⟨41313170436589821642666043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55084227248786428856888057 41313170436589821642666043)
        ·
          refine ⟨61969755654884732463999065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41313170436589821642666043 61969755654884732463999065)
          ·
            refine ⟨46477316741163549347999299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61969755654884732463999065 46477316741163549347999299)
            ·
              refine ⟨69715975111745324021998949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46477316741163549347999299 69715975111745324021998949)
              ·
                refine ⟨13071745333452248254124803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69715975111745324021998949 13071745333452248254124803)
                ·
                  refine ⟨19607618000178372381187205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13071745333452248254124803 19607618000178372381187205)
                  ·
                    refine ⟨3676428375033444821472601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19607618000178372381187205 3676428375033444821472601)
                    ·
                      refine ⟨2757321281275083616104451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3676428375033444821472601 2757321281275083616104451)
                      ·
                        rfl

theorem cell23_5369864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_5369864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369864 prefixEnd_5369864 := by exact prefixLift 5369864
  have htrace : WordTrace (prefixWord ++ tailWord_5369864) baseStart_5369864 baseEnd_5369864 := by
    simpa [prefixWord, tailWord_5369864, baseEnd_5369864] using wordTrace_append hprefix tailTrace_5369864
  have hstable : (prefixWord ++ tailWord_5369864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369864).length < 2 ^ (prefixWord ++ tailWord_5369864).sum := by decide
  have hdescent : baseEnd_5369864 < baseStart_5369864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369887 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 7]
def baseStart_5369887 : Nat := 118140960795 + 5369887 * 2 ^ 59
def prefixEnd_5369887 : Nat := 4983230072969 + 3 ^ 40 * 5369887 * 2
def baseEnd_5369887 : Nat := 306370343481126336235205

theorem tailTrace_5369887 : CollatzResearch.WordTrace tailWord_5369887 prefixEnd_5369887 306370343481126336235205 := by
  unfold tailWord_5369887
  simp only [CollatzResearch.WordTrace]
  refine ⟨195855869096823977530355915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130570579397882651686903943 195855869096823977530355915)
  ·
    refine ⟨293783803645235966295533873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195855869096823977530355915 293783803645235966295533873)
    ·
      refine ⟨220337852733926974721650405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293783803645235966295533873 220337852733926974721650405)
      ·
        refine ⟨41313347387611307760309451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220337852733926974721650405 41313347387611307760309451)
        ·
          refine ⟨61970021081416961640464177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41313347387611307760309451 61970021081416961640464177)
          ·
            refine ⟨46477515811062721230348133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61970021081416961640464177 46477515811062721230348133)
            ·
              refine ⟨8714534214574260230690275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46477515811062721230348133 8714534214574260230690275)
              ·
                refine ⟨13071801321861390346035413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8714534214574260230690275 13071801321861390346035413)
                ·
                  refine ⟨306370343481126336235205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13071801321861390346035413 306370343481126336235205)
                  ·
                    rfl

theorem cell23_5369887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 7].length) (baseStart_5369887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369887 prefixEnd_5369887 := by exact prefixLift 5369887
  have htrace : WordTrace (prefixWord ++ tailWord_5369887) baseStart_5369887 baseEnd_5369887 := by
    simpa [prefixWord, tailWord_5369887, baseEnd_5369887] using wordTrace_append hprefix tailTrace_5369887
  have hstable : (prefixWord ++ tailWord_5369887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369887).length < 2 ^ (prefixWord ++ tailWord_5369887).sum := by decide
  have hdescent : baseEnd_5369887 < baseStart_5369887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369898 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_5369898 : Nat := 118140960795 + 5369898 * 2 ^ 59
def prefixEnd_5369898 : Nat := 4983230072969 + 3 ^ 40 * 5369898 * 2
def baseEnd_5369898 : Nat := 2757338739617336483079295

theorem tailTrace_5369898 : CollatzResearch.WordTrace tailWord_5369898 prefixEnd_5369898 2757338739617336483079295 := by
  unfold tailWord_5369898
  simp only [CollatzResearch.WordTrace]
  refine ⟨48964067574946031602251587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130570846866522750939337565 48964067574946031602251587)
  ·
    refine ⟨73446101362419047403377381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48964067574946031602251587 73446101362419047403377381)
    ·
      refine ⟨13771144005453571388133259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73446101362419047403377381 13771144005453571388133259)
      ·
        refine ⟨20656716008180357082199889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13771144005453571388133259 20656716008180357082199889)
        ·
          refine ⟨15492537006135267811649917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20656716008180357082199889 15492537006135267811649917)
          ·
            refine ⟨5809701377300725429368719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15492537006135267811649917 5809701377300725429368719)
            ·
              refine ⟨8714552065951088144053079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5809701377300725429368719 8714552065951088144053079)
              ·
                refine ⟨13071828098926632216079619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8714552065951088144053079 13071828098926632216079619)
                ·
                  refine ⟨19607742148389948324119429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13071828098926632216079619 19607742148389948324119429)
                  ·
                    refine ⟨3676451652823115310772393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19607742148389948324119429 3676451652823115310772393)
                    ·
                      refine ⟨2757338739617336483079295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3676451652823115310772393 2757338739617336483079295)
                      ·
                        rfl

theorem cell23_5369898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_5369898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369898 prefixEnd_5369898 := by exact prefixLift 5369898
  have htrace : WordTrace (prefixWord ++ tailWord_5369898) baseStart_5369898 baseEnd_5369898 := by
    simpa [prefixWord, tailWord_5369898, baseEnd_5369898] using wordTrace_append hprefix tailTrace_5369898
  have hstable : (prefixWord ++ tailWord_5369898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369898).length < 2 ^ (prefixWord ++ tailWord_5369898).sum := by decide
  have hdescent : baseEnd_5369898 < baseStart_5369898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369917 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_5369917 : Nat := 118140960795 + 5369917 * 2 ^ 59
def prefixEnd_5369917 : Nat := 4983230072969 + 3 ^ 40 * 5369917 * 2
def baseEnd_5369917 : Nat := 919116165249923969580569

theorem tailTrace_5369917 : CollatzResearch.WordTrace tailWord_5369917 prefixEnd_5369917 919116165249923969580569 := by
  unfold tailWord_5369917
  simp only [CollatzResearch.WordTrace]
  refine ⟨195856963286715292653948005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130571308857810195102632003 195856963286715292653948005)
  ·
    refine ⟨36723180616259117372615251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195856963286715292653948005 36723180616259117372615251)
    ·
      refine ⟨55084770924388676058922877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36723180616259117372615251 55084770924388676058922877)
      ·
        refine ⟨20656789096645753522096079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55084770924388676058922877 20656789096645753522096079)
        ·
          refine ⟨30985183644968630283144119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20656789096645753522096079 30985183644968630283144119)
          ·
            refine ⟨46477775467452945424716179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30985183644968630283144119 46477775467452945424716179)
            ·
              refine ⟨69716663201179418137074269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46477775467452945424716179 69716663201179418137074269)
              ·
                refine ⟨26143748700442281801402851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69716663201179418137074269 26143748700442281801402851)
                ·
                  refine ⟨39215623050663422702104277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26143748700442281801402851 39215623050663422702104277)
                  ·
                    refine ⟨919116165249923969580569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39215623050663422702104277 919116165249923969580569)
                    ·
                      rfl

theorem cell23_5369917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_5369917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369917 prefixEnd_5369917 := by exact prefixLift 5369917
  have htrace : WordTrace (prefixWord ++ tailWord_5369917) baseStart_5369917 baseEnd_5369917 := by
    simpa [prefixWord, tailWord_5369917, baseEnd_5369917] using wordTrace_append hprefix tailTrace_5369917
  have hstable : (prefixWord ++ tailWord_5369917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369917).length < 2 ^ (prefixWord ++ tailWord_5369917).sum := by decide
  have hdescent : baseEnd_5369917 < baseStart_5369917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369921 : List Nat := [1, 2, 5, 1, 2, 1, 3, 3, 5]
def baseStart_5369921 : Nat := 118140960795 + 5369921 * 2 ^ 59
def prefixEnd_5369921 : Nat := 4983230072969 + 3 ^ 40 * 5369921 * 2
def baseEnd_5369921 : Nat := 306372283296932210343521

theorem tailTrace_5369921 : CollatzResearch.WordTrace tailWord_5369921 prefixEnd_5369921 306372283296932210343521 := by
  unfold tailWord_5369921
  simp only [CollatzResearch.WordTrace]
  refine ⟨195857109178700801337093617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130571406119133867558062411 195857109178700801337093617)
  ·
    refine ⟨146892831884025601002820213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195857109178700801337093617 146892831884025601002820213)
    ·
      refine ⟨13771202989127400094014395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146892831884025601002820213 13771202989127400094014395)
      ·
        refine ⟨20656804483691100141021593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13771202989127400094014395 20656804483691100141021593)
        ·
          refine ⟨15492603362768325105766195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20656804483691100141021593 15492603362768325105766195)
          ·
            refine ⟨23238905044152487658649293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15492603362768325105766195 23238905044152487658649293)
            ·
              refine ⟨8714589391557182871993485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23238905044152487658649293 8714589391557182871993485)
              ·
                refine ⟨3267971021833943576997557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8714589391557182871993485 3267971021833943576997557)
                ·
                  refine ⟨306372283296932210343521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3267971021833943576997557 306372283296932210343521)
                  ·
                    rfl

theorem cell23_5369921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 5].length) (baseStart_5369921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369921 prefixEnd_5369921 := by exact prefixLift 5369921
  have htrace : WordTrace (prefixWord ++ tailWord_5369921) baseStart_5369921 baseEnd_5369921 := by
    simpa [prefixWord, tailWord_5369921, baseEnd_5369921] using wordTrace_append hprefix tailTrace_5369921
  have hstable : (prefixWord ++ tailWord_5369921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369921).length < 2 ^ (prefixWord ++ tailWord_5369921).sum := by decide
  have hdescent : baseEnd_5369921 < baseStart_5369921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369927 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_5369927 : Nat := 118140960795 + 5369927 * 2 ^ 59
def prefixEnd_5369927 : Nat := 4983230072969 + 3 ^ 40 * 5369927 * 2
def baseEnd_5369927 : Nat := 2757353630556316869616661

theorem tailTrace_5369927 : CollatzResearch.WordTrace tailWord_5369927 prefixEnd_5369927 2757353630556316869616661 := by
  unfold tailWord_5369927
  simp only [CollatzResearch.WordTrace]
  refine ⟨195857328016679064361812035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130571552011119376241208023 195857328016679064361812035)
  ·
    refine ⟨293785992025018596542718053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195857328016679064361812035 293785992025018596542718053)
    ·
      refine ⟨55084873504690986851759635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 293785992025018596542718053 55084873504690986851759635)
      ·
        refine ⟨82627310257036480277639453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55084873504690986851759635 82627310257036480277639453)
        ·
          refine ⟨30985241346388680104114795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82627310257036480277639453 30985241346388680104114795)
          ·
            refine ⟨46477862019583020156172193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30985241346388680104114795 46477862019583020156172193)
            ·
              refine ⟨34858396514687265117129145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46477862019583020156172193 34858396514687265117129145)
              ·
                refine ⟨26143797386015448837846859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34858396514687265117129145 26143797386015448837846859)
                ·
                  refine ⟨39215696079023173256770289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26143797386015448837846859 39215696079023173256770289)
                  ·
                    refine ⟨29411772059267379942577717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39215696079023173256770289 29411772059267379942577717)
                    ·
                      refine ⟨2757353630556316869616661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29411772059267379942577717 2757353630556316869616661)
                      ·
                        rfl

theorem cell23_5369927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_5369927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369927 prefixEnd_5369927 := by exact prefixLift 5369927
  have htrace : WordTrace (prefixWord ++ tailWord_5369927) baseStart_5369927 baseEnd_5369927 := by
    simpa [prefixWord, tailWord_5369927, baseEnd_5369927] using wordTrace_append hprefix tailTrace_5369927
  have hstable : (prefixWord ++ tailWord_5369927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369927).length < 2 ^ (prefixWord ++ tailWord_5369927).sum := by decide
  have hdescent : baseEnd_5369927 < baseStart_5369927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369934 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_5369934 : Nat := 118140960795 + 5369934 * 2 ^ 59
def prefixEnd_5369934 : Nat := 4983230072969 + 3 ^ 40 * 5369934 * 2
def baseEnd_5369934 : Nat := 919119074973632780743043

theorem tailTrace_5369934 : CollatzResearch.WordTrace tailWord_5369934 prefixEnd_5369934 919119074973632780743043 := by
  unfold tailWord_5369934
  simp only [CollatzResearch.WordTrace]
  refine ⟨24482197915956713069664607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130571722218435803038211237 24482197915956713069664607)
  ·
    refine ⟨36723296873935069604496911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24482197915956713069664607 36723296873935069604496911)
    ·
      refine ⟨55084945310902604406745367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36723296873935069604496911 55084945310902604406745367)
      ·
        refine ⟨82627417966353906610118051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55084945310902604406745367 82627417966353906610118051)
        ·
          refine ⟨123941126949530859915177077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82627417966353906610118051 123941126949530859915177077)
          ·
            refine ⟨11619480651518518117047851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123941126949530859915177077 11619480651518518117047851)
            ·
              refine ⟨17429220977277777175571777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11619480651518518117047851 17429220977277777175571777)
              ·
                refine ⟨13071915732958332881678833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17429220977277777175571777 13071915732958332881678833)
                ·
                  refine ⟨9803936799718749661259125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13071915732958332881678833 9803936799718749661259125)
                  ·
                    refine ⟨919119074973632780743043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9803936799718749661259125 919119074973632780743043)
                    ·
                      rfl

theorem cell23_5369934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_5369934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369934 prefixEnd_5369934 := by exact prefixLift 5369934
  have htrace : WordTrace (prefixWord ++ tailWord_5369934) baseStart_5369934 baseEnd_5369934 := by
    simpa [prefixWord, tailWord_5369934, baseEnd_5369934] using wordTrace_append hprefix tailTrace_5369934
  have hstable : (prefixWord ++ tailWord_5369934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369934).length < 2 ^ (prefixWord ++ tailWord_5369934).sum := by decide
  have hdescent : baseEnd_5369934 < baseStart_5369934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369938 : List Nat := [3, 2, 2, 1, 4, 1, 3, 2, 5]
def baseStart_5369938 : Nat := 118140960795 + 5369938 * 2 ^ 59
def prefixEnd_5369938 : Nat := 4983230072969 + 3 ^ 40 * 5369938 * 2
def baseEnd_5369938 : Nat := 306373253204835147397679

theorem tailTrace_5369938 : CollatzResearch.WordTrace tailWord_5369938 prefixEnd_5369938 306373253204835147397679 := by
  unfold tailWord_5369938
  simp only [CollatzResearch.WordTrace]
  refine ⟨48964432304909803310115617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130571819479759475493641645 48964432304909803310115617)
  ·
    refine ⟨36723324228682352482586713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48964432304909803310115617 36723324228682352482586713)
    ·
      refine ⟨27542493171511764361940035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36723324228682352482586713 27542493171511764361940035)
      ·
        refine ⟨41313739757267646542910053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27542493171511764361940035 41313739757267646542910053)
        ·
          refine ⟨7746326204487683726795635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41313739757267646542910053 7746326204487683726795635)
          ·
            refine ⟨11619489306731525590193453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7746326204487683726795635 11619489306731525590193453)
            ·
              refine ⟨4357308490024322096322545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11619489306731525590193453 4357308490024322096322545)
              ·
                refine ⟨3267981367518241572241909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4357308490024322096322545 3267981367518241572241909)
                ·
                  refine ⟨306373253204835147397679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3267981367518241572241909 306373253204835147397679)
                  ·
                    rfl

theorem cell23_5369938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_5369938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369938 prefixEnd_5369938 := by exact prefixLift 5369938
  have htrace : WordTrace (prefixWord ++ tailWord_5369938) baseStart_5369938 baseEnd_5369938 := by
    simpa [prefixWord, tailWord_5369938, baseEnd_5369938] using wordTrace_append hprefix tailTrace_5369938
  have hstable : (prefixWord ++ tailWord_5369938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369938).length < 2 ^ (prefixWord ++ tailWord_5369938).sum := by decide
  have hdescent : baseEnd_5369938 < baseStart_5369938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5369994 : List Nat := [3, 1, 2, 3, 1, 2, 1, 4, 6]
def baseStart_5369994 : Nat := 118140960795 + 5369994 * 2 ^ 59
def prefixEnd_5369994 : Nat := 4983230072969 + 3 ^ 40 * 5369994 * 2
def baseEnd_5369994 : Nat := 306376448195574234164317

theorem tailTrace_5369994 : CollatzResearch.WordTrace tailWord_5369994 prefixEnd_5369994 306376448195574234164317 := by
  unfold tailWord_5369994
  simp only [CollatzResearch.WordTrace]
  refine ⟨48964942926859083701125259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130573181138290889869667357 48964942926859083701125259)
  ·
    refine ⟨73447414390288625551687889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48964942926859083701125259 73447414390288625551687889)
    ·
      refine ⟨55085560792716469163765917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73447414390288625551687889 55085560792716469163765917)
      ·
        refine ⟨20657085297268675936412219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55085560792716469163765917 20657085297268675936412219)
        ·
          refine ⟨30985627945903013904618329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20657085297268675936412219 30985627945903013904618329)
          ·
            refine ⟨23239220959427260428463747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30985627945903013904618329 23239220959427260428463747)
            ·
              refine ⟨34858831439140890642695621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23239220959427260428463747 34858831439140890642695621)
              ·
                refine ⟨6536030894838916995505429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34858831439140890642695621 6536030894838916995505429)
                ·
                  refine ⟨306376448195574234164317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6536030894838916995505429 306376448195574234164317)
                  ·
                    rfl

theorem cell23_5369994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 6].length) (baseStart_5369994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5369994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5369994 prefixEnd_5369994 := by exact prefixLift 5369994
  have htrace : WordTrace (prefixWord ++ tailWord_5369994) baseStart_5369994 baseEnd_5369994 := by
    simpa [prefixWord, tailWord_5369994, baseEnd_5369994] using wordTrace_append hprefix tailTrace_5369994
  have hstable : (prefixWord ++ tailWord_5369994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5369994).length < 2 ^ (prefixWord ++ tailWord_5369994).sum := by decide
  have hdescent : baseEnd_5369994 < baseStart_5369994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5369994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370021 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 3, 1, 3]
def baseStart_5370021 : Nat := 118140960795 + 5370021 * 2 ^ 59
def prefixEnd_5370021 : Nat := 4983230072969 + 3 ^ 40 * 5370021 * 2
def baseEnd_5370021 : Nat := 2757401897737839501841229

theorem tailTrace_5370021 : CollatzResearch.WordTrace tailWord_5370021 prefixEnd_5370021 2757401897737839501841229 := by
  unfold tailWord_5370021
  simp only [CollatzResearch.WordTrace]
  refine ⟨195860756478338518415733917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130573837652225678943822611 195860756478338518415733917)
  ·
    refine ⟨73447783679376944405900219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195860756478338518415733917 73447783679376944405900219)
    ·
      refine ⟨110171675519065416608850329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73447783679376944405900219 110171675519065416608850329)
      ·
        refine ⟨82628756639299062456637747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110171675519065416608850329 82628756639299062456637747)
        ·
          refine ⟨123943134958948593684956621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82628756639299062456637747 123943134958948593684956621)
          ·
            refine ⟨46478675609605722631858733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123943134958948593684956621 46478675609605722631858733)
            ·
              refine ⟨17429503353602145986947025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46478675609605722631858733 17429503353602145986947025)
              ·
                refine ⟨13072127515201609490210269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17429503353602145986947025 13072127515201609490210269)
                ·
                  refine ⟨4902047818200603558828851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13072127515201609490210269 4902047818200603558828851)
                  ·
                    refine ⟨7353071727300905338243277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4902047818200603558828851 7353071727300905338243277)
                    ·
                      refine ⟨2757401897737839501841229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7353071727300905338243277 2757401897737839501841229)
                      ·
                        rfl

theorem cell23_5370021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_5370021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370021 prefixEnd_5370021 := by exact prefixLift 5370021
  have htrace : WordTrace (prefixWord ++ tailWord_5370021) baseStart_5370021 baseEnd_5370021 := by
    simpa [prefixWord, tailWord_5370021, baseEnd_5370021] using wordTrace_append hprefix tailTrace_5370021
  have hstable : (prefixWord ++ tailWord_5370021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370021).length < 2 ^ (prefixWord ++ tailWord_5370021).sum := by decide
  have hdescent : baseEnd_5370021 < baseStart_5370021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370098 : List Nat := [3, 2, 1, 3, 2, 1, 2, 3, 1, 2, 3]
def baseStart_5370098 : Nat := 118140960795 + 5370098 * 2 ^ 59
def prefixEnd_5370098 : Nat := 4983230072969 + 3 ^ 40 * 5370098 * 2
def baseEnd_5370098 : Nat := 2757441435748235700578375

theorem tailTrace_5370098 : CollatzResearch.WordTrace tailWord_5370098 prefixEnd_5370098 2757441435748235700578375 := by
  unfold tailWord_5370098
  simp only [CollatzResearch.WordTrace]
  refine ⟨48965891224764890141571737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130575709932706373710857965 48965891224764890141571737)
  ·
    refine ⟨36724418418573667606178803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48965891224764890141571737 36724418418573667606178803)
    ·
      refine ⟨55086627627860501409268205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36724418418573667606178803 55086627627860501409268205)
      ·
        refine ⟨20657485360447688028475577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55086627627860501409268205 20657485360447688028475577)
        ·
          refine ⟨15493114020335766021356683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20657485360447688028475577 15493114020335766021356683)
          ·
            refine ⟨23239671030503649032035025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15493114020335766021356683 23239671030503649032035025)
            ·
              refine ⟨17429753272877736774026269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23239671030503649032035025 17429753272877736774026269)
              ·
                refine ⟨6536157477329151290259851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17429753272877736774026269 6536157477329151290259851)
                ·
                  refine ⟨9804236215993726935389777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6536157477329151290259851 9804236215993726935389777)
                  ·
                    refine ⟨7353177161995295201542333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9804236215993726935389777 7353177161995295201542333)
                    ·
                      refine ⟨2757441435748235700578375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7353177161995295201542333 2757441435748235700578375)
                      ·
                        rfl

theorem cell23_5370098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_5370098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370098 prefixEnd_5370098 := by exact prefixLift 5370098
  have htrace : WordTrace (prefixWord ++ tailWord_5370098) baseStart_5370098 baseEnd_5370098 := by
    simpa [prefixWord, tailWord_5370098, baseEnd_5370098] using wordTrace_append hprefix tailTrace_5370098
  have hstable : (prefixWord ++ tailWord_5370098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370098).length < 2 ^ (prefixWord ++ tailWord_5370098).sum := by decide
  have hdescent : baseEnd_5370098 < baseStart_5370098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370111 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 4, 1, 3]
def baseStart_5370111 : Nat := 118140960795 + 5370111 * 2 ^ 59
def prefixEnd_5370111 : Nat := 4983230072969 + 3 ^ 40 * 5370111 * 2
def baseEnd_5370111 : Nat := 2757448110996744149715815

theorem tailTrace_5370111 : CollatzResearch.WordTrace tailWord_5370111 prefixEnd_5370111 2757448110996744149715815 := by
  unfold tailWord_5370111
  simp only [CollatzResearch.WordTrace]
  refine ⟨195864039048012463786510187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130576026032008309191006791 195864039048012463786510187)
  ·
    refine ⟨293796058572018695679765281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195864039048012463786510187 293796058572018695679765281)
    ·
      refine ⟨220347043929014021759823961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293796058572018695679765281 220347043929014021759823961)
      ·
        refine ⟨165260282946760516319867971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220347043929014021759823961 165260282946760516319867971)
        ·
          refine ⟨247890424420140774479801957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165260282946760516319867971 247890424420140774479801957)
          ·
            refine ⟨46479454578776395214962867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247890424420140774479801957 46479454578776395214962867)
            ·
              refine ⟨69719181868164592822444301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46479454578776395214962867 69719181868164592822444301)
              ·
                refine ⟨26144693200561722308416613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69719181868164592822444301 26144693200561722308416613)
                ·
                  refine ⟨4902129975105322932828115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26144693200561722308416613 4902129975105322932828115)
                  ·
                    refine ⟨7353194962657984399242173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4902129975105322932828115 7353194962657984399242173)
                    ·
                      refine ⟨2757448110996744149715815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7353194962657984399242173 2757448110996744149715815)
                      ·
                        rfl

theorem cell23_5370111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_5370111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370111 prefixEnd_5370111 := by exact prefixLift 5370111
  have htrace : WordTrace (prefixWord ++ tailWord_5370111) baseStart_5370111 baseEnd_5370111 := by
    simpa [prefixWord, tailWord_5370111, baseEnd_5370111] using wordTrace_append hprefix tailTrace_5370111
  have hstable : (prefixWord ++ tailWord_5370111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370111).length < 2 ^ (prefixWord ++ tailWord_5370111).sum := by decide
  have hdescent : baseEnd_5370111 < baseStart_5370111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370168 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 4, 2, 2]
def baseStart_5370168 : Nat := 118140960795 + 5370168 * 2 ^ 59
def prefixEnd_5370168 : Nat := 4983230072969 + 3 ^ 40 * 5370168 * 2
def baseEnd_5370168 : Nat := 2757477379394050426703053

theorem tailTrace_5370168 : CollatzResearch.WordTrace tailWord_5370168 prefixEnd_5370168 2757477379394050426703053 := by
  unfold tailWord_5370168
  simp only [CollatzResearch.WordTrace]
  refine ⟨97933059004402981260667579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130577412005870641680890105 97933059004402981260667579)
  ·
    refine ⟨146899588506604471891001369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97933059004402981260667579 146899588506604471891001369)
    ·
      refine ⟨110174691379953353918251027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146899588506604471891001369 110174691379953353918251027)
      ·
        refine ⟨165262037069930030877376541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110174691379953353918251027 165262037069930030877376541)
        ·
          refine ⟨61973263901223761579016203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165262037069930030877376541 61973263901223761579016203)
          ·
            refine ⟨92959895851835642368524305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61973263901223761579016203 92959895851835642368524305)
            ·
              refine ⟨69719921888876731776393229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92959895851835642368524305 69719921888876731776393229)
              ·
                refine ⟨26144970708328774416147461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69719921888876731776393229 26144970708328774416147461)
                ·
                  refine ⟨4902182007811645203027649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26144970708328774416147461 4902182007811645203027649)
                  ·
                    refine ⟨3676636505858733902270737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4902182007811645203027649 3676636505858733902270737)
                    ·
                      refine ⟨2757477379394050426703053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3676636505858733902270737 2757477379394050426703053)
                      ·
                        rfl

theorem cell23_5370168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 4, 2, 2].length) (baseStart_5370168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370168 prefixEnd_5370168 := by exact prefixLift 5370168
  have htrace : WordTrace (prefixWord ++ tailWord_5370168) baseStart_5370168 baseEnd_5370168 := by
    simpa [prefixWord, tailWord_5370168, baseEnd_5370168] using wordTrace_append hprefix tailTrace_5370168
  have hstable : (prefixWord ++ tailWord_5370168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370168).length < 2 ^ (prefixWord ++ tailWord_5370168).sum := by decide
  have hdescent : baseEnd_5370168 < baseStart_5370168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370218 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_5370218 : Nat := 118140960795 + 5370218 * 2 ^ 59
def prefixEnd_5370218 : Nat := 4983230072969 + 3 ^ 40 * 5370218 * 2
def baseEnd_5370218 : Nat := 2757503053426775231077823

theorem tailTrace_5370218 : CollatzResearch.WordTrace tailWord_5370218 prefixEnd_5370218 2757503053426775231077823 := by
  unfold tailWord_5370218
  simp only [CollatzResearch.WordTrace]
  refine ⟨48966985414656205265163827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130578627772416547373770205 48966985414656205265163827)
  ·
    refine ⟨73450478121984307897745741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48966985414656205265163827 73450478121984307897745741)
    ·
      refine ⟨27543929295744115461654653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73450478121984307897745741 27543929295744115461654653)
      ·
        refine ⟨10328973485904043298120495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27543929295744115461654653 10328973485904043298120495)
        ·
          refine ⟨15493460228856064947180743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10328973485904043298120495 15493460228856064947180743)
          ·
            refine ⟨23240190343284097420771115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15493460228856064947180743 23240190343284097420771115)
            ·
              refine ⟨34860285514926146131156673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23240190343284097420771115 34860285514926146131156673)
              ·
                refine ⟨26145214136194609598367505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34860285514926146131156673 26145214136194609598367505)
                ·
                  refine ⟨19608910602145957198775629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26145214136194609598367505 19608910602145957198775629)
                  ·
                    refine ⟨7353341475804733949540861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19608910602145957198775629 7353341475804733949540861)
                    ·
                      refine ⟨2757503053426775231077823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7353341475804733949540861 2757503053426775231077823)
                      ·
                        rfl

theorem cell23_5370218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_5370218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370218 prefixEnd_5370218 := by exact prefixLift 5370218
  have htrace : WordTrace (prefixWord ++ tailWord_5370218) baseStart_5370218 baseEnd_5370218 := by
    simpa [prefixWord, tailWord_5370218, baseEnd_5370218] using wordTrace_append hprefix tailTrace_5370218
  have hstable : (prefixWord ++ tailWord_5370218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370218).length < 2 ^ (prefixWord ++ tailWord_5370218).sum := by decide
  have hdescent : baseEnd_5370218 < baseStart_5370218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370221 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_5370221 : Nat := 118140960795 + 5370221 * 2 ^ 59
def prefixEnd_5370221 : Nat := 4983230072969 + 3 ^ 40 * 5370221 * 2
def baseEnd_5370221 : Nat := 919168197956246239780103

theorem tailTrace_5370221 : CollatzResearch.WordTrace tailWord_5370221 prefixEnd_5370221 919168197956246239780103 := by
  unfold tailWord_5370221
  simp only [CollatzResearch.WordTrace]
  refine ⟨195868051077613952573014517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130578700718409301715343011 195868051077613952573014517)
  ·
    refine ⟨18362629788526308053720111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195868051077613952573014517 18362629788526308053720111)
    ·
      refine ⟨27543944682789462080580167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18362629788526308053720111 27543944682789462080580167)
      ·
        refine ⟨41315917024184193120870251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27543944682789462080580167 41315917024184193120870251)
        ·
          refine ⟨61973875536276289681305377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41315917024184193120870251 61973875536276289681305377)
          ·
            refine ⟨46480406652207217260979033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61973875536276289681305377 46480406652207217260979033)
            ·
              refine ⟨34860304989155412945734275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46480406652207217260979033 34860304989155412945734275)
              ·
                refine ⟨52290457483733119418601413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34860304989155412945734275 52290457483733119418601413)
                ·
                  refine ⟨9804460778199959890987765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52290457483733119418601413 9804460778199959890987765)
                  ·
                    refine ⟨919168197956246239780103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9804460778199959890987765 919168197956246239780103)
                    ·
                      rfl

theorem cell23_5370221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_5370221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370221 prefixEnd_5370221 := by exact prefixLift 5370221
  have htrace : WordTrace (prefixWord ++ tailWord_5370221) baseStart_5370221 baseEnd_5370221 := by
    simpa [prefixWord, tailWord_5370221, baseEnd_5370221] using wordTrace_append hprefix tailTrace_5370221
  have hstable : (prefixWord ++ tailWord_5370221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370221).length < 2 ^ (prefixWord ++ tailWord_5370221).sum := by decide
  have hdescent : baseEnd_5370221 < baseStart_5370221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370234 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 4, 8]
def baseStart_5370234 : Nat := 118140960795 + 5370234 * 2 ^ 59
def prefixEnd_5370234 : Nat := 4983230072969 + 3 ^ 40 * 5370234 * 2
def baseEnd_5370234 : Nat := 919170423039082389492583

theorem tailTrace_5370234 : CollatzResearch.WordTrace tailWord_5370234 prefixEnd_5370234 919170423039082389492583 := by
  unfold tailWord_5370234
  simp only [CollatzResearch.WordTrace]
  refine ⟨48967131306641713948309439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130579016817711237195491837 48967131306641713948309439)
  ·
    refine ⟨73450696959962570922464159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48967131306641713948309439 73450696959962570922464159)
    ·
      refine ⟨110176045439943856383696239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73450696959962570922464159 110176045439943856383696239)
      ·
        refine ⟨165264068159915784575544359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110176045439943856383696239 165264068159915784575544359)
        ·
          refine ⟨247896102239873676863316539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165264068159915784575544359 247896102239873676863316539)
          ·
            refine ⟨371844153359810515294974809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247896102239873676863316539 371844153359810515294974809)
            ·
              refine ⟨278883115019857886471231107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371844153359810515294974809 278883115019857886471231107)
              ·
                refine ⟨418324672529786829706846661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278883115019857886471231107 418324672529786829706846661)
                ·
                  refine ⟨78435876099335030570033749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418324672529786829706846661 78435876099335030570033749)
                  ·
                    refine ⟨919170423039082389492583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78435876099335030570033749 919170423039082389492583)
                    ·
                      rfl

theorem cell23_5370234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_5370234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370234 prefixEnd_5370234 := by exact prefixLift 5370234
  have htrace : WordTrace (prefixWord ++ tailWord_5370234) baseStart_5370234 baseEnd_5370234 := by
    simpa [prefixWord, tailWord_5370234, baseEnd_5370234] using wordTrace_append hprefix tailTrace_5370234
  have hstable : (prefixWord ++ tailWord_5370234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370234).length < 2 ^ (prefixWord ++ tailWord_5370234).sum := by decide
  have hdescent : baseEnd_5370234 < baseStart_5370234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370282 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_5370282 : Nat := 118140960795 + 5370282 * 2 ^ 59
def prefixEnd_5370282 : Nat := 4983230072969 + 3 ^ 40 * 5370282 * 2
def baseEnd_5370282 : Nat := 2757535916188662980677529

theorem tailTrace_5370282 : CollatzResearch.WordTrace tailWord_5370282 prefixEnd_5370282 2757535916188662980677529 := by
  unfold tailWord_5370282
  simp only [CollatzResearch.WordTrace]
  refine ⟨48967568982598239997746275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130580183953595306660656733 48967568982598239997746275)
  ·
    refine ⟨73451353473897359996619413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48967568982598239997746275 73451353473897359996619413)
    ·
      refine ⟨3443032194088938749841535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73451353473897359996619413 3443032194088938749841535)
      ·
        refine ⟨5164548291133408124762303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3443032194088938749841535 5164548291133408124762303)
        ·
          refine ⟨7746822436700112187143455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5164548291133408124762303 7746822436700112187143455)
          ·
            refine ⟨11620233655050168280715183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7746822436700112187143455 11620233655050168280715183)
            ·
              refine ⟨17430350482575252421072775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11620233655050168280715183 17430350482575252421072775)
              ·
                refine ⟨26145525723862878631609163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17430350482575252421072775 26145525723862878631609163)
                ·
                  refine ⟨39218288585794317947413745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26145525723862878631609163 39218288585794317947413745)
                  ·
                    refine ⟨29413716439345738460560309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39218288585794317947413745 29413716439345738460560309)
                    ·
                      refine ⟨2757535916188662980677529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29413716439345738460560309 2757535916188662980677529)
                      ·
                        rfl

theorem cell23_5370282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_5370282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370282 prefixEnd_5370282 := by exact prefixLift 5370282
  have htrace : WordTrace (prefixWord ++ tailWord_5370282) baseStart_5370282 baseEnd_5370282 := by
    simpa [prefixWord, tailWord_5370282, baseEnd_5370282] using wordTrace_append hprefix tailTrace_5370282
  have hstable : (prefixWord ++ tailWord_5370282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370282).length < 2 ^ (prefixWord ++ tailWord_5370282).sum := by decide
  have hdescent : baseEnd_5370282 < baseStart_5370282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370335 : List Nat := [1, 1, 2, 3, 3, 2, 2, 2, 2, 3, 2]
def baseStart_5370335 : Nat := 118140960795 + 5370335 * 2 ^ 59
def prefixEnd_5370335 : Nat := 4983230072969 + 3 ^ 40 * 5370335 * 2
def baseEnd_5370335 : Nat := 2757563130663351273314785

theorem tailTrace_5370335 : CollatzResearch.WordTrace tailWord_5370335 prefixEnd_5370335 2757563130663351273314785 := by
  unfold tailWord_5370335
  simp only [CollatzResearch.WordTrace]
  refine ⟨195872208999200950042664459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130581472666133966695109639 195872208999200950042664459)
  ·
    refine ⟨293808313498801425063996689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195872208999200950042664459 293808313498801425063996689)
    ·
      refine ⟨220356235124101068797997517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293808313498801425063996689 220356235124101068797997517)
      ·
        refine ⟨82633588171537900799249069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220356235124101068797997517 82633588171537900799249069)
        ·
          refine ⟨30987595564326712799718401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82633588171537900799249069 30987595564326712799718401)
          ·
            refine ⟨23240696673245034599788801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30987595564326712799718401 23240696673245034599788801)
            ·
              refine ⟨17430522504933775949841601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23240696673245034599788801 17430522504933775949841601)
              ·
                refine ⟨13072891878700331962381201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17430522504933775949841601 13072891878700331962381201)
                ·
                  refine ⟨9804668909025248971785901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13072891878700331962381201 9804668909025248971785901)
                  ·
                    refine ⟨3676750840884468364419713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9804668909025248971785901 3676750840884468364419713)
                    ·
                      refine ⟨2757563130663351273314785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3676750840884468364419713 2757563130663351273314785)
                      ·
                        rfl

theorem cell23_5370335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_5370335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370335 prefixEnd_5370335 := by exact prefixLift 5370335
  have htrace : WordTrace (prefixWord ++ tailWord_5370335) baseStart_5370335 baseEnd_5370335 := by
    simpa [prefixWord, tailWord_5370335, baseEnd_5370335] using wordTrace_append hprefix tailTrace_5370335
  have hstable : (prefixWord ++ tailWord_5370335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370335).length < 2 ^ (prefixWord ++ tailWord_5370335).sum := by decide
  have hdescent : baseEnd_5370335 < baseStart_5370335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370351 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 5]
def baseStart_5370351 : Nat := 118140960795 + 5370351 * 2 ^ 59
def prefixEnd_5370351 : Nat := 4983230072969 + 3 ^ 40 * 5370351 * 2
def baseEnd_5370351 : Nat := 2757571346353823210714711

theorem tailTrace_5370351 : CollatzResearch.WordTrace tailWord_5370351 prefixEnd_5370351 2757571346353823210714711 := by
  unfold tailWord_5370351
  simp only [CollatzResearch.WordTrace]
  refine ⟨195872792567142984775246907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130581861711428656516831271 195872792567142984775246907)
  ·
    refine ⟨293809188850714477162870361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195872792567142984775246907 293809188850714477162870361)
    ·
      refine ⟨220356891638035857872152771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293809188850714477162870361 220356891638035857872152771)
      ·
        refine ⟨330535337457053786808229157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220356891638035857872152771 330535337457053786808229157)
        ·
          refine ⟨61975375773197585026542967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 330535337457053786808229157 61975375773197585026542967)
          ·
            refine ⟨92963063659796377539814451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61975375773197585026542967 92963063659796377539814451)
            ·
              refine ⟨139444595489694566309721677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92963063659796377539814451 139444595489694566309721677)
              ·
                refine ⟨52291723308635462366145629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139444595489694566309721677 52291723308635462366145629)
                ·
                  refine ⟨19609396240738298387304611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52291723308635462366145629 19609396240738298387304611)
                  ·
                    refine ⟨29414094361107447580956917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19609396240738298387304611 29414094361107447580956917)
                    ·
                      refine ⟨2757571346353823210714711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29414094361107447580956917 2757571346353823210714711)
                      ·
                        rfl

theorem cell23_5370351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_5370351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370351 prefixEnd_5370351 := by exact prefixLift 5370351
  have htrace : WordTrace (prefixWord ++ tailWord_5370351) baseStart_5370351 baseEnd_5370351 := by
    simpa [prefixWord, tailWord_5370351, baseEnd_5370351] using wordTrace_append hprefix tailTrace_5370351
  have hstable : (prefixWord ++ tailWord_5370351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370351).length < 2 ^ (prefixWord ++ tailWord_5370351).sum := by decide
  have hdescent : baseEnd_5370351 < baseStart_5370351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370361 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 6]
def baseStart_5370361 : Nat := 118140960795 + 5370361 * 2 ^ 59
def prefixEnd_5370361 : Nat := 4983230072969 + 3 ^ 40 * 5370361 * 2
def baseEnd_5370361 : Nat := 2757576481160368171589665

theorem tailTrace_5370361 : CollatzResearch.WordTrace tailWord_5370361 prefixEnd_5370361 2757576481160368171589665 := by
  unfold tailWord_5370361
  simp only [CollatzResearch.WordTrace]
  refine ⟨195873157297106756483110937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130582104864737837655407291 195873157297106756483110937)
  ·
    refine ⟨146904867972830067362333203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195873157297106756483110937 146904867972830067362333203)
    ·
      refine ⟨220357301959245101043499805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146904867972830067362333203 220357301959245101043499805)
      ·
        refine ⟨82633988234716912891312427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220357301959245101043499805 82633988234716912891312427)
        ·
          refine ⟨123950982352075369336968641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82633988234716912891312427 123950982352075369336968641)
          ·
            refine ⟨92963236764056527002726481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123950982352075369336968641 92963236764056527002726481)
            ·
              refine ⟨69722427573042395252044861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92963236764056527002726481 69722427573042395252044861)
              ·
                refine ⟨26145910339890898219516823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69722427573042395252044861 26145910339890898219516823)
                ·
                  refine ⟨39218865509836347329275235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26145910339890898219516823 39218865509836347329275235)
                  ·
                    refine ⟨58828298264754520993912853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39218865509836347329275235 58828298264754520993912853)
                    ·
                      refine ⟨2757576481160368171589665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58828298264754520993912853 2757576481160368171589665)
                      ·
                        rfl

theorem cell23_5370361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_5370361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370361 prefixEnd_5370361 := by exact prefixLift 5370361
  have htrace : WordTrace (prefixWord ++ tailWord_5370361) baseStart_5370361 baseEnd_5370361 := by
    simpa [prefixWord, tailWord_5370361, baseEnd_5370361] using wordTrace_append hprefix tailTrace_5370361
  have hstable : (prefixWord ++ tailWord_5370361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370361).length < 2 ^ (prefixWord ++ tailWord_5370361).sum := by decide
  have hdescent : baseEnd_5370361 < baseStart_5370361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370378 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_5370378 : Nat := 118140960795 + 5370378 * 2 ^ 59
def prefixEnd_5370378 : Nat := 4983230072969 + 3 ^ 40 * 5370378 * 2
def baseEnd_5370378 : Nat := 2757585210331494605077087

theorem tailTrace_5370378 : CollatzResearch.WordTrace tailWord_5370378 prefixEnd_5370378 2757585210331494605077087 := by
  unfold tailWord_5370378
  simp only [CollatzResearch.WordTrace]
  refine ⟨48968444334511292096619947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130582518225363445590986525 48968444334511292096619947)
  ·
    refine ⟨73452666501766938144929921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48968444334511292096619947 73452666501766938144929921)
    ·
      refine ⟨55089499876325203608697441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73452666501766938144929921 55089499876325203608697441)
      ·
        refine ⟨41317124907243902706523081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55089499876325203608697441 41317124907243902706523081)
        ·
          refine ⟨30987843680432927029892311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41317124907243902706523081 30987843680432927029892311)
          ·
            refine ⟨46481765520649390544838467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30987843680432927029892311 46481765520649390544838467)
            ·
              refine ⟨69722648280974085817257701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46481765520649390544838467 69722648280974085817257701)
              ·
                refine ⟨13072996552682641090735819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69722648280974085817257701 13072996552682641090735819)
                ·
                  refine ⟨19609494829023961636103729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13072996552682641090735819 19609494829023961636103729)
                  ·
                    refine ⟨14707121121767971227077797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19609494829023961636103729 14707121121767971227077797)
                    ·
                      refine ⟨2757585210331494605077087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14707121121767971227077797 2757585210331494605077087)
                      ·
                        rfl

theorem cell23_5370378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_5370378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370378 prefixEnd_5370378 := by exact prefixLift 5370378
  have htrace : WordTrace (prefixWord ++ tailWord_5370378) baseStart_5370378 baseEnd_5370378 := by
    simpa [prefixWord, tailWord_5370378, baseEnd_5370378] using wordTrace_append hprefix tailTrace_5370378
  have hstable : (prefixWord ++ tailWord_5370378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370378).length < 2 ^ (prefixWord ++ tailWord_5370378).sum := by decide
  have hdescent : baseEnd_5370378 < baseStart_5370378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370382 : List Nat := [4, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4]
def baseStart_5370382 : Nat := 118140960795 + 5370382 * 2 ^ 59
def prefixEnd_5370382 : Nat := 4983230072969 + 3 ^ 40 * 5370382 * 2
def baseEnd_5370382 : Nat := 2757587264254112589427069

theorem tailTrace_5370382 : CollatzResearch.WordTrace tailWord_5370382 prefixEnd_5370382 2757587264254112589427069 := by
  unfold tailWord_5370382
  simp only [CollatzResearch.WordTrace]
  refine ⟨24484240403753834633703175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130582615486687118046416933 24484240403753834633703175)
  ·
    refine ⟨36726360605630751950554763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24484240403753834633703175 36726360605630751950554763)
    ·
      refine ⟨55089540908446127925832145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36726360605630751950554763 55089540908446127925832145)
      ·
        refine ⟨41317155681334595944374109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55089540908446127925832145 41317155681334595944374109)
        ·
          refine ⟨15493933380500473479140291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41317155681334595944374109 15493933380500473479140291)
          ·
            refine ⟨23240900070750710218710437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15493933380500473479140291 23240900070750710218710437)
            ·
              refine ⟨4357668763265758166008207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23240900070750710218710437 4357668763265758166008207)
              ·
                refine ⟨6536503144898637249012311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4357668763265758166008207 6536503144898637249012311)
                ·
                  refine ⟨9804754717347955873518467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6536503144898637249012311 9804754717347955873518467)
                  ·
                    refine ⟨14707132076021933810277701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9804754717347955873518467 14707132076021933810277701)
                    ·
                      refine ⟨2757587264254112589427069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14707132076021933810277701 2757587264254112589427069)
                      ·
                        rfl

theorem cell23_5370382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_5370382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370382 prefixEnd_5370382 := by exact prefixLift 5370382
  have htrace : WordTrace (prefixWord ++ tailWord_5370382) baseStart_5370382 baseEnd_5370382 := by
    simpa [prefixWord, tailWord_5370382, baseEnd_5370382] using wordTrace_append hprefix tailTrace_5370382
  have hstable : (prefixWord ++ tailWord_5370382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370382).length < 2 ^ (prefixWord ++ tailWord_5370382).sum := by decide
  have hdescent : baseEnd_5370382 < baseStart_5370382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370392 : List Nat := [2, 1, 2, 3, 3, 3, 1, 2, 2, 4]
def baseStart_5370392 : Nat := 118140960795 + 5370392 * 2 ^ 59
def prefixEnd_5370392 : Nat := 4983230072969 + 3 ^ 40 * 5370392 * 2
def baseEnd_5370392 : Nat := 919197466353552516767341

theorem tailTrace_5370392 : CollatzResearch.WordTrace tailWord_5370392 prefixEnd_5370392 919197466353552516767341 := by
  unfold tailWord_5370392
  simp only [CollatzResearch.WordTrace]
  refine ⟨97937143979997224388744715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130582858639996299184992953 97937143979997224388744715)
  ·
    refine ⟨146905715969995836583117073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97937143979997224388744715 146905715969995836583117073)
    ·
      refine ⟨110179286977496877437337805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146905715969995836583117073 110179286977496877437337805)
      ·
        refine ⟨41317232616561329039001677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110179286977496877437337805 41317232616561329039001677)
        ·
          refine ⟨15493962231210498389625629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41317232616561329039001677 15493962231210498389625629)
          ·
            refine ⟨5810235836703936896109611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15493962231210498389625629 5810235836703936896109611)
            ·
              refine ⟨8715353755055905344164417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5810235836703936896109611 8715353755055905344164417)
              ·
                refine ⟨6536515316291929008123313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8715353755055905344164417 6536515316291929008123313)
                ·
                  refine ⟨4902386487218946756092485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6536515316291929008123313 4902386487218946756092485)
                  ·
                    refine ⟨919197466353552516767341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4902386487218946756092485 919197466353552516767341)
                    ·
                      rfl

theorem cell23_5370392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_5370392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370392 prefixEnd_5370392 := by exact prefixLift 5370392
  have htrace : WordTrace (prefixWord ++ tailWord_5370392) baseStart_5370392 baseEnd_5370392 := by
    simpa [prefixWord, tailWord_5370392, baseEnd_5370392] using wordTrace_append hprefix tailTrace_5370392
  have hstable : (prefixWord ++ tailWord_5370392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370392).length < 2 ^ (prefixWord ++ tailWord_5370392).sum := by decide
  have hdescent : baseEnd_5370392 < baseStart_5370392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370411 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 5]
def baseStart_5370411 : Nat := 118140960795 + 5370411 * 2 ^ 59
def prefixEnd_5370411 : Nat := 4983230072969 + 3 ^ 40 * 5370411 * 2
def baseEnd_5370411 : Nat := 2757602155193092975964435

theorem tailTrace_5370411 : CollatzResearch.WordTrace tailWord_5370411 prefixEnd_5370411 2757602155193092975964435 := by
  unfold tailWord_5370411
  simp only [CollatzResearch.WordTrace]
  refine ⟨195874980946925615022431087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130583320631283743348287391 195874980946925615022431087)
  ·
    refine ⟨293812471420388422533646631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195874980946925615022431087 293812471420388422533646631)
    ·
      refine ⟨440718707130582633800469947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293812471420388422533646631 440718707130582633800469947)
      ·
        refine ⟨661078060695873950700704921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440718707130582633800469947 661078060695873950700704921)
        ·
          refine ⟨495808545521905463025528691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661078060695873950700704921 495808545521905463025528691)
          ·
            refine ⟨743712818282858194538293037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495808545521905463025528691 743712818282858194538293037)
            ·
              refine ⟨278892306856071822951859889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 743712818282858194538293037 278892306856071822951859889)
              ·
                refine ⟨209169230142053867213894917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278892306856071822951859889 209169230142053867213894917)
                ·
                  refine ⟨39219230651635100102605297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209169230142053867213894917 39219230651635100102605297)
                  ·
                    refine ⟨29414422988726325076953973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39219230651635100102605297 29414422988726325076953973)
                    ·
                      refine ⟨2757602155193092975964435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29414422988726325076953973 2757602155193092975964435)
                      ·
                        rfl

theorem cell23_5370411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 5].length) (baseStart_5370411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370411 prefixEnd_5370411 := by exact prefixLift 5370411
  have htrace : WordTrace (prefixWord ++ tailWord_5370411) baseStart_5370411 baseEnd_5370411 := by
    simpa [prefixWord, tailWord_5370411, baseEnd_5370411] using wordTrace_append hprefix tailTrace_5370411
  have hstable : (prefixWord ++ tailWord_5370411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370411).length < 2 ^ (prefixWord ++ tailWord_5370411).sum := by decide
  have hdescent : baseEnd_5370411 < baseStart_5370411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370422 : List Nat := [5, 1, 2, 1, 2, 3, 2, 7]
def baseStart_5370422 : Nat := 118140960795 + 5370422 * 2 ^ 59
def prefixEnd_5370422 : Nat := 4983230072969 + 3 ^ 40 * 5370422 * 2
def baseEnd_5370422 : Nat := 102133622351121941960255

theorem tailTrace_5370422 : CollatzResearch.WordTrace tailWord_5370422 prefixEnd_5370422 102133622351121941960255 := by
  unfold tailWord_5370422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12242211384367860243817595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130583588099923842600721013 12242211384367860243817595)
  ·
    refine ⟨18363317076551790365726393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12242211384367860243817595 18363317076551790365726393)
    ·
      refine ⟨13772487807413842774294795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18363317076551790365726393 13772487807413842774294795)
      ·
        refine ⟨20658731711120764161442193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13772487807413842774294795 20658731711120764161442193)
        ·
          refine ⟨15494048783340573121081645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20658731711120764161442193 15494048783340573121081645)
          ·
            refine ⟨5810268293752714920405617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15494048783340573121081645 5810268293752714920405617)
            ·
              refine ⟨4357701220314536190304213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5810268293752714920405617 4357701220314536190304213)
              ·
                refine ⟨102133622351121941960255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4357701220314536190304213 102133622351121941960255)
                ·
                  rfl

theorem cell23_5370422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_5370422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370422 prefixEnd_5370422 := by exact prefixLift 5370422
  have htrace : WordTrace (prefixWord ++ tailWord_5370422) baseStart_5370422 baseEnd_5370422 := by
    simpa [prefixWord, tailWord_5370422, baseEnd_5370422] using wordTrace_append hprefix tailTrace_5370422
  have hstable : (prefixWord ++ tailWord_5370422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370422).length < 2 ^ (prefixWord ++ tailWord_5370422).sum := by decide
  have hdescent : baseEnd_5370422 < baseStart_5370422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370428 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_5370428 : Nat := 118140960795 + 5370428 * 2 ^ 59
def prefixEnd_5370428 : Nat := 4983230072969 + 3 ^ 40 * 5370428 * 2
def baseEnd_5370428 : Nat := 2757610884364219409451857

theorem tailTrace_5370428 : CollatzResearch.WordTrace tailWord_5370428 prefixEnd_5370428 2757610884364219409451857 := by
  unfold tailWord_5370428
  simp only [CollatzResearch.WordTrace]
  refine ⟨97937800493932013462899969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130583733991909351283866625 97937800493932013462899969)
  ·
    refine ⟨73453350370449010097174977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97937800493932013462899969 73453350370449010097174977)
    ·
      refine ⟨55090012777836757572881233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73453350370449010097174977 55090012777836757572881233)
      ·
        refine ⟨41317509583377568179660925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55090012777836757572881233 41317509583377568179660925)
        ·
          refine ⟨15494066093766588067372847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41317509583377568179660925 15494066093766588067372847)
          ·
            refine ⟨23241099140649882101059271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15494066093766588067372847 23241099140649882101059271)
            ·
              refine ⟨34861648710974823151588907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23241099140649882101059271 34861648710974823151588907)
              ·
                refine ⟨52292473066462234727383361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34861648710974823151588907 52292473066462234727383361)
                ·
                  refine ⟨39219354799846676045537521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52292473066462234727383361 39219354799846676045537521)
                  ·
                    refine ⟨29414516099885007034153141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39219354799846676045537521 29414516099885007034153141)
                    ·
                      refine ⟨2757610884364219409451857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29414516099885007034153141 2757610884364219409451857)
                      ·
                        rfl

theorem cell23_5370428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_5370428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370428 prefixEnd_5370428 := by exact prefixLift 5370428
  have htrace : WordTrace (prefixWord ++ tailWord_5370428) baseStart_5370428 baseEnd_5370428 := by
    simpa [prefixWord, tailWord_5370428, baseEnd_5370428] using wordTrace_append hprefix tailTrace_5370428
  have hstable : (prefixWord ++ tailWord_5370428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370428).length < 2 ^ (prefixWord ++ tailWord_5370428).sum := by decide
  have hdescent : baseEnd_5370428 < baseStart_5370428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370442 : List Nat := [3, 1, 2, 1, 1, 4, 2, 3, 1, 3, 2]
def baseStart_5370442 : Nat := 118140960795 + 5370442 * 2 ^ 59
def prefixEnd_5370442 : Nat := 4983230072969 + 3 ^ 40 * 5370442 * 2
def baseEnd_5370442 : Nat := 2757618073093382354676793

theorem tailTrace_5370442 : CollatzResearch.WordTrace tailWord_5370442 prefixEnd_5370442 2757618073093382354676793 := by
  unfold tailWord_5370442
  simp only [CollatzResearch.WordTrace]
  refine ⟨48969027902453326829202395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130584074406542204877873053 48969027902453326829202395)
  ·
    refine ⟨73453541853679990243803593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48969027902453326829202395 73453541853679990243803593)
    ·
      refine ⟨55090156390259992682852695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73453541853679990243803593 55090156390259992682852695)
      ·
        refine ⟨82635234585389989024279043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55090156390259992682852695 82635234585389989024279043)
        ·
          refine ⟨123952851878084983536418565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82635234585389989024279043 123952851878084983536418565)
          ·
            refine ⟨23241159727140934413078481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123952851878084983536418565 23241159727140934413078481)
            ·
              refine ⟨17430869795355700809808861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23241159727140934413078481 17430869795355700809808861)
              ·
                refine ⟨6536576173258387803678323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17430869795355700809808861 6536576173258387803678323)
                ·
                  refine ⟨9804864259887581705517485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6536576173258387803678323 9804864259887581705517485)
                  ·
                    refine ⟨3676824097457843139569057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9804864259887581705517485 3676824097457843139569057)
                    ·
                      refine ⟨2757618073093382354676793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3676824097457843139569057 2757618073093382354676793)
                      ·
                        rfl

theorem cell23_5370442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_5370442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370442 prefixEnd_5370442 := by exact prefixLift 5370442
  have htrace : WordTrace (prefixWord ++ tailWord_5370442) baseStart_5370442 baseEnd_5370442 := by
    simpa [prefixWord, tailWord_5370442, baseEnd_5370442] using wordTrace_append hprefix tailTrace_5370442
  have hstable : (prefixWord ++ tailWord_5370442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370442).length < 2 ^ (prefixWord ++ tailWord_5370442).sum := by decide
  have hdescent : baseEnd_5370442 < baseStart_5370442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370466 : List Nat := [3, 3, 2, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5370466 : Nat := 118140960795 + 5370466 * 2 ^ 59
def prefixEnd_5370466 : Nat := 4983230072969 + 3 ^ 40 * 5370466 * 2
def baseEnd_5370466 : Nat := 2757630396629090260776683

theorem tailTrace_5370466 : CollatzResearch.WordTrace tailWord_5370466 prefixEnd_5370466 2757630396629090260776683 := by
  unfold tailWord_5370466
  simp only [CollatzResearch.WordTrace]
  refine ⟨48969246740431589853920813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130584657974484239610455501 48969246740431589853920813)
  ·
    refine ⟨18363467527661846195220305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48969246740431589853920813 18363467527661846195220305)
    ·
      refine ⟨13772600645746384646415229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18363467527661846195220305 13772600645746384646415229)
      ·
        refine ⟨5164725242154894242405711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13772600645746384646415229 5164725242154894242405711)
        ·
          refine ⟨7747087863232341363608567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5164725242154894242405711 7747087863232341363608567)
          ·
            refine ⟨11620631794848512045412851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7747087863232341363608567 11620631794848512045412851)
            ·
              refine ⟨17430947692272768068119277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11620631794848512045412851 17430947692272768068119277)
              ·
                refine ⟨6536605384602288025544729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17430947692272768068119277 6536605384602288025544729)
                ·
                  refine ⟨4902454038451716019158547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6536605384602288025544729 4902454038451716019158547)
                  ·
                    refine ⟨7353681057677574028737821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4902454038451716019158547 7353681057677574028737821)
                    ·
                      refine ⟨2757630396629090260776683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7353681057677574028737821 2757630396629090260776683)
                      ·
                        rfl

theorem cell23_5370466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5370466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370466 prefixEnd_5370466 := by exact prefixLift 5370466
  have htrace : WordTrace (prefixWord ++ tailWord_5370466) baseStart_5370466 baseEnd_5370466 := by
    simpa [prefixWord, tailWord_5370466, baseEnd_5370466] using wordTrace_append hprefix tailTrace_5370466
  have hstable : (prefixWord ++ tailWord_5370466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370466).length < 2 ^ (prefixWord ++ tailWord_5370466).sum := by decide
  have hdescent : baseEnd_5370466 < baseStart_5370466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370468 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_5370468 : Nat := 118140960795 + 5370468 * 2 ^ 59
def prefixEnd_5370468 : Nat := 4983230072969 + 3 ^ 40 * 5370468 * 2
def baseEnd_5370468 : Nat := 2757631423590399252951673

theorem tailTrace_5370468 : CollatzResearch.WordTrace tailWord_5370468 prefixEnd_5370468 2757631423590399252951673 := by
  unfold tailWord_5370468
  simp only [CollatzResearch.WordTrace]
  refine ⟨97938529953859556878628029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130584706605146075838170705 97938529953859556878628029)
  ·
    refine ⟨36726948732697333829485511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97938529953859556878628029 36726948732697333829485511)
    ·
      refine ⟨55090423099046000744228267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36726948732697333829485511 55090423099046000744228267)
      ·
        refine ⟨82635634648569001116342401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55090423099046000744228267 82635634648569001116342401)
        ·
          refine ⟨61976725986426750837256801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82635634648569001116342401 61976725986426750837256801)
          ·
            refine ⟨46482544489820063127942601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61976725986426750837256801 46482544489820063127942601)
            ·
              refine ⟨34861908367365047345956951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46482544489820063127942601 34861908367365047345956951)
              ·
                refine ⟨52292862551047571018935427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34861908367365047345956951 52292862551047571018935427)
                ·
                  refine ⟨78439293826571356528403141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52292862551047571018935427 78439293826571356528403141)
                  ·
                    refine ⟨14707367592482129349075589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78439293826571356528403141 14707367592482129349075589)
                    ·
                      refine ⟨2757631423590399252951673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14707367592482129349075589 2757631423590399252951673)
                      ·
                        rfl

theorem cell23_5370468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_5370468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370468 prefixEnd_5370468 := by exact prefixLift 5370468
  have htrace : WordTrace (prefixWord ++ tailWord_5370468) baseStart_5370468 baseEnd_5370468 := by
    simpa [prefixWord, tailWord_5370468, baseEnd_5370468] using wordTrace_append hprefix tailTrace_5370468
  have hstable : (prefixWord ++ tailWord_5370468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370468).length < 2 ^ (prefixWord ++ tailWord_5370468).sum := by decide
  have hdescent : baseEnd_5370468 < baseStart_5370468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370488 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 1, 5, 3]
def baseStart_5370488 : Nat := 118140960795 + 5370488 * 2 ^ 59
def prefixEnd_5370488 : Nat := 4983230072969 + 3 ^ 40 * 5370488 * 2
def baseEnd_5370488 : Nat := 2757641693203489174701581

theorem tailTrace_5370488 : CollatzResearch.WordTrace tailWord_5370488 prefixEnd_5370488 2757641693203489174701581 := by
  unfold tailWord_5370488
  simp only [CollatzResearch.WordTrace]
  refine ⟨97938894683823328586492059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130585192911764438115322745 97938894683823328586492059)
  ·
    refine ⟨146908342025734992879738089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97938894683823328586492059 146908342025734992879738089)
    ·
      refine ⟨110181256519301244659803567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146908342025734992879738089 110181256519301244659803567)
      ·
        refine ⟨165271884778951866989705351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110181256519301244659803567 165271884778951866989705351)
        ·
          refine ⟨247907827168427800484558027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165271884778951866989705351 247907827168427800484558027)
          ·
            refine ⟨371861740752641700726837041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247907827168427800484558027 371861740752641700726837041)
            ·
              refine ⟨278896305564481275545127781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371861740752641700726837041 278896305564481275545127781)
              ·
                refine ⟨52293057293340239164711459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278896305564481275545127781 52293057293340239164711459)
                ·
                  refine ⟨78439585940010358747067189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52293057293340239164711459 78439585940010358747067189)
                  ·
                    refine ⟨7353711181875971132537549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78439585940010358747067189 7353711181875971132537549)
                    ·
                      refine ⟨2757641693203489174701581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7353711181875971132537549 2757641693203489174701581)
                      ·
                        rfl

theorem cell23_5370488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_5370488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370488 prefixEnd_5370488 := by exact prefixLift 5370488
  have htrace : WordTrace (prefixWord ++ tailWord_5370488) baseStart_5370488 baseEnd_5370488 := by
    simpa [prefixWord, tailWord_5370488, baseEnd_5370488] using wordTrace_append hprefix tailTrace_5370488
  have hstable : (prefixWord ++ tailWord_5370488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370488).length < 2 ^ (prefixWord ++ tailWord_5370488).sum := by decide
  have hdescent : baseEnd_5370488 < baseStart_5370488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370506 : List Nat := [3, 1, 2, 3, 3, 1, 2, 2, 2, 2, 2]
def baseStart_5370506 : Nat := 118140960795 + 5370506 * 2 ^ 59
def prefixEnd_5370506 : Nat := 4983230072969 + 3 ^ 40 * 5370506 * 2
def baseEnd_5370506 : Nat := 2757650935855270104276499

theorem tailTrace_5370506 : CollatzResearch.WordTrace tailWord_5370506 prefixEnd_5370506 2757650935855270104276499 := by
  unfold tailWord_5370506
  simp only [CollatzResearch.WordTrace]
  refine ⟨48969611470395361561784843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130585630587720964164759581 48969611470395361561784843)
  ·
    refine ⟨73454417205593042342677265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48969611470395361561784843 73454417205593042342677265)
    ·
      refine ⟨55090812904194781757007949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73454417205593042342677265 55090812904194781757007949)
      ·
        refine ⟨20659054839073043158877981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55090812904194781757007949 20659054839073043158877981)
        ·
          refine ⟨7747145564652391184579243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20659054839073043158877981 7747145564652391184579243)
          ·
            refine ⟨11620718346978586776868865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7747145564652391184579243 11620718346978586776868865)
            ·
              refine ⟨8715538760233940082651649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11620718346978586776868865 8715538760233940082651649)
              ·
                refine ⟨6536654070175455061988737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8715538760233940082651649 6536654070175455061988737)
                ·
                  refine ⟨4902490552631591296491553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6536654070175455061988737 4902490552631591296491553)
                  ·
                    refine ⟨3676867914473693472368665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4902490552631591296491553 3676867914473693472368665)
                    ·
                      refine ⟨2757650935855270104276499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3676867914473693472368665 2757650935855270104276499)
                      ·
                        rfl

theorem cell23_5370506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_5370506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370506 prefixEnd_5370506 := by exact prefixLift 5370506
  have htrace : WordTrace (prefixWord ++ tailWord_5370506) baseStart_5370506 baseEnd_5370506 := by
    simpa [prefixWord, tailWord_5370506, baseEnd_5370506] using wordTrace_append hprefix tailTrace_5370506
  have hstable : (prefixWord ++ tailWord_5370506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370506).length < 2 ^ (prefixWord ++ tailWord_5370506).sum := by decide
  have hdescent : baseEnd_5370506 < baseStart_5370506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370508 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 4, 5]
def baseStart_5370508 : Nat := 118140960795 + 5370508 * 2 ^ 59
def prefixEnd_5370508 : Nat := 4983230072969 + 3 ^ 40 * 5370508 * 2
def baseEnd_5370508 : Nat := 919217320938859698817163

theorem tailTrace_5370508 : CollatzResearch.WordTrace tailWord_5370508 prefixEnd_5370508 919217320938859698817163 := by
  unfold tailWord_5370508
  simp only [CollatzResearch.WordTrace]
  refine ⟨97939259413787100294356089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130585679218382800392474785 97939259413787100294356089)
  ·
    refine ⟨73454444560340325220767067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97939259413787100294356089 73454444560340325220767067)
    ·
      refine ⟨110181666840510487831150601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73454444560340325220767067 110181666840510487831150601)
      ·
        refine ⟨82636250130382865873362951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110181666840510487831150601 82636250130382865873362951)
        ·
          refine ⟨123954375195574298810044427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82636250130382865873362951 123954375195574298810044427)
          ·
            refine ⟨185931562793361448215066641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123954375195574298810044427 185931562793361448215066641)
            ·
              refine ⟨139448672095021086161299981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185931562793361448215066641 139448672095021086161299981)
              ·
                refine ⟨52293252035632907310487493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139448672095021086161299981 52293252035632907310487493)
                ·
                  refine ⟨9804984756681170120716405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52293252035632907310487493 9804984756681170120716405)
                  ·
                    refine ⟨919217320938859698817163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9804984756681170120716405 919217320938859698817163)
                    ·
                      rfl

theorem cell23_5370508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_5370508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370508 prefixEnd_5370508 := by exact prefixLift 5370508
  have htrace : WordTrace (prefixWord ++ tailWord_5370508) baseStart_5370508 baseEnd_5370508 := by
    simpa [prefixWord, tailWord_5370508, baseEnd_5370508] using wordTrace_append hprefix tailTrace_5370508
  have hstable : (prefixWord ++ tailWord_5370508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370508).length < 2 ^ (prefixWord ++ tailWord_5370508).sum := by decide
  have hdescent : baseEnd_5370508 < baseStart_5370508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370542 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_5370542 : Nat := 118140960795 + 5370542 * 2 ^ 59
def prefixEnd_5370542 : Nat := 4983230072969 + 3 ^ 40 * 5370542 * 2
def baseEnd_5370542 : Nat := 919223140386277321142111

theorem tailTrace_5370542 : CollatzResearch.WordTrace tailWord_5370542 prefixEnd_5370542 919223140386277321142111 := by
  unfold tailWord_5370542
  simp only [CollatzResearch.WordTrace]
  refine ⟨24484969863681378049431235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130586505939634016263633253 24484969863681378049431235)
  ·
    refine ⟨36727454795522067074146853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24484969863681378049431235 36727454795522067074146853)
    ·
      refine ⟨6886397774160387576402535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36727454795522067074146853 6886397774160387576402535)
      ·
        refine ⟨10329596661240581364603803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6886397774160387576402535 10329596661240581364603803)
        ·
          refine ⟨15494394991860872046905705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10329596661240581364603803 15494394991860872046905705)
          ·
            refine ⟨11620796243895654035179279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15494394991860872046905705 11620796243895654035179279)
            ·
              refine ⟨17431194365843481052768919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11620796243895654035179279 17431194365843481052768919)
              ·
                refine ⟨26146791548765221579153379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17431194365843481052768919 26146791548765221579153379)
                ·
                  refine ⟨39220187323147832368730069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26146791548765221579153379 39220187323147832368730069)
                  ·
                    refine ⟨919223140386277321142111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39220187323147832368730069 919223140386277321142111)
                    ·
                      rfl

theorem cell23_5370542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_5370542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370542 prefixEnd_5370542 := by exact prefixLift 5370542
  have htrace : WordTrace (prefixWord ++ tailWord_5370542) baseStart_5370542 baseEnd_5370542 := by
    simpa [prefixWord, tailWord_5370542, baseEnd_5370542] using wordTrace_append hprefix tailTrace_5370542
  have hstable : (prefixWord ++ tailWord_5370542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370542).length < 2 ^ (prefixWord ++ tailWord_5370542).sum := by decide
  have hdescent : baseEnd_5370542 < baseStart_5370542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370572 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 3, 4]
def baseStart_5370572 : Nat := 118140960795 + 5370572 * 2 ^ 59
def prefixEnd_5370572 : Nat := 4983230072969 + 3 ^ 40 * 5370572 * 2
def baseEnd_5370572 : Nat := 919228275192822282017065

theorem tailTrace_5370572 : CollatzResearch.WordTrace tailWord_5370572 prefixEnd_5370572 919228275192822282017065 := by
  unfold tailWord_5370572
  simp only [CollatzResearch.WordTrace]
  refine ⟨97940426549671169759520985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130587235399561559679361313 97940426549671169759520985)
  ·
    refine ⟨73455319912253377319640739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97940426549671169759520985 73455319912253377319640739)
    ·
      refine ⟨110182979868380065979461109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73455319912253377319640739 110182979868380065979461109)
      ·
        refine ⟨10329654362660631185574479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110182979868380065979461109 10329654362660631185574479)
        ·
          refine ⟨15494481543990946778361719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10329654362660631185574479 15494481543990946778361719)
          ·
            refine ⟨23241722315986420167542579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15494481543990946778361719 23241722315986420167542579)
            ·
              refine ⟨34862583473979630251313869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23241722315986420167542579 34862583473979630251313869)
              ·
                refine ⟨13073468802742361344242701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34862583473979630251313869 13073468802742361344242701)
                ·
                  refine ⟨4902550801028385504091013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13073468802742361344242701 4902550801028385504091013)
                  ·
                    refine ⟨919228275192822282017065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4902550801028385504091013 919228275192822282017065)
                    ·
                      rfl

theorem cell23_5370572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_5370572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370572 prefixEnd_5370572 := by exact prefixLift 5370572
  have htrace : WordTrace (prefixWord ++ tailWord_5370572) baseStart_5370572 baseEnd_5370572 := by
    simpa [prefixWord, tailWord_5370572, baseEnd_5370572] using wordTrace_append hprefix tailTrace_5370572
  have hstable : (prefixWord ++ tailWord_5370572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370572).length < 2 ^ (prefixWord ++ tailWord_5370572).sum := by decide
  have hdescent : baseEnd_5370572 < baseStart_5370572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370606 : List Nat := [4, 1, 2, 1, 1, 5, 1, 3, 1, 4]
def baseStart_5370606 : Nat := 118140960795 + 5370606 * 2 ^ 59
def prefixEnd_5370606 : Nat := 4983230072969 + 3 ^ 40 * 5370606 * 2
def baseEnd_5370606 : Nat := 919234094640239904342013

theorem tailTrace_5370606 : CollatzResearch.WordTrace tailWord_5370606 prefixEnd_5370606 919234094640239904342013 := by
  unfold tailWord_5370606
  simp only [CollatzResearch.WordTrace]
  refine ⟨24485261647652395415722459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130588062120812775550519781 24485261647652395415722459)
  ·
    refine ⟨36727892471478593123583689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24485261647652395415722459 36727892471478593123583689)
    ·
      refine ⟨27545919353608944842687767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36727892471478593123583689 27545919353608944842687767)
      ·
        refine ⟨41318879030413417264031651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27545919353608944842687767 41318879030413417264031651)
        ·
          refine ⟨61978318545620125896047477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41318879030413417264031651 61978318545620125896047477)
          ·
            refine ⟨5810467363651886802754451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61978318545620125896047477 5810467363651886802754451)
            ·
              refine ⟨8715701045477830204131677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5810467363651886802754451 8715701045477830204131677)
              ·
                refine ⟨3268387892054186326549379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8715701045477830204131677 3268387892054186326549379)
                ·
                  refine ⟨4902581838081279489824069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3268387892054186326549379 4902581838081279489824069)
                  ·
                    refine ⟨919234094640239904342013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4902581838081279489824069 919234094640239904342013)
                    ·
                      rfl

theorem cell23_5370606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_5370606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370606 prefixEnd_5370606 := by exact prefixLift 5370606
  have htrace : WordTrace (prefixWord ++ tailWord_5370606) baseStart_5370606 baseEnd_5370606 := by
    simpa [prefixWord, tailWord_5370606, baseEnd_5370606] using wordTrace_append hprefix tailTrace_5370606
  have hstable : (prefixWord ++ tailWord_5370606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370606).length < 2 ^ (prefixWord ++ tailWord_5370606).sum := by decide
  have hdescent : baseEnd_5370606 < baseStart_5370606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370629 : List Nat := [1, 3, 1, 1, 2, 1, 1, 8, 1, 1, 3]
def baseStart_5370629 : Nat := 118140960795 + 5370629 * 2 ^ 59
def prefixEnd_5370629 : Nat := 4983230072969 + 3 ^ 40 * 5370629 * 2
def baseEnd_5370629 : Nat := 2757714093975773123038433

theorem tailTrace_5370629 : CollatzResearch.WordTrace tailWord_5370629 prefixEnd_5370629 2757714093975773123038433 := by
  unfold tailWord_5370629
  simp only [CollatzResearch.WordTrace]
  refine ⟨195882932060135838253866941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130588621373423892169244627 195882932060135838253866941)
  ·
    refine ⟨73456099522550939345200103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195882932060135838253866941 73456099522550939345200103)
    ·
      refine ⟨110184149283826409017800155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73456099522550939345200103 110184149283826409017800155)
      ·
        refine ⟨165276223925739613526700233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110184149283826409017800155 165276223925739613526700233)
        ·
          refine ⟨123957167944304710145025175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165276223925739613526700233 123957167944304710145025175)
          ·
            refine ⟨185935751916457065217537763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123957167944304710145025175 185935751916457065217537763)
            ·
              refine ⟨278903627874685597826306645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185935751916457065217537763 278903627874685597826306645)
              ·
                refine ⟨3268401889156471849527031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 278903627874685597826306645 3268401889156471849527031)
                ·
                  refine ⟨4902602833734707774290547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3268401889156471849527031 4902602833734707774290547)
                  ·
                    refine ⟨7353904250602061661435821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4902602833734707774290547 7353904250602061661435821)
                    ·
                      refine ⟨2757714093975773123038433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7353904250602061661435821 2757714093975773123038433)
                      ·
                        rfl

theorem cell23_5370629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 1, 1, 3].length) (baseStart_5370629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370629 prefixEnd_5370629 := by exact prefixLift 5370629
  have htrace : WordTrace (prefixWord ++ tailWord_5370629) baseStart_5370629 baseEnd_5370629 := by
    simpa [prefixWord, tailWord_5370629, baseEnd_5370629] using wordTrace_append hprefix tailTrace_5370629
  have hstable : (prefixWord ++ tailWord_5370629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370629).length < 2 ^ (prefixWord ++ tailWord_5370629).sum := by decide
  have hdescent : baseEnd_5370629 < baseStart_5370629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370635 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 4]
def baseStart_5370635 : Nat := 118140960795 + 5370635 * 2 ^ 59
def prefixEnd_5370635 : Nat := 4983230072969 + 3 ^ 40 * 5370635 * 2
def baseEnd_5370635 : Nat := 2757717174859700099563405

theorem tailTrace_5370635 : CollatzResearch.WordTrace tailWord_5370635 prefixEnd_5370635 2757717174859700099563405 := by
  unfold tailWord_5370635
  simp only [CollatzResearch.WordTrace]
  refine ⟨195883150898114101278585359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130588767265409400852390239 195883150898114101278585359)
  ·
    refine ⟨293824726347171151917878039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195883150898114101278585359 293824726347171151917878039)
    ·
      refine ⟨440737089520756727876817059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293824726347171151917878039 440737089520756727876817059)
      ·
        refine ⟨661105634281135091815225589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440737089520756727876817059 661105634281135091815225589)
        ·
          refine ⟨61978653213856414857677399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 661105634281135091815225589 61978653213856414857677399)
          ·
            refine ⟨92967979820784622286516099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61978653213856414857677399 92967979820784622286516099)
            ·
              refine ⟨139451969731176933429774149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92967979820784622286516099 139451969731176933429774149)
              ·
                refine ⟨26147244324595675018082653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139451969731176933429774149 26147244324595675018082653)
                ·
                  refine ⟨9805216621723378131780995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26147244324595675018082653 9805216621723378131780995)
                  ·
                    refine ⟨14707824932585067197671493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9805216621723378131780995 14707824932585067197671493)
                    ·
                      refine ⟨2757717174859700099563405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14707824932585067197671493 2757717174859700099563405)
                      ·
                        rfl

theorem cell23_5370635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 4].length) (baseStart_5370635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370635 prefixEnd_5370635 := by exact prefixLift 5370635
  have htrace : WordTrace (prefixWord ++ tailWord_5370635) baseStart_5370635 baseEnd_5370635 := by
    simpa [prefixWord, tailWord_5370635, baseEnd_5370635] using wordTrace_append hprefix tailTrace_5370635
  have hstable : (prefixWord ++ tailWord_5370635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370635).length < 2 ^ (prefixWord ++ tailWord_5370635).sum := by decide
  have hdescent : baseEnd_5370635 < baseStart_5370635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370645 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 1, 6]
def baseStart_5370645 : Nat := 118140960795 + 5370645 * 2 ^ 59
def prefixEnd_5370645 : Nat := 4983230072969 + 3 ^ 40 * 5370645 * 2
def baseEnd_5370645 : Nat := 919240769888748353479453

theorem tailTrace_5370645 : CollatzResearch.WordTrace tailWord_5370645 prefixEnd_5370645 919240769888748353479453 := by
  unfold tailWord_5370645
  simp only [CollatzResearch.WordTrace]
  refine ⟨195883515628077872986449389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130589010418718581990966259 195883515628077872986449389)
  ·
    refine ⟨73456318360529202369918521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195883515628077872986449389 73456318360529202369918521)
    ·
      refine ⟨55092238770396901777438891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73456318360529202369918521 55092238770396901777438891)
      ·
        refine ⟨82638358155595352666158337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55092238770396901777438891 82638358155595352666158337)
        ·
          refine ⟨61978768616696514499618753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82638358155595352666158337 61978768616696514499618753)
          ·
            refine ⟨46484076462522385874714065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61978768616696514499618753 46484076462522385874714065)
            ·
              refine ⟨34863057346891789406035549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46484076462522385874714065 34863057346891789406035549)
              ·
                refine ⟨13073646505084421027263331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34863057346891789406035549 13073646505084421027263331)
                ·
                  refine ⟨19610469757626631540894997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13073646505084421027263331 19610469757626631540894997)
                  ·
                    refine ⟨919240769888748353479453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19610469757626631540894997 919240769888748353479453)
                    ·
                      rfl

theorem cell23_5370645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_5370645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370645 prefixEnd_5370645 := by exact prefixLift 5370645
  have htrace : WordTrace (prefixWord ++ tailWord_5370645) baseStart_5370645 baseEnd_5370645 := by
    simpa [prefixWord, tailWord_5370645, baseEnd_5370645] using wordTrace_append hprefix tailTrace_5370645
  have hstable : (prefixWord ++ tailWord_5370645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370645).length < 2 ^ (prefixWord ++ tailWord_5370645).sum := by decide
  have hdescent : baseEnd_5370645 < baseStart_5370645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370652 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_5370652 : Nat := 118140960795 + 5370652 * 2 ^ 59
def prefixEnd_5370652 : Nat := 4983230072969 + 3 ^ 40 * 5370652 * 2
def baseEnd_5370652 : Nat := 2757725904030826533050827

theorem tailTrace_5370652 : CollatzResearch.WordTrace tailWord_5370652 prefixEnd_5370652 2757725904030826533050827 := by
  unfold tailWord_5370652
  simp only [CollatzResearch.WordTrace]
  refine ⟨97941885469526256590977105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130589180626035008787969473 97941885469526256590977105)
  ·
    refine ⟨73456414102144692443232829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97941885469526256590977105 73456414102144692443232829)
    ·
      refine ⟨27546155288304259666212311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73456414102144692443232829 27546155288304259666212311)
      ·
        refine ⟨41319232932456389499318467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27546155288304259666212311 41319232932456389499318467)
        ·
          refine ⟨61978849398684584248977701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41319232932456389499318467 61978849398684584248977701)
          ·
            refine ⟨11621034262253359546683319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61978849398684584248977701 11621034262253359546683319)
            ·
              refine ⟨17431551393380039320024979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11621034262253359546683319 17431551393380039320024979)
              ·
                refine ⟨26147327090070058980037469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17431551393380039320024979 26147327090070058980037469)
                ·
                  refine ⟨9805247658776272117514051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26147327090070058980037469 9805247658776272117514051)
                  ·
                    refine ⟨14707871488164408176271077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9805247658776272117514051 14707871488164408176271077)
                    ·
                      refine ⟨2757725904030826533050827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14707871488164408176271077 2757725904030826533050827)
                      ·
                        rfl

theorem cell23_5370652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_5370652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370652 prefixEnd_5370652 := by exact prefixLift 5370652
  have htrace : WordTrace (prefixWord ++ tailWord_5370652) baseStart_5370652 baseEnd_5370652 := by
    simpa [prefixWord, tailWord_5370652, baseEnd_5370652] using wordTrace_append hprefix tailTrace_5370652
  have hstable : (prefixWord ++ tailWord_5370652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370652).length < 2 ^ (prefixWord ++ tailWord_5370652).sum := by decide
  have hdescent : baseEnd_5370652 < baseStart_5370652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370665 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 1, 2, 4]
def baseStart_5370665 : Nat := 118140960795 + 5370665 * 2 ^ 59
def prefixEnd_5370665 : Nat := 4983230072969 + 3 ^ 40 * 5370665 * 2
def baseEnd_5370665 : Nat := 2757732579279334982188267

theorem tailTrace_5370665 : CollatzResearch.WordTrace tailWord_5370665 prefixEnd_5370665 2757732579279334982188267 := by
  unfold tailWord_5370665
  simp only [CollatzResearch.WordTrace]
  refine ⟨195884245088005416402177449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130589496725336944268118299 195884245088005416402177449)
  ·
    refine ⟨146913183816004062301633087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195884245088005416402177449 146913183816004062301633087)
    ·
      refine ⟨220369775724006093452449631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146913183816004062301633087 220369775724006093452449631)
      ·
        refine ⟨330554663586009140178674447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220369775724006093452449631 330554663586009140178674447)
        ·
          refine ⟨495831995379013710268011671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330554663586009140178674447 495831995379013710268011671)
          ·
            refine ⟨743747993068520565402017507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495831995379013710268011671 743747993068520565402017507)
            ·
              refine ⟨1115621989602780848103026261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743747993068520565402017507 1115621989602780848103026261)
              ·
                refine ⟨13073695190657588063707339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1115621989602780848103026261 13073695190657588063707339)
                ·
                  refine ⟨19610542785986382095561009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13073695190657588063707339 19610542785986382095561009)
                  ·
                    refine ⟨14707907089489786571670757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19610542785986382095561009 14707907089489786571670757)
                    ·
                      refine ⟨2757732579279334982188267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14707907089489786571670757 2757732579279334982188267)
                      ·
                        rfl

theorem cell23_5370665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_5370665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370665 prefixEnd_5370665 := by exact prefixLift 5370665
  have htrace : WordTrace (prefixWord ++ tailWord_5370665) baseStart_5370665 baseEnd_5370665 := by
    simpa [prefixWord, tailWord_5370665, baseEnd_5370665] using wordTrace_append hprefix tailTrace_5370665
  have hstable : (prefixWord ++ tailWord_5370665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370665).length < 2 ^ (prefixWord ++ tailWord_5370665).sum := by decide
  have hdescent : baseEnd_5370665 < baseStart_5370665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370672 : List Nat := [2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 3]
def baseStart_5370672 : Nat := 118140960795 + 5370672 * 2 ^ 59
def prefixEnd_5370672 : Nat := 4983230072969 + 3 ^ 40 * 5370672 * 2
def baseEnd_5370672 : Nat := 2757736173643916454800735

theorem tailTrace_5370672 : CollatzResearch.WordTrace tailWord_5370672 prefixEnd_5370672 2757736173643916454800735 := by
  unfold tailWord_5370672
  simp only [CollatzResearch.WordTrace]
  refine ⟨97942250199490028298841135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130589666932653371065121513 97942250199490028298841135)
  ·
    refine ⟨146913375299235042448261703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97942250199490028298841135 146913375299235042448261703)
    ·
      refine ⟨220370062948852563672392555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146913375299235042448261703 220370062948852563672392555)
      ·
        refine ⟨330555094423278845508588833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220370062948852563672392555 330555094423278845508588833)
        ·
          refine ⟨247916320817459134131441625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330555094423278845508588833 247916320817459134131441625)
          ·
            refine ⟨185937240613094350598581219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247916320817459134131441625 185937240613094350598581219)
            ·
              refine ⟨278905860919641525897871829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185937240613094350598581219 278905860919641525897871829)
              ·
                refine ⟨6536856115304098263231371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 278905860919641525897871829 6536856115304098263231371)
                ·
                  refine ⟨9805284172956147394847057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6536856115304098263231371 9805284172956147394847057)
                  ·
                    refine ⟨7353963129717110546135293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9805284172956147394847057 7353963129717110546135293)
                    ·
                      refine ⟨2757736173643916454800735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7353963129717110546135293 2757736173643916454800735)
                      ·
                        rfl

theorem cell23_5370672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 3].length) (baseStart_5370672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370672 prefixEnd_5370672 := by exact prefixLift 5370672
  have htrace : WordTrace (prefixWord ++ tailWord_5370672) baseStart_5370672 baseEnd_5370672 := by
    simpa [prefixWord, tailWord_5370672, baseEnd_5370672] using wordTrace_append hprefix tailTrace_5370672
  have hstable : (prefixWord ++ tailWord_5370672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370672).length < 2 ^ (prefixWord ++ tailWord_5370672).sum := by decide
  have hdescent : baseEnd_5370672 < baseStart_5370672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370849 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 2, 4, 2]
def baseStart_5370849 : Nat := 118140960795 + 5370849 * 2 ^ 59
def prefixEnd_5370849 : Nat := 4983230072969 + 3 ^ 40 * 5370849 * 2
def baseEnd_5370849 : Nat := 2757827059719762262287421

theorem tailTrace_5370849 : CollatzResearch.WordTrace tailWord_5370849 prefixEnd_5370849 2757827059719762262287421 := by
  unfold tailWord_5370849
  simp only [CollatzResearch.WordTrace]
  refine ⟨195890956119338815826875601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130593970746225877217917067 195890956119338815826875601)
  ·
    refine ⟨146918217089504111870156701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195890956119338815826875601 146918217089504111870156701)
    ·
      refine ⟨55094331408564041951308763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146918217089504111870156701 55094331408564041951308763)
      ·
        refine ⟨82641497112846062926963145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55094331408564041951308763 82641497112846062926963145)
        ·
          refine ⟨61981122834634547195222359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82641497112846062926963145 61981122834634547195222359)
          ·
            refine ⟨92971684251951820792833539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61981122834634547195222359 92971684251951820792833539)
            ·
              refine ⟨139457526377927731189250309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92971684251951820792833539 139457526377927731189250309)
              ·
                refine ⟨26148286195861449597984433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139457526377927731189250309 26148286195861449597984433)
                ·
                  refine ⟨19611214646896087198488325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26148286195861449597984433 19611214646896087198488325)
                  ·
                    refine ⟨3677102746293016349716561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19611214646896087198488325 3677102746293016349716561)
                    ·
                      refine ⟨2757827059719762262287421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3677102746293016349716561 2757827059719762262287421)
                      ·
                        rfl

theorem cell23_5370849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_5370849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370849 prefixEnd_5370849 := by exact prefixLift 5370849
  have htrace : WordTrace (prefixWord ++ tailWord_5370849) baseStart_5370849 baseEnd_5370849 := by
    simpa [prefixWord, tailWord_5370849, baseEnd_5370849] using wordTrace_append hprefix tailTrace_5370849
  have hstable : (prefixWord ++ tailWord_5370849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370849).length < 2 ^ (prefixWord ++ tailWord_5370849).sum := by decide
  have hdescent : baseEnd_5370849 < baseStart_5370849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370850 : List Nat := [3, 3, 3, 1, 1, 3, 2, 2, 5]
def baseStart_5370850 : Nat := 118140960795 + 5370850 * 2 ^ 59
def prefixEnd_5370850 : Nat := 4983230072969 + 3 ^ 40 * 5370850 * 2
def baseEnd_5370850 : Nat := 306425285911157417597213

theorem tailTrace_5370850 : CollatzResearch.WordTrace tailWord_5370850 prefixEnd_5370850 306425285911157417597213 := by
  unfold tailWord_5370850
  simp only [CollatzResearch.WordTrace]
  refine ⟨48972748148083798249415501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130593995061556795331774669 48972748148083798249415501)
  ·
    refine ⟨18364780555531424343530813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48972748148083798249415501 18364780555531424343530813)
    ·
      refine ⟨6886792708324284128824055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18364780555531424343530813 6886792708324284128824055)
      ·
        refine ⟨10330189062486426193236083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6886792708324284128824055 10330189062486426193236083)
        ·
          refine ⟨15495283593729639289854125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10330189062486426193236083 15495283593729639289854125)
          ·
            refine ⟨5810731347648614733695297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15495283593729639289854125 5810731347648614733695297)
            ·
              refine ⟨4358048510736461050271473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5810731347648614733695297 4358048510736461050271473)
              ·
                refine ⟨3268536383052345787703605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4358048510736461050271473 3268536383052345787703605)
                ·
                  refine ⟨306425285911157417597213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3268536383052345787703605 306425285911157417597213)
                  ·
                    rfl

theorem cell23_5370850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_5370850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370850 prefixEnd_5370850 := by exact prefixLift 5370850
  have htrace : WordTrace (prefixWord ++ tailWord_5370850) baseStart_5370850 baseEnd_5370850 := by
    simpa [prefixWord, tailWord_5370850, baseEnd_5370850] using wordTrace_append hprefix tailTrace_5370850
  have hstable : (prefixWord ++ tailWord_5370850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370850).length < 2 ^ (prefixWord ++ tailWord_5370850).sum := by decide
  have hdescent : baseEnd_5370850 < baseStart_5370850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370899 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 7, 1, 3]
def baseStart_5370899 : Nat := 118140960795 + 5370899 * 2 ^ 59
def prefixEnd_5370899 : Nat := 4983230072969 + 3 ^ 40 * 5370899 * 2
def baseEnd_5370899 : Nat := 2757852733752487066662191

theorem tailTrace_5370899 : CollatzResearch.WordTrace tailWord_5370899 prefixEnd_5370899 2757852733752487066662191 := by
  unfold tailWord_5370899
  simp only [CollatzResearch.WordTrace]
  refine ⟨195892779769157674366195751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130595186512771782910797167 195892779769157674366195751)
  ·
    refine ⟨293839169653736511549293627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195892779769157674366195751 293839169653736511549293627)
    ·
      refine ⟨440758754480604767323940441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293839169653736511549293627 440758754480604767323940441)
      ·
        refine ⟨330569065860453575492955331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440758754480604767323940441 330569065860453575492955331)
        ·
          refine ⟨495853598790680363239432997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330569065860453575492955331 495853598790680363239432997)
          ·
            refine ⟨92972549773252568107393687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 495853598790680363239432997 92972549773252568107393687)
            ·
              refine ⟨139458824659878852161090531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92972549773252568107393687 139458824659878852161090531)
              ·
                refine ⟨209188236989818278241635797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139458824659878852161090531 209188236989818278241635797)
                ·
                  refine ⟨4902849304448865896288339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 209188236989818278241635797 4902849304448865896288339)
                  ·
                    refine ⟨7354273956673298844432509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4902849304448865896288339 7354273956673298844432509)
                    ·
                      refine ⟨2757852733752487066662191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7354273956673298844432509 2757852733752487066662191)
                      ·
                        rfl

theorem cell23_5370899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 1, 3].length) (baseStart_5370899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370899 prefixEnd_5370899 := by exact prefixLift 5370899
  have htrace : WordTrace (prefixWord ++ tailWord_5370899) baseStart_5370899 baseEnd_5370899 := by
    simpa [prefixWord, tailWord_5370899, baseEnd_5370899] using wordTrace_append hprefix tailTrace_5370899
  have hstable : (prefixWord ++ tailWord_5370899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370899).length < 2 ^ (prefixWord ++ tailWord_5370899).sum := by decide
  have hdescent : baseEnd_5370899 < baseStart_5370899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370926 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_5370926 : Nat := 118140960795 + 5370926 * 2 ^ 59
def prefixEnd_5370926 : Nat := 4983230072969 + 3 ^ 40 * 5370926 * 2
def baseEnd_5370926 : Nat := 2757866597730158461024567

theorem tailTrace_5370926 : CollatzResearch.WordTrace tailWord_5370926 prefixEnd_5370926 2757866597730158461024567 := by
  unfold tailWord_5370926
  simp only [CollatzResearch.WordTrace]
  refine ⟨24486720567507482247178579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130595843026706571984952421 24486720567507482247178579)
  ·
    refine ⟨36730080851261223370767869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24486720567507482247178579 36730080851261223370767869)
    ·
      refine ⟨13773780319222958764037951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36730080851261223370767869 13773780319222958764037951)
      ·
        refine ⟨20660670478834438146056927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13773780319222958764037951 20660670478834438146056927)
        ·
          refine ⟨30991005718251657219085391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20660670478834438146056927 30991005718251657219085391)
          ·
            refine ⟨46486508577377485828628087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30991005718251657219085391 46486508577377485828628087)
            ·
              refine ⟨69729762866066228742942131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46486508577377485828628087 69729762866066228742942131)
              ·
                refine ⟨104594644299099343114413197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69729762866066228742942131 104594644299099343114413197)
                ·
                  refine ⟨39222991612162253667904949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104594644299099343114413197 39222991612162253667904949)
                  ·
                    refine ⟨3677155463640211281366089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39222991612162253667904949 3677155463640211281366089)
                    ·
                      refine ⟨2757866597730158461024567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3677155463640211281366089 2757866597730158461024567)
                      ·
                        rfl

theorem cell23_5370926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_5370926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370926 prefixEnd_5370926 := by exact prefixLift 5370926
  have htrace : WordTrace (prefixWord ++ tailWord_5370926) baseStart_5370926 baseEnd_5370926 := by
    simpa [prefixWord, tailWord_5370926, baseEnd_5370926] using wordTrace_append hprefix tailTrace_5370926
  have hstable : (prefixWord ++ tailWord_5370926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370926).length < 2 ^ (prefixWord ++ tailWord_5370926).sum := by decide
  have hdescent : baseEnd_5370926 < baseStart_5370926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370936 : List Nat := [2, 1, 2, 1, 5, 2, 2, 2, 1, 5]
def baseStart_5370936 : Nat := 118140960795 + 5370936 * 2 ^ 59
def prefixEnd_5370936 : Nat := 4983230072969 + 3 ^ 40 * 5370936 * 2
def baseEnd_5370936 : Nat := 919290577512234473966507

theorem tailTrace_5370936 : CollatzResearch.WordTrace tailWord_5370936 prefixEnd_5370936 919290577512234473966507 := by
  unfold tailWord_5370936
  simp only [CollatzResearch.WordTrace]
  refine ⟨97947064635011814842646331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130596086180015753123528441 97947064635011814842646331)
  ·
    refine ⟨146920596952517722263969497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97947064635011814842646331 146920596952517722263969497)
    ·
      refine ⟨110190447714388291697977123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146920596952517722263969497 110190447714388291697977123)
      ·
        refine ⟨165285671571582437546965685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110190447714388291697977123 165285671571582437546965685)
        ·
          refine ⟨15495531709835853520028033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165285671571582437546965685 15495531709835853520028033)
          ·
            refine ⟨11621648782376890140021025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15495531709835853520028033 11621648782376890140021025)
            ·
              refine ⟨8716236586782667605015769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11621648782376890140021025 8716236586782667605015769)
              ·
                refine ⟨6537177440087000703761827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8716236586782667605015769 6537177440087000703761827)
                ·
                  refine ⟨9805766160130501055642741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6537177440087000703761827 9805766160130501055642741)
                  ·
                    refine ⟨919290577512234473966507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9805766160130501055642741 919290577512234473966507)
                    ·
                      rfl

theorem cell23_5370936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_5370936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370936 prefixEnd_5370936 := by exact prefixLift 5370936
  have htrace : WordTrace (prefixWord ++ tailWord_5370936) baseStart_5370936 baseEnd_5370936 := by
    simpa [prefixWord, tailWord_5370936, baseEnd_5370936] using wordTrace_append hprefix tailTrace_5370936
  have hstable : (prefixWord ++ tailWord_5370936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370936).length < 2 ^ (prefixWord ++ tailWord_5370936).sum := by decide
  have hdescent : baseEnd_5370936 < baseStart_5370936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370949 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 4, 4]
def baseStart_5370949 : Nat := 118140960795 + 5370949 * 2 ^ 59
def prefixEnd_5370949 : Nat := 4983230072969 + 3 ^ 40 * 5370949 * 2
def baseEnd_5370949 : Nat := 919292802595070623678987

theorem tailTrace_5370949 : CollatzResearch.WordTrace tailWord_5370949 prefixEnd_5370949 919292802595070623678987 := by
  unfold tailWord_5370949
  simp only [CollatzResearch.WordTrace]
  refine ⟨195894603418976532905515901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130596402279317688603677267 195894603418976532905515901)
  ·
    refine ⟨73460476282116199839568463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195894603418976532905515901 73460476282116199839568463)
    ·
      refine ⟨110190714423174299759352695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73460476282116199839568463 110190714423174299759352695)
      ·
        refine ⟨165286071634761449639029043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110190714423174299759352695 165286071634761449639029043)
        ·
          refine ⟨247929107452142174458543565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165286071634761449639029043 247929107452142174458543565)
          ·
            refine ⟨92973415294553315421953837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247929107452142174458543565 92973415294553315421953837)
            ·
              refine ⟨34865030735457493283232689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92973415294553315421953837 34865030735457493283232689)
              ·
                refine ⟨26148773051593119962424517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34865030735457493283232689 26148773051593119962424517)
                ·
                  refine ⟨4902894947173709992954597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26148773051593119962424517 4902894947173709992954597)
                  ·
                    refine ⟨919292802595070623678987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4902894947173709992954597 919292802595070623678987)
                    ·
                      rfl

theorem cell23_5370949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_5370949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370949 prefixEnd_5370949 := by exact prefixLift 5370949
  have htrace : WordTrace (prefixWord ++ tailWord_5370949) baseStart_5370949 baseEnd_5370949 := by
    simpa [prefixWord, tailWord_5370949, baseEnd_5370949] using wordTrace_append hprefix tailTrace_5370949
  have hstable : (prefixWord ++ tailWord_5370949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370949).length < 2 ^ (prefixWord ++ tailWord_5370949).sum := by decide
  have hdescent : baseEnd_5370949 < baseStart_5370949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5370983 : List Nat := [1, 1, 5, 1, 1, 3, 4, 1, 2, 4]
def baseStart_5370983 : Nat := 118140960795 + 5370983 * 2 ^ 59
def prefixEnd_5370983 : Nat := 4983230072969 + 3 ^ 40 * 5370983 * 2
def baseEnd_5370983 : Nat := 919298622042488246003935

theorem tailTrace_5370983 : CollatzResearch.WordTrace tailWord_5370983 prefixEnd_5370983 919298622042488246003935 := by
  unfold tailWord_5370983
  simp only [CollatzResearch.WordTrace]
  refine ⟨195895843500853356712253603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130597229000568904474835735 195895843500853356712253603)
  ·
    refine ⟨293843765251280035068380405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195895843500853356712253603 293843765251280035068380405)
    ·
      refine ⟨27547852992307503287660663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 293843765251280035068380405 27547852992307503287660663)
      ·
        refine ⟨41321779488461254931490995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27547852992307503287660663 41321779488461254931490995)
        ·
          refine ⟨61982669232691882397236493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41321779488461254931490995 61982669232691882397236493)
          ·
            refine ⟨23243500962259455898963685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61982669232691882397236493 23243500962259455898963685)
            ·
              refine ⟨4358156430423647981055691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23243500962259455898963685 4358156430423647981055691)
              ·
                refine ⟨6537234645635471971583537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4358156430423647981055691 6537234645635471971583537)
                ·
                  refine ⟨4902925984226603978687653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6537234645635471971583537 4902925984226603978687653)
                  ·
                    refine ⟨919298622042488246003935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4902925984226603978687653 919298622042488246003935)
                    ·
                      rfl

theorem cell23_5370983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_5370983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5370983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5370983 prefixEnd_5370983 := by exact prefixLift 5370983
  have htrace : WordTrace (prefixWord ++ tailWord_5370983) baseStart_5370983 baseEnd_5370983 := by
    simpa [prefixWord, tailWord_5370983, baseEnd_5370983] using wordTrace_append hprefix tailTrace_5370983
  have hstable : (prefixWord ++ tailWord_5370983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5370983).length < 2 ^ (prefixWord ++ tailWord_5370983).sum := by decide
  have hdescent : baseEnd_5370983 < baseStart_5370983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5370983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371050 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_5371050 : Nat := 118140960795 + 5371050 * 2 ^ 59
def prefixEnd_5371050 : Nat := 4983230072969 + 3 ^ 40 * 5371050 * 2
def baseEnd_5371050 : Nat := 2757930269331315975873997

theorem tailTrace_5371050 : CollatzResearch.WordTrace tailWord_5371050 prefixEnd_5371050 2757930269331315975873997 := by
  unfold tailWord_5371050
  simp only [CollatzResearch.WordTrace]
  refine ⟨48974571797902656788735651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130598858127740418103295069 48974571797902656788735651)
  ·
    refine ⟨73461857696853985183103477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48974571797902656788735651 73461857696853985183103477)
    ·
      refine ⟨6887049159080061110915951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73461857696853985183103477 6887049159080061110915951)
      ·
        refine ⟨10330573738620091666373927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6887049159080061110915951 10330573738620091666373927)
        ·
          refine ⟨15495860607930137499560891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10330573738620091666373927 15495860607930137499560891)
          ·
            refine ⟨23243790911895206249341337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15495860607930137499560891 23243790911895206249341337)
            ·
              refine ⟨17432843183921404687006003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23243790911895206249341337 17432843183921404687006003)
              ·
                refine ⟨26149264775882107030509005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17432843183921404687006003 26149264775882107030509005)
                ·
                  refine ⟨9805974290955790136440877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26149264775882107030509005 9805974290955790136440877)
                  ·
                    refine ⟨3677240359108421301165329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9805974290955790136440877 3677240359108421301165329)
                    ·
                      refine ⟨2757930269331315975873997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3677240359108421301165329 2757930269331315975873997)
                      ·
                        rfl

theorem cell23_5371050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_5371050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371050 prefixEnd_5371050 := by exact prefixLift 5371050
  have htrace : WordTrace (prefixWord ++ tailWord_5371050) baseStart_5371050 baseEnd_5371050 := by
    simpa [prefixWord, tailWord_5371050, baseEnd_5371050] using wordTrace_append hprefix tailTrace_5371050
  have hstable : (prefixWord ++ tailWord_5371050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371050).length < 2 ^ (prefixWord ++ tailWord_5371050).sum := by decide
  have hdescent : baseEnd_5371050 < baseStart_5371050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371063 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 4, 2, 2]
def baseStart_5371063 : Nat := 118140960795 + 5371063 * 2 ^ 59
def prefixEnd_5371063 : Nat := 4983230072969 + 3 ^ 40 * 5371063 * 2
def baseEnd_5371063 : Nat := 2757936944579824425011437

theorem tailTrace_5371063 : CollatzResearch.WordTrace tailWord_5371063 prefixEnd_5371063 2757936944579824425011437 := by
  unfold tailWord_5371063
  simp only [CollatzResearch.WordTrace]
  refine ⟨195898761340563530375165843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130599174227042353583443895 195898761340563530375165843)
  ·
    refine ⟨293848142010845295562748765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195898761340563530375165843 293848142010845295562748765)
    ·
      refine ⟨110193053254066985836030787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293848142010845295562748765 110193053254066985836030787)
      ·
        refine ⟨165289579881100478754046181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110193053254066985836030787 165289579881100478754046181)
        ·
          refine ⟨30991796227706339766383659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165289579881100478754046181 30991796227706339766383659)
          ·
            refine ⟨46487694341559509649575489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30991796227706339766383659 46487694341559509649575489)
            ·
              refine ⟨34865770756169632237181617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46487694341559509649575489 34865770756169632237181617)
              ·
                refine ⟨26149328067127224177886213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34865770756169632237181617 26149328067127224177886213)
                ·
                  refine ⟨4902999012586354533353665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26149328067127224177886213 4902999012586354533353665)
                  ·
                    refine ⟨3677249259439765900015249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4902999012586354533353665 3677249259439765900015249)
                    ·
                      refine ⟨2757936944579824425011437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3677249259439765900015249 2757936944579824425011437)
                      ·
                        rfl

theorem cell23_5371063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 2, 2].length) (baseStart_5371063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371063 prefixEnd_5371063 := by exact prefixLift 5371063
  have htrace : WordTrace (prefixWord ++ tailWord_5371063) baseStart_5371063 baseEnd_5371063 := by
    simpa [prefixWord, tailWord_5371063, baseEnd_5371063] using wordTrace_append hprefix tailTrace_5371063
  have hstable : (prefixWord ++ tailWord_5371063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371063).length < 2 ^ (prefixWord ++ tailWord_5371063).sum := by decide
  have hdescent : baseEnd_5371063 < baseStart_5371063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371080 : List Nat := [2, 1, 3, 1, 2, 1, 5, 2, 2, 2, 2]
def baseStart_5371080 : Nat := 118140960795 + 5371080 * 2 ^ 59
def prefixEnd_5371080 : Nat := 4983230072969 + 3 ^ 40 * 5371080 * 2
def baseEnd_5371080 : Nat := 2757945673750950858498859

theorem tailTrace_5371080 : CollatzResearch.WordTrace tailWord_5371080 prefixEnd_5371080 2757945673750950858498859 := by
  unfold tailWord_5371080
  simp only [CollatzResearch.WordTrace]
  refine ⟨97949690690750971139267347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130599587587667961519023129 97949690690750971139267347)
  ·
    refine ⟨146924536036126456708901021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97949690690750971139267347 146924536036126456708901021)
    ·
      refine ⟨55096701013547421265837883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146924536036126456708901021 55096701013547421265837883)
      ·
        refine ⟨82645051520321131898756825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55096701013547421265837883 82645051520321131898756825)
        ·
          refine ⟨61983788640240848924067619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82645051520321131898756825 61983788640240848924067619)
          ·
            refine ⟨92975682960361273386101429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61983788640240848924067619 92975682960361273386101429)
            ·
              refine ⟨8716470277533869379947009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92975682960361273386101429 8716470277533869379947009)
              ·
                refine ⟨6537352708150402034960257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8716470277533869379947009 6537352708150402034960257)
                ·
                  refine ⟨4903014531112801526220193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6537352708150402034960257 4903014531112801526220193)
                  ·
                    refine ⟨3677260898334601144665145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4903014531112801526220193 3677260898334601144665145)
                    ·
                      refine ⟨2757945673750950858498859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3677260898334601144665145 2757945673750950858498859)
                      ·
                        rfl

theorem cell23_5371080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_5371080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371080 prefixEnd_5371080 := by exact prefixLift 5371080
  have htrace : WordTrace (prefixWord ++ tailWord_5371080) baseStart_5371080 baseEnd_5371080 := by
    simpa [prefixWord, tailWord_5371080, baseEnd_5371080] using wordTrace_append hprefix tailTrace_5371080
  have hstable : (prefixWord ++ tailWord_5371080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371080).length < 2 ^ (prefixWord ++ tailWord_5371080).sum := by decide
  have hdescent : baseEnd_5371080 < baseStart_5371080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371126 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_5371126 : Nat := 118140960795 + 5371126 * 2 ^ 59
def prefixEnd_5371126 : Nat := 4983230072969 + 3 ^ 40 * 5371126 * 2
def baseEnd_5371126 : Nat := 2757969293861057678523647

theorem tailTrace_5371126 : CollatzResearch.WordTrace tailWord_5371126 prefixEnd_5371126 2757969293861057678523647 := by
  unfold tailWord_5371126
  simp only [CollatzResearch.WordTrace]
  refine ⟨12243816196208455758419327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130600706092890194756472821 12243816196208455758419327)
  ·
    refine ⟨18365724294312683637628991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12243816196208455758419327 18365724294312683637628991)
    ·
      refine ⟨27548586441469025456443487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18365724294312683637628991 27548586441469025456443487)
      ·
        refine ⟨41322879662203538184665231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27548586441469025456443487 41322879662203538184665231)
        ·
          refine ⟨61984319493305307276997847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41322879662203538184665231 61984319493305307276997847)
          ·
            refine ⟨92976479239957960915496771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61984319493305307276997847 92976479239957960915496771)
            ·
              refine ⟨139464718859936941373245157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92976479239957960915496771 139464718859936941373245157)
              ·
                refine ⟨26149634786238176507483467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139464718859936941373245157 26149634786238176507483467)
                ·
                  refine ⟨39224452179357264761225201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26149634786238176507483467 39224452179357264761225201)
                  ·
                    refine ⟨29418339134517948570918901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39224452179357264761225201 29418339134517948570918901)
                    ·
                      refine ⟨2757969293861057678523647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29418339134517948570918901 2757969293861057678523647)
                      ·
                        rfl

theorem cell23_5371126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_5371126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371126 prefixEnd_5371126 := by exact prefixLift 5371126
  have htrace : WordTrace (prefixWord ++ tailWord_5371126) baseStart_5371126 baseEnd_5371126 := by
    simpa [prefixWord, tailWord_5371126, baseEnd_5371126] using wordTrace_append hprefix tailTrace_5371126
  have hstable : (prefixWord ++ tailWord_5371126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371126).length < 2 ^ (prefixWord ++ tailWord_5371126).sum := by decide
  have hdescent : baseEnd_5371126 < baseStart_5371126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371170 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_5371170 : Nat := 118140960795 + 5371170 * 2 ^ 59
def prefixEnd_5371170 : Nat := 4983230072969 + 3 ^ 40 * 5371170 * 2
def baseEnd_5371170 : Nat := 2757991887009855506373445

theorem tailTrace_5371170 : CollatzResearch.WordTrace tailWord_5371170 prefixEnd_5371170 2757991887009855506373445 := by
  unfold tailWord_5371170
  simp only [CollatzResearch.WordTrace]
  refine ⟨48975665987793971912327741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130601775967450591766207309 48975665987793971912327741)
  ·
    refine ⟨18365874745422739467122903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48975665987793971912327741 18365874745422739467122903)
    ·
      refine ⟨27548812118134109200684355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18365874745422739467122903 27548812118134109200684355)
      ·
        refine ⟨41323218177201163801026533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27548812118134109200684355 41323218177201163801026533)
        ·
          refine ⟨7748103408225218212692475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41323218177201163801026533 7748103408225218212692475)
          ·
            refine ⟨11622155112337827319038713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7748103408225218212692475 11622155112337827319038713)
            ·
              refine ⟨8716616334253370489279035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11622155112337827319038713 8716616334253370489279035)
              ·
                refine ⟨13074924501380055733918553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8716616334253370489279035 13074924501380055733918553)
                ·
                  refine ⟨9806193376035041800438915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13074924501380055733918553 9806193376035041800438915)
                  ·
                    refine ⟨14709290064052562700658373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9806193376035041800438915 14709290064052562700658373)
                    ·
                      refine ⟨2757991887009855506373445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14709290064052562700658373 2757991887009855506373445)
                      ·
                        rfl

theorem cell23_5371170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_5371170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371170 prefixEnd_5371170 := by exact prefixLift 5371170
  have htrace : WordTrace (prefixWord ++ tailWord_5371170) baseStart_5371170 baseEnd_5371170 := by
    simpa [prefixWord, tailWord_5371170, baseEnd_5371170] using wordTrace_append hprefix tailTrace_5371170
  have hstable : (prefixWord ++ tailWord_5371170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371170).length < 2 ^ (prefixWord ++ tailWord_5371170).sum := by decide
  have hdescent : baseEnd_5371170 < baseStart_5371170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371173 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 2, 2, 3]
def baseStart_5371173 : Nat := 118140960795 + 5371173 * 2 ^ 59
def prefixEnd_5371173 : Nat := 4983230072969 + 3 ^ 40 * 5371173 * 2
def baseEnd_5371173 : Nat := 2757993427451818994635931

theorem tailTrace_5371173 : CollatzResearch.WordTrace tailWord_5371173 prefixEnd_5371173 2757993427451818994635931 := by
  unfold tailWord_5371173
  simp only [CollatzResearch.WordTrace]
  refine ⟨195902773370165019161670173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130601848913443346107780115 195902773370165019161670173)
  ·
    refine ⟨73463540013811882185626315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195902773370165019161670173 73463540013811882185626315)
    ·
      refine ⟨110195310020717823278439473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73463540013811882185626315 110195310020717823278439473)
      ·
        refine ⟨82646482515538367458829605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110195310020717823278439473 82646482515538367458829605)
        ·
          refine ⟨15496215471663443898530551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82646482515538367458829605 15496215471663443898530551)
          ·
            refine ⟨23244323207495165847795827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15496215471663443898530551 23244323207495165847795827)
            ·
              refine ⟨34866484811242748771693741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23244323207495165847795827 34866484811242748771693741)
              ·
                refine ⟨13074931804216030789385153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34866484811242748771693741 13074931804216030789385153)
                ·
                  refine ⟨9806198853162023092038865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13074931804216030789385153 9806198853162023092038865)
                  ·
                    refine ⟨7354649139871517319029149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9806198853162023092038865 7354649139871517319029149)
                    ·
                      refine ⟨2757993427451818994635931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7354649139871517319029149 2757993427451818994635931)
                      ·
                        rfl

theorem cell23_5371173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_5371173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371173 prefixEnd_5371173 := by exact prefixLift 5371173
  have htrace : WordTrace (prefixWord ++ tailWord_5371173) baseStart_5371173 baseEnd_5371173 := by
    simpa [prefixWord, tailWord_5371173, baseEnd_5371173] using wordTrace_append hprefix tailTrace_5371173
  have hstable : (prefixWord ++ tailWord_5371173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371173).length < 2 ^ (prefixWord ++ tailWord_5371173).sum := by decide
  have hdescent : baseEnd_5371173 < baseStart_5371173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371179 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 6]
def baseStart_5371179 : Nat := 118140960795 + 5371179 * 2 ^ 59
def prefixEnd_5371179 : Nat := 4983230072969 + 3 ^ 40 * 5371179 * 2
def baseEnd_5371179 : Nat := 2757996508335745971160903

theorem tailTrace_5371179 : CollatzResearch.WordTrace tailWord_5371179 prefixEnd_5371179 2757996508335745971160903 := by
  unfold tailWord_5371179
  simp only [CollatzResearch.WordTrace]
  refine ⟨195902992208143282186388591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130601994805428854790925727 195902992208143282186388591)
  ·
    refine ⟨293854488312214923279582887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195902992208143282186388591 293854488312214923279582887)
    ·
      refine ⟨440781732468322384919374331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293854488312214923279582887 440781732468322384919374331)
      ·
        refine ⟨661172598702483577379061497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440781732468322384919374331 661172598702483577379061497)
        ·
          refine ⟨495879449026862683034296123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661172598702483577379061497 495879449026862683034296123)
          ·
            refine ⟨743819173540294024551444185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495879449026862683034296123 743819173540294024551444185)
            ·
              refine ⟨557864380155220518413583139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743819173540294024551444185 557864380155220518413583139)
              ·
                refine ⟨836796570232830777620374709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557864380155220518413583139 836796570232830777620374709)
                ·
                  refine ⟨78449678459327885401910129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 836796570232830777620374709 78449678459327885401910129)
                  ·
                    refine ⟨58837258844495914051432597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78449678459327885401910129 58837258844495914051432597)
                    ·
                      refine ⟨2757996508335745971160903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58837258844495914051432597 2757996508335745971160903)
                      ·
                        rfl

theorem cell23_5371179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 6].length) (baseStart_5371179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371179 prefixEnd_5371179 := by exact prefixLift 5371179
  have htrace : WordTrace (prefixWord ++ tailWord_5371179) baseStart_5371179 baseEnd_5371179 := by
    simpa [prefixWord, tailWord_5371179, baseEnd_5371179] using wordTrace_append hprefix tailTrace_5371179
  have hstable : (prefixWord ++ tailWord_5371179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371179).length < 2 ^ (prefixWord ++ tailWord_5371179).sum := by decide
  have hdescent : baseEnd_5371179 < baseStart_5371179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371203 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 3, 1, 3]
def baseStart_5371203 : Nat := 118140960795 + 5371203 * 2 ^ 59
def prefixEnd_5371203 : Nat := 4983230072969 + 3 ^ 40 * 5371203 * 2
def baseEnd_5371203 : Nat := 2758008831871453877260793

theorem tailTrace_5371203 : CollatzResearch.WordTrace tailWord_5371203 prefixEnd_5371203 2758008831871453877260793 := by
  unfold tailWord_5371203
  simp only [CollatzResearch.WordTrace]
  refine ⟨195903867560056334285262263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130602578373370889523508175 195903867560056334285262263)
  ·
    refine ⟨293855801340084501427893395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195903867560056334285262263 293855801340084501427893395)
    ·
      refine ⟨440783702010126752141840093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293855801340084501427893395 440783702010126752141840093)
      ·
        refine ⟨165293888253797532053190035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 440783702010126752141840093 165293888253797532053190035)
        ·
          refine ⟨247940832380696298079785053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165293888253797532053190035 247940832380696298079785053)
          ·
            refine ⟨92977812142761111779919395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247940832380696298079785053 92977812142761111779919395)
            ·
              refine ⟨139466718214141667669879093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92977812142761111779919395 139466718214141667669879093)
              ·
                refine ⟨13075004832575781344051165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139466718214141667669879093 13075004832575781344051165)
                ·
                  refine ⟨4903126812215918004019187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13075004832575781344051165 4903126812215918004019187)
                  ·
                    refine ⟨7354690218323877006028781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4903126812215918004019187 7354690218323877006028781)
                    ·
                      refine ⟨2758008831871453877260793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7354690218323877006028781 2758008831871453877260793)
                      ·
                        rfl

theorem cell23_5371203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_5371203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371203 prefixEnd_5371203 := by exact prefixLift 5371203
  have htrace : WordTrace (prefixWord ++ tailWord_5371203) baseStart_5371203 baseEnd_5371203 := by
    simpa [prefixWord, tailWord_5371203, baseEnd_5371203] using wordTrace_append hprefix tailTrace_5371203
  have hstable : (prefixWord ++ tailWord_5371203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371203).length < 2 ^ (prefixWord ++ tailWord_5371203).sum := by decide
  have hdescent : baseEnd_5371203 < baseStart_5371203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371220 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_5371220 : Nat := 118140960795 + 5371220 * 2 ^ 59
def prefixEnd_5371220 : Nat := 4983230072969 + 3 ^ 40 * 5371220 * 2
def baseEnd_5371220 : Nat := 2758017561042580310748215

theorem tailTrace_5371220 : CollatzResearch.WordTrace tailWord_5371220 prefixEnd_5371220 2758017561042580310748215 := by
  unfold tailWord_5371220
  simp only [CollatzResearch.WordTrace]
  refine ⟨97952243800497373094315557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130602991733996497459087409 97952243800497373094315557)
  ·
    refine ⟨18366045712593257455184167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97952243800497373094315557 18366045712593257455184167)
    ·
      refine ⟨27549068568889886182776251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18366045712593257455184167 27549068568889886182776251)
      ·
        refine ⟨41323602853334829274164377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27549068568889886182776251 41323602853334829274164377)
        ·
          refine ⟨30992702140001121955623283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41323602853334829274164377 30992702140001121955623283)
          ·
            refine ⟨46489053210001682933434925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30992702140001121955623283 46489053210001682933434925)
            ·
              refine ⟨17433394953750631100038097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46489053210001682933434925 17433394953750631100038097)
              ·
                refine ⟨13075046215312973325028573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17433394953750631100038097 13075046215312973325028573)
                ·
                  refine ⟨4903142330742364996885715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13075046215312973325028573 4903142330742364996885715)
                  ·
                    refine ⟨7354713496113547495328573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4903142330742364996885715 7354713496113547495328573)
                    ·
                      refine ⟨2758017561042580310748215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7354713496113547495328573 2758017561042580310748215)
                      ·
                        rfl

theorem cell23_5371220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_5371220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371220 prefixEnd_5371220 := by exact prefixLift 5371220
  have htrace : WordTrace (prefixWord ++ tailWord_5371220) baseStart_5371220 baseEnd_5371220 := by
    simpa [prefixWord, tailWord_5371220, baseEnd_5371220] using wordTrace_append hprefix tailTrace_5371220
  have hstable : (prefixWord ++ tailWord_5371220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371220).length < 2 ^ (prefixWord ++ tailWord_5371220).sum := by decide
  have hdescent : baseEnd_5371220 < baseStart_5371220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371237 : List Nat := [1, 3, 1, 3, 1, 2, 4, 3, 1, 1, 3]
def baseStart_5371237 : Nat := 118140960795 + 5371237 * 2 ^ 59
def prefixEnd_5371237 : Nat := 4983230072969 + 3 ^ 40 * 5371237 * 2
def baseEnd_5371237 : Nat := 2758026290213706744235637

theorem tailTrace_5371237 : CollatzResearch.WordTrace tailWord_5371237 prefixEnd_5371237 2758026290213706744235637 := by
  unfold tailWord_5371237
  simp only [CollatzResearch.WordTrace]
  refine ⟨195905107641933158091999965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130603405094622105394666643 195905107641933158091999965)
  ·
    refine ⟨73464415365724934284499987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195905107641933158091999965 73464415365724934284499987)
    ·
      refine ⟨110196623048587401426749981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73464415365724934284499987 110196623048587401426749981)
      ·
        refine ⟨41323733643220275535031243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110196623048587401426749981 41323733643220275535031243)
        ·
          refine ⟨61985600464830413302546865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41323733643220275535031243 61985600464830413302546865)
          ·
            refine ⟨46489200348622809976910149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61985600464830413302546865 46489200348622809976910149)
            ·
              refine ⟨8716725065366776870670653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46489200348622809976910149 8716725065366776870670653)
              ·
                refine ⟨3268771899512541326501495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8716725065366776870670653 3268771899512541326501495)
                ·
                  refine ⟨4903157849268811989752243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3268771899512541326501495 4903157849268811989752243)
                  ·
                    refine ⟨7354736773903217984628365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4903157849268811989752243 7354736773903217984628365)
                    ·
                      refine ⟨2758026290213706744235637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7354736773903217984628365 2758026290213706744235637)
                      ·
                        rfl

theorem cell23_5371237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_5371237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371237 prefixEnd_5371237 := by exact prefixLift 5371237
  have htrace : WordTrace (prefixWord ++ tailWord_5371237) baseStart_5371237 baseEnd_5371237 := by
    simpa [prefixWord, tailWord_5371237, baseEnd_5371237] using wordTrace_append hprefix tailTrace_5371237
  have hstable : (prefixWord ++ tailWord_5371237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371237).length < 2 ^ (prefixWord ++ tailWord_5371237).sum := by decide
  have hdescent : baseEnd_5371237 < baseStart_5371237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371240 : List Nat := [2, 1, 4, 2, 3, 1, 1, 3, 1, 5]
def baseStart_5371240 : Nat := 118140960795 + 5371240 * 2 ^ 59
def prefixEnd_5371240 : Nat := 4983230072969 + 3 ^ 40 * 5371240 * 2
def baseEnd_5371240 : Nat := 919342610218556744166041

theorem tailTrace_5371240 : CollatzResearch.WordTrace tailWord_5371240 prefixEnd_5371240 919342610218556744166041 := by
  unfold tailWord_5371240
  simp only [CollatzResearch.WordTrace]
  refine ⟨97952608530461144802179587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130603478040614859736239449 97952608530461144802179587)
  ·
    refine ⟨146928912795691717203269381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97952608530461144802179587 146928912795691717203269381)
    ·
      refine ⟨27549171149192196975613009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146928912795691717203269381 27549171149192196975613009)
      ·
        refine ⟨20661878361894147731709757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27549171149192196975613009 20661878361894147731709757)
        ·
          refine ⟨7748204385710305399391159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20661878361894147731709757 7748204385710305399391159)
          ·
            refine ⟨11622306578565458099086739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7748204385710305399391159 11622306578565458099086739)
            ·
              refine ⟨17433459867848187148630109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11622306578565458099086739 17433459867848187148630109)
              ·
                refine ⟨6537547450443070180736291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17433459867848187148630109 6537547450443070180736291)
                ·
                  refine ⟨9806321175664605271104437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6537547450443070180736291 9806321175664605271104437)
                  ·
                    refine ⟨919342610218556744166041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9806321175664605271104437 919342610218556744166041)
                    ·
                      rfl

theorem cell23_5371240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_5371240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371240 prefixEnd_5371240 := by exact prefixLift 5371240
  have htrace : WordTrace (prefixWord ++ tailWord_5371240) baseStart_5371240 baseEnd_5371240 := by
    simpa [prefixWord, tailWord_5371240, baseEnd_5371240] using wordTrace_append hprefix tailTrace_5371240
  have hstable : (prefixWord ++ tailWord_5371240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371240).length < 2 ^ (prefixWord ++ tailWord_5371240).sum := by decide
  have hdescent : baseEnd_5371240 < baseStart_5371240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371273 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 6]
def baseStart_5371273 : Nat := 118140960795 + 5371273 * 2 ^ 59
def prefixEnd_5371273 : Nat := 4983230072969 + 3 ^ 40 * 5371273 * 2
def baseEnd_5371273 : Nat := 2758044775517268603385471

theorem tailTrace_5371273 : CollatzResearch.WordTrace tailWord_5371273 prefixEnd_5371273 2758044775517268603385471 := by
  unfold tailWord_5371273
  simp only [CollatzResearch.WordTrace]
  refine ⟨195906420669802736240310473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130604280446535157493540315 195906420669802736240310473)
  ·
    refine ⟨146929815502352052180232855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195906420669802736240310473 146929815502352052180232855)
    ·
      refine ⟨220394723253528078270349283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146929815502352052180232855 220394723253528078270349283)
      ·
        refine ⟨330592084880292117405523925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220394723253528078270349283 330592084880292117405523925)
        ·
          refine ⟨7748251989381846501691967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 330592084880292117405523925 7748251989381846501691967)
          ·
            refine ⟨11622377984072769752537951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7748251989381846501691967 11622377984072769752537951)
            ·
              refine ⟨17433566976109154628806927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11622377984072769752537951 17433566976109154628806927)
              ·
                refine ⟨26150350464163731943210391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17433566976109154628806927 26150350464163731943210391)
                ·
                  refine ⟨39225525696245597914815587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26150350464163731943210391 39225525696245597914815587)
                  ·
                    refine ⟨58838288544368396872223381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39225525696245597914815587 58838288544368396872223381)
                    ·
                      refine ⟨2758044775517268603385471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58838288544368396872223381 2758044775517268603385471)
                      ·
                        rfl

theorem cell23_5371273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 1, 6].length) (baseStart_5371273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371273 prefixEnd_5371273 := by exact prefixLift 5371273
  have htrace : WordTrace (prefixWord ++ tailWord_5371273) baseStart_5371273 baseEnd_5371273 := by
    simpa [prefixWord, tailWord_5371273, baseEnd_5371273] using wordTrace_append hprefix tailTrace_5371273
  have hstable : (prefixWord ++ tailWord_5371273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371273).length < 2 ^ (prefixWord ++ tailWord_5371273).sum := by decide
  have hdescent : baseEnd_5371273 < baseStart_5371273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371353 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 2, 1, 5]
def baseStart_5371353 : Nat := 118140960795 + 5371353 * 2 ^ 59
def prefixEnd_5371353 : Nat := 4983230072969 + 3 ^ 40 * 5371353 * 2
def baseEnd_5371353 : Nat := 2758085853969628290385103

theorem tailTrace_5371353 : CollatzResearch.WordTrace tailWord_5371353 prefixEnd_5371353 2758085853969628290385103 := by
  unfold tailWord_5371353
  simp only [CollatzResearch.WordTrace]
  refine ⟨195909338509512909903222713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130606225673008606602148475 195909338509512909903222713)
  ·
    refine ⟨146932003882134682427417035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195909338509512909903222713 146932003882134682427417035)
    ·
      refine ⟨220398005823202023641125553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146932003882134682427417035 220398005823202023641125553)
      ·
        refine ⟨165298504367401517730844165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220398005823202023641125553 165298504367401517730844165)
        ·
          refine ⟨30993469568887784574533281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165298504367401517730844165 30993469568887784574533281)
          ·
            refine ⟨23245102176665838430899961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30993469568887784574533281 23245102176665838430899961)
            ·
              refine ⟨17433826632499378823174971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23245102176665838430899961 17433826632499378823174971)
              ·
                refine ⟨26150739948749068234762457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17433826632499378823174971 26150739948749068234762457)
                ·
                  refine ⟨19613054961561801176071843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26150739948749068234762457 19613054961561801176071843)
                  ·
                    refine ⟨29419582442342701764107765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19613054961561801176071843 29419582442342701764107765)
                    ·
                      refine ⟨2758085853969628290385103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29419582442342701764107765 2758085853969628290385103)
                      ·
                        rfl

theorem cell23_5371353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_5371353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371353 prefixEnd_5371353 := by exact prefixLift 5371353
  have htrace : WordTrace (prefixWord ++ tailWord_5371353) baseStart_5371353 baseEnd_5371353 := by
    simpa [prefixWord, tailWord_5371353, baseEnd_5371353] using wordTrace_append hprefix tailTrace_5371353
  have hstable : (prefixWord ++ tailWord_5371353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371353).length < 2 ^ (prefixWord ++ tailWord_5371353).sum := by decide
  have hdescent : baseEnd_5371353 < baseStart_5371353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371354 : List Nat := [3, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2]
def baseStart_5371354 : Nat := 118140960795 + 5371354 * 2 ^ 59
def prefixEnd_5371354 : Nat := 4983230072969 + 3 ^ 40 * 5371354 * 2
def baseEnd_5371354 : Nat := 2758086367450282786472599

theorem tailTrace_5371354 : CollatzResearch.WordTrace tailWord_5371354 prefixEnd_5371354 2758086367450282786472599 := by
  unfold tailWord_5371354
  simp only [CollatzResearch.WordTrace]
  refine ⟨48977343745627321768502279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130606249988339524716006077 48977343745627321768502279)
  ·
    refine ⟨73466015618440982652753419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48977343745627321768502279 73466015618440982652753419)
    ·
      refine ⟨110199023427661473979130129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73466015618440982652753419 110199023427661473979130129)
      ·
        refine ⟨82649267570746105484347597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110199023427661473979130129 82649267570746105484347597)
        ·
          refine ⟨30993475339029789556630349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82649267570746105484347597 30993475339029789556630349)
          ·
            refine ⟨11622553252136171083736381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30993475339029789556630349 11622553252136171083736381)
            ·
              refine ⟨4358457469551064156401143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11622553252136171083736381 4358457469551064156401143)
              ·
                refine ⟨6537686204326596234601715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4358457469551064156401143 6537686204326596234601715)
                ·
                  refine ⟨9806529306489894351902573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6537686204326596234601715 9806529306489894351902573)
                  ·
                    refine ⟨3677448489933710381963465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9806529306489894351902573 3677448489933710381963465)
                    ·
                      refine ⟨2758086367450282786472599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3677448489933710381963465 2758086367450282786472599)
                      ·
                        rfl

theorem cell23_5371354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_5371354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371354 prefixEnd_5371354 := by exact prefixLift 5371354
  have htrace : WordTrace (prefixWord ++ tailWord_5371354) baseStart_5371354 baseEnd_5371354 := by
    simpa [prefixWord, tailWord_5371354, baseEnd_5371354] using wordTrace_append hprefix tailTrace_5371354
  have hstable : (prefixWord ++ tailWord_5371354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371354).length < 2 ^ (prefixWord ++ tailWord_5371354).sum := by decide
  have hdescent : baseEnd_5371354 < baseStart_5371354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371405 : List Nat := [1, 7, 1, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_5371405 : Nat := 118140960795 + 5371405 * 2 ^ 59
def prefixEnd_5371405 : Nat := 4983230072969 + 3 ^ 40 * 5371405 * 2
def baseEnd_5371405 : Nat := 2758112554963662086934865

theorem tailTrace_5371405 : CollatzResearch.WordTrace tailWord_5371405 prefixEnd_5371405 2758112554963662086934865 := by
  unfold tailWord_5371405
  simp only [CollatzResearch.WordTrace]
  refine ⟨195911235105324522784115669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130607490070216348522743779 195911235105324522784115669)
  ·
    refine ⟨4591669572781043502752711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 195911235105324522784115669 4591669572781043502752711)
    ·
      refine ⟨6887504359171565254129067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4591669572781043502752711 6887504359171565254129067)
      ·
        refine ⟨10331256538757347881193601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6887504359171565254129067 10331256538757347881193601)
        ·
          refine ⟨7748442404068010910895201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10331256538757347881193601 7748442404068010910895201)
          ·
            refine ⟨5811331803051008183171401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7748442404068010910895201 5811331803051008183171401)
            ·
              refine ⟨4358498852288256137378551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5811331803051008183171401 4358498852288256137378551)
              ·
                refine ⟨6537748278432384206067827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4358498852288256137378551 6537748278432384206067827)
                ·
                  refine ⟨9806622417648576309101741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6537748278432384206067827 9806622417648576309101741)
                  ·
                    refine ⟨3677483406618216115913153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9806622417648576309101741 3677483406618216115913153)
                    ·
                      refine ⟨2758112554963662086934865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3677483406618216115913153 2758112554963662086934865)
                      ·
                        rfl

theorem cell23_5371405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_5371405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371405 prefixEnd_5371405 := by exact prefixLift 5371405
  have htrace : WordTrace (prefixWord ++ tailWord_5371405) baseStart_5371405 baseEnd_5371405 := by
    simpa [prefixWord, tailWord_5371405, baseEnd_5371405] using wordTrace_append hprefix tailTrace_5371405
  have hstable : (prefixWord ++ tailWord_5371405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371405).length < 2 ^ (prefixWord ++ tailWord_5371405).sum := by decide
  have hdescent : baseEnd_5371405 < baseStart_5371405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371450 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 3, 4]
def baseStart_5371450 : Nat := 118140960795 + 5371450 * 2 ^ 59
def prefixEnd_5371450 : Nat := 4983230072969 + 3 ^ 40 * 5371450 * 2
def baseEnd_5371450 : Nat := 919378553864371470290719

theorem tailTrace_5371450 : CollatzResearch.WordTrace tailWord_5371450 prefixEnd_5371450 919378553864371470290719 := by
  unfold tailWord_5371450
  simp only [CollatzResearch.WordTrace]
  refine ⟨48978219097540373867375951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130608584260107663646335869 48978219097540373867375951)
  ·
    refine ⟨73467328646310560801063927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48978219097540373867375951 73467328646310560801063927)
    ·
      refine ⟨110200992969465841201595891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73467328646310560801063927 110200992969465841201595891)
      ·
        refine ⟨165301489454198761802393837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110200992969465841201595891 165301489454198761802393837)
        ·
          refine ⟨61988058545324535675897689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165301489454198761802393837 61988058545324535675897689)
          ·
            refine ⟨46491043908993401756923267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61988058545324535675897689 46491043908993401756923267)
            ·
              refine ⟨69736565863490102635384901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46491043908993401756923267 69736565863490102635384901)
              ·
                refine ⟨13075606099404394244134669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69736565863490102635384901 13075606099404394244134669)
                ·
                  refine ⟨4903352287276647841550501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13075606099404394244134669 4903352287276647841550501)
                  ·
                    refine ⟨919378553864371470290719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4903352287276647841550501 919378553864371470290719)
                    ·
                      rfl

theorem cell23_5371450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_5371450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371450 prefixEnd_5371450 := by exact prefixLift 5371450
  have htrace : WordTrace (prefixWord ++ tailWord_5371450) baseStart_5371450 baseEnd_5371450 := by
    simpa [prefixWord, tailWord_5371450, baseEnd_5371450] using wordTrace_append hprefix tailTrace_5371450
  have hstable : (prefixWord ++ tailWord_5371450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371450).length < 2 ^ (prefixWord ++ tailWord_5371450).sum := by decide
  have hdescent : baseEnd_5371450 < baseStart_5371450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371484 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 3, 4]
def baseStart_5371484 : Nat := 118140960795 + 5371484 * 2 ^ 59
def prefixEnd_5371484 : Nat := 4983230072969 + 3 ^ 40 * 5371484 * 2
def baseEnd_5371484 : Nat := 919384373311789092615667

theorem tailTrace_5371484 : CollatzResearch.WordTrace tailWord_5371484 prefixEnd_5371484 919384373311789092615667 := by
  unfold tailWord_5371484
  simp only [CollatzResearch.WordTrace]
  refine ⟨97957058236019159638120753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130609410981358879517494337 97957058236019159638120753)
  ·
    refine ⟨73467793677014369728590565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97957058236019159638120753 73467793677014369728590565)
    ·
      refine ⟨13775211314440194324110731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73467793677014369728590565 13775211314440194324110731)
      ·
        refine ⟨20662816971660291486166097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13775211314440194324110731 20662816971660291486166097)
        ·
          refine ⟨15497112728745218614624573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20662816971660291486166097 15497112728745218614624573)
          ·
            refine ⟨5811417273279456980484215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15497112728745218614624573 5811417273279456980484215)
            ·
              refine ⟨8717125909919185470726323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5811417273279456980484215 8717125909919185470726323)
              ·
                refine ⟨13075688864878778206089485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8717125909919185470726323 13075688864878778206089485)
                ·
                  refine ⟨4903383324329541827283557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13075688864878778206089485 4903383324329541827283557)
                  ·
                    refine ⟨919384373311789092615667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4903383324329541827283557 919384373311789092615667)
                    ·
                      rfl

theorem cell23_5371484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_5371484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371484 prefixEnd_5371484 := by exact prefixLift 5371484
  have htrace : WordTrace (prefixWord ++ tailWord_5371484) baseStart_5371484 baseEnd_5371484 := by
    simpa [prefixWord, tailWord_5371484, baseEnd_5371484] using wordTrace_append hprefix tailTrace_5371484
  have hstable : (prefixWord ++ tailWord_5371484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371484).length < 2 ^ (prefixWord ++ tailWord_5371484).sum := by decide
  have hdescent : baseEnd_5371484 < baseStart_5371484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371534 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2]
def baseStart_5371534 : Nat := 118140960795 + 5371534 * 2 ^ 59
def prefixEnd_5371534 : Nat := 4983230072969 + 3 ^ 40 * 5371534 * 2
def baseEnd_5371534 : Nat := 2758178793968092082221771

theorem tailTrace_5371534 : CollatzResearch.WordTrace tailWord_5371534 prefixEnd_5371534 2758178793968092082221771 := by
  unfold tailWord_5371534
  simp only [CollatzResearch.WordTrace]
  refine ⟨24489492515232147226945207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130610626747904785210374437 24489492515232147226945207)
  ·
    refine ⟨36734238772848220840417811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24489492515232147226945207 36734238772848220840417811)
    ·
      refine ⟨55101358159272331260626717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36734238772848220840417811 55101358159272331260626717)
      ·
        refine ⟨20663009309727124222735019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55101358159272331260626717 20663009309727124222735019)
        ·
          refine ⟨30994513964590686334102529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20663009309727124222735019 30994513964590686334102529)
          ·
            refine ⟨23245885473443014750576897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30994513964590686334102529 23245885473443014750576897)
            ·
              refine ⟨17434414105082261062932673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23245885473443014750576897 17434414105082261062932673)
              ·
                refine ⟨13075810578811695797199505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17434414105082261062932673 13075810578811695797199505)
                ·
                  refine ⟨9806857934108771847899629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13075810578811695797199505 9806857934108771847899629)
                  ·
                    refine ⟨3677571725290789442962361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9806857934108771847899629 3677571725290789442962361)
                    ·
                      refine ⟨2758178793968092082221771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3677571725290789442962361 2758178793968092082221771)
                      ·
                        rfl

theorem cell23_5371534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_5371534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371534 prefixEnd_5371534 := by exact prefixLift 5371534
  have htrace : WordTrace (prefixWord ++ tailWord_5371534) baseStart_5371534 baseEnd_5371534 := by
    simpa [prefixWord, tailWord_5371534, baseEnd_5371534] using wordTrace_append hprefix tailTrace_5371534
  have hstable : (prefixWord ++ tailWord_5371534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371534).length < 2 ^ (prefixWord ++ tailWord_5371534).sum := by decide
  have hdescent : baseEnd_5371534 < baseStart_5371534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371557 : List Nat := [1, 3, 1, 2, 1, 2, 4, 3, 2, 4]
def baseStart_5371557 : Nat := 118140960795 + 5371557 * 2 ^ 59
def prefixEnd_5371557 : Nat := 4983230072969 + 3 ^ 40 * 5371557 * 2
def baseEnd_5371557 : Nat := 919396868007715164078055

theorem tailTrace_5371557 : CollatzResearch.WordTrace tailWord_5371557 prefixEnd_5371557 919396868007715164078055 := by
  unfold tailWord_5371557
  simp only [CollatzResearch.WordTrace]
  refine ⟨195916779000773852743648925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130611186000515901829099283 195916779000773852743648925)
  ·
    refine ⟨73468792125290194778868347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195916779000773852743648925 73468792125290194778868347)
    ·
      refine ⟨110203188187935292168302521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73468792125290194778868347 110203188187935292168302521)
      ·
        refine ⟨82652391140951469126226891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110203188187935292168302521 82652391140951469126226891)
        ·
          refine ⟨123978586711427203689340337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82652391140951469126226891 123978586711427203689340337)
          ·
            refine ⟨92983940033570402767005253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123978586711427203689340337 92983940033570402767005253)
            ·
              refine ⟨17434488756294450518813485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92983940033570402767005253 17434488756294450518813485)
              ·
                refine ⟨6537933283610418944555057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17434488756294450518813485 6537933283610418944555057)
                ·
                  refine ⟨4903449962707814208416293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6537933283610418944555057 4903449962707814208416293)
                  ·
                    refine ⟨919396868007715164078055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4903449962707814208416293 919396868007715164078055)
                    ·
                      rfl

theorem cell23_5371557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_5371557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371557 prefixEnd_5371557 := by exact prefixLift 5371557
  have htrace : WordTrace (prefixWord ++ tailWord_5371557) baseStart_5371557 baseEnd_5371557 := by
    simpa [prefixWord, tailWord_5371557, baseEnd_5371557] using wordTrace_append hprefix tailTrace_5371557
  have hstable : (prefixWord ++ tailWord_5371557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371557).length < 2 ^ (prefixWord ++ tailWord_5371557).sum := by decide
  have hdescent : baseEnd_5371557 < baseStart_5371557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371567 : List Nat := [1, 1, 2, 1, 2, 4, 2, 4, 1, 2, 3]
def baseStart_5371567 : Nat := 118140960795 + 5371567 * 2 ^ 59
def prefixEnd_5371567 : Nat := 4983230072969 + 3 ^ 40 * 5371567 * 2
def baseEnd_5371567 : Nat := 2758195738829690453109119

theorem tailTrace_5371567 : CollatzResearch.WordTrace tailWord_5371567 prefixEnd_5371567 2758195738829690453109119 := by
  unfold tailWord_5371567
  simp only [CollatzResearch.WordTrace]
  refine ⟨195917143730737624451512955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130611429153825082967675303 195917143730737624451512955)
  ·
    refine ⟨293875715596106436677269433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195917143730737624451512955 293875715596106436677269433)
    ·
      refine ⟨220406786697079827507952075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293875715596106436677269433 220406786697079827507952075)
      ·
        refine ⟨330610180045619741261928113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220406786697079827507952075 330610180045619741261928113)
        ·
          refine ⟨247957635034214805946446085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330610180045619741261928113 247957635034214805946446085)
          ·
            refine ⟨46492056568915276114958641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247957635034214805946446085 46492056568915276114958641)
            ·
              refine ⟨34869042426686457086218981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46492056568915276114958641 34869042426686457086218981)
              ·
                refine ⟨6537945455003710703666059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34869042426686457086218981 6537945455003710703666059)
                ·
                  refine ⟨9806918182505566055499089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6537945455003710703666059 9806918182505566055499089)
                  ·
                    refine ⟨7355188636879174541624317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9806918182505566055499089 7355188636879174541624317)
                    ·
                      refine ⟨2758195738829690453109119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7355188636879174541624317 2758195738829690453109119)
                      ·
                        rfl

theorem cell23_5371567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 2, 3].length) (baseStart_5371567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371567 prefixEnd_5371567 := by exact prefixLift 5371567
  have htrace : WordTrace (prefixWord ++ tailWord_5371567) baseStart_5371567 baseEnd_5371567 := by
    simpa [prefixWord, tailWord_5371567, baseEnd_5371567] using wordTrace_append hprefix tailTrace_5371567
  have hstable : (prefixWord ++ tailWord_5371567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371567).length < 2 ^ (prefixWord ++ tailWord_5371567).sum := by decide
  have hdescent : baseEnd_5371567 < baseStart_5371567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371574 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_5371574 : Nat := 118140960795 + 5371574 * 2 ^ 59
def prefixEnd_5371574 : Nat := 4983230072969 + 3 ^ 40 * 5371574 * 2
def baseEnd_5371574 : Nat := 919399777731423975240529

theorem tailTrace_5371574 : CollatzResearch.WordTrace tailWord_5371574 prefixEnd_5371574 919399777731423975240529 := by
  unfold tailWord_5371574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12244837440107016540438611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130611599361141509764678517 12244837440107016540438611)
  ·
    refine ⟨18367256160160524810657917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12244837440107016540438611 18367256160160524810657917)
    ·
      refine ⟨6887721060060196803996719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18367256160160524810657917 6887721060060196803996719)
      ·
        refine ⟨10331581590090295205995079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6887721060060196803996719 10331581590090295205995079)
        ·
          refine ⟨15497372385135442808992619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10331581590090295205995079 15497372385135442808992619)
          ·
            refine ⟨23246058577703164213488929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15497372385135442808992619 23246058577703164213488929)
            ·
              refine ⟨17434543933277373160116697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23246058577703164213488929 17434543933277373160116697)
              ·
                refine ⟨13075907949958029870087523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17434543933277373160116697 13075907949958029870087523)
                ·
                  refine ⟨19613861924937044805131285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13075907949958029870087523 19613861924937044805131285)
                  ·
                    refine ⟨919399777731423975240529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19613861924937044805131285 919399777731423975240529)
                    ·
                      rfl

theorem cell23_5371574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_5371574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371574 prefixEnd_5371574 := by exact prefixLift 5371574
  have htrace : WordTrace (prefixWord ++ tailWord_5371574) baseStart_5371574 baseEnd_5371574 := by
    simpa [prefixWord, tailWord_5371574, baseEnd_5371574] using wordTrace_append hprefix tailTrace_5371574
  have hstable : (prefixWord ++ tailWord_5371574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371574).length < 2 ^ (prefixWord ++ tailWord_5371574).sum := by decide
  have hdescent : baseEnd_5371574 < baseStart_5371574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371705 : List Nat := [1, 2, 1, 7, 1, 1, 2, 2, 2, 2, 2]
def baseStart_5371705 : Nat := 118140960795 + 5371705 * 2 ^ 59
def prefixEnd_5371705 : Nat := 4983230072969 + 3 ^ 40 * 5371705 * 2
def baseEnd_5371705 : Nat := 2758266599160010913183485

theorem tailTrace_5371705 : CollatzResearch.WordTrace tailWord_5371705 prefixEnd_5371705 2758266599160010913183485 := by
  unfold tailWord_5371705
  simp only [CollatzResearch.WordTrace]
  refine ⟨195922177004237674020036569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130614784669491782680024379 195922177004237674020036569)
  ·
    refine ⟨146941632753178255515027427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195922177004237674020036569 146941632753178255515027427)
    ·
      refine ⟨220412449129767383272541141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146941632753178255515027427 220412449129767383272541141)
      ·
        refine ⟨5165916776478923045450183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 220412449129767383272541141 5165916776478923045450183)
        ·
          refine ⟨7748875164718384568175275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5165916776478923045450183 7748875164718384568175275)
          ·
            refine ⟨11623312747077576852262913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7748875164718384568175275 11623312747077576852262913)
            ·
              refine ⟨8717484560308182639197185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11623312747077576852262913 8717484560308182639197185)
              ·
                refine ⟨6538113420231136979397889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8717484560308182639197185 6538113420231136979397889)
                ·
                  refine ⟨4903585065173352734548417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6538113420231136979397889 4903585065173352734548417)
                  ·
                    refine ⟨3677688798880014550911313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4903585065173352734548417 3677688798880014550911313)
                    ·
                      refine ⟨2758266599160010913183485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3677688798880014550911313 2758266599160010913183485)
                      ·
                        rfl

theorem cell23_5371705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_5371705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371705 prefixEnd_5371705 := by exact prefixLift 5371705
  have htrace : WordTrace (prefixWord ++ tailWord_5371705) baseStart_5371705 baseEnd_5371705 := by
    simpa [prefixWord, tailWord_5371705, baseEnd_5371705] using wordTrace_append hprefix tailTrace_5371705
  have hstable : (prefixWord ++ tailWord_5371705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371705).length < 2 ^ (prefixWord ++ tailWord_5371705).sum := by decide
  have hdescent : baseEnd_5371705 < baseStart_5371705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371744 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 4]
def baseStart_5371744 : Nat := 118140960795 + 5371744 * 2 ^ 59
def prefixEnd_5371744 : Nat := 4983230072969 + 3 ^ 40 * 5371744 * 2
def baseEnd_5371744 : Nat := 2758286624905536260595805

theorem tailTrace_5371744 : CollatzResearch.WordTrace tailWord_5371744 prefixEnd_5371744 2758286624905536260595805 := by
  unfold tailWord_5371744
  simp only [CollatzResearch.WordTrace]
  refine ⟨97961799725548191840353143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130615732967397589120470857 97961799725548191840353143)
  ·
    refine ⟨146942699588322287760529715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97961799725548191840353143 146942699588322287760529715)
    ·
      refine ⟨220414049382483431640794573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146942699588322287760529715 220414049382483431640794573)
      ·
        refine ⟨82655268518431286865297965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220414049382483431640794573 82655268518431286865297965)
        ·
          refine ⟨30995725694411732574486737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82655268518431286865297965 30995725694411732574486737)
          ·
            refine ⟨23246794270808799430865053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30995725694411732574486737 23246794270808799430865053)
            ·
              refine ⟨8717547851553299786574395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23246794270808799430865053 8717547851553299786574395)
              ·
                refine ⟨13076321777329949679861593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8717547851553299786574395 13076321777329949679861593)
                ·
                  refine ⟨9807241332997462259896195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13076321777329949679861593 9807241332997462259896195)
                  ·
                    refine ⟨14710861999496193389844293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9807241332997462259896195 14710861999496193389844293)
                    ·
                      refine ⟨2758286624905536260595805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14710861999496193389844293 2758286624905536260595805)
                      ·
                        rfl

theorem cell23_5371744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_5371744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371744 prefixEnd_5371744 := by exact prefixLift 5371744
  have htrace : WordTrace (prefixWord ++ tailWord_5371744) baseStart_5371744 baseEnd_5371744 := by
    simpa [prefixWord, tailWord_5371744, baseEnd_5371744] using wordTrace_append hprefix tailTrace_5371744
  have hstable : (prefixWord ++ tailWord_5371744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371744).length < 2 ^ (prefixWord ++ tailWord_5371744).sum := by decide
  have hdescent : baseEnd_5371744 < baseStart_5371744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371757 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_5371757 : Nat := 118140960795 + 5371757 * 2 ^ 59
def prefixEnd_5371757 : Nat := 4983230072969 + 3 ^ 40 * 5371757 * 2
def baseEnd_5371757 : Nat := 2758293300154044709733245

theorem tailTrace_5371757 : CollatzResearch.WordTrace tailWord_5371757 prefixEnd_5371757 2758293300154044709733245 := by
  unfold tailWord_5371757
  simp only [CollatzResearch.WordTrace]
  refine ⟨195924073600049286900929525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130616049066699524600619683 195924073600049286900929525)
  ·
    refine ⟨18367881900004620646962143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195924073600049286900929525 18367881900004620646962143)
    ·
      refine ⟨27551822850006930970443215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18367881900004620646962143 27551822850006930970443215)
      ·
        refine ⟨41327734275010396455664823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27551822850006930970443215 41327734275010396455664823)
        ·
          refine ⟨61991601412515594683497235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41327734275010396455664823 61991601412515594683497235)
          ·
            refine ⟨92987402118773392025245853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61991601412515594683497235 92987402118773392025245853)
            ·
              refine ⟨34870275794540022009467195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92987402118773392025245853 34870275794540022009467195)
              ·
                refine ⟨52305413691810033014200793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34870275794540022009467195 52305413691810033014200793)
                ·
                  refine ⟨39229060268857524760650595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52305413691810033014200793 39229060268857524760650595)
                  ·
                    refine ⟨58843590403286287140975893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39229060268857524760650595 58843590403286287140975893)
                    ·
                      refine ⟨2758293300154044709733245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58843590403286287140975893 2758293300154044709733245)
                      ·
                        rfl

theorem cell23_5371757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_5371757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371757 prefixEnd_5371757 := by exact prefixLift 5371757
  have htrace : WordTrace (prefixWord ++ tailWord_5371757) baseStart_5371757 baseEnd_5371757 := by
    simpa [prefixWord, tailWord_5371757, baseEnd_5371757] using wordTrace_append hprefix tailTrace_5371757
  have hstable : (prefixWord ++ tailWord_5371757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371757).length < 2 ^ (prefixWord ++ tailWord_5371757).sum := by decide
  have hdescent : baseEnd_5371757 < baseStart_5371757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371822 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 3, 4]
def baseStart_5371822 : Nat := 118140960795 + 5371822 * 2 ^ 59
def prefixEnd_5371822 : Nat := 4983230072969 + 3 ^ 40 * 5371822 * 2
def baseEnd_5371822 : Nat := 919442225465528985140149

theorem tailTrace_5371822 : CollatzResearch.WordTrace tailWord_5371822 prefixEnd_5371822 919442225465528985140149 := by
  unfold tailWord_5371822
  simp only [CollatzResearch.WordTrace]
  refine ⟨24490805543101725375255715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130617629563209202001363813 24490805543101725375255715)
  ·
    refine ⟨36736208314652588062883573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24490805543101725375255715 36736208314652588062883573)
    ·
      refine ⟨3444019529498680130895335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36736208314652588062883573 3444019529498680130895335)
      ·
        refine ⟨5166029294248020196343003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3444019529498680130895335 5166029294248020196343003)
        ·
          refine ⟨7749043941372030294514505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5166029294248020196343003 7749043941372030294514505)
          ·
            refine ⟨5811782956029022720885879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7749043941372030294514505 5811782956029022720885879)
            ·
              refine ⟨8717674434043534081328819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5811782956029022720885879 8717674434043534081328819)
              ·
                refine ⟨13076511651065301121993229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8717674434043534081328819 13076511651065301121993229)
                ·
                  refine ⟨4903691869149487920747461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13076511651065301121993229 4903691869149487920747461)
                  ·
                    refine ⟨919442225465528985140149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4903691869149487920747461 919442225465528985140149)
                    ·
                      rfl

theorem cell23_5371822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_5371822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371822 prefixEnd_5371822 := by exact prefixLift 5371822
  have htrace : WordTrace (prefixWord ++ tailWord_5371822) baseStart_5371822 baseEnd_5371822 := by
    simpa [prefixWord, tailWord_5371822, baseEnd_5371822] using wordTrace_append hprefix tailTrace_5371822
  have hstable : (prefixWord ++ tailWord_5371822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371822).length < 2 ^ (prefixWord ++ tailWord_5371822).sum := by decide
  have hdescent : baseEnd_5371822 < baseStart_5371822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371834 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2]
def baseStart_5371834 : Nat := 118140960795 + 5371834 * 2 ^ 59
def prefixEnd_5371834 : Nat := 4983230072969 + 3 ^ 40 * 5371834 * 2
def baseEnd_5371834 : Nat := 2758332838164440908470391

theorem tailTrace_5371834 : CollatzResearch.WordTrace tailWord_5371834 prefixEnd_5371834 2758332838164440908470391 := by
  unfold tailWord_5371834
  simp only [CollatzResearch.WordTrace]
  refine ⟨48981720505192582262870639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130617921347180219367655037 48981720505192582262870639)
  ·
    refine ⟨73472580757788873394305959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48981720505192582262870639 73472580757788873394305959)
    ·
      refine ⟨110208871136683310091458939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73472580757788873394305959 110208871136683310091458939)
      ·
        refine ⟨165313306705024965137188409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110208871136683310091458939 165313306705024965137188409)
        ·
          refine ⟨123984980028768723852891307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165313306705024965137188409 123984980028768723852891307)
          ·
            refine ⟨185977470043153085779336961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123984980028768723852891307 185977470043153085779336961)
            ·
              refine ⟨139483102532364814334502721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185977470043153085779336961 139483102532364814334502721)
              ·
                refine ⟨104612326899273610750877041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139483102532364814334502721 104612326899273610750877041)
                ·
                  refine ⟨78459245174455208063157781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104612326899273610750877041 78459245174455208063157781)
                  ·
                    refine ⟨3677777117552587877960521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78459245174455208063157781 3677777117552587877960521)
                    ·
                      refine ⟨2758332838164440908470391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3677777117552587877960521 2758332838164440908470391)
                      ·
                        rfl

theorem cell23_5371834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2].length) (baseStart_5371834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371834 prefixEnd_5371834 := by exact prefixLift 5371834
  have htrace : WordTrace (prefixWord ++ tailWord_5371834) baseStart_5371834 baseEnd_5371834 := by
    simpa [prefixWord, tailWord_5371834, baseEnd_5371834] using wordTrace_append hprefix tailTrace_5371834
  have hstable : (prefixWord ++ tailWord_5371834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371834).length < 2 ^ (prefixWord ++ tailWord_5371834).sum := by decide
  have hdescent : baseEnd_5371834 < baseStart_5371834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371851 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 5, 2, 2]
def baseStart_5371851 : Nat := 118140960795 + 5371851 * 2 ^ 59
def prefixEnd_5371851 : Nat := 4983230072969 + 3 ^ 40 * 5371851 * 2
def baseEnd_5371851 : Nat := 2758341567335567341957813

theorem tailTrace_5371851 : CollatzResearch.WordTrace tailWord_5371851 prefixEnd_5371851 2758341567335567341957813 := by
  unfold tailWord_5371851
  simp only [CollatzResearch.WordTrace]
  refine ⟨195927502061708740954851407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130618334707805827303234271 195927502061708740954851407)
  ·
    refine ⟨293891253092563111432277111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195927502061708740954851407 293891253092563111432277111)
    ·
      refine ⟨440836879638844667148415667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293891253092563111432277111 440836879638844667148415667)
      ·
        refine ⟨661255319458267000722623501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440836879638844667148415667 661255319458267000722623501)
        ·
          refine ⟨247970744796850125270983813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 661255319458267000722623501 247970744796850125270983813)
          ·
            refine ⟨46494514649409398488309465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247970744796850125270983813 46494514649409398488309465)
            ·
              refine ⟨34870885987057048866232099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46494514649409398488309465 34870885987057048866232099)
              ·
                refine ⟨52306328980585573299348149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34870885987057048866232099 52306328980585573299348149)
                ·
                  refine ⟨4903718341929897496813889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52306328980585573299348149 4903718341929897496813889)
                  ·
                    refine ⟨3677788756447423122610417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4903718341929897496813889 3677788756447423122610417)
                    ·
                      refine ⟨2758341567335567341957813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3677788756447423122610417 2758341567335567341957813)
                      ·
                        rfl

theorem cell23_5371851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 2, 2].length) (baseStart_5371851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371851 prefixEnd_5371851 := by exact prefixLift 5371851
  have htrace : WordTrace (prefixWord ++ tailWord_5371851) baseStart_5371851 baseEnd_5371851 := by
    simpa [prefixWord, tailWord_5371851, baseEnd_5371851] using wordTrace_append hprefix tailTrace_5371851
  have hstable : (prefixWord ++ tailWord_5371851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371851).length < 2 ^ (prefixWord ++ tailWord_5371851).sum := by decide
  have hdescent : baseEnd_5371851 < baseStart_5371851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371864 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 1, 2, 4]
def baseStart_5371864 : Nat := 118140960795 + 5371864 * 2 ^ 59
def prefixEnd_5371864 : Nat := 4983230072969 + 3 ^ 40 * 5371864 * 2
def baseEnd_5371864 : Nat := 2758348242584075791095253

theorem tailTrace_5371864 : CollatzResearch.WordTrace tailWord_5371864 prefixEnd_5371864 2758348242584075791095253 := by
  unfold tailWord_5371864
  simp only [CollatzResearch.WordTrace]
  refine ⟨97963988105330822087537323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130618650807107762783383097 97963988105330822087537323)
  ·
    refine ⟨146945982157996233131305985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97963988105330822087537323 146945982157996233131305985)
    ·
      refine ⟨110209486618497174848479489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146945982157996233131305985 110209486618497174848479489)
      ·
        refine ⟨82657114963872881136359617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110209486618497174848479489 82657114963872881136359617)
        ·
          refine ⟨61992836222904660852269713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82657114963872881136359617 61992836222904660852269713)
          ·
            refine ⟨46494627167178495639202285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61992836222904660852269713 46494627167178495639202285)
            ·
              refine ⟨17435485187691935864700857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46494627167178495639202285 17435485187691935864700857)
              ·
                refine ⟨13076613890768951898525643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17435485187691935864700857 13076613890768951898525643)
                ·
                  refine ⟨19614920836153427847788465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13076613890768951898525643 19614920836153427847788465)
                  ·
                    refine ⟨14711190627115070885841349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19614920836153427847788465 14711190627115070885841349)
                    ·
                      refine ⟨2758348242584075791095253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14711190627115070885841349 2758348242584075791095253)
                      ·
                        rfl

theorem cell23_5371864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_5371864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371864 prefixEnd_5371864 := by exact prefixLift 5371864
  have htrace : WordTrace (prefixWord ++ tailWord_5371864) baseStart_5371864 baseEnd_5371864 := by
    simpa [prefixWord, tailWord_5371864, baseEnd_5371864] using wordTrace_append hprefix tailTrace_5371864
  have hstable : (prefixWord ++ tailWord_5371864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371864).length < 2 ^ (prefixWord ++ tailWord_5371864).sum := by decide
  have hdescent : baseEnd_5371864 < baseStart_5371864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371871 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 1, 1, 5]
def baseStart_5371871 : Nat := 118140960795 + 5371871 * 2 ^ 59
def prefixEnd_5371871 : Nat := 4983230072969 + 3 ^ 40 * 5371871 * 2
def baseEnd_5371871 : Nat := 2758351836948657263707721

theorem tailTrace_5371871 : CollatzResearch.WordTrace tailWord_5371871 prefixEnd_5371871 2758351836948657263707721 := by
  unfold tailWord_5371871
  simp only [CollatzResearch.WordTrace]
  refine ⟨195928231521636284370579467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130618821014424189580386311 195928231521636284370579467)
  ·
    refine ⟨293892347282454426555869201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195928231521636284370579467 293892347282454426555869201)
    ·
      refine ⟨220419260461840819916901901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293892347282454426555869201 220419260461840819916901901)
      ·
        refine ⟨82657222673190307468838213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220419260461840819916901901 82657222673190307468838213)
        ·
          refine ⟨15498229251223182650407165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82657222673190307468838213 15498229251223182650407165)
          ·
            refine ⟨5811835969208693493902687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15498229251223182650407165 5811835969208693493902687)
            ·
              refine ⟨8717753953813040240854031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5811835969208693493902687 8717753953813040240854031)
              ·
                refine ⟨13076630930719560361281047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8717753953813040240854031 13076630930719560361281047)
                ·
                  refine ⟨19614946396079340541921571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13076630930719560361281047 19614946396079340541921571)
                  ·
                    refine ⟨29422419594119010812882357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19614946396079340541921571 29422419594119010812882357)
                    ·
                      refine ⟨2758351836948657263707721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29422419594119010812882357 2758351836948657263707721)
                      ·
                        rfl

theorem cell23_5371871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_5371871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371871 prefixEnd_5371871 := by exact prefixLift 5371871
  have htrace : WordTrace (prefixWord ++ tailWord_5371871) baseStart_5371871 baseEnd_5371871 := by
    simpa [prefixWord, tailWord_5371871, baseEnd_5371871] using wordTrace_append hprefix tailTrace_5371871
  have hstable : (prefixWord ++ tailWord_5371871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371871).length < 2 ^ (prefixWord ++ tailWord_5371871).sum := by decide
  have hdescent : baseEnd_5371871 < baseStart_5371871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371874 : List Nat := [3, 3, 3, 1, 13]
def baseStart_5371874 : Nat := 118140960795 + 5371874 * 2 ^ 59
def prefixEnd_5371874 : Nat := 4983230072969 + 3 ^ 40 * 5371874 * 2
def baseEnd_5371874 : Nat := 3783749488876022979383

theorem tailTrace_5371874 : CollatzResearch.WordTrace tailWord_5371874 prefixEnd_5371874 3783749488876022979383 := by
  unfold tailWord_5371874
  simp only [CollatzResearch.WordTrace]
  refine ⟨48982085235156353970734669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130618893960416943921959117 48982085235156353970734669)
  ·
    refine ⟨18368281963183632739025501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48982085235156353970734669 18368281963183632739025501)
    ·
      refine ⟨6888105736193862277134563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18368281963183632739025501 6888105736193862277134563)
      ·
        refine ⟨10332158604290793415701845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6888105736193862277134563 10332158604290793415701845)
        ·
          refine ⟨3783749488876022979383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 10332158604290793415701845 3783749488876022979383)
          ·
            rfl

theorem cell23_5371874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 13].length) (baseStart_5371874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371874 prefixEnd_5371874 := by exact prefixLift 5371874
  have htrace : WordTrace (prefixWord ++ tailWord_5371874) baseStart_5371874 baseEnd_5371874 := by
    simpa [prefixWord, tailWord_5371874, baseEnd_5371874] using wordTrace_append hprefix tailTrace_5371874
  have hstable : (prefixWord ++ tailWord_5371874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371874).length < 2 ^ (prefixWord ++ tailWord_5371874).sum := by decide
  have hdescent : baseEnd_5371874 < baseStart_5371874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371879 : List Nat := [1, 1, 5, 2, 4, 1, 2, 2, 1, 1, 3]
def baseStart_5371879 : Nat := 118140960795 + 5371879 * 2 ^ 59
def prefixEnd_5371879 : Nat := 4983230072969 + 3 ^ 40 * 5371879 * 2
def baseEnd_5371879 : Nat := 2758355944793893232407685

theorem tailTrace_5371879 : CollatzResearch.WordTrace tailWord_5371879 prefixEnd_5371879 2758355944793893232407685 := by
  unfold tailWord_5371879
  simp only [CollatzResearch.WordTrace]
  refine ⟨195928523305607301736870691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130619015537071534491247127 195928523305607301736870691)
  ·
    refine ⟨293892784958410952605306037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195928523305607301736870691 293892784958410952605306037)
    ·
      refine ⟨27552448589851026806747441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 293892784958410952605306037 27552448589851026806747441)
      ·
        refine ⟨20664336442388270105060581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27552448589851026806747441 20664336442388270105060581)
        ·
          refine ⟨3874563082947800644698859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20664336442388270105060581 3874563082947800644698859)
          ·
            refine ⟨5811844624421700967048289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874563082947800644698859 5811844624421700967048289)
            ·
              refine ⟨4358883468316275725286217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5811844624421700967048289 4358883468316275725286217)
              ·
                refine ⟨3269162601237206793964663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4358883468316275725286217 3269162601237206793964663)
                ·
                  refine ⟨4903743901855810190946995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3269162601237206793964663 4903743901855810190946995)
                  ·
                    refine ⟨7355615852783715286420493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4903743901855810190946995 7355615852783715286420493)
                    ·
                      refine ⟨2758355944793893232407685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7355615852783715286420493 2758355944793893232407685)
                      ·
                        rfl

theorem cell23_5371879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_5371879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371879 prefixEnd_5371879 := by exact prefixLift 5371879
  have htrace : WordTrace (prefixWord ++ tailWord_5371879) baseStart_5371879 baseEnd_5371879 := by
    simpa [prefixWord, tailWord_5371879, baseEnd_5371879] using wordTrace_append hprefix tailTrace_5371879
  have hstable : (prefixWord ++ tailWord_5371879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371879).length < 2 ^ (prefixWord ++ tailWord_5371879).sum := by decide
  have hdescent : baseEnd_5371879 < baseStart_5371879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371887 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 1, 9]
def baseStart_5371887 : Nat := 118140960795 + 5371887 * 2 ^ 59
def prefixEnd_5371887 : Nat := 4983230072969 + 3 ^ 40 * 5371887 * 2
def baseEnd_5371887 : Nat := 919453350879709733702549

theorem tailTrace_5371887 : CollatzResearch.WordTrace tailWord_5371887 prefixEnd_5371887 919453350879709733702549 := by
  unfold tailWord_5371887
  simp only [CollatzResearch.WordTrace]
  refine ⟨195928815089578319103161915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130619210059718879402107943 195928815089578319103161915)
  ·
    refine ⟨293893222634367478654742873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195928815089578319103161915 293893222634367478654742873)
    ·
      refine ⟨220419916975775608991057155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293893222634367478654742873 220419916975775608991057155)
      ·
        refine ⟨330629875463663413486585733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220419916975775608991057155 330629875463663413486585733)
        ·
          refine ⟨61993101649436890028734825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 330629875463663413486585733 61993101649436890028734825)
          ·
            refine ⟨46494826237077667521551119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61993101649436890028734825 46494826237077667521551119)
            ·
              refine ⟨69742239355616501282326679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46494826237077667521551119 69742239355616501282326679)
              ·
                refine ⟨104613359033424751923490019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69742239355616501282326679 104613359033424751923490019)
                ·
                  refine ⟨156920038550137127885235029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104613359033424751923490019 156920038550137127885235029)
                  ·
                    refine ⟨919453350879709733702549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 156920038550137127885235029 919453350879709733702549)
                    ·
                      rfl

theorem cell23_5371887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_5371887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371887 prefixEnd_5371887 := by exact prefixLift 5371887
  have htrace : WordTrace (prefixWord ++ tailWord_5371887) baseStart_5371887 baseEnd_5371887 := by
    simpa [prefixWord, tailWord_5371887, baseEnd_5371887] using wordTrace_append hprefix tailTrace_5371887
  have hstable : (prefixWord ++ tailWord_5371887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371887).length < 2 ^ (prefixWord ++ tailWord_5371887).sum := by decide
  have hdescent : baseEnd_5371887 < baseStart_5371887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371908 : List Nat := [2, 3, 2, 4, 1, 1, 3, 7]
def baseStart_5371908 : Nat := 118140960795 + 5371908 * 2 ^ 59
def prefixEnd_5371908 : Nat := 4983230072969 + 3 ^ 40 * 5371908 * 2
def baseEnd_5371908 : Nat := 102161882804921245146113

theorem tailTrace_5371908 : CollatzResearch.WordTrace tailWord_5371908 prefixEnd_5371908 102161882804921245146113 := by
  unfold tailWord_5371908
  simp only [CollatzResearch.WordTrace]
  refine ⟨97964790511251119844838189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130619720681668159793117585 97964790511251119844838189)
  ·
    refine ⟨36736796441719169941814321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97964790511251119844838189 36736796441719169941814321)
    ·
      refine ⟨27552597331289377456360741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36736796441719169941814321 27552597331289377456360741)
      ·
        refine ⟨5166111999616758273067639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27552597331289377456360741 5166111999616758273067639)
        ·
          refine ⟨7749167999425137409601459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5166111999616758273067639 7749167999425137409601459)
          ·
            refine ⟨11623751999137706114402189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7749167999425137409601459 11623751999137706114402189)
            ·
              refine ⟨4358906999676639792900821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11623751999137706114402189 4358906999676639792900821)
              ·
                refine ⟨102161882804921245146113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4358906999676639792900821 102161882804921245146113)
                ·
                  rfl

theorem cell23_5371908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 7].length) (baseStart_5371908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371908 prefixEnd_5371908 := by exact prefixLift 5371908
  have htrace : WordTrace (prefixWord ++ tailWord_5371908) baseStart_5371908 baseEnd_5371908 := by
    simpa [prefixWord, tailWord_5371908, baseEnd_5371908] using wordTrace_append hprefix tailTrace_5371908
  have hstable : (prefixWord ++ tailWord_5371908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371908).length < 2 ^ (prefixWord ++ tailWord_5371908).sum := by decide
  have hdescent : baseEnd_5371908 < baseStart_5371908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371928 : List Nat := [2, 1, 2, 3, 2, 1, 3, 3, 1, 3, 2]
def baseStart_5371928 : Nat := 118140960795 + 5371928 * 2 ^ 59
def prefixEnd_5371928 : Nat := 4983230072969 + 3 ^ 40 * 5371928 * 2
def baseEnd_5371928 : Nat := 2758381105345963540694959

theorem tailTrace_5371928 : CollatzResearch.WordTrace tailWord_5371928 prefixEnd_5371928 2758381105345963540694959 := by
  unfold tailWord_5371928
  simp only [CollatzResearch.WordTrace]
  refine ⟨97965155241214891552702219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130620206988286522070269625 97965155241214891552702219)
  ·
    refine ⟨146947732861822337329053329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97965155241214891552702219 146947732861822337329053329)
    ·
      refine ⟨110210799646366752996789997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146947732861822337329053329 110210799646366752996789997)
      ·
        refine ⟨41329049867387532373796249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110210799646366752996789997 41329049867387532373796249)
        ·
          refine ⟨30996787400540649280347187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41329049867387532373796249 30996787400540649280347187)
          ·
            refine ⟨46495181100810973920520781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30996787400540649280347187 46495181100810973920520781)
            ·
              refine ⟨17435692912804115220195293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46495181100810973920520781 17435692912804115220195293)
              ·
                refine ⟨6538384842301543207573235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17435692912804115220195293 6538384842301543207573235)
                ·
                  refine ⟨9807577263452314811359853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6538384842301543207573235 9807577263452314811359853)
                  ·
                    refine ⟨3677841473794618054259945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9807577263452314811359853 3677841473794618054259945)
                    ·
                      refine ⟨2758381105345963540694959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3677841473794618054259945 2758381105345963540694959)
                      ·
                        rfl

theorem cell23_5371928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_5371928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371928 prefixEnd_5371928 := by exact prefixLift 5371928
  have htrace : WordTrace (prefixWord ++ tailWord_5371928) baseStart_5371928 baseEnd_5371928 := by
    simpa [prefixWord, tailWord_5371928, baseEnd_5371928] using wordTrace_append hprefix tailTrace_5371928
  have hstable : (prefixWord ++ tailWord_5371928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371928).length < 2 ^ (prefixWord ++ tailWord_5371928).sum := by decide
  have hdescent : baseEnd_5371928 < baseStart_5371928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5371964 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 7]
def baseStart_5371964 : Nat := 118140960795 + 5371964 * 2 ^ 59
def prefixEnd_5371964 : Nat := 4983230072969 + 3 ^ 40 * 5371964 * 2
def baseEnd_5371964 : Nat := 306488843405502822204977

theorem tailTrace_5371964 : CollatzResearch.WordTrace tailWord_5371964 prefixEnd_5371964 306488843405502822204977 := by
  unfold tailWord_5371964
  simp only [CollatzResearch.WordTrace]
  refine ⟨97965811755149680626857473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130621082340199574169143297 97965811755149680626857473)
  ·
    refine ⟨73474358816362260470143105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97965811755149680626857473 73474358816362260470143105)
    ·
      refine ⟨55105769112271695352607329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73474358816362260470143105 55105769112271695352607329)
      ·
        refine ⟨41329326834203771514455497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55105769112271695352607329 41329326834203771514455497)
        ·
          refine ⟨30996995125652828635841623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41329326834203771514455497 30996995125652828635841623)
          ·
            refine ⟨46495492688479242953762435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30996995125652828635841623 46495492688479242953762435)
            ·
              refine ⟨69743239032718864430643653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46495492688479242953762435 69743239032718864430643653)
              ·
                refine ⟨13076857318634787080745685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69743239032718864430643653 13076857318634787080745685)
                ·
                  refine ⟨306488843405502822204977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13076857318634787080745685 306488843405502822204977)
                  ·
                    rfl

theorem cell23_5371964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_5371964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5371964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5371964 prefixEnd_5371964 := by exact prefixLift 5371964
  have htrace : WordTrace (prefixWord ++ tailWord_5371964) baseStart_5371964 baseEnd_5371964 := by
    simpa [prefixWord, tailWord_5371964, baseEnd_5371964] using wordTrace_append hprefix tailTrace_5371964
  have hstable : (prefixWord ++ tailWord_5371964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5371964).length < 2 ^ (prefixWord ++ tailWord_5371964).sum := by decide
  have hdescent : baseEnd_5371964 < baseStart_5371964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5371964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372001 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 2, 5, 2]
def baseStart_5372001 : Nat := 118140960795 + 5372001 * 2 ^ 59
def prefixEnd_5372001 : Nat := 4983230072969 + 3 ^ 40 * 5372001 * 2
def baseEnd_5372001 : Nat := 2758418589433741755082123

theorem tailTrace_5372001 : CollatzResearch.WordTrace tailWord_5372001 prefixEnd_5372001 2758418589433741755082123 := by
  unfold tailWord_5372001
  simp only [CollatzResearch.WordTrace]
  refine ⟨195932973011165316572811857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130621982007443544381874571 195932973011165316572811857)
  ·
    refine ⟨146949729758373987429608893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195932973011165316572811857 146949729758373987429608893)
    ·
      refine ⟨55106148659390245286103335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146949729758373987429608893 55106148659390245286103335)
      ·
        refine ⟨82659222989085367929155003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55106148659390245286103335 82659222989085367929155003)
        ·
          refine ⟨123988834483628051893732505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82659222989085367929155003 123988834483628051893732505)
          ·
            refine ⟨92991625862721038920299379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123988834483628051893732505 92991625862721038920299379)
            ·
              refine ⟨139487438794081558380449069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92991625862721038920299379 139487438794081558380449069)
              ·
                refine ⟨52307789547780584392668401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139487438794081558380449069 52307789547780584392668401)
                ·
                  refine ⟨39230842160835438294501301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52307789547780584392668401 39230842160835438294501301)
                  ·
                    refine ⟨3677891452578322340109497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39230842160835438294501301 3677891452578322340109497)
                    ·
                      refine ⟨2758418589433741755082123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3677891452578322340109497 2758418589433741755082123)
                      ·
                        rfl

theorem cell23_5372001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_5372001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372001 prefixEnd_5372001 := by exact prefixLift 5372001
  have htrace : WordTrace (prefixWord ++ tailWord_5372001) baseStart_5372001 baseEnd_5372001 := by
    simpa [prefixWord, tailWord_5372001, baseEnd_5372001] using wordTrace_append hprefix tailTrace_5372001
  have hstable : (prefixWord ++ tailWord_5372001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372001).length < 2 ^ (prefixWord ++ tailWord_5372001).sum := by decide
  have hdescent : baseEnd_5372001 < baseStart_5372001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372004 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_5372004 : Nat := 118140960795 + 5372004 * 2 ^ 59
def prefixEnd_5372004 : Nat := 4983230072969 + 3 ^ 40 * 5372004 * 2
def baseEnd_5372004 : Nat := 2758420129875705243344609

theorem tailTrace_5372004 : CollatzResearch.WordTrace tailWord_5372004 prefixEnd_5372004 2758420129875705243344609 := by
  unfold tailWord_5372004
  simp only [CollatzResearch.WordTrace]
  refine ⟨97966541215077224042585533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130622054953436298723447377 97966541215077224042585533)
  ·
    refine ⟨36737452955653959015969575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97966541215077224042585533 36737452955653959015969575)
    ·
      refine ⟨55106179433480938523954363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36737452955653959015969575 55106179433480938523954363)
      ·
        refine ⟨82659269150221407785931545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55106179433480938523954363 82659269150221407785931545)
        ·
          refine ⟨61994451862666055839448659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82659269150221407785931545 61994451862666055839448659)
          ·
            refine ⟨92991677793999083759172989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61994451862666055839448659 92991677793999083759172989)
            ·
              refine ⟨34871879172749656409689871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92991677793999083759172989 34871879172749656409689871)
              ·
                refine ⟨52307818759124484614534807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34871879172749656409689871 52307818759124484614534807)
                ·
                  refine ⟨78461728138686726921802211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52307818759124484614534807 78461728138686726921802211)
                  ·
                    refine ⟨117692592208030090382703317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78461728138686726921802211 117692592208030090382703317)
                    ·
                      refine ⟨2758420129875705243344609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117692592208030090382703317 2758420129875705243344609)
                      ·
                        rfl

theorem cell23_5372004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_5372004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372004 prefixEnd_5372004 := by exact prefixLift 5372004
  have htrace : WordTrace (prefixWord ++ tailWord_5372004) baseStart_5372004 baseEnd_5372004 := by
    simpa [prefixWord, tailWord_5372004, baseEnd_5372004] using wordTrace_append hprefix tailTrace_5372004
  have hstable : (prefixWord ++ tailWord_5372004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372004).length < 2 ^ (prefixWord ++ tailWord_5372004).sum := by decide
  have hdescent : baseEnd_5372004 < baseStart_5372004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372085 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_5372085 : Nat := 118140960795 + 5372085 * 2 ^ 59
def prefixEnd_5372085 : Nat := 4983230072969 + 3 ^ 40 * 5372085 * 2
def baseEnd_5372085 : Nat := 2758461721808719426431737

theorem tailTrace_5372085 : CollatzResearch.WordTrace tailWord_5372085 prefixEnd_5372085 2758461721808719426431737 := by
  unfold tailWord_5372085
  simp only [CollatzResearch.WordTrace]
  refine ⟨195936036742860998918869709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130624024495240665945913139 195936036742860998918869709)
  ·
    refine ⟨73476013778572874594576141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195936036742860998918869709 73476013778572874594576141)
    ·
      refine ⟨27553505166964827972966053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73476013778572874594576141 27553505166964827972966053)
      ·
        refine ⟨5166282218805905244931135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27553505166964827972966053 5166282218805905244931135)
        ·
          refine ⟨7749423328208857867396703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5166282218805905244931135 7749423328208857867396703)
          ·
            refine ⟨11624134992313286801095055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7749423328208857867396703 11624134992313286801095055)
            ·
              refine ⟨17436202488469930201642583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11624134992313286801095055 17436202488469930201642583)
              ·
                refine ⟨26154303732704895302463875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17436202488469930201642583 26154303732704895302463875)
                ·
                  refine ⟨39231455599057342953695813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26154303732704895302463875 39231455599057342953695813)
                  ·
                    refine ⟨7355897924823251803817965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39231455599057342953695813 7355897924823251803817965)
                    ·
                      refine ⟨2758461721808719426431737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7355897924823251803817965 2758461721808719426431737)
                      ·
                        rfl

theorem cell23_5372085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_5372085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372085 prefixEnd_5372085 := by exact prefixLift 5372085
  have htrace : WordTrace (prefixWord ++ tailWord_5372085) baseStart_5372085 baseEnd_5372085 := by
    simpa [prefixWord, tailWord_5372085, baseEnd_5372085] using wordTrace_append hprefix tailTrace_5372085
  have hstable : (prefixWord ++ tailWord_5372085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372085).length < 2 ^ (prefixWord ++ tailWord_5372085).sum := by decide
  have hdescent : baseEnd_5372085 < baseStart_5372085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372092 : List Nat := [2, 2, 2, 3, 3, 1, 2, 3, 1, 4]
def baseStart_5372092 : Nat := 118140960795 + 5372092 * 2 ^ 59
def prefixEnd_5372092 : Nat := 4983230072969 + 3 ^ 40 * 5372092 * 2
def baseEnd_5372092 : Nat := 919488438724433633014735

theorem tailTrace_5372092 : CollatzResearch.WordTrace tailWord_5372092 prefixEnd_5372092 919488438724433633014735 := by
  unfold tailWord_5372092
  simp only [CollatzResearch.WordTrace]
  refine ⟨97968146026917819557187265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130624194702557092742916353 97968146026917819557187265)
  ·
    refine ⟨73476109520188364667890449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97968146026917819557187265 73476109520188364667890449)
    ·
      refine ⟨55107082140141273500917837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73476109520188364667890449 55107082140141273500917837)
      ·
        refine ⟨20665155802552977562844189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55107082140141273500917837 20665155802552977562844189)
        ·
          refine ⟨7749433425957366586066571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20665155802552977562844189 7749433425957366586066571)
          ·
            refine ⟨11624150138936049879099857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7749433425957366586066571 11624150138936049879099857)
            ·
              refine ⟨8718112604202037409324893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11624150138936049879099857 8718112604202037409324893)
              ·
                refine ⟨3269292226575764028496835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8718112604202037409324893 3269292226575764028496835)
                ·
                  refine ⟨4903938339863646042745253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3269292226575764028496835 4903938339863646042745253)
                  ·
                    refine ⟨919488438724433633014735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4903938339863646042745253 919488438724433633014735)
                    ·
                      rfl

theorem cell23_5372092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_5372092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372092 prefixEnd_5372092 := by exact prefixLift 5372092
  have htrace : WordTrace (prefixWord ++ tailWord_5372092) baseStart_5372092 baseEnd_5372092 := by
    simpa [prefixWord, tailWord_5372092, baseEnd_5372092] using wordTrace_append hprefix tailTrace_5372092
  have hstable : (prefixWord ++ tailWord_5372092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372092).length < 2 ^ (prefixWord ++ tailWord_5372092).sum := by decide
  have hdescent : baseEnd_5372092 < baseStart_5372092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372121 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 5, 1, 4]
def baseStart_5372121 : Nat := 118140960795 + 5372121 * 2 ^ 59
def prefixEnd_5372121 : Nat := 4983230072969 + 3 ^ 40 * 5372121 * 2
def baseEnd_5372121 : Nat := 2758480207112281285581571

theorem tailTrace_5372121 : CollatzResearch.WordTrace tailWord_5372121 prefixEnd_5372121 2758480207112281285581571 := by
  unfold tailWord_5372121
  simp only [CollatzResearch.WordTrace]
  refine ⟨195937349770730577067180217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130624899847153718044786811 195937349770730577067180217)
  ·
    refine ⟨146953012328047932800385163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195937349770730577067180217 146953012328047932800385163)
    ·
      refine ⟨220429518492071899200577745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146953012328047932800385163 220429518492071899200577745)
      ·
        refine ⟨165322138869053924400433309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220429518492071899200577745 165322138869053924400433309)
        ·
          refine ⟨61995802075895221650162491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165322138869053924400433309 61995802075895221650162491)
          ·
            refine ⟨92993703113842832475243737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61995802075895221650162491 92993703113842832475243737)
            ·
              refine ⟨69745277335382124356432803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92993703113842832475243737 69745277335382124356432803)
              ·
                refine ⟨104617916003073186534649205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69745277335382124356432803 104617916003073186534649205)
                ·
                  refine ⟨9807929625288111237623363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104617916003073186534649205 9807929625288111237623363)
                  ·
                    refine ⟨14711894437932166856435045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9807929625288111237623363 14711894437932166856435045)
                    ·
                      refine ⟨2758480207112281285581571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14711894437932166856435045 2758480207112281285581571)
                      ·
                        rfl

theorem cell23_5372121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_5372121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372121 prefixEnd_5372121 := by exact prefixLift 5372121
  have htrace : WordTrace (prefixWord ++ tailWord_5372121) baseStart_5372121 baseEnd_5372121 := by
    simpa [prefixWord, tailWord_5372121, baseEnd_5372121] using wordTrace_append hprefix tailTrace_5372121
  have hstable : (prefixWord ++ tailWord_5372121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372121).length < 2 ^ (prefixWord ++ tailWord_5372121).sum := by decide
  have hdescent : baseEnd_5372121 < baseStart_5372121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372125 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_5372125 : Nat := 118140960795 + 5372125 * 2 ^ 59
def prefixEnd_5372125 : Nat := 4983230072969 + 3 ^ 40 * 5372125 * 2
def baseEnd_5372125 : Nat := 2758482261034899269931553

theorem tailTrace_5372125 : CollatzResearch.WordTrace tailWord_5372125 prefixEnd_5372125 2758482261034899269931553 := by
  unfold tailWord_5372125
  simp only [CollatzResearch.WordTrace]
  refine ⟨195937495662716085750325829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130624997108477390500217219 195937495662716085750325829)
  ·
    refine ⟨36738280436759266078186093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195937495662716085750325829 36738280436759266078186093)
    ·
      refine ⟨13776855163784724779319785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36738280436759266078186093 13776855163784724779319785)
      ·
        refine ⟨10332641372838543584489839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13776855163784724779319785 10332641372838543584489839)
        ·
          refine ⟨15498962059257815376734759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10332641372838543584489839 15498962059257815376734759)
          ·
            refine ⟨23248443088886723065102139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15498962059257815376734759 23248443088886723065102139)
            ·
              refine ⟨34872664633330084597653209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23248443088886723065102139 34872664633330084597653209)
              ·
                refine ⟨26154498474997563448239907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34872664633330084597653209 26154498474997563448239907)
                ·
                  refine ⟨39231747712496345172359861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26154498474997563448239907 39231747712496345172359861)
                  ·
                    refine ⟨3677976348046532359908737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39231747712496345172359861 3677976348046532359908737)
                    ·
                      refine ⟨2758482261034899269931553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3677976348046532359908737 2758482261034899269931553)
                      ·
                        rfl

theorem cell23_5372125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_5372125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372125 prefixEnd_5372125 := by exact prefixLift 5372125
  have htrace : WordTrace (prefixWord ++ tailWord_5372125) baseStart_5372125 baseEnd_5372125 := by
    simpa [prefixWord, tailWord_5372125, baseEnd_5372125] using wordTrace_append hprefix tailTrace_5372125
  have hstable : (prefixWord ++ tailWord_5372125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372125).length < 2 ^ (prefixWord ++ tailWord_5372125).sum := by decide
  have hdescent : baseEnd_5372125 < baseStart_5372125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372135 : List Nat := [1, 1, 5, 3, 1, 2, 2, 2, 1, 5]
def baseStart_5372135 : Nat := 118140960795 + 5372135 * 2 ^ 59
def prefixEnd_5372135 : Nat := 4983230072969 + 3 ^ 40 * 5372135 * 2
def baseEnd_5372135 : Nat := 919495798613814743602169

theorem tailTrace_5372135 : CollatzResearch.WordTrace tailWord_5372135 prefixEnd_5372135 919495798613814743602169 := by
  unfold tailWord_5372135
  simp only [CollatzResearch.WordTrace]
  refine ⟨195937860392679857458189859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130625240261786571638793239 195937860392679857458189859)
  ·
    refine ⟨293906790589019786187284789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195937860392679857458189859 293906790589019786187284789)
    ·
      refine ⟨27553761617720604955057949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 293906790589019786187284789 27553761617720604955057949)
      ·
        refine ⟨10332660606645226858146731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27553761617720604955057949 10332660606645226858146731)
        ·
          refine ⟨15498990909967840287220097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10332660606645226858146731 15498990909967840287220097)
          ·
            refine ⟨11624243182475880215415073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15498990909967840287220097 11624243182475880215415073)
            ·
              refine ⟨8718182386856910161561305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11624243182475880215415073 8718182386856910161561305)
              ·
                refine ⟨6538636790142682621170979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8718182386856910161561305 6538636790142682621170979)
                ·
                  refine ⟨9807955185214023931756469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6538636790142682621170979 9807955185214023931756469)
                  ·
                    refine ⟨919495798613814743602169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9807955185214023931756469 919495798613814743602169)
                    ·
                      rfl

theorem cell23_5372135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_5372135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372135 prefixEnd_5372135 := by exact prefixLift 5372135
  have htrace : WordTrace (prefixWord ++ tailWord_5372135) baseStart_5372135 baseEnd_5372135 := by
    simpa [prefixWord, tailWord_5372135, baseEnd_5372135] using wordTrace_append hprefix tailTrace_5372135
  have hstable : (prefixWord ++ tailWord_5372135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372135).length < 2 ^ (prefixWord ++ tailWord_5372135).sum := by decide
  have hdescent : baseEnd_5372135 < baseStart_5372135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372138 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_5372138 : Nat := 118140960795 + 5372138 * 2 ^ 59
def prefixEnd_5372138 : Nat := 4983230072969 + 3 ^ 40 * 5372138 * 2
def baseEnd_5372138 : Nat := 2758488936283407719068993

theorem tailTrace_5372138 : CollatzResearch.WordTrace tailWord_5372138 prefixEnd_5372138 2758488936283407719068993 := by
  unfold tailWord_5372138
  simp only [CollatzResearch.WordTrace]
  refine ⟨48984492452917247242637267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130625313207779325980366045 48984492452917247242637267)
  ·
    refine ⟨73476738679375870863955901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48984492452917247242637267 73476738679375870863955901)
    ·
      refine ⟨27553777004765951573983463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73476738679375870863955901 27553777004765951573983463)
      ·
        refine ⟨41330665507148927360975195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27553777004765951573983463 41330665507148927360975195)
        ·
          refine ⟨61995998260723391041462793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41330665507148927360975195 61995998260723391041462793)
          ·
            refine ⟨46496998695542543281097095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61995998260723391041462793 46496998695542543281097095)
            ·
              refine ⟨69745498043313814921645643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46496998695542543281097095 69745498043313814921645643)
              ·
                refine ⟨104618247064970722382468465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69745498043313814921645643 104618247064970722382468465)
                ·
                  refine ⟨78463685298728041786851349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104618247064970722382468465 78463685298728041786851349)
                  ·
                    refine ⟨3677985248377876958758657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78463685298728041786851349 3677985248377876958758657)
                    ·
                      refine ⟨2758488936283407719068993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3677985248377876958758657 2758488936283407719068993)
                      ·
                        rfl

theorem cell23_5372138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_5372138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372138 prefixEnd_5372138 := by exact prefixLift 5372138
  have htrace : WordTrace (prefixWord ++ tailWord_5372138) baseStart_5372138 baseEnd_5372138 := by
    simpa [prefixWord, tailWord_5372138, baseEnd_5372138] using wordTrace_append hprefix tailTrace_5372138
  have hstable : (prefixWord ++ tailWord_5372138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372138).length < 2 ^ (prefixWord ++ tailWord_5372138).sum := by decide
  have hdescent : baseEnd_5372138 < baseStart_5372138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372188 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_5372188 : Nat := 118140960795 + 5372188 * 2 ^ 59
def prefixEnd_5372188 : Nat := 4983230072969 + 3 ^ 40 * 5372188 * 2
def baseEnd_5372188 : Nat := 2758514610316132523443763

theorem tailTrace_5372188 : CollatzResearch.WordTrace tailWord_5372188 prefixEnd_5372188 2758514610316132523443763 := by
  unfold tailWord_5372188
  simp only [CollatzResearch.WordTrace]
  refine ⟨97969896730743923754934609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130626528974325231673246145 97969896730743923754934609)
  ·
    refine ⟨73477422548057942816200957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97969896730743923754934609 73477422548057942816200957)
    ·
      refine ⟨27554033455521728556075359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73477422548057942816200957 27554033455521728556075359)
      ·
        refine ⟨41331050183282592834113039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27554033455521728556075359 41331050183282592834113039)
        ·
          refine ⟨61996575274923889251169559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41331050183282592834113039 61996575274923889251169559)
          ·
            refine ⟨92994862912385833876754339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61996575274923889251169559 92994862912385833876754339)
            ·
              refine ⟨139492294368578750815131509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92994862912385833876754339 139492294368578750815131509)
              ·
                refine ⟨13077402597054257888918579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139492294368578750815131509 13077402597054257888918579)
                ·
                  refine ⟨19616103895581386833377869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13077402597054257888918579 19616103895581386833377869)
                  ·
                    refine ⟨7356038960843020062516701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19616103895581386833377869 7356038960843020062516701)
                    ·
                      refine ⟨2758514610316132523443763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7356038960843020062516701 2758514610316132523443763)
                      ·
                        rfl

theorem cell23_5372188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_5372188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372188 prefixEnd_5372188 := by exact prefixLift 5372188
  have htrace : WordTrace (prefixWord ++ tailWord_5372188) baseStart_5372188 baseEnd_5372188 := by
    simpa [prefixWord, tailWord_5372188, baseEnd_5372188] using wordTrace_append hprefix tailTrace_5372188
  have hstable : (prefixWord ++ tailWord_5372188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372188).length < 2 ^ (prefixWord ++ tailWord_5372188).sum := by decide
  have hdescent : baseEnd_5372188 < baseStart_5372188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372189 : List Nat := [1, 4, 2, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_5372189 : Nat := 118140960795 + 5372189 * 2 ^ 59
def prefixEnd_5372189 : Nat := 4983230072969 + 3 ^ 40 * 5372189 * 2
def baseEnd_5372189 : Nat := 2758515123796787019531259

theorem tailTrace_5372189 : CollatzResearch.WordTrace tailWord_5372189 prefixEnd_5372189 2758515123796787019531259 := by
  unfold tailWord_5372189
  simp only [CollatzResearch.WordTrace]
  refine ⟨195939829934484224680655621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130626553289656149787103747 195939829934484224680655621)
  ·
    refine ⟨36738718112715792127622929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195939829934484224680655621 36738718112715792127622929)
    ·
      refine ⟨27554038584536844095717197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36738718112715792127622929 27554038584536844095717197)
      ·
        refine ⟨10332764469201316535893949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27554038584536844095717197 10332764469201316535893949)
        ·
          refine ⟨3874786675950493700960231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10332764469201316535893949 3874786675950493700960231)
          ·
            refine ⟨5812180013925740551440347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874786675950493700960231 5812180013925740551440347)
            ·
              refine ⟨8718270020888610827160521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5812180013925740551440347 8718270020888610827160521)
              ·
                refine ⟨6538702515666458120370391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8718270020888610827160521 6538702515666458120370391)
                ·
                  refine ⟨9808053773499687180555587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6538702515666458120370391 9808053773499687180555587)
                  ·
                    refine ⟨14712080660249530770833381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9808053773499687180555587 14712080660249530770833381)
                    ·
                      refine ⟨2758515123796787019531259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14712080660249530770833381 2758515123796787019531259)
                      ·
                        rfl

theorem cell23_5372189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_5372189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372189 prefixEnd_5372189 := by exact prefixLift 5372189
  have htrace : WordTrace (prefixWord ++ tailWord_5372189) baseStart_5372189 baseEnd_5372189 := by
    simpa [prefixWord, tailWord_5372189, baseEnd_5372189] using wordTrace_append hprefix tailTrace_5372189
  have hstable : (prefixWord ++ tailWord_5372189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372189).length < 2 ^ (prefixWord ++ tailWord_5372189).sum := by decide
  have hdescent : baseEnd_5372189 < baseStart_5372189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372192 : List Nat := [2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 3]
def baseStart_5372192 : Nat := 118140960795 + 5372192 * 2 ^ 59
def prefixEnd_5372192 : Nat := 4983230072969 + 3 ^ 40 * 5372192 * 2
def baseEnd_5372192 : Nat := 2758516664238750507793745

theorem tailTrace_5372192 : CollatzResearch.WordTrace tailWord_5372192 prefixEnd_5372192 2758516664238750507793745 := by
  unfold tailWord_5372192
  simp only [CollatzResearch.WordTrace]
  refine ⟨97969969676736678096507415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130626626235648904128676553 97969969676736678096507415)
  ·
    refine ⟨146954954515105017144761123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97969969676736678096507415 146954954515105017144761123)
    ·
      refine ⟨220432431772657525717141685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146954954515105017144761123 220432431772657525717141685)
      ·
        refine ⟨20665540478686643035982033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 220432431772657525717141685 20665540478686643035982033)
        ·
          refine ⟨15499155359014982276986525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20665540478686643035982033 15499155359014982276986525)
          ·
            refine ⟨5812183259630618353869947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15499155359014982276986525 5812183259630618353869947)
            ·
              refine ⟨8718274889445927530804921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5812183259630618353869947 8718274889445927530804921)
              ·
                refine ⟨6538706167084445648103691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8718274889445927530804921 6538706167084445648103691)
                ·
                  refine ⟨9808059250626668472155537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6538706167084445648103691 9808059250626668472155537)
                  ·
                    refine ⟨7356044437970001354116653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9808059250626668472155537 7356044437970001354116653)
                    ·
                      refine ⟨2758516664238750507793745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7356044437970001354116653 2758516664238750507793745)
                      ·
                        rfl

theorem cell23_5372192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_5372192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372192 prefixEnd_5372192 := by exact prefixLift 5372192
  have htrace : WordTrace (prefixWord ++ tailWord_5372192) baseStart_5372192 baseEnd_5372192 := by
    simpa [prefixWord, tailWord_5372192, baseEnd_5372192] using wordTrace_append hprefix tailTrace_5372192
  have hstable : (prefixWord ++ tailWord_5372192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372192).length < 2 ^ (prefixWord ++ tailWord_5372192).sum := by decide
  have hdescent : baseEnd_5372192 < baseStart_5372192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372215 : List Nat := [1, 1, 3, 1, 2, 1, 1, 7, 1, 3, 2]
def baseStart_5372215 : Nat := 118140960795 + 5372215 * 2 ^ 59
def prefixEnd_5372215 : Nat := 4983230072969 + 3 ^ 40 * 5372215 * 2
def baseEnd_5372215 : Nat := 2758528474293803917806139

theorem tailTrace_5372215 : CollatzResearch.WordTrace tailWord_5372215 prefixEnd_5372215 2758528474293803917806139 := by
  unfold tailWord_5372215
  simp only [CollatzResearch.WordTrace]
  refine ⟨195940778232390031121102099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130627185488260020747401399 195940778232390031121102099)
  ·
    refine ⟨293911167348585046681653149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195940778232390031121102099 293911167348585046681653149)
    ·
      refine ⟨110216687755719392505619931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293911167348585046681653149 110216687755719392505619931)
      ·
        refine ⟨165325031633579088758429897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110216687755719392505619931 165325031633579088758429897)
        ·
          refine ⟨123993773725184316568822423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165325031633579088758429897 123993773725184316568822423)
          ·
            refine ⟨185990660587776474853233635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123993773725184316568822423 185990660587776474853233635)
            ·
              refine ⟨278985990881664712279850453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185990660587776474853233635 278985990881664712279850453)
              ·
                refine ⟨6538734161289016694058995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 278985990881664712279850453 6538734161289016694058995)
                ·
                  refine ⟨9808101241933525041088493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6538734161289016694058995 9808101241933525041088493)
                  ·
                    refine ⟨3678037965725071890408185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9808101241933525041088493 3678037965725071890408185)
                    ·
                      refine ⟨2758528474293803917806139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3678037965725071890408185 2758528474293803917806139)
                      ·
                        rfl

theorem cell23_5372215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 3, 2].length) (baseStart_5372215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372215 prefixEnd_5372215 := by exact prefixLift 5372215
  have htrace : WordTrace (prefixWord ++ tailWord_5372215) baseStart_5372215 baseEnd_5372215 := by
    simpa [prefixWord, tailWord_5372215, baseEnd_5372215] using wordTrace_append hprefix tailTrace_5372215
  have hstable : (prefixWord ++ tailWord_5372215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372215).length < 2 ^ (prefixWord ++ tailWord_5372215).sum := by decide
  have hdescent : baseEnd_5372215 < baseStart_5372215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372222 : List Nat := [4, 2, 1, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_5372222 : Nat := 118140960795 + 5372222 * 2 ^ 59
def prefixEnd_5372222 : Nat := 4983230072969 + 3 ^ 40 * 5372222 * 2
def baseEnd_5372222 : Nat := 2758532068658385390418607

theorem tailTrace_5372222 : CollatzResearch.WordTrace tailWord_5372222 prefixEnd_5372222 2758532068658385390418607 := by
  unfold tailWord_5372222
  simp only [CollatzResearch.WordTrace]
  refine ⟨24492629192920583914575865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130627355695576447544404613 24492629192920583914575865)
  ·
    refine ⟨18369471894690437935931899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24492629192920583914575865 18369471894690437935931899)
    ·
      refine ⟨27554207842035656903897849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18369471894690437935931899 27554207842035656903897849)
      ·
        refine ⟨20665655881526742677923387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27554207842035656903897849 20665655881526742677923387)
        ·
          refine ⟨30998483822290114016885081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20665655881526742677923387 30998483822290114016885081)
          ·
            refine ⟨23248862866717585512663811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30998483822290114016885081 23248862866717585512663811)
            ·
              refine ⟨34873294300076378268995717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23248862866717585512663811 34873294300076378268995717)
              ·
                refine ⟨6538742681264320925436697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34873294300076378268995717 6538742681264320925436697)
                ·
                  refine ⟨4904057010948240694077523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6538742681264320925436697 4904057010948240694077523)
                  ·
                    refine ⟨7356085516422361041116285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4904057010948240694077523 7356085516422361041116285)
                    ·
                      refine ⟨2758532068658385390418607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7356085516422361041116285 2758532068658385390418607)
                      ·
                        rfl

theorem cell23_5372222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_5372222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372222 prefixEnd_5372222 := by exact prefixLift 5372222
  have htrace : WordTrace (prefixWord ++ tailWord_5372222) baseStart_5372222 baseEnd_5372222 := by
    simpa [prefixWord, tailWord_5372222, baseEnd_5372222] using wordTrace_append hprefix tailTrace_5372222
  have hstable : (prefixWord ++ tailWord_5372222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372222).length < 2 ^ (prefixWord ++ tailWord_5372222).sum := by decide
  have hdescent : baseEnd_5372222 < baseStart_5372222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372266 : List Nat := [3, 1, 3, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_5372266 : Nat := 118140960795 + 5372266 * 2 ^ 59
def prefixEnd_5372266 : Nat := 4983230072969 + 3 ^ 40 * 5372266 * 2
def baseEnd_5372266 : Nat := 2758554661807183218268405

theorem tailTrace_5372266 : CollatzResearch.WordTrace tailWord_5372266 prefixEnd_5372266 2758554661807183218268405 := by
  unfold tailWord_5372266
  simp only [CollatzResearch.WordTrace]
  refine ⟨48985659588801316707802163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130628425570136844554139101 48985659588801316707802163)
  ·
    refine ⟨73478489383201975061703245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48985659588801316707802163 73478489383201975061703245)
    ·
      refine ⟨27554433518700740648138717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73478489383201975061703245 27554433518700740648138717)
      ·
        refine ⟨10332912569512777743052019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27554433518700740648138717 10332912569512777743052019)
        ·
          refine ⟨15499368854269166614578029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10332912569512777743052019 15499368854269166614578029)
          ·
            refine ⟨5812263320350937480466761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15499368854269166614578029 5812263320350937480466761)
            ·
              refine ⟨4359197490263203110350071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5812263320350937480466761 4359197490263203110350071)
              ·
                refine ⟨6538796235394804665525107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4359197490263203110350071 6538796235394804665525107)
                ·
                  refine ⟨9808194353092206998287661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6538796235394804665525107 9808194353092206998287661)
                  ·
                    refine ⟨3678072882409577624357873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9808194353092206998287661 3678072882409577624357873)
                    ·
                      refine ⟨2758554661807183218268405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3678072882409577624357873 2758554661807183218268405)
                      ·
                        rfl

theorem cell23_5372266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_5372266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372266 prefixEnd_5372266 := by exact prefixLift 5372266
  have htrace : WordTrace (prefixWord ++ tailWord_5372266) baseStart_5372266 baseEnd_5372266 := by
    simpa [prefixWord, tailWord_5372266, baseEnd_5372266] using wordTrace_append hprefix tailTrace_5372266
  have hstable : (prefixWord ++ tailWord_5372266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372266).length < 2 ^ (prefixWord ++ tailWord_5372266).sum := by decide
  have hdescent : baseEnd_5372266 < baseStart_5372266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372285 : List Nat := [1, 4, 1, 1, 2, 3, 2, 4, 5]
def baseStart_5372285 : Nat := 118140960795 + 5372285 * 2 ^ 59
def prefixEnd_5372285 : Nat := 4983230072969 + 3 ^ 40 * 5372285 * 2
def baseEnd_5372285 : Nat := 306507157548846515992313

theorem tailTrace_5372285 : CollatzResearch.WordTrace tailWord_5372285 prefixEnd_5372285 306507157548846515992313 := by
  unfold tailWord_5372285
  simp only [CollatzResearch.WordTrace]
  refine ⟨195943331342136433076150309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130628887561424288717433539 195943331342136433076150309)
  ·
    refine ⟨36739374626650581201778183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195943331342136433076150309 36739374626650581201778183)
    ·
      refine ⟨55109061939975871802667275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36739374626650581201778183 55109061939975871802667275)
      ·
        refine ⟨82663592909963807704000913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55109061939975871802667275 82663592909963807704000913)
        ·
          refine ⟨61997694682472855778000685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82663592909963807704000913 61997694682472855778000685)
          ·
            refine ⟨23249135505927320916750257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61997694682472855778000685 23249135505927320916750257)
            ·
              refine ⟨17436851629445490687562693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23249135505927320916750257 17436851629445490687562693)
              ·
                refine ⟨3269409680521029503918005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17436851629445490687562693 3269409680521029503918005)
                ·
                  refine ⟨306507157548846515992313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3269409680521029503918005 306507157548846515992313)
                  ·
                    rfl

theorem cell23_5372285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_5372285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372285 prefixEnd_5372285 := by exact prefixLift 5372285
  have htrace : WordTrace (prefixWord ++ tailWord_5372285) baseStart_5372285 baseEnd_5372285 := by
    simpa [prefixWord, tailWord_5372285, baseEnd_5372285] using wordTrace_append hprefix tailTrace_5372285
  have hstable : (prefixWord ++ tailWord_5372285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372285).length < 2 ^ (prefixWord ++ tailWord_5372285).sum := by decide
  have hdescent : baseEnd_5372285 < baseStart_5372285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372372 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_5372372 : Nat := 118140960795 + 5372372 * 2 ^ 59
def prefixEnd_5372372 : Nat := 4983230072969 + 3 ^ 40 * 5372372 * 2
def baseEnd_5372372 : Nat := 2758609090756559803542917

theorem tailTrace_5372372 : CollatzResearch.WordTrace tailWord_5372372 prefixEnd_5372372 2758609090756559803542917 := by
  unfold tailWord_5372372
  simp only [CollatzResearch.WordTrace]
  refine ⟨97973252246410623467283685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130631002995214164623044913 97973252246410623467283685)
  ·
    refine ⟨18369984796201991900115691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97973252246410623467283685 18369984796201991900115691)
    ·
      refine ⟨27554977194302987850173537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18369984796201991900115691 27554977194302987850173537)
      ·
        refine ⟨20666232895727240887630153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27554977194302987850173537 20666232895727240887630153)
        ·
          refine ⟨15499674671795430665722615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20666232895727240887630153 15499674671795430665722615)
          ·
            refine ⟨23249512007693145998583923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15499674671795430665722615 23249512007693145998583923)
            ·
              refine ⟨34874268011539718997875885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23249512007693145998583923 34874268011539718997875885)
              ·
                refine ⟨13077850504327394624203457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34874268011539718997875885 13077850504327394624203457)
                ·
                  refine ⟨9808387878245545968152593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13077850504327394624203457 9808387878245545968152593)
                  ·
                    refine ⟨7356290908684159476114445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9808387878245545968152593 7356290908684159476114445)
                    ·
                      refine ⟨2758609090756559803542917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7356290908684159476114445 2758609090756559803542917)
                      ·
                        rfl

theorem cell23_5372372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_5372372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372372 prefixEnd_5372372 := by exact prefixLift 5372372
  have htrace : WordTrace (prefixWord ++ tailWord_5372372) baseStart_5372372 baseEnd_5372372 := by
    simpa [prefixWord, tailWord_5372372, baseEnd_5372372] using wordTrace_append hprefix tailTrace_5372372
  have hstable : (prefixWord ++ tailWord_5372372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372372).length < 2 ^ (prefixWord ++ tailWord_5372372).sum := by decide
  have hdescent : baseEnd_5372372 < baseStart_5372372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372425 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 1, 8, 2]
def baseStart_5372425 : Nat := 118140960795 + 5372425 * 2 ^ 59
def prefixEnd_5372425 : Nat := 4983230072969 + 3 ^ 40 * 5372425 * 2
def baseEnd_5372425 : Nat := 2758636305231248096180173

theorem tailTrace_5372425 : CollatzResearch.WordTrace tailWord_5372425 prefixEnd_5372425 2758636305231248096180173 := by
  unfold tailWord_5372425
  simp only [CollatzResearch.WordTrace]
  refine ⟨195948437561629236986246729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130632291707752824657497819 195948437561629236986246729)
  ·
    refine ⟨146961328171221927739685047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195948437561629236986246729 146961328171221927739685047)
    ·
      refine ⟨220441992256832891609527571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146961328171221927739685047 220441992256832891609527571)
      ·
        refine ⟨330662988385249337414291357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220441992256832891609527571 330662988385249337414291357)
        ·
          refine ⟨123998620644468501530359259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330662988385249337414291357 123998620644468501530359259)
          ·
            refine ⟨185997930966702752295538889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123998620644468501530359259 185997930966702752295538889)
            ·
              refine ⟨139498448225027064221654167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185997930966702752295538889 139498448225027064221654167)
              ·
                refine ⟨209247672337540596332481251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139498448225027064221654167 209247672337540596332481251)
                ·
                  refine ⟨313871508506310894498721877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209247672337540596332481251 313871508506310894498721877)
                  ·
                    refine ⟨3678181740308330794906897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 313871508506310894498721877 3678181740308330794906897)
                    ·
                      refine ⟨2758636305231248096180173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3678181740308330794906897 2758636305231248096180173)
                      ·
                        rfl

theorem cell23_5372425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 8, 2].length) (baseStart_5372425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372425 prefixEnd_5372425 := by exact prefixLift 5372425
  have htrace : WordTrace (prefixWord ++ tailWord_5372425) baseStart_5372425 baseEnd_5372425 := by
    simpa [prefixWord, tailWord_5372425, baseEnd_5372425] using wordTrace_append hprefix tailTrace_5372425
  have hstable : (prefixWord ++ tailWord_5372425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372425).length < 2 ^ (prefixWord ++ tailWord_5372425).sum := by decide
  have hdescent : baseEnd_5372425 < baseStart_5372425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372435 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 4, 4]
def baseStart_5372435 : Nat := 118140960795 + 5372435 * 2 ^ 59
def prefixEnd_5372435 : Nat := 4983230072969 + 3 ^ 40 * 5372435 * 2
def baseEnd_5372435 : Nat := 919547146679264352351709

theorem tailTrace_5372435 : CollatzResearch.WordTrace tailWord_5372435 prefixEnd_5372435 919547146679264352351709 := by
  unfold tailWord_5372435
  simp only [CollatzResearch.WordTrace]
  refine ⟨195948802291593008694110759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130632534861062005796073839 195948802291593008694110759)
  ·
    refine ⟨293923203437389513041166139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195948802291593008694110759 293923203437389513041166139)
    ·
      refine ⟨440884805156084269561749209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293923203437389513041166139 440884805156084269561749209)
      ·
        refine ⟨330663603867063202171311907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440884805156084269561749209 330663603867063202171311907)
        ·
          refine ⟨495995405800594803256967861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330663603867063202171311907 495995405800594803256967861)
          ·
            refine ⟨46499569293805762805340737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 495995405800594803256967861 46499569293805762805340737)
            ·
              refine ⟨34874676970354322104005553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46499569293805762805340737 34874676970354322104005553)
              ·
                refine ⟨26156007727765741578004165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34874676970354322104005553 26156007727765741578004165)
                ·
                  refine ⟨4904251448956076545875781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26156007727765741578004165 4904251448956076545875781)
                  ·
                    refine ⟨919547146679264352351709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4904251448956076545875781 919547146679264352351709)
                    ·
                      rfl

theorem cell23_5372435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 4].length) (baseStart_5372435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372435 prefixEnd_5372435 := by exact prefixLift 5372435
  have htrace : WordTrace (prefixWord ++ tailWord_5372435) baseStart_5372435 baseEnd_5372435 := by
    simpa [prefixWord, tailWord_5372435, baseEnd_5372435] using wordTrace_append hprefix tailTrace_5372435
  have hstable : (prefixWord ++ tailWord_5372435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372435).length < 2 ^ (prefixWord ++ tailWord_5372435).sum := by decide
  have hdescent : baseEnd_5372435 < baseStart_5372435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372439 : List Nat := [1, 1, 3, 6, 1, 1, 1, 3, 1, 5]
def baseStart_5372439 : Nat := 118140960795 + 5372439 * 2 ^ 59
def prefixEnd_5372439 : Nat := 4983230072969 + 3 ^ 40 * 5372439 * 2
def baseEnd_5372439 : Nat := 919547831320137013801703

theorem tailTrace_5372439 : CollatzResearch.WordTrace tailWord_5372439 prefixEnd_5372439 919547831320137013801703 := by
  unfold tailWord_5372439
  simp only [CollatzResearch.WordTrace]
  refine ⟨195948948183578517377256371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130632632122385678251504247 195948948183578517377256371)
  ·
    refine ⟨293923422275367776065884557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195948948183578517377256371 293923422275367776065884557)
    ·
      refine ⟨110221283353262916024706709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293923422275367776065884557 110221283353262916024706709)
      ·
        refine ⟨5166622657184199188658127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110221283353262916024706709 5166622657184199188658127)
        ·
          refine ⟨7749933985776298782987191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5166622657184199188658127 7749933985776298782987191)
          ·
            refine ⟨11624900978664448174480787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7749933985776298782987191 11624900978664448174480787)
            ·
              refine ⟨17437351467996672261721181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11624900978664448174480787 17437351467996672261721181)
              ·
                refine ⟨6539006800498752098145443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17437351467996672261721181 6539006800498752098145443)
                ·
                  refine ⟨9808510200748128147218165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6539006800498752098145443 9808510200748128147218165)
                  ·
                    refine ⟨919547831320137013801703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9808510200748128147218165 919547831320137013801703)
                    ·
                      rfl

theorem cell23_5372439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_5372439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372439 prefixEnd_5372439 := by exact prefixLift 5372439
  have htrace : WordTrace (prefixWord ++ tailWord_5372439) baseStart_5372439 baseEnd_5372439 := by
    simpa [prefixWord, tailWord_5372439, baseEnd_5372439] using wordTrace_append hprefix tailTrace_5372439
  have hstable : (prefixWord ++ tailWord_5372439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372439).length < 2 ^ (prefixWord ++ tailWord_5372439).sum := by decide
  have hdescent : baseEnd_5372439 < baseStart_5372439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372469 : List Nat := [1, 3, 3, 1, 1, 2, 5, 1, 2, 4]
def baseStart_5372469 : Nat := 118140960795 + 5372469 * 2 ^ 59
def prefixEnd_5372469 : Nat := 4983230072969 + 3 ^ 40 * 5372469 * 2
def baseEnd_5372469 : Nat := 919552966126681974676657

theorem tailTrace_5372469 : CollatzResearch.WordTrace tailWord_5372469 prefixEnd_5372469 919552966126681974676657 := by
  unfold tailWord_5372469
  simp only [CollatzResearch.WordTrace]
  refine ⟨195950042373469832500848461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130633361582313221667232307 195950042373469832500848461)
  ·
    refine ⟨73481265890051187187818173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195950042373469832500848461 73481265890051187187818173)
    ·
      refine ⟨27555474708769195195431815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73481265890051187187818173 27555474708769195195431815)
      ·
        refine ⟨41333212063153792793147723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27555474708769195195431815 41333212063153792793147723)
        ·
          refine ⟨61999818094730689189721585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41333212063153792793147723 61999818094730689189721585)
          ·
            refine ⟨46499863571048016892291189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61999818094730689189721585 46499863571048016892291189)
            ·
              refine ⟨4359362209785751583652299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46499863571048016892291189 4359362209785751583652299)
              ·
                refine ⟨6539043314678627375478449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4359362209785751583652299 6539043314678627375478449)
                ·
                  refine ⟨4904282486008970531608837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6539043314678627375478449 4904282486008970531608837)
                  ·
                    refine ⟨919552966126681974676657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4904282486008970531608837 919552966126681974676657)
                    ·
                      rfl

theorem cell23_5372469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_5372469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372469 prefixEnd_5372469 := by exact prefixLift 5372469
  have htrace : WordTrace (prefixWord ++ tailWord_5372469) baseStart_5372469 baseEnd_5372469 := by
    simpa [prefixWord, tailWord_5372469, baseEnd_5372469] using wordTrace_append hprefix tailTrace_5372469
  have hstable : (prefixWord ++ tailWord_5372469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372469).length < 2 ^ (prefixWord ++ tailWord_5372469).sum := by decide
  have hdescent : baseEnd_5372469 < baseStart_5372469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372492 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 6, 1, 3]
def baseStart_5372492 : Nat := 118140960795 + 5372492 * 2 ^ 59
def prefixEnd_5372492 : Nat := 4983230072969 + 3 ^ 40 * 5372492 * 2
def baseEnd_5372492 : Nat := 2758670708435099334042365

theorem tailTrace_5372492 : CollatzResearch.WordTrace tailWord_5372492 prefixEnd_5372492 2758670708435099334042365 := by
  unfold tailWord_5372492
  simp only [CollatzResearch.WordTrace]
  refine ⟨97975440626193253714467865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130633920834924338285957153 97975440626193253714467865)
  ·
    refine ⟨73481580469644940285850899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97975440626193253714467865 73481580469644940285850899)
    ·
      refine ⟨110222370704467410428776349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73481580469644940285850899 110222370704467410428776349)
      ·
        refine ⟨41333389014175278910791131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110222370704467410428776349 41333389014175278910791131)
        ·
          refine ⟨62000083521262918366186697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41333389014175278910791131 62000083521262918366186697)
          ·
            refine ⟨46500062640947188774640023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62000083521262918366186697 46500062640947188774640023)
            ·
              refine ⟨69750093961420783161960035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46500062640947188774640023 69750093961420783161960035)
              ·
                refine ⟨104625140942131174742940053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69750093961420783161960035 104625140942131174742940053)
                ·
                  refine ⟨4904303481662398816075315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104625140942131174742940053 4904303481662398816075315)
                  ·
                    refine ⟨7356455222493598224112973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4904303481662398816075315 7356455222493598224112973)
                    ·
                      refine ⟨2758670708435099334042365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7356455222493598224112973 2758670708435099334042365)
                      ·
                        rfl

theorem cell23_5372492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_5372492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372492 prefixEnd_5372492 := by exact prefixLift 5372492
  have htrace : WordTrace (prefixWord ++ tailWord_5372492) baseStart_5372492 baseEnd_5372492 := by
    simpa [prefixWord, tailWord_5372492, baseEnd_5372492] using wordTrace_append hprefix tailTrace_5372492
  have hstable : (prefixWord ++ tailWord_5372492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372492).length < 2 ^ (prefixWord ++ tailWord_5372492).sum := by decide
  have hdescent : baseEnd_5372492 < baseStart_5372492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372515 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 4]
def baseStart_5372515 : Nat := 118140960795 + 5372515 * 2 ^ 59
def prefixEnd_5372515 : Nat := 4983230072969 + 3 ^ 40 * 5372515 * 2
def baseEnd_5372515 : Nat := 2758682518490152744054759

theorem tailTrace_5372515 : CollatzResearch.WordTrace tailWord_5372515 prefixEnd_5372515 2758682518490152744054759 := by
  unfold tailWord_5372515
  simp only [CollatzResearch.WordTrace]
  refine ⟨195951720131303182357022999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130634480087535454904681999 195951720131303182357022999)
  ·
    refine ⟨293927580196954773535534499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195951720131303182357022999 293927580196954773535534499)
    ·
      refine ⟨440891370295432160303301749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293927580196954773535534499 440891370295432160303301749)
      ·
        refine ⟨41333565965196765028434539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 440891370295432160303301749 41333565965196765028434539)
        ·
          refine ⟨62000348947795147542651809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41333565965196765028434539 62000348947795147542651809)
          ·
            refine ⟨46500261710846360656988857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62000348947795147542651809 46500261710846360656988857)
            ·
              refine ⟨34875196283134770492741643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46500261710846360656988857 34875196283134770492741643)
              ·
                refine ⟨52312794424702155739112465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34875196283134770492741643 52312794424702155739112465)
                ·
                  refine ⟨39234595818526616804334349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52312794424702155739112465 39234595818526616804334349)
                  ·
                    refine ⟨14712973431947481301625381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39234595818526616804334349 14712973431947481301625381)
                    ·
                      refine ⟨2758682518490152744054759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14712973431947481301625381 2758682518490152744054759)
                      ·
                        rfl

theorem cell23_5372515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_5372515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372515 prefixEnd_5372515 := by exact prefixLift 5372515
  have htrace : WordTrace (prefixWord ++ tailWord_5372515) baseStart_5372515 baseEnd_5372515 := by
    simpa [prefixWord, tailWord_5372515, baseEnd_5372515] using wordTrace_append hprefix tailTrace_5372515
  have hstable : (prefixWord ++ tailWord_5372515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372515).length < 2 ^ (prefixWord ++ tailWord_5372515).sum := by decide
  have hdescent : baseEnd_5372515 < baseStart_5372515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372526 : List Nat := [4, 1, 2, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_5372526 : Nat := 118140960795 + 5372526 * 2 ^ 59
def prefixEnd_5372526 : Nat := 4983230072969 + 3 ^ 40 * 5372526 * 2
def baseEnd_5372526 : Nat := 2758688166777352201017209

theorem tailTrace_5372526 : CollatzResearch.WordTrace tailWord_5372526 prefixEnd_5372526 2758688166777352201017209 := by
  unfold tailWord_5372526
  simp only [CollatzResearch.WordTrace]
  refine ⟨24494015166782916404459179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130634747556175554157115621 24494015166782916404459179)
  ·
    refine ⟨36741022750174374606688769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24494015166782916404459179 36741022750174374606688769)
    ·
      refine ⟨27555767062630780955016577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36741022750174374606688769 27555767062630780955016577)
      ·
        refine ⟨20666825296973085716262433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27555767062630780955016577 20666825296973085716262433)
        ·
          refine ⟨15500118972729814287196825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20666825296973085716262433 15500118972729814287196825)
          ·
            refine ⟨11625089229547360715397619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15500118972729814287196825 11625089229547360715397619)
            ·
              refine ⟨17437633844321041073096429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11625089229547360715397619 17437633844321041073096429)
              ·
                refine ⟨6539112691620390402411161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17437633844321041073096429 6539112691620390402411161)
                ·
                  refine ⟨4904334518715292801808371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6539112691620390402411161 4904334518715292801808371)
                  ·
                    refine ⟨7356501778072939202712557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4904334518715292801808371 7356501778072939202712557)
                    ·
                      refine ⟨2758688166777352201017209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7356501778072939202712557 2758688166777352201017209)
                      ·
                        rfl

theorem cell23_5372526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_5372526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372526 prefixEnd_5372526 := by exact prefixLift 5372526
  have htrace : WordTrace (prefixWord ++ tailWord_5372526) baseStart_5372526 baseEnd_5372526 := by
    simpa [prefixWord, tailWord_5372526, baseEnd_5372526] using wordTrace_append hprefix tailTrace_5372526
  have hstable : (prefixWord ++ tailWord_5372526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372526).length < 2 ^ (prefixWord ++ tailWord_5372526).sum := by decide
  have hdescent : baseEnd_5372526 < baseStart_5372526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372535 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_5372535 : Nat := 118140960795 + 5372535 * 2 ^ 59
def prefixEnd_5372535 : Nat := 4983230072969 + 3 ^ 40 * 5372535 * 2
def baseEnd_5372535 : Nat := 2758692788103242665804667

theorem tailTrace_5372535 : CollatzResearch.WordTrace tailWord_5372535 prefixEnd_5372535 2758692788103242665804667 := by
  unfold tailWord_5372535
  simp only [CollatzResearch.WordTrace]
  refine ⟨195952449591230725772751059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130634966394153817181834039 195952449591230725772751059)
  ·
    refine ⟨293928674386846088659126589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195952449591230725772751059 293928674386846088659126589)
    ·
      refine ⟨110223252895067283247172471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293928674386846088659126589 110223252895067283247172471)
      ·
        refine ⟨165334879342600924870758707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110223252895067283247172471 165334879342600924870758707)
        ·
          refine ⟨248002319013901387306138061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165334879342600924870758707 248002319013901387306138061)
          ·
            refine ⟨93000869630213020239801773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248002319013901387306138061 93000869630213020239801773)
            ·
              refine ⟨34875326111329882589925665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93000869630213020239801773 34875326111329882589925665)
              ·
                refine ⟨26156494583497411942444249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34875326111329882589925665 26156494583497411942444249)
                ·
                  refine ⟨19617370937623058956833187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26156494583497411942444249 19617370937623058956833187)
                  ·
                    refine ⟨29426056406434588435249781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19617370937623058956833187 29426056406434588435249781)
                    ·
                      refine ⟨2758692788103242665804667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29426056406434588435249781 2758692788103242665804667)
                      ·
                        rfl

theorem cell23_5372535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_5372535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372535 prefixEnd_5372535 := by exact prefixLift 5372535
  have htrace : WordTrace (prefixWord ++ tailWord_5372535) baseStart_5372535 baseEnd_5372535 := by
    simpa [prefixWord, tailWord_5372535, baseEnd_5372535] using wordTrace_append hprefix tailTrace_5372535
  have hstable : (prefixWord ++ tailWord_5372535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372535).length < 2 ^ (prefixWord ++ tailWord_5372535).sum := by decide
  have hdescent : baseEnd_5372535 < baseStart_5372535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372549 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 1, 4, 2]
def baseStart_5372549 : Nat := 118140960795 + 5372549 * 2 ^ 59
def prefixEnd_5372549 : Nat := 4983230072969 + 3 ^ 40 * 5372549 * 2
def baseEnd_5372549 : Nat := 2758699976832405611029603

theorem tailTrace_5372549 : CollatzResearch.WordTrace tailWord_5372549 prefixEnd_5372549 2758699976832405611029603 := by
  unfold tailWord_5372549
  simp only [CollatzResearch.WordTrace]
  refine ⟨195952960213180006163760701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130635306808786670775840467 195952960213180006163760701)
  ·
    refine ⟨73482360079942502311410263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195952960213180006163760701 73482360079942502311410263)
    ·
      refine ⟨110223540119913753467115395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73482360079942502311410263 110223540119913753467115395)
      ·
        refine ⟨165335310179870630200673093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110223540119913753467115395 165335310179870630200673093)
        ·
          refine ⟨31000370658725743162626205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165335310179870630200673093 31000370658725743162626205)
          ·
            refine ⟨11625138997022153685984827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31000370658725743162626205 11625138997022153685984827)
            ·
              refine ⟨17437708495533230528977241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11625138997022153685984827 17437708495533230528977241)
              ·
                refine ⟨13078281371649922896732931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17437708495533230528977241 13078281371649922896732931)
                ·
                  refine ⟨19617422057474884345099397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13078281371649922896732931 19617422057474884345099397)
                  ·
                    refine ⟨3678266635776540814706137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19617422057474884345099397 3678266635776540814706137)
                    ·
                      refine ⟨2758699976832405611029603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3678266635776540814706137 2758699976832405611029603)
                      ·
                        rfl

theorem cell23_5372549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 4, 2].length) (baseStart_5372549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372549 prefixEnd_5372549 := by exact prefixLift 5372549
  have htrace : WordTrace (prefixWord ++ tailWord_5372549) baseStart_5372549 baseEnd_5372549 := by
    simpa [prefixWord, tailWord_5372549, baseEnd_5372549] using wordTrace_append hprefix tailTrace_5372549
  have hstable : (prefixWord ++ tailWord_5372549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372549).length < 2 ^ (prefixWord ++ tailWord_5372549).sum := by decide
  have hdescent : baseEnd_5372549 < baseStart_5372549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372583 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_5372583 : Nat := 118140960795 + 5372583 * 2 ^ 59
def prefixEnd_5372583 : Nat := 4983230072969 + 3 ^ 40 * 5372583 * 2
def baseEnd_5372583 : Nat := 2758717435174658478004447

theorem tailTrace_5372583 : CollatzResearch.WordTrace tailWord_5372583 prefixEnd_5372583 2758717435174658478004447 := by
  unfold tailWord_5372583
  simp only [CollatzResearch.WordTrace]
  refine ⟨195954200295056829970498403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130636133530037886646998935 195954200295056829970498403)
  ·
    refine ⟨293931300442585244955747605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195954200295056829970498403 293931300442585244955747605)
    ·
      refine ⟨13778029708246183357300669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 293931300442585244955747605 13778029708246183357300669)
      ·
        refine ⟨5166761140592318758987751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13778029708246183357300669 5166761140592318758987751)
        ·
          refine ⟨7750141710888478138481627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5166761140592318758987751 7750141710888478138481627)
          ·
            refine ⟨11625212566332717207722441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7750141710888478138481627 11625212566332717207722441)
            ·
              refine ⟨8718909424749537905791831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11625212566332717207722441 8718909424749537905791831)
              ·
                refine ⟨13078364137124306858687747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8718909424749537905791831 13078364137124306858687747)
                ·
                  refine ⟨19617546205686460288031621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13078364137124306858687747 19617546205686460288031621)
                  ·
                    refine ⟨3678289913566211304005929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19617546205686460288031621 3678289913566211304005929)
                    ·
                      refine ⟨2758717435174658478004447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3678289913566211304005929 2758717435174658478004447)
                      ·
                        rfl

theorem cell23_5372583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_5372583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372583 prefixEnd_5372583 := by exact prefixLift 5372583
  have htrace : WordTrace (prefixWord ++ tailWord_5372583) baseStart_5372583 baseEnd_5372583 := by
    simpa [prefixWord, tailWord_5372583, baseEnd_5372583] using wordTrace_append hprefix tailTrace_5372583
  have hstable : (prefixWord ++ tailWord_5372583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372583).length < 2 ^ (prefixWord ++ tailWord_5372583).sum := by decide
  have hdescent : baseEnd_5372583 < baseStart_5372583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372585 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 6, 5]
def baseStart_5372585 : Nat := 118140960795 + 5372585 * 2 ^ 59
def prefixEnd_5372585 : Nat := 4983230072969 + 3 ^ 40 * 5372585 * 2
def baseEnd_5372585 : Nat := 919572820711989156726479

theorem tailTrace_5372585 : CollatzResearch.WordTrace tailWord_5372585 prefixEnd_5372585 919572820711989156726479 := by
  unfold tailWord_5372585
  simp only [CollatzResearch.WordTrace]
  refine ⟨195954273241049584312071209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130636182160699722874714139 195954273241049584312071209)
  ·
    refine ⟨146965704930787188234053407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195954273241049584312071209 146965704930787188234053407)
    ·
      refine ⟨220448557396180782351080111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146965704930787188234053407 220448557396180782351080111)
      ·
        refine ⟨330672836094271173526620167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220448557396180782351080111 330672836094271173526620167)
        ·
          refine ⟨496009254141406760289930251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330672836094271173526620167 496009254141406760289930251)
          ·
            refine ⟨744013881212110140434895377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496009254141406760289930251 744013881212110140434895377)
            ·
              refine ⟨558010410909082605326171533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 744013881212110140434895377 558010410909082605326171533)
              ·
                refine ⟨209253904090905976997314325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 558010410909082605326171533 209253904090905976997314325)
                ·
                  refine ⟨9808776754261217671749109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 209253904090905976997314325 9808776754261217671749109)
                  ·
                    refine ⟨919572820711989156726479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9808776754261217671749109 919572820711989156726479)
                    ·
                      rfl

theorem cell23_5372585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 5].length) (baseStart_5372585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372585 prefixEnd_5372585 := by exact prefixLift 5372585
  have htrace : WordTrace (prefixWord ++ tailWord_5372585) baseStart_5372585 baseEnd_5372585 := by
    simpa [prefixWord, tailWord_5372585, baseEnd_5372585] using wordTrace_append hprefix tailTrace_5372585
  have hstable : (prefixWord ++ tailWord_5372585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372585).length < 2 ^ (prefixWord ++ tailWord_5372585).sum := by decide
  have hdescent : baseEnd_5372585 < baseStart_5372585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372592 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 4, 5, 2]
def baseStart_5372592 : Nat := 118140960795 + 5372592 * 2 ^ 59
def prefixEnd_5372592 : Nat := 4983230072969 + 3 ^ 40 * 5372592 * 2
def baseEnd_5372592 : Nat := 2758722056500548942791905

theorem tailTrace_5372592 : CollatzResearch.WordTrace tailWord_5372592 prefixEnd_5372592 2758722056500548942791905 := by
  unfold tailWord_5372592
  simp only [CollatzResearch.WordTrace]
  refine ⟨97977264276012112253788015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130636352368016149671717353 97977264276012112253788015)
  ·
    refine ⟨146965896414018168380682023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97977264276012112253788015 146965896414018168380682023)
    ·
      refine ⟨220448844621027252571023035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146965896414018168380682023 220448844621027252571023035)
      ·
        refine ⟨330673266931540878856534553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220448844621027252571023035 330673266931540878856534553)
        ·
          refine ⟨248004950198655659142400915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330673266931540878856534553 248004950198655659142400915)
          ·
            refine ⟨372007425297983488713601373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248004950198655659142400915 372007425297983488713601373)
            ·
              refine ⟨139502784486743808267600515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 372007425297983488713601373 139502784486743808267600515)
              ·
                refine ⟨209254176730115712401400773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139502784486743808267600515 209254176730115712401400773)
                ·
                  refine ⟨39235158136896696075262645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209254176730115712401400773 39235158136896696075262645)
                  ·
                    refine ⟨3678296075334065257055873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39235158136896696075262645 3678296075334065257055873)
                    ·
                      refine ⟨2758722056500548942791905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3678296075334065257055873 2758722056500548942791905)
                      ·
                        rfl

theorem cell23_5372592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 5, 2].length) (baseStart_5372592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372592 prefixEnd_5372592 := by exact prefixLift 5372592
  have htrace : WordTrace (prefixWord ++ tailWord_5372592) baseStart_5372592 baseEnd_5372592 := by
    simpa [prefixWord, tailWord_5372592, baseEnd_5372592] using wordTrace_append hprefix tailTrace_5372592
  have hstable : (prefixWord ++ tailWord_5372592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372592).length < 2 ^ (prefixWord ++ tailWord_5372592).sum := by decide
  have hdescent : baseEnd_5372592 < baseStart_5372592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372639 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 2, 4, 2]
def baseStart_5372639 : Nat := 118140960795 + 5372639 * 2 ^ 59
def prefixEnd_5372639 : Nat := 4983230072969 + 3 ^ 40 * 5372639 * 2
def baseEnd_5372639 : Nat := 2758746190091310258904189

theorem tailTrace_5372639 : CollatzResearch.WordTrace tailWord_5372639 prefixEnd_5372639 2758746190091310258904189 := by
  unfold tailWord_5372639
  simp only [CollatzResearch.WordTrace]
  refine ⟨195956242782853951534536971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130637495188569301023024647 195956242782853951534536971)
  ·
    refine ⟨293934364174280927301805457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195956242782853951534536971 293934364174280927301805457)
    ·
      refine ⟨220450773130710695476354093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293934364174280927301805457 220450773130710695476354093)
      ·
        refine ⟨82669039924016510803632785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220450773130710695476354093 82669039924016510803632785)
        ·
          refine ⟨62001779943012383102724589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82669039924016510803632785 62001779943012383102724589)
          ·
            refine ⟨23250667478629643663521721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62001779943012383102724589 23250667478629643663521721)
            ·
              refine ⟨17438000608972232747641291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23250667478629643663521721 17438000608972232747641291)
              ·
                refine ⟨26157000913458349121461937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17438000608972232747641291 26157000913458349121461937)
                ·
                  refine ⟨19617750685093761841096453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26157000913458349121461937 19617750685093761841096453)
                  ·
                    refine ⟨3678328253455080345205585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19617750685093761841096453 3678328253455080345205585)
                    ·
                      refine ⟨2758746190091310258904189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3678328253455080345205585 2758746190091310258904189)
                      ·
                        rfl

theorem cell23_5372639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_5372639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372639 prefixEnd_5372639 := by exact prefixLift 5372639
  have htrace : WordTrace (prefixWord ++ tailWord_5372639) baseStart_5372639 baseEnd_5372639 := by
    simpa [prefixWord, tailWord_5372639, baseEnd_5372639] using wordTrace_append hprefix tailTrace_5372639
  have hstable : (prefixWord ++ tailWord_5372639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372639).length < 2 ^ (prefixWord ++ tailWord_5372639).sum := by decide
  have hdescent : baseEnd_5372639 < baseStart_5372639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372662 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_5372662 : Nat := 118140960795 + 5372662 * 2 ^ 59
def prefixEnd_5372662 : Nat := 4983230072969 + 3 ^ 40 * 5372662 * 2
def baseEnd_5372662 : Nat := 306528666682929296546287

theorem tailTrace_5372662 : CollatzResearch.WordTrace tailWord_5372662 prefixEnd_5372662 306528666682929296546287 := by
  unfold tailWord_5372662
  simp only [CollatzResearch.WordTrace]
  refine ⟨12247317603860664153914015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130638054441180417641749493 12247317603860664153914015)
  ·
    refine ⟨18370976405790996230871023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12247317603860664153914015 18370976405790996230871023)
    ·
      refine ⟨27556464608686494346306535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18370976405790996230871023 27556464608686494346306535)
      ·
        refine ⟨41334696913029741519459803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27556464608686494346306535 41334696913029741519459803)
        ·
          refine ⟨62002045369544612279189705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41334696913029741519459803 62002045369544612279189705)
          ·
            refine ⟨46501534027158459209392279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62002045369544612279189705 46501534027158459209392279)
            ·
              refine ⟨69752301040737688814088419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46501534027158459209392279 69752301040737688814088419)
              ·
                refine ⟨104628451561106533221132629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69752301040737688814088419 104628451561106533221132629)
                ·
                  refine ⟨306528666682929296546287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 104628451561106533221132629 306528666682929296546287)
                  ·
                    rfl

theorem cell23_5372662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_5372662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372662 prefixEnd_5372662 := by exact prefixLift 5372662
  have htrace : WordTrace (prefixWord ++ tailWord_5372662) baseStart_5372662 baseEnd_5372662 := by
    simpa [prefixWord, tailWord_5372662, baseEnd_5372662] using wordTrace_append hprefix tailTrace_5372662
  have hstable : (prefixWord ++ tailWord_5372662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372662).length < 2 ^ (prefixWord ++ tailWord_5372662).sum := by decide
  have hdescent : baseEnd_5372662 < baseStart_5372662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372666 : List Nat := [3, 1, 1, 1, 1, 3, 5, 3, 1, 4]
def baseStart_5372666 : Nat := 118140960795 + 5372666 * 2 ^ 59
def prefixEnd_5372666 : Nat := 4983230072969 + 3 ^ 40 * 5372666 * 2
def baseEnd_5372666 : Nat := 919586684689660551088855

theorem tailTrace_5372666 : CollatzResearch.WordTrace tailWord_5372666 prefixEnd_5372666 919586684689660551088855 := by
  unfold tailWord_5372666
  simp only [CollatzResearch.WordTrace]
  refine ⟨48989306888439033786442463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130638151702504090097179901 48989306888439033786442463)
  ·
    refine ⟨73483960332658550679663695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48989306888439033786442463 73483960332658550679663695)
    ·
      refine ⟨110225940498987826019495543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73483960332658550679663695 110225940498987826019495543)
      ·
        refine ⟨165338910748481739029243315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110225940498987826019495543 165338910748481739029243315)
        ·
          refine ⟨248008366122722608543864973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165338910748481739029243315 248008366122722608543864973)
          ·
            refine ⟨93003137296020978203949365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248008366122722608543864973 93003137296020978203949365)
            ·
              refine ⟨8719044121501966706620253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93003137296020978203949365 8719044121501966706620253)
              ·
                refine ⟨3269641545563237514982595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8719044121501966706620253 3269641545563237514982595)
                ·
                  refine ⟨4904462318344856272473893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3269641545563237514982595 4904462318344856272473893)
                  ·
                    refine ⟨919586684689660551088855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4904462318344856272473893 919586684689660551088855)
                    ·
                      rfl

theorem cell23_5372666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_5372666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372666 prefixEnd_5372666 := by exact prefixLift 5372666
  have htrace : WordTrace (prefixWord ++ tailWord_5372666) baseStart_5372666 baseEnd_5372666 := by
    simpa [prefixWord, tailWord_5372666, baseEnd_5372666] using wordTrace_append hprefix tailTrace_5372666
  have hstable : (prefixWord ++ tailWord_5372666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372666).length < 2 ^ (prefixWord ++ tailWord_5372666).sum := by decide
  have hdescent : baseEnd_5372666 < baseStart_5372666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372716 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 2, 3, 2]
def baseStart_5372716 : Nat := 118140960795 + 5372716 * 2 ^ 59
def prefixEnd_5372716 : Nat := 4983230072969 + 3 ^ 40 * 5372716 * 2
def baseEnd_5372716 : Nat := 2758785728101706457641335

theorem tailTrace_5372716 : CollatzResearch.WordTrace tailWord_5372716 prefixEnd_5372716 2758785728101706457641335 := by
  unfold tailWord_5372716
  simp only [CollatzResearch.WordTrace]
  refine ⟨97979525601787496842545001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130639367469049995790060001 97979525601787496842545001)
  ·
    refine ⟨73484644201340622631908751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97979525601787496842545001 73484644201340622631908751)
    ·
      refine ⟨110226966302010933947863127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73484644201340622631908751 110226966302010933947863127)
      ·
        refine ⟨165340449453016400921794691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110226966302010933947863127 165340449453016400921794691)
        ·
          refine ⟨248010674179524601382692037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165340449453016400921794691 248010674179524601382692037)
          ·
            refine ⟨46502001408660862759254757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 248010674179524601382692037 46502001408660862759254757)
            ·
              refine ⟨8719125264123911767360267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46502001408660862759254757 8719125264123911767360267)
              ·
                refine ⟨13078687896185867651040401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8719125264123911767360267 13078687896185867651040401)
                ·
                  refine ⟨9809015922139400738280301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13078687896185867651040401 9809015922139400738280301)
                  ·
                    refine ⟨3678380970802275276855113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9809015922139400738280301 3678380970802275276855113)
                    ·
                      refine ⟨2758785728101706457641335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3678380970802275276855113 2758785728101706457641335)
                      ·
                        rfl

theorem cell23_5372716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 3, 2].length) (baseStart_5372716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372716 prefixEnd_5372716 := by exact prefixLift 5372716
  have htrace : WordTrace (prefixWord ++ tailWord_5372716) baseStart_5372716 baseEnd_5372716 := by
    simpa [prefixWord, tailWord_5372716, baseEnd_5372716] using wordTrace_append hprefix tailTrace_5372716
  have hstable : (prefixWord ++ tailWord_5372716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372716).length < 2 ^ (prefixWord ++ tailWord_5372716).sum := by decide
  have hdescent : baseEnd_5372716 < baseStart_5372716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372752 : List Nat := [2, 1, 1, 1, 1, 4, 5, 8]
def baseStart_5372752 : Nat := 118140960795 + 5372752 * 2 ^ 59
def prefixEnd_5372752 : Nat := 4983230072969 + 3 ^ 40 * 5372752 * 2
def baseEnd_5372752 : Nat := 102177933829824752473747

theorem tailTrace_5372752 : CollatzResearch.WordTrace tailWord_5372752 prefixEnd_5372752 102177933829824752473747 := by
  unfold tailWord_5372752
  simp only [CollatzResearch.WordTrace]
  refine ⟨97980182115722285916700255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130640242820963047888933673 97980182115722285916700255)
  ·
    refine ⟨146970273173583428875050383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97980182115722285916700255 146970273173583428875050383)
    ·
      refine ⟨220455409760375143312575575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146970273173583428875050383 220455409760375143312575575)
      ·
        refine ⟨330683114640562714968863363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220455409760375143312575575 330683114640562714968863363)
        ·
          refine ⟨496024671960844072453295045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330683114640562714968863363 496024671960844072453295045)
          ·
            refine ⟨93004625992658263584992821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 496024671960844072453295045 93004625992658263584992821)
            ·
              refine ⟨8719183686811712211093077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93004625992658263584992821 8719183686811712211093077)
              ·
                refine ⟨102177933829824752473747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8719183686811712211093077 102177933829824752473747)
                ·
                  rfl

theorem cell23_5372752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 8].length) (baseStart_5372752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372752 prefixEnd_5372752 := by exact prefixLift 5372752
  have htrace : WordTrace (prefixWord ++ tailWord_5372752) baseStart_5372752 baseEnd_5372752 := by
    simpa [prefixWord, tailWord_5372752, baseEnd_5372752] using wordTrace_append hprefix tailTrace_5372752
  have hstable : (prefixWord ++ tailWord_5372752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372752).length < 2 ^ (prefixWord ++ tailWord_5372752).sum := by decide
  have hdescent : baseEnd_5372752 < baseStart_5372752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372756 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_5372756 : Nat := 118140960795 + 5372756 * 2 ^ 59
def prefixEnd_5372756 : Nat := 4983230072969 + 3 ^ 40 * 5372756 * 2
def baseEnd_5372756 : Nat := 919602089109295433713717

theorem tailTrace_5372756 : CollatzResearch.WordTrace tailWord_5372756 prefixEnd_5372756 919602089109295433713717 := by
  unfold tailWord_5372756
  simp only [CollatzResearch.WordTrace]
  refine ⟨97980255061715040258273061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130640340082286720344364081 97980255061715040258273061)
  ·
    refine ⟨18371297824071570048426199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97980255061715040258273061 18371297824071570048426199)
    ·
      refine ⟨27556946736107355072639299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18371297824071570048426199 27556946736107355072639299)
      ·
        refine ⟨41335420104161032608958949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27556946736107355072639299 41335420104161032608958949)
        ·
          refine ⟨7750391269530193614179803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41335420104161032608958949 7750391269530193614179803)
          ·
            refine ⟨11625586904295290421269705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7750391269530193614179803 11625586904295290421269705)
            ·
              refine ⟨8719190178221467815952279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11625586904295290421269705 8719190178221467815952279)
              ·
                refine ⟨13078785267332201723928419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8719190178221467815952279 13078785267332201723928419)
                ·
                  refine ⟨19618177900998302585892629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13078785267332201723928419 19618177900998302585892629)
                  ·
                    refine ⟨919602089109295433713717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19618177900998302585892629 919602089109295433713717)
                    ·
                      rfl

theorem cell23_5372756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_5372756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372756 prefixEnd_5372756 := by exact prefixLift 5372756
  have htrace : WordTrace (prefixWord ++ tailWord_5372756) baseStart_5372756 baseEnd_5372756 := by
    simpa [prefixWord, tailWord_5372756, baseEnd_5372756] using wordTrace_append hprefix tailTrace_5372756
  have hstable : (prefixWord ++ tailWord_5372756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372756).length < 2 ^ (prefixWord ++ tailWord_5372756).sum := by decide
  have hdescent : baseEnd_5372756 < baseStart_5372756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372759 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 4]
def baseStart_5372759 : Nat := 118140960795 + 5372759 * 2 ^ 59
def prefixEnd_5372759 : Nat := 4983230072969 + 3 ^ 40 * 5372759 * 2
def baseEnd_5372759 : Nat := 2758807807769849789403637

theorem tailTrace_5372759 : CollatzResearch.WordTrace tailWord_5372759 prefixEnd_5372759 2758807807769849789403637 := by
  unfold tailWord_5372759
  simp only [CollatzResearch.WordTrace]
  refine ⟨195960619542419212028905331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130640413028279474685936887 195960619542419212028905331)
  ·
    refine ⟨293940929313628818043357997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195960619542419212028905331 293940929313628818043357997)
    ·
      refine ⟨110227848492610806766259249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293940929313628818043357997 110227848492610806766259249)
      ·
        refine ⟨82670886369458105074694437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110227848492610806766259249 82670886369458105074694437)
        ·
          refine ⟨15500791194273394701505207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82670886369458105074694437 15500791194273394701505207)
          ·
            refine ⟨23251186791410092052257811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15500791194273394701505207 23251186791410092052257811)
            ·
              refine ⟨34876780187115138078386717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23251186791410092052257811 34876780187115138078386717)
              ·
                refine ⟨13078792570168176779395019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34876780187115138078386717 13078792570168176779395019)
                ·
                  refine ⟨19618188855252265169092529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13078792570168176779395019 19618188855252265169092529)
                  ·
                    refine ⟨14713641641439198876819397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19618188855252265169092529 14713641641439198876819397)
                    ·
                      refine ⟨2758807807769849789403637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14713641641439198876819397 2758807807769849789403637)
                      ·
                        rfl

theorem cell23_5372759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_5372759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372759 prefixEnd_5372759 := by exact prefixLift 5372759
  have htrace : WordTrace (prefixWord ++ tailWord_5372759) baseStart_5372759 baseEnd_5372759 := by
    simpa [prefixWord, tailWord_5372759, baseEnd_5372759] using wordTrace_append hprefix tailTrace_5372759
  have hstable : (prefixWord ++ tailWord_5372759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372759).length < 2 ^ (prefixWord ++ tailWord_5372759).sum := by decide
  have hdescent : baseEnd_5372759 < baseStart_5372759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372779 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 3]
def baseStart_5372779 : Nat := 118140960795 + 5372779 * 2 ^ 59
def prefixEnd_5372779 : Nat := 4983230072969 + 3 ^ 40 * 5372779 * 2
def baseEnd_5372779 : Nat := 2758818077382939711153545

theorem tailTrace_5372779 : CollatzResearch.WordTrace tailWord_5372779 prefixEnd_5372779 2758818077382939711153545 := by
  unfold tailWord_5372779
  simp only [CollatzResearch.WordTrace]
  refine ⟨195961349002346755444633391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130640899334897836963088927 195961349002346755444633391)
  ·
    refine ⟨293942023503520133166950087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195961349002346755444633391 293942023503520133166950087)
    ·
      refine ⟨440913035255280199750425131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293942023503520133166950087 440913035255280199750425131)
      ·
        refine ⟨661369552882920299625637697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440913035255280199750425131 661369552882920299625637697)
        ·
          refine ⟨496027164662190224719228273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661369552882920299625637697 496027164662190224719228273)
          ·
            refine ⟨372020373496642668539421205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496027164662190224719228273 372020373496642668539421205)
            ·
              refine ⟨17438455007655125087785369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 372020373496642668539421205 17438455007655125087785369)
              ·
                refine ⟨13078841255741343815839027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17438455007655125087785369 13078841255741343815839027)
                ·
                  refine ⟨19618261883612015723758541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13078841255741343815839027 19618261883612015723758541)
                  ·
                    refine ⟨7356848206354505896409453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19618261883612015723758541 7356848206354505896409453)
                    ·
                      refine ⟨2758818077382939711153545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7356848206354505896409453 2758818077382939711153545)
                      ·
                        rfl

theorem cell23_5372779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 3].length) (baseStart_5372779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372779 prefixEnd_5372779 := by exact prefixLift 5372779
  have htrace : WordTrace (prefixWord ++ tailWord_5372779) baseStart_5372779 baseEnd_5372779 := by
    simpa [prefixWord, tailWord_5372779, baseEnd_5372779] using wordTrace_append hprefix tailTrace_5372779
  have hstable : (prefixWord ++ tailWord_5372779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372779).length < 2 ^ (prefixWord ++ tailWord_5372779).sum := by decide
  have hdescent : baseEnd_5372779 < baseStart_5372779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372780 : List Nat := [2, 2, 1, 1, 4, 1, 4, 3, 1, 2, 2]
def baseStart_5372780 : Nat := 118140960795 + 5372780 * 2 ^ 59
def prefixEnd_5372780 : Nat := 4983230072969 + 3 ^ 40 * 5372780 * 2
def baseEnd_5372780 : Nat := 2758818590863594207241041

theorem tailTrace_5372780 : CollatzResearch.WordTrace tailWord_5372780 prefixEnd_5372780 2758818590863594207241041 := by
  unfold tailWord_5372780
  simp only [CollatzResearch.WordTrace]
  refine ⟨97980692737671566307709897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130640923650228755076946529 97980692737671566307709897)
  ·
    refine ⟨73485519553253674730782423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97980692737671566307709897 73485519553253674730782423)
    ·
      refine ⟨110228279329880512096173635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73485519553253674730782423 110228279329880512096173635)
      ·
        refine ⟨165342418994820768144260453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110228279329880512096173635 165342418994820768144260453)
        ·
          refine ⟨31001703561528894027048835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165342418994820768144260453 31001703561528894027048835)
          ·
            refine ⟨46502555342293341040573253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31001703561528894027048835 46502555342293341040573253)
            ·
              refine ⟨8719229126680001445107485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46502555342293341040573253 8719229126680001445107485)
              ·
                refine ⟨3269710922505000541915307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8719229126680001445107485 3269710922505000541915307)
                ·
                  refine ⟨4904566383757500812872961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3269710922505000541915307 4904566383757500812872961)
                  ·
                    refine ⟨3678424787818125609654721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4904566383757500812872961 3678424787818125609654721)
                    ·
                      refine ⟨2758818590863594207241041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3678424787818125609654721 2758818590863594207241041)
                      ·
                        rfl

theorem cell23_5372780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 1, 2, 2].length) (baseStart_5372780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372780 prefixEnd_5372780 := by exact prefixLift 5372780
  have htrace : WordTrace (prefixWord ++ tailWord_5372780) baseStart_5372780 baseEnd_5372780 := by
    simpa [prefixWord, tailWord_5372780, baseEnd_5372780] using wordTrace_append hprefix tailTrace_5372780
  have hstable : (prefixWord ++ tailWord_5372780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372780).length < 2 ^ (prefixWord ++ tailWord_5372780).sum := by decide
  have hdescent : baseEnd_5372780 < baseStart_5372780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372790 : List Nat := [5, 1, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_5372790 : Nat := 118140960795 + 5372790 * 2 ^ 59
def prefixEnd_5372790 : Nat := 4983230072969 + 3 ^ 40 * 5372790 * 2
def baseEnd_5372790 : Nat := 919607908556713056038665

theorem tailTrace_5372790 : CollatzResearch.WordTrace tailWord_5372790 prefixEnd_5372790 919607908556713056038665 := by
  unfold tailWord_5372790
  simp only [CollatzResearch.WordTrace]
  refine ⟨12247609387831681520205239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130641166803537936215522549 12247609387831681520205239)
  ·
    refine ⟨18371414081747522280307859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12247609387831681520205239 18371414081747522280307859)
    ·
      refine ⟨27557121122621283420461789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18371414081747522280307859 27557121122621283420461789)
      ·
        refine ⟨10333920420982981282673171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27557121122621283420461789 10333920420982981282673171)
        ·
          refine ⟨15500880631474471924009757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10333920420982981282673171 15500880631474471924009757)
          ·
            refine ⟨5812830236802926971503659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15500880631474471924009757 5812830236802926971503659)
            ·
              refine ⟨8719245355204390457255489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5812830236802926971503659 8719245355204390457255489)
              ·
                refine ⟨6539434016403292842941617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8719245355204390457255489 6539434016403292842941617)
                ·
                  refine ⟨4904575512302469632206213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6539434016403292842941617 4904575512302469632206213)
                  ·
                    refine ⟨919607908556713056038665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4904575512302469632206213 919607908556713056038665)
                    ·
                      rfl

theorem cell23_5372790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_5372790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372790 prefixEnd_5372790 := by exact prefixLift 5372790
  have htrace : WordTrace (prefixWord ++ tailWord_5372790) baseStart_5372790 baseEnd_5372790 := by
    simpa [prefixWord, tailWord_5372790, baseEnd_5372790] using wordTrace_append hprefix tailTrace_5372790
  have hstable : (prefixWord ++ tailWord_5372790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372790).length < 2 ^ (prefixWord ++ tailWord_5372790).sum := by decide
  have hdescent : baseEnd_5372790 < baseStart_5372790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372792 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_5372792 : Nat := 118140960795 + 5372792 * 2 ^ 59
def prefixEnd_5372792 : Nat := 4983230072969 + 3 ^ 40 * 5372792 * 2
def baseEnd_5372792 : Nat := 2758824752631448160290985

theorem tailTrace_5372792 : CollatzResearch.WordTrace tailWord_5372792 prefixEnd_5372792 2758824752631448160290985 := by
  unfold tailWord_5372792
  simp only [CollatzResearch.WordTrace]
  refine ⟨97980911575649829332428315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130641215434199772443237753 97980911575649829332428315)
  ·
    refine ⟨146971367363474743998642473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97980911575649829332428315 146971367363474743998642473)
    ·
      refine ⟨110228525522606057998981855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146971367363474743998642473 110228525522606057998981855)
      ·
        refine ⟨165342788283909086998472783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110228525522606057998981855 165342788283909086998472783)
        ·
          refine ⟨248014182425863630497709175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165342788283909086998472783 248014182425863630497709175)
          ·
            refine ⟨372021273638795445746563763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248014182425863630497709175 372021273638795445746563763)
            ·
              refine ⟨558031910458193168619845645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372021273638795445746563763 558031910458193168619845645)
              ·
                refine ⟨209261966421822438232442117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 558031910458193168619845645 209261966421822438232442117)
                ·
                  refine ⟨39236618704091707168582897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209261966421822438232442117 39236618704091707168582897)
                  ·
                    refine ⟨29427464028068780376437173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39236618704091707168582897 29427464028068780376437173)
                    ·
                      refine ⟨2758824752631448160290985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29427464028068780376437173 2758824752631448160290985)
                      ·
                        rfl

theorem cell23_5372792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_5372792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372792 prefixEnd_5372792 := by exact prefixLift 5372792
  have htrace : WordTrace (prefixWord ++ tailWord_5372792) baseStart_5372792 baseEnd_5372792 := by
    simpa [prefixWord, tailWord_5372792, baseEnd_5372792] using wordTrace_append hprefix tailTrace_5372792
  have hstable : (prefixWord ++ tailWord_5372792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372792).length < 2 ^ (prefixWord ++ tailWord_5372792).sum := by decide
  have hdescent : baseEnd_5372792 < baseStart_5372792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372823 : List Nat := [1, 1, 3, 3, 1, 2, 4, 2, 1, 3, 2]
def baseStart_5372823 : Nat := 118140960795 + 5372823 * 2 ^ 59
def prefixEnd_5372823 : Nat := 4983230072969 + 3 ^ 40 * 5372823 * 2
def baseEnd_5372823 : Nat := 2758840670531737539003343

theorem tailTrace_5372823 : CollatzResearch.WordTrace tailWord_5372823 prefixEnd_5372823 2758840670531737539003343 := by
  unfold tailWord_5372823
  simp only [CollatzResearch.WordTrace]
  refine ⟨195962953814187350959235123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130641969209458233972823415 195962953814187350959235123)
  ·
    refine ⟨293944430721281026438852685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195962953814187350959235123 293944430721281026438852685)
    ·
      refine ⟨110229161520480384914569757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293944430721281026438852685 110229161520480384914569757)
      ·
        refine ⟨41335935570180144342963659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110229161520480384914569757 41335935570180144342963659)
        ·
          refine ⟨62003903355270216514445489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41335935570180144342963659 62003903355270216514445489)
          ·
            refine ⟨46502927516452662385834117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62003903355270216514445489 46502927516452662385834117)
            ·
              refine ⟨8719298909334874197343897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46502927516452662385834117 8719298909334874197343897)
              ·
                refine ⟨6539474182001155648007923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8719298909334874197343897 6539474182001155648007923)
                ·
                  refine ⟨9809211273001733472011885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6539474182001155648007923 9809211273001733472011885)
                  ·
                    refine ⟨3678454227375650052004457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9809211273001733472011885 3678454227375650052004457)
                    ·
                      refine ⟨2758840670531737539003343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3678454227375650052004457 2758840670531737539003343)
                      ·
                        rfl

theorem cell23_5372823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_5372823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372823 prefixEnd_5372823 := by exact prefixLift 5372823
  have htrace : WordTrace (prefixWord ++ tailWord_5372823) baseStart_5372823 baseEnd_5372823 := by
    simpa [prefixWord, tailWord_5372823, baseEnd_5372823] using wordTrace_append hprefix tailTrace_5372823
  have hstable : (prefixWord ++ tailWord_5372823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372823).length < 2 ^ (prefixWord ++ tailWord_5372823).sum := by decide
  have hdescent : baseEnd_5372823 < baseStart_5372823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372836 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 3, 4, 2]
def baseStart_5372836 : Nat := 118140960795 + 5372836 * 2 ^ 59
def prefixEnd_5372836 : Nat := 4983230072969 + 3 ^ 40 * 5372836 * 2
def baseEnd_5372836 : Nat := 2758847345780245988140783

theorem tailTrace_5372836 : CollatzResearch.WordTrace tailWord_5372836 prefixEnd_5372836 2758847345780245988140783 := by
  unfold tailWord_5372836
  simp only [CollatzResearch.WordTrace]
  refine ⟨97981713981570127089729181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130642285308760169452972241 97981713981570127089729181)
  ·
    refine ⟨36743142743088797658648443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97981713981570127089729181 36743142743088797658648443)
    ·
      refine ⟨55114714114633196487972665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36743142743088797658648443 55114714114633196487972665)
      ·
        refine ⟨41336035585974897365979499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55114714114633196487972665 41336035585974897365979499)
        ·
          refine ⟨62004053378962346048969249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41336035585974897365979499 62004053378962346048969249)
          ·
            refine ⟨46503040034221759536726937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62004053378962346048969249 46503040034221759536726937)
            ·
              refine ⟨34877280025666319652545203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46503040034221759536726937 34877280025666319652545203)
              ·
                refine ⟨52315920038499479478817805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34877280025666319652545203 52315920038499479478817805)
                ·
                  refine ⟨19618470014437304804556677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52315920038499479478817805 19618470014437304804556677)
                  ·
                    refine ⟨3678463127706994650854377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19618470014437304804556677 3678463127706994650854377)
                    ·
                      refine ⟨2758847345780245988140783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3678463127706994650854377 2758847345780245988140783)
                      ·
                        rfl

theorem cell23_5372836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_5372836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372836 prefixEnd_5372836 := by exact prefixLift 5372836
  have htrace : WordTrace (prefixWord ++ tailWord_5372836) baseStart_5372836 baseEnd_5372836 := by
    simpa [prefixWord, tailWord_5372836, baseEnd_5372836] using wordTrace_append hprefix tailTrace_5372836
  have hstable : (prefixWord ++ tailWord_5372836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372836).length < 2 ^ (prefixWord ++ tailWord_5372836).sum := by decide
  have hdescent : baseEnd_5372836 < baseStart_5372836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372853 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_5372853 : Nat := 118140960795 + 5372853 * 2 ^ 59
def prefixEnd_5372853 : Nat := 4983230072969 + 3 ^ 40 * 5372853 * 2
def baseEnd_5372853 : Nat := 2758856074951372421628205

theorem tailTrace_5372853 : CollatzResearch.WordTrace tailWord_5372853 prefixEnd_5372853 2758856074951372421628205 := by
  unfold tailWord_5372853
  simp only [CollatzResearch.WordTrace]
  refine ⟨195964048004078666082827213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130642698669385777388551475 195964048004078666082827213)
  ·
    refine ⟨73486518001529499781060205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195964048004078666082827213 73486518001529499781060205)
    ·
      refine ⟨27557444250573562417897577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73486518001529499781060205 27557444250573562417897577)
      ·
        refine ⟨20668083187930171813423183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27557444250573562417897577 20668083187930171813423183)
        ·
          refine ⟨31002124781895257720134775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20668083187930171813423183 31002124781895257720134775)
          ·
            refine ⟨46503187172842886580202163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31002124781895257720134775 46503187172842886580202163)
            ·
              refine ⟨69754780759264329870303245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46503187172842886580202163 69754780759264329870303245)
              ·
                refine ⟨26158042784724123701363717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69754780759264329870303245 26158042784724123701363717)
                ·
                  refine ⟨4904633022135773194005697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26158042784724123701363717 4904633022135773194005697)
                  ·
                    refine ⟨3678474766601829895504273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4904633022135773194005697 3678474766601829895504273)
                    ·
                      refine ⟨2758856074951372421628205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3678474766601829895504273 2758856074951372421628205)
                      ·
                        rfl

theorem cell23_5372853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_5372853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372853 prefixEnd_5372853 := by exact prefixLift 5372853
  have htrace : WordTrace (prefixWord ++ tailWord_5372853) baseStart_5372853 baseEnd_5372853 := by
    simpa [prefixWord, tailWord_5372853, baseEnd_5372853] using wordTrace_append hprefix tailTrace_5372853
  have hstable : (prefixWord ++ tailWord_5372853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372853).length < 2 ^ (prefixWord ++ tailWord_5372853).sum := by decide
  have hdescent : baseEnd_5372853 < baseStart_5372853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372869 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 6, 3, 3]
def baseStart_5372869 : Nat := 118140960795 + 5372869 * 2 ^ 59
def prefixEnd_5372869 : Nat := 4983230072969 + 3 ^ 40 * 5372869 * 2
def baseEnd_5372869 : Nat := 2758864290641844359028131

theorem tailTrace_5372869 : CollatzResearch.WordTrace tailWord_5372869 prefixEnd_5372869 2758864290641844359028131 := by
  unfold tailWord_5372869
  simp only [CollatzResearch.WordTrace]
  refine ⟨195964631572020700815409661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130643087714680467210273107 195964631572020700815409661)
  ·
    refine ⟨73486736839507762805778623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195964631572020700815409661 73486736839507762805778623)
    ·
      refine ⟨110230105259261644208667935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73486736839507762805778623 110230105259261644208667935)
      ·
        refine ⟨165345157888892466313001903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110230105259261644208667935 165345157888892466313001903)
        ·
          refine ⟨248017736833338699469502855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165345157888892466313001903 248017736833338699469502855)
          ·
            refine ⟨372026605250008049204254283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248017736833338699469502855 372026605250008049204254283)
            ·
              refine ⟨558039907875012073806381425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372026605250008049204254283 558039907875012073806381425)
              ·
                refine ⟨418529930906259055354786069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558039907875012073806381425 418529930906259055354786069)
                ·
                  refine ⟨19618590511230893219755597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 418529930906259055354786069 19618590511230893219755597)
                  ·
                    refine ⟨7356971441711584957408349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19618590511230893219755597 7356971441711584957408349)
                    ·
                      refine ⟨2758864290641844359028131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7356971441711584957408349 2758864290641844359028131)
                      ·
                        rfl

theorem cell23_5372869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_5372869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372869 prefixEnd_5372869 := by exact prefixLift 5372869
  have htrace : WordTrace (prefixWord ++ tailWord_5372869) baseStart_5372869 baseEnd_5372869 := by
    simpa [prefixWord, tailWord_5372869, baseEnd_5372869] using wordTrace_append hprefix tailTrace_5372869
  have hstable : (prefixWord ++ tailWord_5372869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372869).length < 2 ^ (prefixWord ++ tailWord_5372869).sum := by decide
  have hdescent : baseEnd_5372869 < baseStart_5372869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372899 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 5]
def baseStart_5372899 : Nat := 118140960795 + 5372899 * 2 ^ 59
def prefixEnd_5372899 : Nat := 4983230072969 + 3 ^ 40 * 5372899 * 2
def baseEnd_5372899 : Nat := 2758879695061479241652993

theorem tailTrace_5372899 : CollatzResearch.WordTrace tailWord_5372899 prefixEnd_5372899 2758879695061479241652993 := by
  unfold tailWord_5372899
  simp only [CollatzResearch.WordTrace]
  refine ⟨195965725761912015939001751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130643817174608010626001167 195965725761912015939001751)
  ·
    refine ⟨293948588642868023908502627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195965725761912015939001751 293948588642868023908502627)
    ·
      refine ⟨440922882964302035862753941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293948588642868023908502627 440922882964302035862753941)
      ·
        refine ⟨20668260138951657931066591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 440922882964302035862753941 20668260138951657931066591)
        ·
          refine ⟨31002390208427486896599887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20668260138951657931066591 31002390208427486896599887)
          ·
            refine ⟨46503585312641230344899831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31002390208427486896599887 46503585312641230344899831)
            ·
              refine ⟨69755377968961845517349747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46503585312641230344899831 69755377968961845517349747)
              ·
                refine ⟨104633066953442768276024621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69755377968961845517349747 104633066953442768276024621)
                ·
                  refine ⟨39237400107541038103509233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104633066953442768276024621 39237400107541038103509233)
                  ·
                    refine ⟨29428050080655778577631925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39237400107541038103509233 29428050080655778577631925)
                    ·
                      refine ⟨2758879695061479241652993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29428050080655778577631925 2758879695061479241652993)
                      ·
                        rfl

theorem cell23_5372899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_5372899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372899 prefixEnd_5372899 := by exact prefixLift 5372899
  have htrace : WordTrace (prefixWord ++ tailWord_5372899) baseStart_5372899 baseEnd_5372899 := by
    simpa [prefixWord, tailWord_5372899, baseEnd_5372899] using wordTrace_append hprefix tailTrace_5372899
  have hstable : (prefixWord ++ tailWord_5372899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372899).length < 2 ^ (prefixWord ++ tailWord_5372899).sum := by decide
  have hdescent : baseEnd_5372899 < baseStart_5372899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372906 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 2, 5]
def baseStart_5372906 : Nat := 118140960795 + 5372906 * 2 ^ 59
def prefixEnd_5372906 : Nat := 4983230072969 + 3 ^ 40 * 5372906 * 2
def baseEnd_5372906 : Nat := 919627763142020238088487

theorem tailTrace_5372906 : CollatzResearch.WordTrace tailWord_5372906 prefixEnd_5372906 919627763142020238088487 := by
  unfold tailWord_5372906
  simp only [CollatzResearch.WordTrace]
  refine ⟨48991495268221664033626643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130643987381924437423004381 48991495268221664033626643)
  ·
    refine ⟨73487242902332496050439965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48991495268221664033626643 73487242902332496050439965)
    ·
      refine ⟨27557716088374686018914987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73487242902332496050439965 27557716088374686018914987)
      ·
        refine ⟨41336574132562029028372481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27557716088374686018914987 41336574132562029028372481)
        ·
          refine ⟨31002430599421521771279361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41336574132562029028372481 31002430599421521771279361)
          ·
            refine ⟨23251822949566141328459521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31002430599421521771279361 23251822949566141328459521)
            ·
              refine ⟨17438867212174605996344641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23251822949566141328459521 17438867212174605996344641)
              ·
                refine ⟨13079150409130954497258481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17438867212174605996344641 13079150409130954497258481)
                ·
                  refine ⟨9809362806848215872943861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13079150409130954497258481 9809362806848215872943861)
                  ·
                    refine ⟨919627763142020238088487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9809362806848215872943861 919627763142020238088487)
                    ·
                      rfl

theorem cell23_5372906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_5372906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372906 prefixEnd_5372906 := by exact prefixLift 5372906
  have htrace : WordTrace (prefixWord ++ tailWord_5372906) baseStart_5372906 baseEnd_5372906 := by
    simpa [prefixWord, tailWord_5372906, baseEnd_5372906] using wordTrace_append hprefix tailTrace_5372906
  have hstable : (prefixWord ++ tailWord_5372906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372906).length < 2 ^ (prefixWord ++ tailWord_5372906).sum := by decide
  have hdescent : baseEnd_5372906 < baseStart_5372906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372936 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 5, 4]
def baseStart_5372936 : Nat := 118140960795 + 5372936 * 2 ^ 59
def prefixEnd_5372936 : Nat := 4983230072969 + 3 ^ 40 * 5372936 * 2
def baseEnd_5372936 : Nat := 919632897948565198963441

theorem tailTrace_5372936 : CollatzResearch.WordTrace tailWord_5372936 prefixEnd_5372936 919632897948565198963441 := by
  unfold tailWord_5372936
  simp only [CollatzResearch.WordTrace]
  refine ⟨97983537631388985629049331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130644716841851980838732441 97983537631388985629049331)
  ·
    refine ⟨146975306447083478443573997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97983537631388985629049331 146975306447083478443573997)
    ·
      refine ⟨55115739917656304416340249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146975306447083478443573997 55115739917656304416340249)
      ·
        refine ⟨41336804938242228312255187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55115739917656304416340249 41336804938242228312255187)
        ·
          refine ⟨62005207407363342468382781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41336804938242228312255187 62005207407363342468382781)
          ·
            refine ⟨23251952777761253425643543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62005207407363342468382781 23251952777761253425643543)
            ·
              refine ⟨34877929166641880138465315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23251952777761253425643543 34877929166641880138465315)
              ·
                refine ⟨52316893749962820207697973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34877929166641880138465315 52316893749962820207697973)
                ·
                  refine ⟨4904708789059014394471685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52316893749962820207697973 4904708789059014394471685)
                  ·
                    refine ⟨919632897948565198963441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4904708789059014394471685 919632897948565198963441)
                    ·
                      rfl

theorem cell23_5372936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_5372936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372936 prefixEnd_5372936 := by exact prefixLift 5372936
  have htrace : WordTrace (prefixWord ++ tailWord_5372936) baseStart_5372936 baseEnd_5372936 := by
    simpa [prefixWord, tailWord_5372936, baseEnd_5372936] using wordTrace_append hprefix tailTrace_5372936
  have hstable : (prefixWord ++ tailWord_5372936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372936).length < 2 ^ (prefixWord ++ tailWord_5372936).sum := by decide
  have hdescent : baseEnd_5372936 < baseStart_5372936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372953 : List Nat := [1, 2, 1, 2, 1, 1, 5, 5, 1, 4]
def baseStart_5372953 : Nat := 118140960795 + 5372953 * 2 ^ 59
def prefixEnd_5372953 : Nat := 4983230072969 + 3 ^ 40 * 5372953 * 2
def baseEnd_5372953 : Nat := 919635807672274010125915

theorem tailTrace_5372953 : CollatzResearch.WordTrace tailWord_5372953 prefixEnd_5372953 919635807672274010125915 := by
  unfold tailWord_5372953
  simp only [CollatzResearch.WordTrace]
  refine ⟨195967695303716383161467513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130645130202477588774311675 195967695303716383161467513)
  ·
    refine ⟨146975771477787287371100635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195967695303716383161467513 146975771477787287371100635)
    ·
      refine ⟨220463657216680931056650953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146975771477787287371100635 220463657216680931056650953)
      ·
        refine ⟨165347742912510698292488215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220463657216680931056650953 165347742912510698292488215)
        ·
          refine ⟨248021614368766047438732323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165347742912510698292488215 248021614368766047438732323)
          ·
            refine ⟨372032421553149071158098485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248021614368766047438732323 372032421553149071158098485)
            ·
              refine ⟨34878039520607725421071733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 372032421553149071158098485 34878039520607725421071733)
              ·
                refine ⟨3269816205056974258225475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34878039520607725421071733 3269816205056974258225475)
                ·
                  refine ⟨4904724307585461387338213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3269816205056974258225475 4904724307585461387338213)
                  ·
                    refine ⟨919635807672274010125915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4904724307585461387338213 919635807672274010125915)
                    ·
                      rfl

theorem cell23_5372953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 1, 4].length) (baseStart_5372953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372953 prefixEnd_5372953 := by exact prefixLift 5372953
  have htrace : WordTrace (prefixWord ++ tailWord_5372953) baseStart_5372953 baseEnd_5372953 := by
    simpa [prefixWord, tailWord_5372953, baseEnd_5372953] using wordTrace_append hprefix tailTrace_5372953
  have hstable : (prefixWord ++ tailWord_5372953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372953).length < 2 ^ (prefixWord ++ tailWord_5372953).sum := by decide
  have hdescent : baseEnd_5372953 < baseStart_5372953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5372970 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 3, 4]
def baseStart_5372970 : Nat := 118140960795 + 5372970 * 2 ^ 59
def prefixEnd_5372970 : Nat := 4983230072969 + 3 ^ 40 * 5372970 * 2
def baseEnd_5372970 : Nat := 919638717395982821288389

theorem tailTrace_5372970 : CollatzResearch.WordTrace tailWord_5372970 prefixEnd_5372970 919638717395982821288389 := by
  unfold tailWord_5372970
  simp only [CollatzResearch.WordTrace]
  refine ⟨48992078836163698766209091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130645543563103196709890909 48992078836163698766209091)
  ·
    refine ⟨73488118254245548149313637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48992078836163698766209091 73488118254245548149313637)
    ·
      refine ⟨13779022172671040277996307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73488118254245548149313637 13779022172671040277996307)
      ·
        refine ⟨20668533259006560416994461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13779022172671040277996307 20668533259006560416994461)
        ·
          refine ⟨7750699972127460156372923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20668533259006560416994461 7750699972127460156372923)
          ·
            refine ⟨11626049958191190234559385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7750699972127460156372923 11626049958191190234559385)
            ·
              refine ⟨8719537468643392675919539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11626049958191190234559385 8719537468643392675919539)
              ·
                refine ⟨13079306202965089013879309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8719537468643392675919539 13079306202965089013879309)
                ·
                  refine ⟨4904739826111908380204741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13079306202965089013879309 4904739826111908380204741)
                  ·
                    refine ⟨919638717395982821288389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4904739826111908380204741 919638717395982821288389)
                    ·
                      rfl

theorem cell23_5372970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_5372970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5372970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5372970 prefixEnd_5372970 := by exact prefixLift 5372970
  have htrace : WordTrace (prefixWord ++ tailWord_5372970) baseStart_5372970 baseEnd_5372970 := by
    simpa [prefixWord, tailWord_5372970, baseEnd_5372970] using wordTrace_append hprefix tailTrace_5372970
  have hstable : (prefixWord ++ tailWord_5372970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5372970).length < 2 ^ (prefixWord ++ tailWord_5372970).sum := by decide
  have hdescent : baseEnd_5372970 < baseStart_5372970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5372970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373020 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_5373020 : Nat := 118140960795 + 5373020 * 2 ^ 59
def prefixEnd_5373020 : Nat := 4983230072969 + 3 ^ 40 * 5373020 * 2
def baseEnd_5373020 : Nat := 2758941826220673268239937

theorem tailTrace_5373020 : CollatzResearch.WordTrace tailWord_5373020 prefixEnd_5373020 2758941826220673268239937 := by
  unfold tailWord_5373020
  simp only [CollatzResearch.WordTrace]
  refine ⟨97985069497236826802078257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130646759329649102402771009 97985069497236826802078257)
  ·
    refine ⟨73488802122927620101558693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97985069497236826802078257 73488802122927620101558693)
    ·
      refine ⟨13779150398048928769042255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73488802122927620101558693 13779150398048928769042255)
      ·
        refine ⟨20668725597073393153563383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13779150398048928769042255 20668725597073393153563383)
        ·
          refine ⟨31003088395610089730345075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20668725597073393153563383 31003088395610089730345075)
          ·
            refine ⟨46504632593415134595517613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31003088395610089730345075 46504632593415134595517613)
            ·
              refine ⟨17439237222530675473319105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46504632593415134595517613 17439237222530675473319105)
              ·
                refine ⟨13079427916898006604989329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17439237222530675473319105 13079427916898006604989329)
                ·
                  refine ⟨9809570937673504953741997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13079427916898006604989329 9809570937673504953741997)
                  ·
                    refine ⟨3678589101627564357653249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9809570937673504953741997 3678589101627564357653249)
                    ·
                      refine ⟨2758941826220673268239937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3678589101627564357653249 2758941826220673268239937)
                      ·
                        rfl

theorem cell23_5373020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_5373020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373020 prefixEnd_5373020 := by exact prefixLift 5373020
  have htrace : WordTrace (prefixWord ++ tailWord_5373020) baseStart_5373020 baseEnd_5373020 := by
    simpa [prefixWord, tailWord_5373020, baseEnd_5373020] using wordTrace_append hprefix tailTrace_5373020
  have hstable : (prefixWord ++ tailWord_5373020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373020).length < 2 ^ (prefixWord ++ tailWord_5373020).sum := by decide
  have hdescent : baseEnd_5373020 < baseStart_5373020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373036 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 5]
def baseStart_5373036 : Nat := 118140960795 + 5373036 * 2 ^ 59
def prefixEnd_5373036 : Nat := 4983230072969 + 3 ^ 40 * 5373036 * 2
def baseEnd_5373036 : Nat := 2758950041911145205639863

theorem tailTrace_5373036 : CollatzResearch.WordTrace tailWord_5373036 prefixEnd_5373036 2758950041911145205639863 := by
  unfold tailWord_5373036
  simp only [CollatzResearch.WordTrace]
  refine ⟨97985361281207844168369481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130647148374943792224492641 97985361281207844168369481)
  ·
    refine ⟨73489020960905883126277111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97985361281207844168369481 73489020960905883126277111)
    ·
      refine ⟨110233531441358824689415667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73489020960905883126277111 110233531441358824689415667)
      ·
        refine ⟨165350297162038237034123501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110233531441358824689415667 165350297162038237034123501)
        ·
          refine ⟨62006361435764338887796313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165350297162038237034123501 62006361435764338887796313)
          ·
            refine ⟨46504771076823254165847235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62006361435764338887796313 46504771076823254165847235)
            ·
              refine ⟨69757156615234881248770853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46504771076823254165847235 69757156615234881248770853)
              ·
                refine ⟨13079466865356540234144535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69757156615234881248770853 13079466865356540234144535)
                ·
                  refine ⟨19619200298034810351216803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13079466865356540234144535 19619200298034810351216803)
                  ·
                    refine ⟨29428800447052215526825205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19619200298034810351216803 29428800447052215526825205)
                    ·
                      refine ⟨2758950041911145205639863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29428800447052215526825205 2758950041911145205639863)
                      ·
                        rfl

theorem cell23_5373036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_5373036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373036 prefixEnd_5373036 := by exact prefixLift 5373036
  have htrace : WordTrace (prefixWord ++ tailWord_5373036) baseStart_5373036 baseEnd_5373036 := by
    simpa [prefixWord, tailWord_5373036, baseEnd_5373036] using wordTrace_append hprefix tailTrace_5373036
  have hstable : (prefixWord ++ tailWord_5373036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373036).length < 2 ^ (prefixWord ++ tailWord_5373036).sum := by decide
  have hdescent : baseEnd_5373036 < baseStart_5373036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373053 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_5373053 : Nat := 118140960795 + 5373053 * 2 ^ 59
def prefixEnd_5373053 : Nat := 4983230072969 + 3 ^ 40 * 5373053 * 2
def baseEnd_5373053 : Nat := 2758958771082271639127285

theorem tailTrace_5373053 : CollatzResearch.WordTrace tailWord_5373053 prefixEnd_5373053 2758958771082271639127285 := by
  unfold tailWord_5373053
  simp only [CollatzResearch.WordTrace]
  refine ⟨195971342603354100240107813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130647561735569400160071875 195971342603354100240107813)
  ·
    refine ⟨36744626738128893795020215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195971342603354100240107813 36744626738128893795020215)
    ·
      refine ⟨55116940107193340692530323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36744626738128893795020215 55116940107193340692530323)
      ·
        refine ⟨82675410160790011038795485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55116940107193340692530323 82675410160790011038795485)
        ·
          refine ⟨31003278810296254139548307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82675410160790011038795485 31003278810296254139548307)
          ·
            refine ⟨46504918215444381209322461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31003278810296254139548307 46504918215444381209322461)
            ·
              refine ⟨17439344330791642953495923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46504918215444381209322461 17439344330791642953495923)
              ·
                refine ⟨26159016496187464430243885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17439344330791642953495923 26159016496187464430243885)
                ·
                  refine ⟨9809631186070299161341457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26159016496187464430243885 9809631186070299161341457)
                  ·
                    refine ⟨7357223389552724371006093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9809631186070299161341457 7357223389552724371006093)
                    ·
                      refine ⟨2758958771082271639127285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7357223389552724371006093 2758958771082271639127285)
                      ·
                        rfl

theorem cell23_5373053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_5373053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373053 prefixEnd_5373053 := by exact prefixLift 5373053
  have htrace : WordTrace (prefixWord ++ tailWord_5373053) baseStart_5373053 baseEnd_5373053 := by
    simpa [prefixWord, tailWord_5373053, baseEnd_5373053] using wordTrace_append hprefix tailTrace_5373053
  have hstable : (prefixWord ++ tailWord_5373053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373053).length < 2 ^ (prefixWord ++ tailWord_5373053).sum := by decide
  have hdescent : baseEnd_5373053 < baseStart_5373053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373070 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5]
def baseStart_5373070 : Nat := 118140960795 + 5373070 * 2 ^ 59
def prefixEnd_5373070 : Nat := 4983230072969 + 3 ^ 40 * 5373070 * 2
def baseEnd_5373070 : Nat := 2758967500253398072614707

theorem tailTrace_5373070 : CollatzResearch.WordTrace tailWord_5373070 prefixEnd_5373070 2758967500253398072614707 := by
  unfold tailWord_5373070
  simp only [CollatzResearch.WordTrace]
  refine ⟨24496495330536564017934583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130647975096195008095651109 24496495330536564017934583)
  ·
    refine ⟨36744742995804846026901875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24496495330536564017934583 36744742995804846026901875)
    ·
      refine ⟨55117114493707269040352813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36744742995804846026901875 55117114493707269040352813)
      ·
        refine ⟨20668917935140225890132305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55117114493707269040352813 20668917935140225890132305)
        ·
          refine ⟨15501688451355169417599229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20668917935140225890132305 15501688451355169417599229)
          ·
            refine ⟨5813133169258188531599711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15501688451355169417599229 5813133169258188531599711)
            ·
              refine ⟨8719699753887282797399567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5813133169258188531599711 8719699753887282797399567)
              ·
                refine ⟨13079549630830924196099351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8719699753887282797399567 13079549630830924196099351)
                ·
                  refine ⟨19619324446246386294149027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13079549630830924196099351 19619324446246386294149027)
                  ·
                    refine ⟨29428986669369579441223541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19619324446246386294149027 29428986669369579441223541)
                    ·
                      refine ⟨2758967500253398072614707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29428986669369579441223541 2758967500253398072614707)
                      ·
                        rfl

theorem cell23_5373070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_5373070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373070 prefixEnd_5373070 := by exact prefixLift 5373070
  have htrace : WordTrace (prefixWord ++ tailWord_5373070) baseStart_5373070 baseEnd_5373070 := by
    simpa [prefixWord, tailWord_5373070, baseEnd_5373070] using wordTrace_append hprefix tailTrace_5373070
  have hstable : (prefixWord ++ tailWord_5373070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373070).length < 2 ^ (prefixWord ++ tailWord_5373070).sum := by decide
  have hdescent : baseEnd_5373070 < baseStart_5373070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373084 : List Nat := [2, 2, 3, 2, 1, 3, 1, 4, 1, 2, 2]
def baseStart_5373084 : Nat := 118140960795 + 5373084 * 2 ^ 59
def prefixEnd_5373084 : Nat := 4983230072969 + 3 ^ 40 * 5373084 * 2
def baseEnd_5373084 : Nat := 2758974688982561017839643

theorem tailTrace_5373084 : CollatzResearch.WordTrace tailWord_5373084 prefixEnd_5373084 2758974688982561017839643 := by
  unfold tailWord_5373084
  simp only [CollatzResearch.WordTrace]
  refine ⟨97986236633120896267243153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130648315510827861689657537 97986236633120896267243153)
  ·
    refine ⟨73489677474840672200432365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97986236633120896267243153 73489677474840672200432365)
    ·
      refine ⟨27558629053065252075162137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73489677474840672200432365 27558629053065252075162137)
      ·
        refine ⟨20668971789798939056371603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27558629053065252075162137 20668971789798939056371603)
        ·
          refine ⟨31003457684698408584557405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20668971789798939056371603 31003457684698408584557405)
          ·
            refine ⟨11626296631761903219209027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31003457684698408584557405 11626296631761903219209027)
            ·
              refine ⟨17439444947642854828813541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11626296631761903219209027 17439444947642854828813541)
              ·
                refine ⟨3269895927683035280402539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17439444947642854828813541 3269895927683035280402539)
                ·
                  refine ⟨4904843891524552920603809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3269895927683035280402539 4904843891524552920603809)
                  ·
                    refine ⟨3678632918643414690452857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4904843891524552920603809 3678632918643414690452857)
                    ·
                      refine ⟨2758974688982561017839643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3678632918643414690452857 2758974688982561017839643)
                      ·
                        rfl

theorem cell23_5373084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_5373084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373084 prefixEnd_5373084 := by exact prefixLift 5373084
  have htrace : WordTrace (prefixWord ++ tailWord_5373084) baseStart_5373084 baseEnd_5373084 := by
    simpa [prefixWord, tailWord_5373084, baseEnd_5373084] using wordTrace_append hprefix tailTrace_5373084
  have hstable : (prefixWord ++ tailWord_5373084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373084).length < 2 ^ (prefixWord ++ tailWord_5373084).sum := by decide
  have hdescent : baseEnd_5373084 < baseStart_5373084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373090 : List Nat := [3, 3, 1, 3, 2, 2, 1, 8]
def baseStart_5373090 : Nat := 118140960795 + 5373090 * 2 ^ 59
def prefixEnd_5373090 : Nat := 4983230072969 + 3 ^ 40 * 5373090 * 2
def baseEnd_5373090 : Nat := 102184361846906962754245

theorem tailTrace_5373090 : CollatzResearch.WordTrace tailWord_5373090 prefixEnd_5373090 102184361846906962754245 := by
  unfold tailWord_5373090
  simp only [CollatzResearch.WordTrace]
  refine ⟨48993173026055013889801181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130648461402813370372803149 48993173026055013889801181)
  ·
    refine ⟨18372439884770630208675443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48993173026055013889801181 18372439884770630208675443)
    ·
      refine ⟨27558659827155945313013165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18372439884770630208675443 27558659827155945313013165)
      ·
        refine ⟨10334497435183479492379937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27558659827155945313013165 10334497435183479492379937)
        ·
          refine ⟨7750873076387609619284953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10334497435183479492379937 7750873076387609619284953)
          ·
            refine ⟨5813154807290707214463715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7750873076387609619284953 5813154807290707214463715)
            ·
              refine ⟨8719732210936060821695573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5813154807290707214463715 8719732210936060821695573)
              ·
                refine ⟨102184361846906962754245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8719732210936060821695573 102184361846906962754245)
                ·
                  rfl

theorem cell23_5373090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 8].length) (baseStart_5373090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373090 prefixEnd_5373090 := by exact prefixLift 5373090
  have htrace : WordTrace (prefixWord ++ tailWord_5373090) baseStart_5373090 baseEnd_5373090 := by
    simpa [prefixWord, tailWord_5373090, baseEnd_5373090] using wordTrace_append hprefix tailTrace_5373090
  have hstable : (prefixWord ++ tailWord_5373090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373090).length < 2 ^ (prefixWord ++ tailWord_5373090).sum := by decide
  have hdescent : baseEnd_5373090 < baseStart_5373090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373123 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 3, 4, 2]
def baseStart_5373123 : Nat := 118140960795 + 5373123 * 2 ^ 59
def prefixEnd_5373123 : Nat := 4983230072969 + 3 ^ 40 * 5373123 * 2
def baseEnd_5373123 : Nat := 2758994714728086365251963

theorem tailTrace_5373123 : CollatzResearch.WordTrace tailWord_5373123 prefixEnd_5373123 2758994714728086365251963 := by
  unfold tailWord_5373123
  simp only [CollatzResearch.WordTrace]
  refine ⟨195973895713100502195156023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130649263808733668130104015 195973895713100502195156023)
  ·
    refine ⟨293960843569650753292734035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195973895713100502195156023 293960843569650753292734035)
    ·
      refine ⟨440941265354476129939101053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293960843569650753292734035 440941265354476129939101053)
      ·
        refine ⟨165352974507928548727162895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 440941265354476129939101053 165352974507928548727162895)
        ·
          refine ⟨248029461761892823090744343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165352974507928548727162895 248029461761892823090744343)
          ·
            refine ⟨372044192642839234636116515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248029461761892823090744343 372044192642839234636116515)
            ·
              refine ⟨558066288964258851954174773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372044192642839234636116515 558066288964258851954174773)
              ·
                refine ⟨52318714590399267370703885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 558066288964258851954174773 52318714590399267370703885)
                ·
                  refine ⟨19619517971399725264013957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52318714590399267370703885 19619517971399725264013957)
                  ·
                    refine ⟨3678659619637448487002617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19619517971399725264013957 3678659619637448487002617)
                    ·
                      refine ⟨2758994714728086365251963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3678659619637448487002617 2758994714728086365251963)
                      ·
                        rfl

theorem cell23_5373123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 4, 2].length) (baseStart_5373123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373123 prefixEnd_5373123 := by exact prefixLift 5373123
  have htrace : WordTrace (prefixWord ++ tailWord_5373123) baseStart_5373123 baseEnd_5373123 := by
    simpa [prefixWord, tailWord_5373123, baseEnd_5373123] using wordTrace_append hprefix tailTrace_5373123
  have hstable : (prefixWord ++ tailWord_5373123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373123).length < 2 ^ (prefixWord ++ tailWord_5373123).sum := by decide
  have hdescent : baseEnd_5373123 < baseStart_5373123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373134 : List Nat := [4, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3]
def baseStart_5373134 : Nat := 118140960795 + 5373134 * 2 ^ 59
def prefixEnd_5373134 : Nat := 4983230072969 + 3 ^ 40 * 5373134 * 2
def baseEnd_5373134 : Nat := 2759000363015285822214413

theorem tailTrace_5373134 : CollatzResearch.WordTrace tailWord_5373134 prefixEnd_5373134 2759000363015285822214413 := by
  unfold tailWord_5373134
  simp only [CollatzResearch.WordTrace]
  refine ⟨24496787114507581384225807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130649531277373767382537637 24496787114507581384225807)
  ·
    refine ⟨36745180671761372076338711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24496787114507581384225807 36745180671761372076338711)
    ·
      refine ⟨55117771007642058114508067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36745180671761372076338711 55117771007642058114508067)
      ·
        refine ⟨82676656511463087171762101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55117771007642058114508067 82676656511463087171762101)
        ·
          refine ⟨7750936547949664422352697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82676656511463087171762101 7750936547949664422352697)
          ·
            refine ⟨5813202410962248316764523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7750936547949664422352697 5813202410962248316764523)
            ·
              refine ⟨8719803616443372475146785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5813202410962248316764523 8719803616443372475146785)
              ·
                refine ⟨6539852712332529356360089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8719803616443372475146785 6539852712332529356360089)
                ·
                  refine ⟨4904889534249397017270067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6539852712332529356360089 4904889534249397017270067)
                  ·
                    refine ⟨7357334301374095525905101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4904889534249397017270067 7357334301374095525905101)
                    ·
                      refine ⟨2759000363015285822214413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7357334301374095525905101 2759000363015285822214413)
                      ·
                        rfl

theorem cell23_5373134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_5373134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373134 prefixEnd_5373134 := by exact prefixLift 5373134
  have htrace : WordTrace (prefixWord ++ tailWord_5373134) baseStart_5373134 baseEnd_5373134 := by
    simpa [prefixWord, tailWord_5373134, baseEnd_5373134] using wordTrace_append hprefix tailTrace_5373134
  have hstable : (prefixWord ++ tailWord_5373134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373134).length < 2 ^ (prefixWord ++ tailWord_5373134).sum := by decide
  have hdescent : baseEnd_5373134 < baseStart_5373134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373153 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_5373153 : Nat := 118140960795 + 5373153 * 2 ^ 59
def prefixEnd_5373153 : Nat := 4983230072969 + 3 ^ 40 * 5373153 * 2
def baseEnd_5373153 : Nat := 2759010119147721247876825

theorem tailTrace_5373153 : CollatzResearch.WordTrace tailWord_5373153 prefixEnd_5373153 2759010119147721247876825 := by
  unfold tailWord_5373153
  simp only [CollatzResearch.WordTrace]
  refine ⟨195974989902991817318748113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130649993268661211545832075 195974989902991817318748113)
  ·
    refine ⟨146981242427243862989061085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195974989902991817318748113 146981242427243862989061085)
    ·
      refine ⟨55117965910216448620897907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146981242427243862989061085 55117965910216448620897907)
      ·
        refine ⟨82676948865324672931346861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55117965910216448620897907 82676948865324672931346861)
        ·
          refine ⟨31003855824496752349255073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82676948865324672931346861 31003855824496752349255073)
          ·
            refine ⟨23252891868372564261941305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31003855824496752349255073 23252891868372564261941305)
            ·
              refine ⟨17439668901279423196455979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23252891868372564261941305 17439668901279423196455979)
              ·
                refine ⟨26159503351919134794683969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17439668901279423196455979 26159503351919134794683969)
                ·
                  refine ⟨19619627513939351096012977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26159503351919134794683969 19619627513939351096012977)
                  ·
                    refine ⟨14714720635454513322009733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19619627513939351096012977 14714720635454513322009733)
                    ·
                      refine ⟨2759010119147721247876825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14714720635454513322009733 2759010119147721247876825)
                      ·
                        rfl

theorem cell23_5373153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_5373153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373153 prefixEnd_5373153 := by exact prefixLift 5373153
  have htrace : WordTrace (prefixWord ++ tailWord_5373153) baseStart_5373153 baseEnd_5373153 := by
    simpa [prefixWord, tailWord_5373153, baseEnd_5373153] using wordTrace_append hprefix tailTrace_5373153
  have hstable : (prefixWord ++ tailWord_5373153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373153).length < 2 ^ (prefixWord ++ tailWord_5373153).sum := by decide
  have hdescent : baseEnd_5373153 < baseStart_5373153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373193 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 2, 5]
def baseStart_5373193 : Nat := 118140960795 + 5373193 * 2 ^ 59
def prefixEnd_5373193 : Nat := 4983230072969 + 3 ^ 40 * 5373193 * 2
def baseEnd_5373193 : Nat := 919676886124633697125547

theorem tailTrace_5373193 : CollatzResearch.WordTrace tailWord_5373193 prefixEnd_5373193 919676886124633697125547 := by
  unfold tailWord_5373193
  simp only [CollatzResearch.WordTrace]
  refine ⟨195976448822846904150204233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130650965881897936100136155 195976448822846904150204233)
  ·
    refine ⟨146982336617135178112653175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195976448822846904150204233 146982336617135178112653175)
    ·
      refine ⟨220473504925702767168979763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146982336617135178112653175 220473504925702767168979763)
      ·
        refine ⟨330710257388554150753469645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220473504925702767168979763 330710257388554150753469645)
        ·
          refine ⟨124016346520707806532551117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330710257388554150753469645 124016346520707806532551117)
          ·
            refine ⟨46506129945265427449706669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124016346520707806532551117 46506129945265427449706669)
            ·
              refine ⟨17439798729474535293640001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46506129945265427449706669 17439798729474535293640001)
              ·
                refine ⟨13079849047105901470230001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17439798729474535293640001 13079849047105901470230001)
                ·
                  refine ⟨9809886785329426102672501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13079849047105901470230001 9809886785329426102672501)
                  ·
                    refine ⟨919676886124633697125547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9809886785329426102672501 919676886124633697125547)
                    ·
                      rfl

theorem cell23_5373193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 5].length) (baseStart_5373193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373193 prefixEnd_5373193 := by exact prefixLift 5373193
  have htrace : WordTrace (prefixWord ++ tailWord_5373193) baseStart_5373193 baseEnd_5373193 := by
    simpa [prefixWord, tailWord_5373193, baseEnd_5373193] using wordTrace_append hprefix tailTrace_5373193
  have hstable : (prefixWord ++ tailWord_5373193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373193).length < 2 ^ (prefixWord ++ tailWord_5373193).sum := by decide
  have hdescent : baseEnd_5373193 < baseStart_5373193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373337 : List Nat := [1, 2, 1, 2, 1, 6, 2, 2, 1, 1, 4]
def baseStart_5373337 : Nat := 118140960795 + 5373337 * 2 ^ 59
def prefixEnd_5373337 : Nat := 4983230072969 + 3 ^ 40 * 5373337 * 2
def baseEnd_5373337 : Nat := 2759104599588148527975979

theorem tailTrace_5373337 : CollatzResearch.WordTrace tailWord_5373337 prefixEnd_5373337 2759104599588148527975979 := by
  unfold tailWord_5373337
  simp only [CollatzResearch.WordTrace]
  refine ⟨195981700934325216743446265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130654467289550144495630843 195981700934325216743446265)
  ·
    refine ⟨146986275700743912557584699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195981700934325216743446265 146986275700743912557584699)
    ·
      refine ⟨220479413551115868836377049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146986275700743912557584699 220479413551115868836377049)
      ·
        refine ⟨165359560163336901627282787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220479413551115868836377049 165359560163336901627282787)
        ·
          refine ⟨248039340245005352440924181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165359560163336901627282787 248039340245005352440924181)
          ·
            refine ⟨11626844073984625895668321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 248039340245005352440924181 11626844073984625895668321)
            ·
              refine ⟨8720133055488469421751241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11626844073984625895668321 8720133055488469421751241)
              ·
                refine ⟨6540099791616352066313431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8720133055488469421751241 6540099791616352066313431)
                ·
                  refine ⟨9810149687424528099470147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6540099791616352066313431 9810149687424528099470147)
                  ·
                    refine ⟨14715224531136792149205221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9810149687424528099470147 14715224531136792149205221)
                    ·
                      refine ⟨2759104599588148527975979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14715224531136792149205221 2759104599588148527975979)
                      ·
                        rfl

theorem cell23_5373337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_5373337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373337 prefixEnd_5373337 := by exact prefixLift 5373337
  have htrace : WordTrace (prefixWord ++ tailWord_5373337) baseStart_5373337 baseEnd_5373337 := by
    simpa [prefixWord, tailWord_5373337, baseEnd_5373337] using wordTrace_append hprefix tailTrace_5373337
  have hstable : (prefixWord ++ tailWord_5373337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373337).length < 2 ^ (prefixWord ++ tailWord_5373337).sum := by decide
  have hdescent : baseEnd_5373337 < baseStart_5373337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373357 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_5373357 : Nat := 118140960795 + 5373357 * 2 ^ 59
def prefixEnd_5373357 : Nat := 4983230072969 + 3 ^ 40 * 5373357 * 2
def baseEnd_5373357 : Nat := 2759114869201238449725887

theorem tailTrace_5373357 : CollatzResearch.WordTrace tailWord_5373357 prefixEnd_5373357 2759114869201238449725887 := by
  unfold tailWord_5373357
  simp only [CollatzResearch.WordTrace]
  refine ⟨195982430394252760159174325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130654953596168506772782883 195982430394252760159174325)
  ·
    refine ⟨18373352849461196264922593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195982430394252760159174325 18373352849461196264922593)
    ·
      refine ⟨13780014637095897198691945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18373352849461196264922593 13780014637095897198691945)
      ·
        refine ⟨10335010977821922899018959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13780014637095897198691945 10335010977821922899018959)
        ·
          refine ⟨15502516466732884348528439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10335010977821922899018959 15502516466732884348528439)
          ·
            refine ⟨23253774700099326522792659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15502516466732884348528439 23253774700099326522792659)
            ·
              refine ⟨34880662050148989784188989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23253774700099326522792659 34880662050148989784188989)
              ·
                refine ⟨13080248268805871169070871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34880662050148989784188989 13080248268805871169070871)
                ·
                  refine ⟨19620372403208806753606307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13080248268805871169070871 19620372403208806753606307)
                  ·
                    refine ⟨29430558604813210130409461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19620372403208806753606307 29430558604813210130409461)
                    ·
                      refine ⟨2759114869201238449725887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29430558604813210130409461 2759114869201238449725887)
                      ·
                        rfl

theorem cell23_5373357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_5373357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373357 prefixEnd_5373357 := by exact prefixLift 5373357
  have htrace : WordTrace (prefixWord ++ tailWord_5373357) baseStart_5373357 baseEnd_5373357 := by
    simpa [prefixWord, tailWord_5373357, baseEnd_5373357] using wordTrace_append hprefix tailTrace_5373357
  have hstable : (prefixWord ++ tailWord_5373357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373357).length < 2 ^ (prefixWord ++ tailWord_5373357).sum := by decide
  have hdescent : baseEnd_5373357 < baseStart_5373357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373393 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_5373393 : Nat := 118140960795 + 5373393 * 2 ^ 59
def prefixEnd_5373393 : Nat := 4983230072969 + 3 ^ 40 * 5373393 * 2
def baseEnd_5373393 : Nat := 2759133354504800308875721

theorem tailTrace_5373393 : CollatzResearch.WordTrace tailWord_5373393 prefixEnd_5373393 2759133354504800308875721 := by
  unfold tailWord_5373393
  simp only [CollatzResearch.WordTrace]
  refine ⟨195983743422122338307484833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130655828948081558871656555 195983743422122338307484833)
  ·
    refine ⟨146987807566591753730613625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195983743422122338307484833 146987807566591753730613625)
    ·
      refine ⟨110240855674943815297960219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146987807566591753730613625 110240855674943815297960219)
      ·
        refine ⟨165361283512415722946940329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110240855674943815297960219 165361283512415722946940329)
        ·
          refine ⟨124020962634311792210205247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165361283512415722946940329 124020962634311792210205247)
          ·
            refine ⟨186031443951467688315307871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124020962634311792210205247 186031443951467688315307871)
            ·
              refine ⟨279047165927201532472961807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186031443951467688315307871 279047165927201532472961807)
              ·
                refine ⟨418570748890802298709442711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279047165927201532472961807 418570748890802298709442711)
                ·
                  refine ⟨627856123336203448064164067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 418570748890802298709442711 627856123336203448064164067)
                  ·
                    refine ⟨941784185004305172096246101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 627856123336203448064164067 941784185004305172096246101)
                    ·
                      refine ⟨2759133354504800308875721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 941784185004305172096246101 2759133354504800308875721)
                      ·
                        rfl

theorem cell23_5373393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_5373393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373393 prefixEnd_5373393 := by exact prefixLift 5373393
  have htrace : WordTrace (prefixWord ++ tailWord_5373393) baseStart_5373393 baseEnd_5373393 := by
    simpa [prefixWord, tailWord_5373393, baseEnd_5373393] using wordTrace_append hprefix tailTrace_5373393
  have hstable : (prefixWord ++ tailWord_5373393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373393).length < 2 ^ (prefixWord ++ tailWord_5373393).sum := by decide
  have hdescent : baseEnd_5373393 < baseStart_5373393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373450 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 9]
def baseStart_5373450 : Nat := 118140960795 + 5373450 * 2 ^ 59
def prefixEnd_5373450 : Nat := 4983230072969 + 3 ^ 40 * 5373450 * 2
def baseEnd_5373450 : Nat := 306573624766900731762551

theorem tailTrace_5373450 : CollatzResearch.WordTrace tailWord_5373450 prefixEnd_5373450 306573624766900731762551 := by
  unfold tailWord_5373450
  simp only [CollatzResearch.WordTrace]
  refine ⟨48996455595728959260577451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130657214921943891361539869 48996455595728959260577451)
  ·
    refine ⟨73494683393593438890866177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48996455595728959260577451 73494683393593438890866177)
    ·
      refine ⟨55121012545195079168149633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73494683393593438890866177 55121012545195079168149633)
      ·
        refine ⟨41340759408896309376112225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55121012545195079168149633 41340759408896309376112225)
        ·
          refine ⟨31005569556672232032084169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41340759408896309376112225 31005569556672232032084169)
          ·
            refine ⟨23254177167504174024063127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31005569556672232032084169 23254177167504174024063127)
            ·
              refine ⟨34881265751256261036094691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23254177167504174024063127 34881265751256261036094691)
              ·
                refine ⟨52321898626884391554142037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34881265751256261036094691 52321898626884391554142037)
                ·
                  refine ⟨306573624766900731762551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52321898626884391554142037 306573624766900731762551)
                  ·
                    rfl

theorem cell23_5373450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_5373450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373450 prefixEnd_5373450 := by exact prefixLift 5373450
  have htrace : WordTrace (prefixWord ++ tailWord_5373450) baseStart_5373450 baseEnd_5373450 := by
    simpa [prefixWord, tailWord_5373450, baseEnd_5373450] using wordTrace_append hprefix tailTrace_5373450
  have hstable : (prefixWord ++ tailWord_5373450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373450).length < 2 ^ (prefixWord ++ tailWord_5373450).sum := by decide
  have hdescent : baseEnd_5373450 < baseStart_5373450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373490 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_5373490 : Nat := 118140960795 + 5373490 * 2 ^ 59
def prefixEnd_5373490 : Nat := 4983230072969 + 3 ^ 40 * 5373490 * 2
def baseEnd_5373490 : Nat := 2759183162128286429362775

theorem tailTrace_5373490 : CollatzResearch.WordTrace tailWord_5373490 prefixEnd_5373490 2759183162128286429362775 := by
  unfold tailWord_5373490
  simp only [CollatzResearch.WordTrace]
  refine ⟨48996820325692730968441481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130658187535180615915843949 48996820325692730968441481)
  ·
    refine ⟨36747615244269548226331111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48996820325692730968441481 36747615244269548226331111)
    ·
      refine ⟨55121422866404322339496667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36747615244269548226331111 55121422866404322339496667)
      ·
        refine ⟨82682134299606483509245001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55121422866404322339496667 82682134299606483509245001)
        ·
          refine ⟨62011600724704862631933751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82682134299606483509245001 62011600724704862631933751)
          ·
            refine ⟨93017401087057293947900627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62011600724704862631933751 93017401087057293947900627)
            ·
              refine ⟨139526101630585940921850941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93017401087057293947900627 139526101630585940921850941)
              ·
                refine ⟨52322288111469727845694103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139526101630585940921850941 52322288111469727845694103)
                ·
                  refine ⟨78483432167204591768541155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52322288111469727845694103 78483432167204591768541155)
                  ·
                    refine ⟨117725148250806887652811733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78483432167204591768541155 117725148250806887652811733)
                    ·
                      refine ⟨2759183162128286429362775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117725148250806887652811733 2759183162128286429362775)
                      ·
                        rfl

theorem cell23_5373490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_5373490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373490 prefixEnd_5373490 := by exact prefixLift 5373490
  have htrace : WordTrace (prefixWord ++ tailWord_5373490) baseStart_5373490 baseEnd_5373490 := by
    simpa [prefixWord, tailWord_5373490, baseEnd_5373490] using wordTrace_append hprefix tailTrace_5373490
  have hstable : (prefixWord ++ tailWord_5373490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373490).length < 2 ^ (prefixWord ++ tailWord_5373490).sum := by decide
  have hdescent : baseEnd_5373490 < baseStart_5373490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373530 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_5373530 : Nat := 118140960795 + 5373530 * 2 ^ 59
def prefixEnd_5373530 : Nat := 4983230072969 + 3 ^ 40 * 5373530 * 2
def baseEnd_5373530 : Nat := 2759203701354466272862591

theorem tailTrace_5373530 : CollatzResearch.WordTrace tailWord_5373530 prefixEnd_5373530 2759203701354466272862591 := by
  unfold tailWord_5373530
  simp only [CollatzResearch.WordTrace]
  refine ⟨48997185055656502676305511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130659160148417340470148029 48997185055656502676305511)
  ·
    refine ⟨73495777583484754014458267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48997185055656502676305511 73495777583484754014458267)
    ·
      refine ⟨110243666375227131021687401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73495777583484754014458267 110243666375227131021687401)
      ·
        refine ⟨82682749781420348266265551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110243666375227131021687401 82682749781420348266265551)
        ·
          refine ⟨124024124672130522399398327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82682749781420348266265551 124024124672130522399398327)
          ·
            refine ⟨186036187008195783599097491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124024124672130522399398327 186036187008195783599097491)
            ·
              refine ⟨279054280512293675398646237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186036187008195783599097491 279054280512293675398646237)
              ·
                refine ⟨104645355192110128274492339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279054280512293675398646237 104645355192110128274492339)
                ·
                  refine ⟨156968032788165192411738509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104645355192110128274492339 156968032788165192411738509)
                  ·
                    refine ⟨58863012295561947154401941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156968032788165192411738509 58863012295561947154401941)
                    ·
                      refine ⟨2759203701354466272862591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58863012295561947154401941 2759203701354466272862591)
                      ·
                        rfl

theorem cell23_5373530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_5373530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373530 prefixEnd_5373530 := by exact prefixLift 5373530
  have htrace : WordTrace (prefixWord ++ tailWord_5373530) baseStart_5373530 baseEnd_5373530 := by
    simpa [prefixWord, tailWord_5373530, baseEnd_5373530] using wordTrace_append hprefix tailTrace_5373530
  have hstable : (prefixWord ++ tailWord_5373530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373530).length < 2 ^ (prefixWord ++ tailWord_5373530).sum := by decide
  have hdescent : baseEnd_5373530 < baseStart_5373530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373628 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 2, 3, 2]
def baseStart_5373628 : Nat := 118140960795 + 5373628 * 2 ^ 59
def prefixEnd_5373628 : Nat := 4983230072969 + 3 ^ 40 * 5373628 * 2
def baseEnd_5373628 : Nat := 2759254022458606889437141

theorem tailTrace_5373628 : CollatzResearch.WordTrace tailWord_5373628 prefixEnd_5373628 2759254022458606889437141 := by
  unfold tailWord_5373628
  simp only [CollatzResearch.WordTrace]
  refine ⟨97996157288135486721144769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130661543050847315628193025 97996157288135486721144769)
  ·
    refine ⟨73497117966101615040858577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97996157288135486721144769 73497117966101615040858577)
    ·
      refine ⟨55122838474576211280643933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73497117966101615040858577 55122838474576211280643933)
      ·
        refine ⟨20671064427966079230241475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55122838474576211280643933 20671064427966079230241475)
        ·
          refine ⟨31006596641949118845362213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20671064427966079230241475 31006596641949118845362213)
          ·
            refine ⟨5813736870365459783505415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31006596641949118845362213 5813736870365459783505415)
            ·
              refine ⟨8720605305548189675258123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5813736870365459783505415 8720605305548189675258123)
              ·
                refine ⟨13080907958322284512887185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8720605305548189675258123 13080907958322284512887185)
                ·
                  refine ⟨9810680968741713384665389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13080907958322284512887185 9810680968741713384665389)
                  ·
                    refine ⟨3679005363278142519249521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9810680968741713384665389 3679005363278142519249521)
                    ·
                      refine ⟨2759254022458606889437141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3679005363278142519249521 2759254022458606889437141)
                      ·
                        rfl

theorem cell23_5373628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_5373628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373628 prefixEnd_5373628 := by exact prefixLift 5373628
  have htrace : WordTrace (prefixWord ++ tailWord_5373628) baseStart_5373628 baseEnd_5373628 := by
    simpa [prefixWord, tailWord_5373628, baseEnd_5373628] using wordTrace_append hprefix tailTrace_5373628
  have hstable : (prefixWord ++ tailWord_5373628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373628).length < 2 ^ (prefixWord ++ tailWord_5373628).sum := by decide
  have hdescent : baseEnd_5373628 < baseStart_5373628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373658 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2]
def baseStart_5373658 : Nat := 118140960795 + 5373658 * 2 ^ 59
def prefixEnd_5373658 : Nat := 4983230072969 + 3 ^ 40 * 5373658 * 2
def baseEnd_5373658 : Nat := 2759269426878241772062003

theorem tailTrace_5373658 : CollatzResearch.WordTrace tailWord_5373658 prefixEnd_5373658 2759269426878241772062003 := by
  unfold tailWord_5373658
  simp only [CollatzResearch.WordTrace]
  refine ⟨48998352191540572141470407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130662272510774859043921085 48998352191540572141470407)
  ·
    refine ⟨73497528287310858212205611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48998352191540572141470407 73497528287310858212205611)
    ·
      refine ⟨110246292430966287318308417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73497528287310858212205611 110246292430966287318308417)
      ·
        refine ⟨82684719323224715488731313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110246292430966287318308417 82684719323224715488731313)
        ·
          refine ⟨62013539492418536616548485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82684719323224715488731313 62013539492418536616548485)
          ·
            refine ⟨11627538654828475615602841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62013539492418536616548485 11627538654828475615602841)
            ·
              refine ⟨8720653991121356711702131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11627538654828475615602841 8720653991121356711702131)
              ·
                refine ⟨13080980986682035067553197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8720653991121356711702131 13080980986682035067553197)
                ·
                  refine ⟨4905367870005763150332449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13080980986682035067553197 4905367870005763150332449)
                  ·
                    refine ⟨3679025902504322362749337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4905367870005763150332449 3679025902504322362749337)
                    ·
                      refine ⟨2759269426878241772062003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3679025902504322362749337 2759269426878241772062003)
                      ·
                        rfl

theorem cell23_5373658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_5373658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373658 prefixEnd_5373658 := by exact prefixLift 5373658
  have htrace : WordTrace (prefixWord ++ tailWord_5373658) baseStart_5373658 baseEnd_5373658 := by
    simpa [prefixWord, tailWord_5373658, baseEnd_5373658] using wordTrace_append hprefix tailTrace_5373658
  have hstable : (prefixWord ++ tailWord_5373658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373658).length < 2 ^ (prefixWord ++ tailWord_5373658).sum := by decide
  have hdescent : baseEnd_5373658 < baseStart_5373658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373671 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5373671 : Nat := 118140960795 + 5373671 * 2 ^ 59
def prefixEnd_5373671 : Nat := 4983230072969 + 3 ^ 40 * 5373671 * 2
def baseEnd_5373671 : Nat := 2759276102126750221199443

theorem tailTrace_5373671 : CollatzResearch.WordTrace tailWord_5373671 prefixEnd_5373671 2759276102126750221199443 := by
  unfold tailWord_5373671
  simp only [CollatzResearch.WordTrace]
  refine ⟨195993882915115191786104867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130662588610076794524069911 195993882915115191786104867)
  ·
    refine ⟨293990824372672787679157301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195993882915115191786104867 293990824372672787679157301)
    ·
      refine ⟨27561639784938073844920997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 293990824372672787679157301 27561639784938073844920997)
      ·
        refine ⟨5167807459675888845922687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27561639784938073844920997 5167807459675888845922687)
        ·
          refine ⟨7751711189513833268884031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5167807459675888845922687 7751711189513833268884031)
          ·
            refine ⟨11627566784270749903326047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7751711189513833268884031 11627566784270749903326047)
            ·
              refine ⟨17441350176406124854989071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11627566784270749903326047 17441350176406124854989071)
              ·
                refine ⟨26162025264609187282483607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17441350176406124854989071 26162025264609187282483607)
                ·
                  refine ⟨39243037896913780923725411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26162025264609187282483607 39243037896913780923725411)
                  ·
                    refine ⟨58864556845370671385588117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39243037896913780923725411 58864556845370671385588117)
                    ·
                      refine ⟨2759276102126750221199443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58864556845370671385588117 2759276102126750221199443)
                      ·
                        rfl

theorem cell23_5373671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5373671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373671 prefixEnd_5373671 := by exact prefixLift 5373671
  have htrace : WordTrace (prefixWord ++ tailWord_5373671) baseStart_5373671 baseEnd_5373671 := by
    simpa [prefixWord, tailWord_5373671, baseEnd_5373671] using wordTrace_append hprefix tailTrace_5373671
  have hstable : (prefixWord ++ tailWord_5373671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373671).length < 2 ^ (prefixWord ++ tailWord_5373671).sum := by decide
  have hdescent : baseEnd_5373671 < baseStart_5373671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373687 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_5373687 : Nat := 118140960795 + 5373687 * 2 ^ 59
def prefixEnd_5373687 : Nat := 4983230072969 + 3 ^ 40 * 5373687 * 2
def baseEnd_5373687 : Nat := 2759284317817222158599369

theorem tailTrace_5373687 : CollatzResearch.WordTrace tailWord_5373687 prefixEnd_5373687 2759284317817222158599369 := by
  unfold tailWord_5373687
  simp only [CollatzResearch.WordTrace]
  refine ⟨195994466483057226518687315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130662977655371484345791543 195994466483057226518687315)
  ·
    refine ⟨293991699724585839778030973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195994466483057226518687315 293991699724585839778030973)
    ·
      refine ⟨110246887396719689916761615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293991699724585839778030973 110246887396719689916761615)
      ·
        refine ⟨165370331095079534875142423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110246887396719689916761615 165370331095079534875142423)
        ·
          refine ⟨248055496642619302312713635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165370331095079534875142423 248055496642619302312713635)
          ·
            refine ⟨372083244963928953469070453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248055496642619302312713635 372083244963928953469070453)
            ·
              refine ⟨34882804215368339387725355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 372083244963928953469070453 34882804215368339387725355)
              ·
                refine ⟨52324206323052509081588033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34882804215368339387725355 52324206323052509081588033)
                ·
                  refine ⟨39243154742289381811191025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52324206323052509081588033 39243154742289381811191025)
                  ·
                    refine ⟨29432366056717036358393269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39243154742289381811191025 29432366056717036358393269)
                    ·
                      refine ⟨2759284317817222158599369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29432366056717036358393269 2759284317817222158599369)
                      ·
                        rfl

theorem cell23_5373687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_5373687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373687 prefixEnd_5373687 := by exact prefixLift 5373687
  have htrace : WordTrace (prefixWord ++ tailWord_5373687) baseStart_5373687 baseEnd_5373687 := by
    simpa [prefixWord, tailWord_5373687, baseEnd_5373687] using wordTrace_append hprefix tailTrace_5373687
  have hstable : (prefixWord ++ tailWord_5373687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373687).length < 2 ^ (prefixWord ++ tailWord_5373687).sum := by decide
  have hdescent : baseEnd_5373687 < baseStart_5373687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373707 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 4, 6]
def baseStart_5373707 : Nat := 118140960795 + 5373707 * 2 ^ 59
def prefixEnd_5373707 : Nat := 4983230072969 + 3 ^ 40 * 5373707 * 2
def baseEnd_5373707 : Nat := 919764862476770693449759

theorem tailTrace_5373707 : CollatzResearch.WordTrace tailWord_5373707 prefixEnd_5373707 919764862476770693449759 := by
  unfold tailWord_5373707
  simp only [CollatzResearch.WordTrace]
  refine ⟨195995195942984769934415375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130663463961989846622943583 195995195942984769934415375)
  ·
    refine ⟨293992793914477154901623063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195995195942984769934415375 293992793914477154901623063)
    ·
      refine ⟨440989190871715732352434595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293992793914477154901623063 440989190871715732352434595)
      ·
        refine ⟨661483786307573598528651893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440989190871715732352434595 661483786307573598528651893)
        ·
          refine ⟨62014104966335024862061115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 661483786307573598528651893 62014104966335024862061115)
          ·
            refine ⟨93021157449502537293091673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62014104966335024862061115 93021157449502537293091673)
            ·
              refine ⟨69765868087126902969818755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93021157449502537293091673 69765868087126902969818755)
              ·
                refine ⟨104648802130690354454728133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69765868087126902969818755 104648802130690354454728133)
                ·
                  refine ⟨19621650399504441460261525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104648802130690354454728133 19621650399504441460261525)
                  ·
                    refine ⟨919764862476770693449759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19621650399504441460261525 919764862476770693449759)
                    ·
                      rfl

theorem cell23_5373707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 6].length) (baseStart_5373707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373707 prefixEnd_5373707 := by exact prefixLift 5373707
  have htrace : WordTrace (prefixWord ++ tailWord_5373707) baseStart_5373707 baseEnd_5373707 := by
    simpa [prefixWord, tailWord_5373707, baseEnd_5373707] using wordTrace_append hprefix tailTrace_5373707
  have hstable : (prefixWord ++ tailWord_5373707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373707).length < 2 ^ (prefixWord ++ tailWord_5373707).sum := by decide
  have hdescent : baseEnd_5373707 < baseStart_5373707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373748 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_5373748 : Nat := 118140960795 + 5373748 * 2 ^ 59
def prefixEnd_5373748 : Nat := 4983230072969 + 3 ^ 40 * 5373748 * 2
def baseEnd_5373748 : Nat := 2759315640137146419936589

theorem tailTrace_5373748 : CollatzResearch.WordTrace tailWord_5373748 prefixEnd_5373748 2759315640137146419936589 := by
  unfold tailWord_5373748
  simp only [CollatzResearch.WordTrace]
  refine ⟨97998345667918116968328949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130664460890557489291105265 97998345667918116968328949)
  ·
    refine ⟨9187344906367323465780839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97998345667918116968328949 9187344906367323465780839)
    ·
      refine ⟨13781017359550985198671259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9187344906367323465780839 13781017359550985198671259)
      ·
        refine ⟨20671526039326477798006889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13781017359550985198671259 20671526039326477798006889)
        ·
          refine ⟨15503644529494858348505167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20671526039326477798006889 15503644529494858348505167)
          ·
            refine ⟨23255466794242287522757751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15503644529494858348505167 23255466794242287522757751)
            ·
              refine ⟨34883200191363431284136627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23255466794242287522757751 34883200191363431284136627)
              ·
                refine ⟨52324800287045146926204941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34883200191363431284136627 52324800287045146926204941)
                ·
                  refine ⟨19621800107641930097326853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52324800287045146926204941 19621800107641930097326853)
                  ·
                    refine ⟨3679087520182861893248785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19621800107641930097326853 3679087520182861893248785)
                    ·
                      refine ⟨2759315640137146419936589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3679087520182861893248785 2759315640137146419936589)
                      ·
                        rfl

theorem cell23_5373748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_5373748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373748 prefixEnd_5373748 := by exact prefixLift 5373748
  have htrace : WordTrace (prefixWord ++ tailWord_5373748) baseStart_5373748 baseEnd_5373748 := by
    simpa [prefixWord, tailWord_5373748, baseEnd_5373748] using wordTrace_append hprefix tailTrace_5373748
  have hstable : (prefixWord ++ tailWord_5373748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373748).length < 2 ^ (prefixWord ++ tailWord_5373748).sum := by decide
  have hdescent : baseEnd_5373748 < baseStart_5373748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373781 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_5373781 : Nat := 118140960795 + 5373781 * 2 ^ 59
def prefixEnd_5373781 : Nat := 4983230072969 + 3 ^ 40 * 5373781 * 2
def baseEnd_5373781 : Nat := 2759332584998744790823937

theorem tailTrace_5373781 : CollatzResearch.WordTrace tailWord_5373781 prefixEnd_5373781 2759332584998744790823937 := by
  unfold tailWord_5373781
  simp only [CollatzResearch.WordTrace]
  refine ⟨195997894944716680572609197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130665263296477787048406131 195997894944716680572609197)
  ·
    refine ⟨73499210604268755214728449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195997894944716680572609197 73499210604268755214728449)
    ·
      refine ⟨55124407953201566411046337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73499210604268755214728449 55124407953201566411046337)
      ·
        refine ⟨41343305964901174808284753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55124407953201566411046337 41343305964901174808284753)
        ·
          refine ⟨31007479473675881106213565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41343305964901174808284753 31007479473675881106213565)
          ·
            refine ⟨11627804802628455414830087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31007479473675881106213565 11627804802628455414830087)
            ·
              refine ⟨17441707203942683122245131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11627804802628455414830087 17441707203942683122245131)
              ·
                refine ⟨26162560805914024683367697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17441707203942683122245131 26162560805914024683367697)
                ·
                  refine ⟨19621920604435518512525773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26162560805914024683367697 19621920604435518512525773)
                  ·
                    refine ⟨7358220226663319442197165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19621920604435518512525773 7358220226663319442197165)
                    ·
                      refine ⟨2759332584998744790823937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7358220226663319442197165 2759332584998744790823937)
                      ·
                        rfl

theorem cell23_5373781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_5373781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373781 prefixEnd_5373781 := by exact prefixLift 5373781
  have htrace : WordTrace (prefixWord ++ tailWord_5373781) baseStart_5373781 baseEnd_5373781 := by
    simpa [prefixWord, tailWord_5373781, baseEnd_5373781] using wordTrace_append hprefix tailTrace_5373781
  have hstable : (prefixWord ++ tailWord_5373781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373781).length < 2 ^ (prefixWord ++ tailWord_5373781).sum := by decide
  have hdescent : baseEnd_5373781 < baseStart_5373781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373787 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 8]
def baseStart_5373787 : Nat := 118140960795 + 5373787 * 2 ^ 59
def prefixEnd_5373787 : Nat := 4983230072969 + 3 ^ 40 * 5373787 * 2
def baseEnd_5373787 : Nat := 2759335665882671767348909

theorem tailTrace_5373787 : CollatzResearch.WordTrace tailWord_5373787 prefixEnd_5373787 2759335665882671767348909 := by
  unfold tailWord_5373787
  simp only [CollatzResearch.WordTrace]
  refine ⟨195998113782694943597327615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130665409188463295731551743 195998113782694943597327615)
  ·
    refine ⟨293997170674042415395991423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195998113782694943597327615 293997170674042415395991423)
    ·
      refine ⟨440995756011063623093987135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293997170674042415395991423 440995756011063623093987135)
      ·
        refine ⟨661493634016595434640980703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440995756011063623093987135 661493634016595434640980703)
        ·
          refine ⟨992240451024893151961471055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 661493634016595434640980703 992240451024893151961471055)
          ·
            refine ⟨1488360676537339727942206583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992240451024893151961471055 1488360676537339727942206583)
            ·
              refine ⟨2232541014806009591913309875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1488360676537339727942206583 2232541014806009591913309875)
              ·
                refine ⟨3348811522209014387869964813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2232541014806009591913309875 3348811522209014387869964813)
                ·
                  refine ⟨1255804320828380395451236805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3348811522209014387869964813 1255804320828380395451236805)
                  ·
                    refine ⟨235463310155321324147106901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1255804320828380395451236805 235463310155321324147106901)
                    ·
                      refine ⟨2759335665882671767348909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 235463310155321324147106901 2759335665882671767348909)
                      ·
                        rfl

theorem cell23_5373787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_5373787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373787 prefixEnd_5373787 := by exact prefixLift 5373787
  have htrace : WordTrace (prefixWord ++ tailWord_5373787) baseStart_5373787 baseEnd_5373787 := by
    simpa [prefixWord, tailWord_5373787, baseEnd_5373787] using wordTrace_append hprefix tailTrace_5373787
  have hstable : (prefixWord ++ tailWord_5373787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373787).length < 2 ^ (prefixWord ++ tailWord_5373787).sum := by decide
  have hdescent : baseEnd_5373787 < baseStart_5373787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373911 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 4]
def baseStart_5373911 : Nat := 118140960795 + 5373911 * 2 ^ 59
def prefixEnd_5373911 : Nat := 4983230072969 + 3 ^ 40 * 5373911 * 2
def baseEnd_5373911 : Nat := 2759399337483829282198339

theorem tailTrace_5373911 : CollatzResearch.WordTrace tailWord_5373911 prefixEnd_5373911 2759399337483829282198339 := by
  unfold tailWord_5373911
  simp only [CollatzResearch.WordTrace]
  refine ⟨196002636434245712774841587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130668424289497141849894391 196002636434245712774841587)
  ·
    refine ⟨294003954651368569162262381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196002636434245712774841587 294003954651368569162262381)
    ·
      refine ⟨110251482994263213435848393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294003954651368569162262381 110251482994263213435848393)
      ·
        refine ⟨82688612245697410076886295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110251482994263213435848393 82688612245697410076886295)
        ·
          refine ⟨124032918368546115115329443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82688612245697410076886295 124032918368546115115329443)
          ·
            refine ⟨186049377552819172672994165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124032918368546115115329443 186049377552819172672994165)
            ·
              refine ⟨17442129145576797438093203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 186049377552819172672994165 17442129145576797438093203)
              ·
                refine ⟨26163193718365196157139805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17442129145576797438093203 26163193718365196157139805)
                ·
                  refine ⟨9811197644386948558927427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26163193718365196157139805 9811197644386948558927427)
                  ·
                    refine ⟨14716796466580422838391141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9811197644386948558927427 14716796466580422838391141)
                    ·
                      refine ⟨2759399337483829282198339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14716796466580422838391141 2759399337483829282198339)
                      ·
                        rfl

theorem cell23_5373911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_5373911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373911 prefixEnd_5373911 := by exact prefixLift 5373911
  have htrace : WordTrace (prefixWord ++ tailWord_5373911) baseStart_5373911 baseEnd_5373911 := by
    simpa [prefixWord, tailWord_5373911, baseEnd_5373911] using wordTrace_append hprefix tailTrace_5373911
  have hstable : (prefixWord ++ tailWord_5373911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373911).length < 2 ^ (prefixWord ++ tailWord_5373911).sum := by decide
  have hdescent : baseEnd_5373911 < baseStart_5373911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373921 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 6, 4]
def baseStart_5373921 : Nat := 118140960795 + 5373921 * 2 ^ 59
def prefixEnd_5373921 : Nat := 4983230072969 + 3 ^ 40 * 5373921 * 2
def baseEnd_5373921 : Nat := 919801490763458081024431

theorem tailTrace_5373921 : CollatzResearch.WordTrace tailWord_5373921 prefixEnd_5373921 919801490763458081024431 := by
  unfold tailWord_5373921
  simp only [CollatzResearch.WordTrace]
  refine ⟨196003001164209484482705617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130668667442806322988470411 196003001164209484482705617)
  ·
    refine ⟨147002250873157113362029213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 196003001164209484482705617 147002250873157113362029213)
    ·
      refine ⟨55125844077433917510760955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147002250873157113362029213 55125844077433917510760955)
      ·
        refine ⟨82688766116150876266141433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55125844077433917510760955 82688766116150876266141433)
        ·
          refine ⟨62016574587113157199606075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82688766116150876266141433 62016574587113157199606075)
          ·
            refine ⟨93024861880669735799409113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62016574587113157199606075 93024861880669735799409113)
            ·
              refine ⟨69768646410502301849556835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93024861880669735799409113 69768646410502301849556835)
              ·
                refine ⟨104652969615753452774335253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69768646410502301849556835 104652969615753452774335253)
                ·
                  refine ⟨4905607950738443098796965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104652969615753452774335253 4905607950738443098796965)
                  ·
                    refine ⟨919801490763458081024431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4905607950738443098796965 919801490763458081024431)
                    ·
                      rfl

theorem cell23_5373921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_5373921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373921 prefixEnd_5373921 := by exact prefixLift 5373921
  have htrace : WordTrace (prefixWord ++ tailWord_5373921) baseStart_5373921 baseEnd_5373921 := by
    simpa [prefixWord, tailWord_5373921, baseEnd_5373921] using wordTrace_append hprefix tailTrace_5373921
  have hstable : (prefixWord ++ tailWord_5373921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373921).length < 2 ^ (prefixWord ++ tailWord_5373921).sum := by decide
  have hdescent : baseEnd_5373921 < baseStart_5373921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373962 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 3, 2, 2]
def baseStart_5373962 : Nat := 118140960795 + 5373962 * 2 ^ 59
def prefixEnd_5373962 : Nat := 4983230072969 + 3 ^ 40 * 5373962 * 2
def baseEnd_5373962 : Nat := 2759425524997208582660605

theorem tailTrace_5373962 : CollatzResearch.WordTrace tailWord_5373962 prefixEnd_5373962 2759425524997208582660605 := by
  unfold tailWord_5373962
  simp only [CollatzResearch.WordTrace]
  refine ⟨49001124139265237121237035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130669664371373965656632093 49001124139265237121237035)
  ·
    refine ⟨73501686208897855681855553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49001124139265237121237035 73501686208897855681855553)
    ·
      refine ⟨55126264656673391761391665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73501686208897855681855553 55126264656673391761391665)
      ·
        refine ⟨41344698492505043821043749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55126264656673391761391665 41344698492505043821043749)
        ·
          refine ⟨7752130967344695716445703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41344698492505043821043749 7752130967344695716445703)
          ·
            refine ⟨11628196451017043574668555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7752130967344695716445703 11628196451017043574668555)
            ·
              refine ⟨17442294676525565362002833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11628196451017043574668555 17442294676525565362002833)
              ·
                refine ⟨13081721007394174021502125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17442294676525565362002833 13081721007394174021502125)
                ·
                  refine ⟨4905645377772815258063297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13081721007394174021502125 4905645377772815258063297)
                  ·
                    refine ⟨3679234033329611443547473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4905645377772815258063297 3679234033329611443547473)
                    ·
                      refine ⟨2759425524997208582660605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3679234033329611443547473 2759425524997208582660605)
                      ·
                        rfl

theorem cell23_5373962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_5373962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373962 prefixEnd_5373962 := by exact prefixLift 5373962
  have htrace : WordTrace (prefixWord ++ tailWord_5373962) baseStart_5373962 baseEnd_5373962 := by
    simpa [prefixWord, tailWord_5373962, baseEnd_5373962] using wordTrace_append hprefix tailTrace_5373962
  have hstable : (prefixWord ++ tailWord_5373962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373962).length < 2 ^ (prefixWord ++ tailWord_5373962).sum := by decide
  have hdescent : baseEnd_5373962 < baseStart_5373962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5373978 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3]
def baseStart_5373978 : Nat := 118140960795 + 5373978 * 2 ^ 59
def prefixEnd_5373978 : Nat := 4983230072969 + 3 ^ 40 * 5373978 * 2
def baseEnd_5373978 : Nat := 2759433740687680520060531

theorem tailTrace_5373978 : CollatzResearch.WordTrace tailWord_5373978 prefixEnd_5373978 2759433740687680520060531 := by
  unfold tailWord_5373978
  simp only [CollatzResearch.WordTrace]
  refine ⟨49001270031250745804382647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130670053416668655478353725 49001270031250745804382647)
  ·
    refine ⟨73501905046876118706573971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49001270031250745804382647 73501905046876118706573971)
    ·
      refine ⟨110252857570314178059860957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73501905046876118706573971 110252857570314178059860957)
      ·
        refine ⟨41344821588867816772447859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110252857570314178059860957 41344821588867816772447859)
        ·
          refine ⟨62017232383301725158671789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41344821588867816772447859 62017232383301725158671789)
          ·
            refine ⟨23256462143738146934501921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62017232383301725158671789 23256462143738146934501921)
            ·
              refine ⟨17442346607803610200876441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23256462143738146934501921 17442346607803610200876441)
              ·
                refine ⟨13081759955852707650657331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17442346607803610200876441 13081759955852707650657331)
                ·
                  refine ⟨19622639933779061475985997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13081759955852707650657331 19622639933779061475985997)
                  ·
                    refine ⟨7358489975167148053494749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19622639933779061475985997 7358489975167148053494749)
                    ·
                      refine ⟨2759433740687680520060531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7358489975167148053494749 2759433740687680520060531)
                      ·
                        rfl

theorem cell23_5373978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_5373978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5373978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5373978 prefixEnd_5373978 := by exact prefixLift 5373978
  have htrace : WordTrace (prefixWord ++ tailWord_5373978) baseStart_5373978 baseEnd_5373978 := by
    simpa [prefixWord, tailWord_5373978, baseEnd_5373978] using wordTrace_append hprefix tailTrace_5373978
  have hstable : (prefixWord ++ tailWord_5373978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5373978).length < 2 ^ (prefixWord ++ tailWord_5373978).sum := by decide
  have hdescent : baseEnd_5373978 < baseStart_5373978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5373978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374012 : List Nat := [2, 2, 2, 2, 2, 1, 5, 1, 2, 1, 3]
def baseStart_5374012 : Nat := 118140960795 + 5374012 * 2 ^ 59
def prefixEnd_5374012 : Nat := 4983230072969 + 3 ^ 40 * 5374012 * 2
def baseEnd_5374012 : Nat := 2759451199029933387035375

theorem tailTrace_5374012 : CollatzResearch.WordTrace tailWord_5374012 prefixEnd_5374012 2759451199029933387035375 := by
  unfold tailWord_5374012
  simp only [CollatzResearch.WordTrace]
  refine ⟨98003160103439903512134145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130670880137919871349512193 98003160103439903512134145)
  ·
    refine ⟨73502370077579927634100609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98003160103439903512134145 73502370077579927634100609)
    ·
      refine ⟨55126777558184945725575457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73502370077579927634100609 55126777558184945725575457)
      ·
        refine ⟨41345083168638709294181593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55126777558184945725575457 41345083168638709294181593)
        ·
          refine ⟨31008812376479031970636195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41345083168638709294181593 31008812376479031970636195)
          ·
            refine ⟨46513218564718547955954293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31008812376479031970636195 46513218564718547955954293)
            ·
              refine ⟨4360614240442363870870715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46513218564718547955954293 4360614240442363870870715)
              ·
                refine ⟨6540921360663545806306073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4360614240442363870870715 6540921360663545806306073)
                ·
                  refine ⟨4905691020497659354729555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6540921360663545806306073 4905691020497659354729555)
                  ·
                    refine ⟨7358536530746489032094333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4905691020497659354729555 7358536530746489032094333)
                    ·
                      refine ⟨2759451199029933387035375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7358536530746489032094333 2759451199029933387035375)
                      ·
                        rfl

theorem cell23_5374012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_5374012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374012 prefixEnd_5374012 := by exact prefixLift 5374012
  have htrace : WordTrace (prefixWord ++ tailWord_5374012) baseStart_5374012 baseEnd_5374012 := by
    simpa [prefixWord, tailWord_5374012, baseEnd_5374012] using wordTrace_append hprefix tailTrace_5374012
  have hstable : (prefixWord ++ tailWord_5374012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374012).length < 2 ^ (prefixWord ++ tailWord_5374012).sum := by decide
  have hdescent : baseEnd_5374012 < baseStart_5374012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374021 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_5374021 : Nat := 118140960795 + 5374021 * 2 ^ 59
def prefixEnd_5374021 : Nat := 4983230072969 + 3 ^ 40 * 5374021 * 2
def baseEnd_5374021 : Nat := 2759455820355823851822833

theorem tailTrace_5374021 : CollatzResearch.WordTrace tailWord_5374021 prefixEnd_5374021 2759455820355823851822833 := by
  unfold tailWord_5374021
  simp only [CollatzResearch.WordTrace]
  refine ⟨196006648463847201561345917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130671098975898134374230611 196006648463847201561345917)
  ·
    refine ⟨73502493173942700585504719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196006648463847201561345917 73502493173942700585504719)
    ·
      refine ⟨110253739760914050878257079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73502493173942700585504719 110253739760914050878257079)
      ·
        refine ⟨165380609641371076317385619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110253739760914050878257079 165380609641371076317385619)
        ·
          refine ⟨248070914462056614476078429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165380609641371076317385619 248070914462056614476078429)
          ·
            refine ⟨93026592923271230428529411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 248070914462056614476078429 93026592923271230428529411)
            ·
              refine ⟨139539889384906845642794117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93026592923271230428529411 139539889384906845642794117)
              ·
                refine ⟨26163729259670033558023897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139539889384906845642794117 26163729259670033558023897)
                ·
                  refine ⟨19622796944752525168517923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26163729259670033558023897 19622796944752525168517923)
                  ·
                    refine ⟨29434195417128787752776885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19622796944752525168517923 29434195417128787752776885)
                    ·
                      refine ⟨2759455820355823851822833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29434195417128787752776885 2759455820355823851822833)
                      ·
                        rfl

theorem cell23_5374021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_5374021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374021 prefixEnd_5374021 := by exact prefixLift 5374021
  have htrace : WordTrace (prefixWord ++ tailWord_5374021) baseStart_5374021 baseEnd_5374021 := by
    simpa [prefixWord, tailWord_5374021, baseEnd_5374021] using wordTrace_append hprefix tailTrace_5374021
  have hstable : (prefixWord ++ tailWord_5374021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374021).length < 2 ^ (prefixWord ++ tailWord_5374021).sum := by decide
  have hdescent : baseEnd_5374021 < baseStart_5374021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374098 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_5374098 : Nat := 118140960795 + 5374098 * 2 ^ 59
def prefixEnd_5374098 : Nat := 4983230072969 + 3 ^ 40 * 5374098 * 2
def baseEnd_5374098 : Nat := 2759495358366220050559979

theorem tailTrace_5374098 : CollatzResearch.WordTrace tailWord_5374098 prefixEnd_5374098 2759495358366220050559979 := by
  unfold tailWord_5374098
  simp only [CollatzResearch.WordTrace]
  refine ⟨49002364221142060927974737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130672971256378829141265965 49002364221142060927974737)
  ·
    refine ⟨36751773165856545695981053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49002364221142060927974737 36751773165856545695981053)
    ·
      refine ⟨13781914937196204635992895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36751773165856545695981053 13781914937196204635992895)
      ·
        refine ⟨20672872405794306953989343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13781914937196204635992895 20672872405794306953989343)
        ·
          refine ⟨31009308608691460430984015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20672872405794306953989343 31009308608691460430984015)
          ·
            refine ⟨46513962913037190646476023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31009308608691460430984015 46513962913037190646476023)
            ·
              refine ⟨69770944369555785969714035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46513962913037190646476023 69770944369555785969714035)
              ·
                refine ⟨104656416554333678954571053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69770944369555785969714035 104656416554333678954571053)
                ·
                  refine ⟨39246156207875129607964145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104656416554333678954571053 39246156207875129607964145)
                  ·
                    refine ⟨29434617155906347205973109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39246156207875129607964145 29434617155906347205973109)
                    ·
                      refine ⟨2759495358366220050559979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29434617155906347205973109 2759495358366220050559979)
                      ·
                        rfl

theorem cell23_5374098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_5374098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374098 prefixEnd_5374098 := by exact prefixLift 5374098
  have htrace : WordTrace (prefixWord ++ tailWord_5374098) baseStart_5374098 baseEnd_5374098 := by
    simpa [prefixWord, tailWord_5374098, baseEnd_5374098] using wordTrace_append hprefix tailTrace_5374098
  have hstable : (prefixWord ++ tailWord_5374098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374098).length < 2 ^ (prefixWord ++ tailWord_5374098).sum := by decide
  have hdescent : baseEnd_5374098 < baseStart_5374098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374131 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 10]
def baseStart_5374131 : Nat := 118140960795 + 5374131 * 2 ^ 59
def prefixEnd_5374131 : Nat := 4983230072969 + 3 ^ 40 * 5374131 * 2
def baseEnd_5374131 : Nat := 306612478136424269049703

theorem tailTrace_5374131 : CollatzResearch.WordTrace tailWord_5374131 prefixEnd_5374131 306612478136424269049703 := by
  unfold tailWord_5374131
  simp only [CollatzResearch.WordTrace]
  refine ⟨196010660493448690347850247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130673773662299126898566831 196010660493448690347850247)
  ·
    refine ⟨294015990740173035521775371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196010660493448690347850247 294015990740173035521775371)
    ·
      refine ⟨441023986110259553282663057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294015990740173035521775371 441023986110259553282663057)
      ·
        refine ⟨330767989582694664961997293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441023986110259553282663057 330767989582694664961997293)
        ·
          refine ⟨124037996093510499360748985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330767989582694664961997293 124037996093510499360748985)
          ·
            refine ⟨93028497070132874520561739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124037996093510499360748985 93028497070132874520561739)
            ·
              refine ⟨139542745605199311780842609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93028497070132874520561739 139542745605199311780842609)
              ·
                refine ⟨104657059203899483835631957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139542745605199311780842609 104657059203899483835631957)
                ·
                  refine ⟨306612478136424269049703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 104657059203899483835631957 306612478136424269049703)
                  ·
                    rfl

theorem cell23_5374131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 10].length) (baseStart_5374131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374131 prefixEnd_5374131 := by exact prefixLift 5374131
  have htrace : WordTrace (prefixWord ++ tailWord_5374131) baseStart_5374131 baseEnd_5374131 := by
    simpa [prefixWord, tailWord_5374131, baseEnd_5374131] using wordTrace_append hprefix tailTrace_5374131
  have hstable : (prefixWord ++ tailWord_5374131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374131).length < 2 ^ (prefixWord ++ tailWord_5374131).sum := by decide
  have hdescent : baseEnd_5374131 < baseStart_5374131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374135 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 3, 4]
def baseStart_5374135 : Nat := 118140960795 + 5374135 * 2 ^ 59
def prefixEnd_5374135 : Nat := 4983230072969 + 3 ^ 40 * 5374135 * 2
def baseEnd_5374135 : Nat := 919838119050145468599103

theorem tailTrace_5374135 : CollatzResearch.WordTrace tailWord_5374135 prefixEnd_5374135 919838119050145468599103 := by
  unfold tailWord_5374135
  simp only [CollatzResearch.WordTrace]
  refine ⟨196010806385434199030995859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130673870923622799353997239 196010806385434199030995859)
  ·
    refine ⟨294016209578151298546493789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196010806385434199030995859 294016209578151298546493789)
    ·
      refine ⟨110256078591806736954935171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 294016209578151298546493789 110256078591806736954935171)
      ·
        refine ⟨165384117887710105432402757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110256078591806736954935171 165384117887710105432402757)
        ·
          refine ⟨31009522103945644768575517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165384117887710105432402757 31009522103945644768575517)
          ·
            refine ⟨11628570788979616788215819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31009522103945644768575517 11628570788979616788215819)
            ·
              refine ⟨17442856183469425182323729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11628570788979616788215819 17442856183469425182323729)
              ·
                refine ⟨13082142137602068886742797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17442856183469425182323729 13082142137602068886742797)
                ·
                  refine ⟨4905803301600775832528549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13082142137602068886742797 4905803301600775832528549)
                  ·
                    refine ⟨919838119050145468599103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4905803301600775832528549 919838119050145468599103)
                    ·
                      rfl

theorem cell23_5374135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_5374135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374135 prefixEnd_5374135 := by exact prefixLift 5374135
  have htrace : WordTrace (prefixWord ++ tailWord_5374135) baseStart_5374135 baseEnd_5374135 := by
    simpa [prefixWord, tailWord_5374135, baseEnd_5374135] using wordTrace_append hprefix tailTrace_5374135
  have hstable : (prefixWord ++ tailWord_5374135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374135).length < 2 ^ (prefixWord ++ tailWord_5374135).sum := by decide
  have hdescent : baseEnd_5374135 < baseStart_5374135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5374165 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 8]
def baseStart_5374165 : Nat := 118140960795 + 5374165 * 2 ^ 59
def prefixEnd_5374165 : Nat := 4983230072969 + 3 ^ 40 * 5374165 * 2
def baseEnd_5374165 : Nat := 306614417952230143158019

theorem tailTrace_5374165 : CollatzResearch.WordTrace tailWord_5374165 prefixEnd_5374165 306614417952230143158019 := by
  unfold tailWord_5374165
  simp only [CollatzResearch.WordTrace]
  refine ⟨196011900575325514154587949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130674600383550342769725299 196011900575325514154587949)
  ·
    refine ⟨73504462715747067807970481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196011900575325514154587949 73504462715747067807970481)
    ·
      refine ⟨55128347036810300855977861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73504462715747067807970481 55128347036810300855977861)
      ·
        refine ⟨10336565069401931410495849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55128347036810300855977861 10336565069401931410495849)
        ·
          refine ⟨7752423802051448557871887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10336565069401931410495849 7752423802051448557871887)
          ·
            refine ⟨11628635703077172836807831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7752423802051448557871887 11628635703077172836807831)
            ·
              refine ⟨17442953554615759255211747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11628635703077172836807831 17442953554615759255211747)
              ·
                refine ⟨26164430331923638882817621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17442953554615759255211747 26164430331923638882817621)
                ·
                  refine ⟨306614417952230143158019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26164430331923638882817621 306614417952230143158019)
                  ·
                    rfl

theorem cell23_5374165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 8].length) (baseStart_5374165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5374165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5374165 prefixEnd_5374165 := by exact prefixLift 5374165
  have htrace : WordTrace (prefixWord ++ tailWord_5374165) baseStart_5374165 baseEnd_5374165 := by
    simpa [prefixWord, tailWord_5374165, baseEnd_5374165] using wordTrace_append hprefix tailTrace_5374165
  have hstable : (prefixWord ++ tailWord_5374165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5374165).length < 2 ^ (prefixWord ++ tailWord_5374165).sum := by decide
  have hdescent : baseEnd_5374165 < baseStart_5374165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5374165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
