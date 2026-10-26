import V185TrunkScan23Chunk0267

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1585445 : List Nat := [1, 3, 1, 2, 6, 10]
def baseStart_1585445 : Nat := 118140960795 + 1585445 * 2 ^ 59
def prefixEnd_1585445 : Nat := 4983230072969 + 3 ^ 40 * 1585445 * 2
def baseEnd_1585445 : Nat := 3350186569002694126939

theorem tailTrace_1585445 : CollatzResearch.WordTrace tailWord_1585445 prefixEnd_1585445 3350186569002694126939 := by
  unfold tailWord_1585445
  simp only [CollatzResearch.WordTrace]
  refine ⟨57825929741211012293813789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38550619827474008195875859 57825929741211012293813789)
  ·
    refine ⟨21684723652954129610180171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57825929741211012293813789 21684723652954129610180171)
    ·
      refine ⟨32527085479431194415270257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21684723652954129610180171 32527085479431194415270257)
      ·
        refine ⟨24395314109573395811452693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32527085479431194415270257 24395314109573395811452693)
        ·
          refine ⟨1143530348886252928661845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24395314109573395811452693 1143530348886252928661845)
          ·
            refine ⟨3350186569002694126939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1143530348886252928661845 3350186569002694126939)
            ·
              rfl

theorem cell23_1585445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 10].length) (baseStart_1585445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585445 prefixEnd_1585445 := by exact prefixLift 1585445
  have htrace : WordTrace (prefixWord ++ tailWord_1585445) baseStart_1585445 baseEnd_1585445 := by
    simpa [prefixWord, tailWord_1585445, baseEnd_1585445] using wordTrace_append hprefix tailTrace_1585445
  have hstable : (prefixWord ++ tailWord_1585445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585445).length < 2 ^ (prefixWord ++ tailWord_1585445).sum := by decide
  have hdescent : baseEnd_1585445 < baseStart_1585445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585450 : List Nat := [3, 1, 4, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_1585450 : Nat := 118140960795 + 1585450 * 2 ^ 59
def prefixEnd_1585450 : Nat := 4983230072969 + 3 ^ 40 * 1585450 * 2
def baseEnd_1585450 : Nat := 814097903670927153283655

theorem tailTrace_1585450 : CollatzResearch.WordTrace tailWord_1585450 prefixEnd_1585450 814097903670927153283655 := by
  unfold tailWord_1585450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14456528026548224536936451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38550741404128598765163869 14456528026548224536936451)
  ·
    refine ⟨21684792039822336805404677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14456528026548224536936451 21684792039822336805404677)
    ·
      refine ⟨4065898507466688151013377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21684792039822336805404677 4065898507466688151013377)
      ·
        refine ⟨3049423880600016113260033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4065898507466688151013377 3049423880600016113260033)
        ·
          refine ⟨2287067910450012084945025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3049423880600016113260033 2287067910450012084945025)
          ·
            refine ⟨1715300932837509063708769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2287067910450012084945025 1715300932837509063708769)
            ·
              refine ⟨1286475699628131797781577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1715300932837509063708769 1286475699628131797781577)
              ·
                refine ⟨964856774721098848336183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286475699628131797781577 964856774721098848336183)
                ·
                  refine ⟨1447285162081648272504275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 964856774721098848336183 1447285162081648272504275)
                  ·
                    refine ⟨2170927743122472408756413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1447285162081648272504275 2170927743122472408756413)
                    ·
                      refine ⟨814097903670927153283655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2170927743122472408756413 814097903670927153283655)
                      ·
                        rfl

theorem cell23_1585450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_1585450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585450 prefixEnd_1585450 := by exact prefixLift 1585450
  have htrace : WordTrace (prefixWord ++ tailWord_1585450) baseStart_1585450 baseEnd_1585450 := by
    simpa [prefixWord, tailWord_1585450, baseEnd_1585450] using wordTrace_append hprefix tailTrace_1585450
  have hstable : (prefixWord ++ tailWord_1585450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585450).length < 2 ^ (prefixWord ++ tailWord_1585450).sum := by decide
  have hdescent : baseEnd_1585450 < baseStart_1585450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585493 : List Nat := [1, 3, 2, 2, 5, 1, 2, 1, 1, 2, 3]
def baseStart_1585493 : Nat := 118140960795 + 1585493 * 2 ^ 59
def prefixEnd_1585493 : Nat := 4983230072969 + 3 ^ 40 * 1585493 * 2
def baseEnd_1585493 : Nat := 814119983339070485045957

theorem tailTrace_1585493 : CollatzResearch.WordTrace tailWord_1585493 prefixEnd_1585493 814119983339070485045957 := by
  unfold tailWord_1585493
  simp only [CollatzResearch.WordTrace]
  refine ⟨57827680445037116491561133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38551786963358077661040755 57827680445037116491561133)
  ·
    refine ⟨21685380166888918684335425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57827680445037116491561133 21685380166888918684335425)
    ·
      refine ⟨16264035125166689013251569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21685380166888918684335425 16264035125166689013251569)
      ·
        refine ⟨12198026343875016759938677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16264035125166689013251569 12198026343875016759938677)
        ·
          refine ⟨1143564969738282821244251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12198026343875016759938677 1143564969738282821244251)
          ·
            refine ⟨1715347454607424231866377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143564969738282821244251 1715347454607424231866377)
            ·
              refine ⟨1286510590955568173899783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1715347454607424231866377 1286510590955568173899783)
              ·
                refine ⟨1929765886433352260849675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1286510590955568173899783 1929765886433352260849675)
                ·
                  refine ⟨2894648829650028391274513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1929765886433352260849675 2894648829650028391274513)
                  ·
                    refine ⟨2170986622237521293455885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2894648829650028391274513 2170986622237521293455885)
                    ·
                      refine ⟨814119983339070485045957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2170986622237521293455885 814119983339070485045957)
                      ·
                        rfl

theorem cell23_1585493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_1585493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585493 prefixEnd_1585493 := by exact prefixLift 1585493
  have htrace : WordTrace (prefixWord ++ tailWord_1585493) baseStart_1585493 baseEnd_1585493 := by
    simpa [prefixWord, tailWord_1585493, baseEnd_1585493] using wordTrace_append hprefix tailTrace_1585493
  have hstable : (prefixWord ++ tailWord_1585493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585493).length < 2 ^ (prefixWord ++ tailWord_1585493).sum := by decide
  have hdescent : baseEnd_1585493 < baseStart_1585493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585506 : List Nat := [3, 3, 2, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_1585506 : Nat := 118140960795 + 1585506 * 2 ^ 59
def prefixEnd_1585506 : Nat := 4983230072969 + 3 ^ 40 * 1585506 * 2
def baseEnd_1585506 : Nat := 814126658587578934183397

theorem tailTrace_1585506 : CollatzResearch.WordTrace tailWord_1585506 prefixEnd_1585506 814126658587578934183397 := by
  unfold tailWord_1585506
  simp only [CollatzResearch.WordTrace]
  refine ⟨14457038648497504927946093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38552103062660013141189581 14457038648497504927946093)
  ·
    refine ⟨5421389493186564347979785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14457038648497504927946093 5421389493186564347979785)
    ·
      refine ⟨4066042119889923260984839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5421389493186564347979785 4066042119889923260984839)
      ·
        refine ⟨6099063179834884891477259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4066042119889923260984839 6099063179834884891477259)
        ·
          refine ⟨9148594769752327337215889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6099063179834884891477259 9148594769752327337215889)
          ·
            refine ⟨6861446077314245502911917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9148594769752327337215889 6861446077314245502911917)
            ·
              refine ⟨2573042278992842063591969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6861446077314245502911917 2573042278992842063591969)
              ·
                refine ⟨1929781709244631547693977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2573042278992842063591969 1929781709244631547693977)
                ·
                  refine ⟨1447336281933473660770483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1929781709244631547693977 1447336281933473660770483)
                  ·
                    refine ⟨2171004422900210491155725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1447336281933473660770483 2171004422900210491155725)
                    ·
                      refine ⟨814126658587578934183397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2171004422900210491155725 814126658587578934183397)
                      ·
                        rfl

theorem cell23_1585506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_1585506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585506 prefixEnd_1585506 := by exact prefixLift 1585506
  have htrace : WordTrace (prefixWord ++ tailWord_1585506) baseStart_1585506 baseEnd_1585506 := by
    simpa [prefixWord, tailWord_1585506, baseEnd_1585506] using wordTrace_append hprefix tailTrace_1585506
  have hstable : (prefixWord ++ tailWord_1585506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585506).length < 2 ^ (prefixWord ++ tailWord_1585506).sum := by decide
  have hdescent : baseEnd_1585506 < baseStart_1585506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585615 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 6]
def baseStart_1585615 : Nat := 118140960795 + 1585615 * 2 ^ 59
def prefixEnd_1585615 : Nat := 4983230072969 + 3 ^ 40 * 1585615 * 2
def baseEnd_1585615 : Nat := 814182627978919007720395

theorem tailTrace_1585615 : CollatzResearch.WordTrace tailWord_1585615 prefixEnd_1585615 814182627978919007720395 := by
  unfold tailWord_1585615
  simp only [CollatzResearch.WordTrace]
  refine ⟨57832130150595131327502299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38554753433730087551668199 57832130150595131327502299)
  ·
    refine ⟨86748195225892696991253449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57832130150595131327502299 86748195225892696991253449)
    ·
      refine ⟨65061146419419522743440087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86748195225892696991253449 65061146419419522743440087)
      ·
        refine ⟨97591719629129284115160131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65061146419419522743440087 97591719629129284115160131)
        ·
          refine ⟨146387579443693926172740197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97591719629129284115160131 146387579443693926172740197)
          ·
            refine ⟨27447671145692611157388787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146387579443693926172740197 27447671145692611157388787)
            ·
              refine ⟨41171506718538916736083181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27447671145692611157388787 41171506718538916736083181)
              ·
                refine ⟨15439315019452093776031193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41171506718538916736083181 15439315019452093776031193)
                ·
                  refine ⟨11579486264589070332023395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15439315019452093776031193 11579486264589070332023395)
                  ·
                    refine ⟨17369229396883605498035093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11579486264589070332023395 17369229396883605498035093)
                    ·
                      refine ⟨814182627978919007720395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17369229396883605498035093 814182627978919007720395)
                      ·
                        rfl

theorem cell23_1585615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_1585615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585615 prefixEnd_1585615 := by exact prefixLift 1585615
  have htrace : WordTrace (prefixWord ++ tailWord_1585615) baseStart_1585615 baseEnd_1585615 := by
    simpa [prefixWord, tailWord_1585615, baseEnd_1585615] using wordTrace_append hprefix tailTrace_1585615
  have hstable : (prefixWord ++ tailWord_1585615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585615).length < 2 ^ (prefixWord ++ tailWord_1585615).sum := by decide
  have hdescent : baseEnd_1585615 < baseStart_1585615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585629 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1585629 : Nat := 118140960795 + 1585629 * 2 ^ 59
def prefixEnd_1585629 : Nat := 4983230072969 + 3 ^ 40 * 1585629 * 2
def baseEnd_1585629 : Nat := 271396605569360650981777

theorem tailTrace_1585629 : CollatzResearch.WordTrace tailWord_1585629 prefixEnd_1585629 271396605569360650981777 := by
  unfold tailWord_1585629
  simp only [CollatzResearch.WordTrace]
  refine ⟨57832640772544411718511941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38555093848362941145674627 57832640772544411718511941)
  ·
    refine ⟨10843620144852077197220989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57832640772544411718511941 10843620144852077197220989)
    ·
      refine ⟨4066357554319528948957871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10843620144852077197220989 4066357554319528948957871)
      ·
        refine ⟨6099536331479293423436807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4066357554319528948957871 6099536331479293423436807)
        ·
          refine ⟨9149304497218940135155211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6099536331479293423436807 9149304497218940135155211)
          ·
            refine ⟨13723956745828410202732817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9149304497218940135155211 13723956745828410202732817)
            ·
              refine ⟨10292967559371307652049613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13723956745828410202732817 10292967559371307652049613)
              ·
                refine ⟨3859862834764240369518605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10292967559371307652049613 3859862834764240369518605)
                ·
                  refine ⟨1447448563036590138569477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3859862834764240369518605 1447448563036590138569477)
                  ·
                    refine ⟨271396605569360650981777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1447448563036590138569477 271396605569360650981777)
                    ·
                      rfl

theorem cell23_1585629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1585629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585629 prefixEnd_1585629 := by exact prefixLift 1585629
  have htrace : WordTrace (prefixWord ++ tailWord_1585629) baseStart_1585629 baseEnd_1585629 := by
    simpa [prefixWord, tailWord_1585629, baseEnd_1585629] using wordTrace_append hprefix tailTrace_1585629
  have hstable : (prefixWord ++ tailWord_1585629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585629).length < 2 ^ (prefixWord ++ tailWord_1585629).sum := by decide
  have hdescent : baseEnd_1585629 < baseStart_1585629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585653 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1585653 : Nat := 118140960795 + 1585653 * 2 ^ 59
def prefixEnd_1585653 : Nat := 4983230072969 + 3 ^ 40 * 1585653 * 2
def baseEnd_1585653 : Nat := 814202140243789859045221

theorem tailTrace_1585653 : CollatzResearch.WordTrace tailWord_1585653 prefixEnd_1585653 814202140243789859045221 := by
  unfold tailWord_1585653
  simp only [CollatzResearch.WordTrace]
  refine ⟨57833516124457463817385613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38555677416304975878257075 57833516124457463817385613)
  ·
    refine ⟨21687568546671548931519605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57833516124457463817385613 21687568546671548931519605)
    ·
      refine ⟨2033209551250457712329963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21687568546671548931519605 2033209551250457712329963)
      ·
        refine ⟨3049814326875686568494945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2033209551250457712329963 3049814326875686568494945)
        ·
          refine ⟨2287360745156764926371209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3049814326875686568494945 2287360745156764926371209)
          ·
            refine ⟨1715520558867573694778407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2287360745156764926371209 1715520558867573694778407)
            ·
              refine ⟨2573280838301360542167611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1715520558867573694778407 2573280838301360542167611)
              ·
                refine ⟨3859921257452040813251417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2573280838301360542167611 3859921257452040813251417)
                ·
                  refine ⟨2894940943089030609938563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3859921257452040813251417 2894940943089030609938563)
                  ·
                    refine ⟨4342411414633545914907845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2894940943089030609938563 4342411414633545914907845)
                    ·
                      refine ⟨814202140243789859045221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4342411414633545914907845 814202140243789859045221)
                      ·
                        rfl

theorem cell23_1585653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1585653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585653 prefixEnd_1585653 := by exact prefixLift 1585653
  have htrace : WordTrace (prefixWord ++ tailWord_1585653) baseStart_1585653 baseEnd_1585653 := by
    simpa [prefixWord, tailWord_1585653, baseEnd_1585653] using wordTrace_append hprefix tailTrace_1585653
  have hstable : (prefixWord ++ tailWord_1585653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585653).length < 2 ^ (prefixWord ++ tailWord_1585653).sum := by decide
  have hdescent : baseEnd_1585653 < baseStart_1585653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585670 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_1585670 : Nat := 118140960795 + 1585670 * 2 ^ 59
def prefixEnd_1585670 : Nat := 4983230072969 + 3 ^ 40 * 1585670 * 2
def baseEnd_1585670 : Nat := 814210869414916292532643

theorem tailTrace_1585670 : CollatzResearch.WordTrace tailWord_1585670 prefixEnd_1585670 814210869414916292532643 := by
  unfold tailWord_1585670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1807316755168621116273577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38556090776930583813836309 1807316755168621116273577)
  ·
    refine ⟨1355487566376465837205183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1807316755168621116273577 1355487566376465837205183)
    ·
      refine ⟨2033231349564698755807775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1355487566376465837205183 2033231349564698755807775)
      ·
        refine ⟨3049847024347048133711663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2033231349564698755807775 3049847024347048133711663)
        ·
          refine ⟨4574770536520572200567495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3049847024347048133711663 4574770536520572200567495)
          ·
            refine ⟨6862155804780858300851243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4574770536520572200567495 6862155804780858300851243)
            ·
              refine ⟨10293233707171287451276865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6862155804780858300851243 10293233707171287451276865)
              ·
                refine ⟨7719925280378465588457649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10293233707171287451276865 7719925280378465588457649)
                ·
                  refine ⟨5789943960283849191343237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7719925280378465588457649 5789943960283849191343237)
                  ·
                    refine ⟨1085614492553221723376857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5789943960283849191343237 1085614492553221723376857)
                    ·
                      refine ⟨814210869414916292532643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1085614492553221723376857 814210869414916292532643)
                      ·
                        rfl

theorem cell23_1585670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_1585670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585670 prefixEnd_1585670 := by exact prefixLift 1585670
  have htrace : WordTrace (prefixWord ++ tailWord_1585670) baseStart_1585670 baseEnd_1585670 := by
    simpa [prefixWord, tailWord_1585670, baseEnd_1585670] using wordTrace_append hprefix tailTrace_1585670
  have hstable : (prefixWord ++ tailWord_1585670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585670).length < 2 ^ (prefixWord ++ tailWord_1585670).sum := by decide
  have hdescent : baseEnd_1585670 < baseStart_1585670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585706 : List Nat := [3, 1, 4, 1, 1, 3, 2, 2, 1, 5]
def baseStart_1585706 : Nat := 118140960795 + 1585706 * 2 ^ 59
def prefixEnd_1585706 : Nat := 4983230072969 + 3 ^ 40 * 1585706 * 2
def baseEnd_1585706 : Nat := 271409784906159383894159

theorem tailTrace_1585706 : CollatzResearch.WordTrace tailWord_1585706 prefixEnd_1585706 271409784906159383894159 := by
  unfold tailWord_1585706
  simp only [CollatzResearch.WordTrace]
  refine ⟨14458862298316363467266243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38556966128843635912709981 14458862298316363467266243)
  ·
    refine ⟨21688293447474545200899365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14458862298316363467266243 21688293447474545200899365)
    ·
      refine ⟨4066555021401477225168631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21688293447474545200899365 4066555021401477225168631)
      ·
        refine ⟨6099832532102215837752947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4066555021401477225168631 6099832532102215837752947)
        ·
          refine ⟨9149748798153323756629421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6099832532102215837752947 9149748798153323756629421)
          ·
            refine ⟨3431155799307496408736033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9149748798153323756629421 3431155799307496408736033)
            ·
              refine ⟨2573366849480622306552025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3431155799307496408736033 2573366849480622306552025)
              ·
                refine ⟨1930025137110466729914019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2573366849480622306552025 1930025137110466729914019)
                ·
                  refine ⟨2895037705665700094871029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930025137110466729914019 2895037705665700094871029)
                  ·
                    refine ⟨271409784906159383894159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2895037705665700094871029 271409784906159383894159)
                    ·
                      rfl

theorem cell23_1585706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_1585706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585706 prefixEnd_1585706 := by exact prefixLift 1585706
  have htrace : WordTrace (prefixWord ++ tailWord_1585706) baseStart_1585706 baseEnd_1585706 := by
    simpa [prefixWord, tailWord_1585706, baseEnd_1585706] using wordTrace_append hprefix tailTrace_1585706
  have hstable : (prefixWord ++ tailWord_1585706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585706).length < 2 ^ (prefixWord ++ tailWord_1585706).sum := by decide
  have hdescent : baseEnd_1585706 < baseStart_1585706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585729 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1585729 : Nat := 118140960795 + 1585729 * 2 ^ 59
def prefixEnd_1585729 : Nat := 4983230072969 + 3 ^ 40 * 1585729 * 2
def baseEnd_1585729 : Nat := 814241164773531561694871

theorem tailTrace_1585729 : CollatzResearch.WordTrace tailWord_1585729 prefixEnd_1585729 814241164773531561694871 := by
  unfold tailWord_1585729
  simp only [CollatzResearch.WordTrace]
  refine ⟨57836288072182128797152241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38557525381454752531434827 57836288072182128797152241)
  ·
    refine ⟨43377216054136596597864181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57836288072182128797152241 43377216054136596597864181)
    ·
      refine ⟨4066614005075305931049767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43377216054136596597864181 4066614005075305931049767)
      ·
        refine ⟨6099921007612958896574651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4066614005075305931049767 6099921007612958896574651)
        ·
          refine ⟨9149881511419438344861977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6099921007612958896574651 9149881511419438344861977)
          ·
            refine ⟨6862411133564578758646483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9149881511419438344861977 6862411133564578758646483)
            ·
              refine ⟨10293616700346868137969725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6862411133564578758646483 10293616700346868137969725)
              ·
                refine ⟨3860106262630075551738647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10293616700346868137969725 3860106262630075551738647)
                ·
                  refine ⟨5790159393945113327607971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3860106262630075551738647 5790159393945113327607971)
                  ·
                    refine ⟨8685239090917669991411957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5790159393945113327607971 8685239090917669991411957)
                    ·
                      refine ⟨814241164773531561694871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8685239090917669991411957 814241164773531561694871)
                      ·
                        rfl

theorem cell23_1585729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1585729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585729 prefixEnd_1585729 := by exact prefixLift 1585729
  have htrace : WordTrace (prefixWord ++ tailWord_1585729) baseStart_1585729 baseEnd_1585729 := by
    simpa [prefixWord, tailWord_1585729, baseEnd_1585729] using wordTrace_append hprefix tailTrace_1585729
  have hstable : (prefixWord ++ tailWord_1585729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585729).length < 2 ^ (prefixWord ++ tailWord_1585729).sum := by decide
  have hdescent : baseEnd_1585729 < baseStart_1585729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585743 : List Nat := [1, 1, 2, 1, 1, 2, 4, 6, 1, 2, 2]
def baseStart_1585743 : Nat := 118140960795 + 1585743 * 2 ^ 59
def prefixEnd_1585743 : Nat := 4983230072969 + 3 ^ 40 * 1585743 * 2
def baseEnd_1585743 : Nat := 814248353502694506919807

theorem tailTrace_1585743 : CollatzResearch.WordTrace tailWord_1585743 prefixEnd_1585743 814248353502694506919807 := by
  unfold tailWord_1585743
  simp only [CollatzResearch.WordTrace]
  refine ⟨57836798694131409188161883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38557865796087606125441255 57836798694131409188161883)
  ·
    refine ⟨86755198041197113782242825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57836798694131409188161883 86755198041197113782242825)
    ·
      refine ⟨65066398530897835336682119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86755198041197113782242825 65066398530897835336682119)
      ·
        refine ⟨97599597796346753005023179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65066398530897835336682119 97599597796346753005023179)
        ·
          refine ⟨146399396694520129507534769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97599597796346753005023179 146399396694520129507534769)
          ·
            refine ⟨109799547520890097130651077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146399396694520129507534769 109799547520890097130651077)
            ·
              refine ⟨20587415160166893211997077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109799547520890097130651077 20587415160166893211997077)
              ·
                refine ⟨965035085632823119312363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20587415160166893211997077 965035085632823119312363)
                ·
                  refine ⟨1447552628449234678968545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965035085632823119312363 1447552628449234678968545)
                  ·
                    refine ⟨1085664471336926009226409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1447552628449234678968545 1085664471336926009226409)
                    ·
                      refine ⟨814248353502694506919807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1085664471336926009226409 814248353502694506919807)
                      ·
                        rfl

theorem cell23_1585743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 1, 2, 2].length) (baseStart_1585743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585743 prefixEnd_1585743 := by exact prefixLift 1585743
  have htrace : WordTrace (prefixWord ++ tailWord_1585743) baseStart_1585743 baseEnd_1585743 := by
    simpa [prefixWord, tailWord_1585743, baseEnd_1585743] using wordTrace_append hprefix tailTrace_1585743
  have hstable : (prefixWord ++ tailWord_1585743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585743).length < 2 ^ (prefixWord ++ tailWord_1585743).sum := by decide
  have hdescent : baseEnd_1585743 < baseStart_1585743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585772 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_1585772 : Nat := 118140960795 + 1585772 * 2 ^ 59
def prefixEnd_1585772 : Nat := 4983230072969 + 3 ^ 40 * 1585772 * 2
def baseEnd_1585772 : Nat := 814263244441674893457173

theorem tailTrace_1585772 : CollatzResearch.WordTrace tailWord_1585772 prefixEnd_1585772 814263244441674893457173 := by
  unfold tailWord_1585772
  simp only [CollatzResearch.WordTrace]
  refine ⟨28918928205513173570483785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38558570940684231427311713 28918928205513173570483785)
  ·
    refine ⟨21689196154134880177862839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28918928205513173570483785 21689196154134880177862839)
    ·
      refine ⟨32533794231202320266794259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21689196154134880177862839 32533794231202320266794259)
      ·
        refine ⟨48800691346803480400191389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32533794231202320266794259 48800691346803480400191389)
        ·
          refine ⟨18300259255051305150071771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48800691346803480400191389 18300259255051305150071771)
          ·
            refine ⟨27450388882576957725107657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18300259255051305150071771 27450388882576957725107657)
            ·
              refine ⟨20587791661932718293830743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27450388882576957725107657 20587791661932718293830743)
              ·
                refine ⟨30881687492899077440746115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20587791661932718293830743 30881687492899077440746115)
                ·
                  refine ⟨46322531239348616161119173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30881687492899077440746115 46322531239348616161119173)
                  ·
                    refine ⟨8685474607377865530209845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46322531239348616161119173 8685474607377865530209845)
                    ·
                      refine ⟨814263244441674893457173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8685474607377865530209845 814263244441674893457173)
                      ·
                        rfl

theorem cell23_1585772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_1585772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585772 prefixEnd_1585772 := by exact prefixLift 1585772
  have htrace : WordTrace (prefixWord ++ tailWord_1585772) baseStart_1585772 baseEnd_1585772 := by
    simpa [prefixWord, tailWord_1585772, baseEnd_1585772] using wordTrace_append hprefix tailTrace_1585772
  have hstable : (prefixWord ++ tailWord_1585772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585772).length < 2 ^ (prefixWord ++ tailWord_1585772).sum := by decide
  have hdescent : baseEnd_1585772 < baseStart_1585772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585776 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 3]
def baseStart_1585776 : Nat := 118140960795 + 1585776 * 2 ^ 59
def prefixEnd_1585776 : Nat := 4983230072969 + 3 ^ 40 * 1585776 * 2
def baseEnd_1585776 : Nat := 814265298364292877807155

theorem tailTrace_1585776 : CollatzResearch.WordTrace tailWord_1585776 prefixEnd_1585776 814265298364292877807155 := by
  unfold tailWord_1585776
  simp only [CollatzResearch.WordTrace]
  refine ⟨28919001151505927912056591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38558668202007903882742121 28919001151505927912056591)
  ·
    refine ⟨43378501727258891868084887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28919001151505927912056591 43378501727258891868084887)
    ·
      refine ⟨65067752590888337802127331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43378501727258891868084887 65067752590888337802127331)
      ·
        refine ⟨97601628886332506703190997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65067752590888337802127331 97601628886332506703190997)
        ·
          refine ⟨2287538177023418125856039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 97601628886332506703190997 2287538177023418125856039)
          ·
            refine ⟨3431307265535127188784059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2287538177023418125856039 3431307265535127188784059)
            ·
              refine ⟨5146960898302690783176089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3431307265535127188784059 5146960898302690783176089)
              ·
                refine ⟨3860220673727018087382067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5146960898302690783176089 3860220673727018087382067)
                ·
                  refine ⟨5790331010590527131073101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3860220673727018087382067 5790331010590527131073101)
                  ·
                    refine ⟨2171374128971447674152413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5790331010590527131073101 2171374128971447674152413)
                    ·
                      refine ⟨814265298364292877807155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2171374128971447674152413 814265298364292877807155)
                      ·
                        rfl

theorem cell23_1585776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 3].length) (baseStart_1585776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585776 prefixEnd_1585776 := by exact prefixLift 1585776
  have htrace : WordTrace (prefixWord ++ tailWord_1585776) baseStart_1585776 baseEnd_1585776 := by
    simpa [prefixWord, tailWord_1585776, baseEnd_1585776] using wordTrace_append hprefix tailTrace_1585776
  have hstable : (prefixWord ++ tailWord_1585776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585776).length < 2 ^ (prefixWord ++ tailWord_1585776).sum := by decide
  have hdescent : baseEnd_1585776 < baseStart_1585776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585793 : List Nat := [1, 2, 4, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_1585793 : Nat := 118140960795 + 1585793 * 2 ^ 59
def prefixEnd_1585793 : Nat := 4983230072969 + 3 ^ 40 * 1585793 * 2
def baseEnd_1585793 : Nat := 814274027535419311294577

theorem tailTrace_1585793 : CollatzResearch.WordTrace tailWord_1585793 prefixEnd_1585793 814274027535419311294577 := by
  unfold tailWord_1585793
  simp only [CollatzResearch.WordTrace]
  refine ⟨57838622343950267727482033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38559081562633511818321355 57838622343950267727482033)
  ·
    refine ⟨43378966757962700795611525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57838622343950267727482033 43378966757962700795611525)
    ·
      refine ⟨8133556267118006399177161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43378966757962700795611525 8133556267118006399177161)
      ·
        refine ⟨6100167200338504799382871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8133556267118006399177161 6100167200338504799382871)
        ·
          refine ⟨9150250800507757199074307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6100167200338504799382871 9150250800507757199074307)
          ·
            refine ⟨13725376200761635798611461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9150250800507757199074307 13725376200761635798611461)
            ·
              refine ⟨2573508037642806712239649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13725376200761635798611461 2573508037642806712239649)
              ·
                refine ⟨1930131028232105034179737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2573508037642806712239649 1930131028232105034179737)
                ·
                  refine ⟨1447598271174078775634803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1930131028232105034179737 1447598271174078775634803)
                  ·
                    refine ⟨2171397406761118163452205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1447598271174078775634803 2171397406761118163452205)
                    ·
                      refine ⟨814274027535419311294577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2171397406761118163452205 814274027535419311294577)
                      ·
                        rfl

theorem cell23_1585793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_1585793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585793 prefixEnd_1585793 := by exact prefixLift 1585793
  have htrace : WordTrace (prefixWord ++ tailWord_1585793) baseStart_1585793 baseEnd_1585793 := by
    simpa [prefixWord, tailWord_1585793, baseEnd_1585793] using wordTrace_append hprefix tailTrace_1585793
  have hstable : (prefixWord ++ tailWord_1585793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585793).length < 2 ^ (prefixWord ++ tailWord_1585793).sum := by decide
  have hdescent : baseEnd_1585793 < baseStart_1585793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585837 : List Nat := [1, 5, 2, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_1585837 : Nat := 118140960795 + 1585837 * 2 ^ 59
def prefixEnd_1585837 : Nat := 4983230072969 + 3 ^ 40 * 1585837 * 2
def baseEnd_1585837 : Nat := 814296620684217139144375

theorem tailTrace_1585837 : CollatzResearch.WordTrace tailWord_1585837 prefixEnd_1585837 814296620684217139144375 := by
  unfold tailWord_1585837
  simp only [CollatzResearch.WordTrace]
  refine ⟨57840227155790863242083765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38560151437193908828055843 57840227155790863242083765)
  ·
    refine ⟨5422521295855393428945353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57840227155790863242083765 5422521295855393428945353)
    ·
      refine ⟨4066890971891545071709015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5422521295855393428945353 4066890971891545071709015)
      ·
        refine ⟨6100336457837317607563523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4066890971891545071709015 6100336457837317607563523)
        ·
          refine ⟨9150504686755976411345285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6100336457837317607563523 9150504686755976411345285)
          ·
            refine ⟨1715719628766745577127241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9150504686755976411345285 1715719628766745577127241)
            ·
              refine ⟨1286789721575059182845431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1715719628766745577127241 1286789721575059182845431)
              ·
                refine ⟨1930184582362588774268147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1286789721575059182845431 1930184582362588774268147)
                ·
                  refine ⟨2895276873543883161402221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930184582362588774268147 2895276873543883161402221)
                  ·
                    refine ⟨1085728827578956185525833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2895276873543883161402221 1085728827578956185525833)
                    ·
                      refine ⟨814296620684217139144375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1085728827578956185525833 814296620684217139144375)
                      ·
                        rfl

theorem cell23_1585837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_1585837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585837 prefixEnd_1585837 := by exact prefixLift 1585837
  have htrace : WordTrace (prefixWord ++ tailWord_1585837) baseStart_1585837 baseEnd_1585837 := by
    simpa [prefixWord, tailWord_1585837, baseEnd_1585837] using wordTrace_append hprefix tailTrace_1585837
  have hstable : (prefixWord ++ tailWord_1585837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585837).length < 2 ^ (prefixWord ++ tailWord_1585837).sum := by decide
  have hdescent : baseEnd_1585837 < baseStart_1585837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585856 : List Nat := [2, 1, 1, 2, 4, 2, 2, 4, 5]
def baseStart_1585856 : Nat := 118140960795 + 1585856 * 2 ^ 59
def prefixEnd_1585856 : Nat := 4983230072969 + 3 ^ 40 * 1585856 * 2
def baseEnd_1585856 : Nat := 90478486312961396089643

theorem tailTrace_1585856 : CollatzResearch.WordTrace tailWord_1585856 prefixEnd_1585856 90478486312961396089643 := by
  unfold tailWord_1585856
  simp only [CollatzResearch.WordTrace]
  refine ⟨28920460071361014743512711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38560613428481352991350281 28920460071361014743512711)
  ·
    refine ⟨43380690107041522115269067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28920460071361014743512711 43380690107041522115269067)
    ·
      refine ⟨65071035160562283172903601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43380690107041522115269067 65071035160562283172903601)
      ·
        refine ⟨48803276370421712379677701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65071035160562283172903601 48803276370421712379677701)
        ·
          refine ⟨9150614319454071071189569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48803276370421712379677701 9150614319454071071189569)
          ·
            refine ⟨6862960739590553303392177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9150614319454071071189569 6862960739590553303392177)
            ·
              refine ⟨5147220554692914977544133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6862960739590553303392177 5147220554692914977544133)
              ·
                refine ⟨965103854004921558289525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5147220554692914977544133 965103854004921558289525)
                ·
                  refine ⟨90478486312961396089643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 965103854004921558289525 90478486312961396089643)
                  ·
                    rfl

theorem cell23_1585856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 5].length) (baseStart_1585856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585856 prefixEnd_1585856 := by exact prefixLift 1585856
  have htrace : WordTrace (prefixWord ++ tailWord_1585856) baseStart_1585856 baseEnd_1585856 := by
    simpa [prefixWord, tailWord_1585856, baseEnd_1585856] using wordTrace_append hprefix tailTrace_1585856
  have hstable : (prefixWord ++ tailWord_1585856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585856).length < 2 ^ (prefixWord ++ tailWord_1585856).sum := by decide
  have hdescent : baseEnd_1585856 < baseStart_1585856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585866 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_1585866 : Nat := 118140960795 + 1585866 * 2 ^ 59
def prefixEnd_1585866 : Nat := 4983230072969 + 3 ^ 40 * 1585866 * 2
def baseEnd_1585866 : Nat := 814311511623197525681741

theorem tailTrace_1585866 : CollatzResearch.WordTrace tailWord_1585866 prefixEnd_1585866 814311511623197525681741 := by
  unfold tailWord_1585866
  simp only [CollatzResearch.WordTrace]
  refine ⟨14460321218171450298722363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38560856581790534129926301 14460321218171450298722363)
  ·
    refine ⟨21690481827257175448083545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14460321218171450298722363 21690481827257175448083545)
    ·
      refine ⟨16267861370442881586062659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21690481827257175448083545 16267861370442881586062659)
      ·
        refine ⟨24401792055664322379093989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16267861370442881586062659 24401792055664322379093989)
        ·
          refine ⟨4575336010437060446080123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24401792055664322379093989 4575336010437060446080123)
          ·
            refine ⟨6863004015655590669120185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4575336010437060446080123 6863004015655590669120185)
            ·
              refine ⟨5147253011741693001840139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6863004015655590669120185 5147253011741693001840139)
              ·
                refine ⟨7720879517612539502760209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147253011741693001840139 7720879517612539502760209)
                ·
                  refine ⟨5790659638209404627070157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7720879517612539502760209 5790659638209404627070157)
                  ·
                    refine ⟨2171497364328526735151309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5790659638209404627070157 2171497364328526735151309)
                    ·
                      refine ⟨814311511623197525681741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2171497364328526735151309 814311511623197525681741)
                      ·
                        rfl

theorem cell23_1585866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_1585866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585866 prefixEnd_1585866 := by exact prefixLift 1585866
  have htrace : WordTrace (prefixWord ++ tailWord_1585866) baseStart_1585866 baseEnd_1585866 := by
    simpa [prefixWord, tailWord_1585866, baseEnd_1585866] using wordTrace_append hprefix tailTrace_1585866
  have hstable : (prefixWord ++ tailWord_1585866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585866).length < 2 ^ (prefixWord ++ tailWord_1585866).sum := by decide
  have hdescent : baseEnd_1585866 < baseStart_1585866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1585906 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1585906 : Nat := 118140960795 + 1585906 * 2 ^ 59
def prefixEnd_1585906 : Nat := 4983230072969 + 3 ^ 40 * 1585906 * 2
def baseEnd_1585906 : Nat := 814332050849377369181557

theorem tailTrace_1585906 : CollatzResearch.WordTrace tailWord_1585906 prefixEnd_1585906 814332050849377369181557 := by
  unfold tailWord_1585906
  simp only [CollatzResearch.WordTrace]
  refine ⟨14460685948135222006586393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38561829195027258684230381 14460685948135222006586393)
  ·
    refine ⟨10845514461101416504939795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14460685948135222006586393 10845514461101416504939795)
    ·
      refine ⟨16268271691652124757409693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10845514461101416504939795 16268271691652124757409693)
      ·
        refine ⟨6100601884369546784028635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16268271691652124757409693 6100601884369546784028635)
        ·
          refine ⟨9150902826554320176042953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6100601884369546784028635 9150902826554320176042953)
          ·
            refine ⟨6863177119915740132032215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9150902826554320176042953 6863177119915740132032215)
            ·
              refine ⟨10294765679873610198048323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6863177119915740132032215 10294765679873610198048323)
              ·
                refine ⟨15442148519810415297072485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10294765679873610198048323 15442148519810415297072485)
                ·
                  refine ⟨2895402847464452868201091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15442148519810415297072485 2895402847464452868201091)
                  ·
                    refine ⟨4343104271196679302301637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2895402847464452868201091 4343104271196679302301637)
                    ·
                      refine ⟨814332050849377369181557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4343104271196679302301637 814332050849377369181557)
                      ·
                        rfl

theorem cell23_1585906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1585906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1585906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1585906 prefixEnd_1585906 := by exact prefixLift 1585906
  have htrace : WordTrace (prefixWord ++ tailWord_1585906) baseStart_1585906 baseEnd_1585906 := by
    simpa [prefixWord, tailWord_1585906, baseEnd_1585906] using wordTrace_append hprefix tailTrace_1585906
  have hstable : (prefixWord ++ tailWord_1585906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1585906).length < 2 ^ (prefixWord ++ tailWord_1585906).sum := by decide
  have hdescent : baseEnd_1585906 < baseStart_1585906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1585906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586007 : List Nat := [1, 1, 3, 2, 4, 2, 2, 3, 1, 1, 3]
def baseStart_1586007 : Nat := 118140960795 + 1586007 * 2 ^ 59
def prefixEnd_1586007 : Nat := 4983230072969 + 3 ^ 40 * 1586007 * 2
def baseEnd_1586007 : Nat := 814383912395481474018593

theorem tailTrace_1586007 : CollatzResearch.WordTrace tailWord_1586007 prefixEnd_1586007 814383912395481474018593 := by
  unfold tailWord_1586007
  simp only [CollatzResearch.WordTrace]
  refine ⟨57846427565174982275772275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38564285043449988183848183 57846427565174982275772275)
  ·
    refine ⟨86769641347762473413658413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57846427565174982275772275 86769641347762473413658413)
    ·
      refine ⟨32538615505410927530121905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86769641347762473413658413 32538615505410927530121905)
      ·
        refine ⟨24403961629058195647591429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32538615505410927530121905 24403961629058195647591429)
        ·
          refine ⟨4575742805448411683923393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24403961629058195647591429 4575742805448411683923393)
          ·
            refine ⟨3431807104086308762942545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4575742805448411683923393 3431807104086308762942545)
            ·
              refine ⟨2573855328064731572206909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3431807104086308762942545 2573855328064731572206909)
              ·
                refine ⟨965195748024274339577591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2573855328064731572206909 965195748024274339577591)
                ·
                  refine ⟨1447793622036411509366387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965195748024274339577591 1447793622036411509366387)
                  ·
                    refine ⟨2171690433054617264049581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1447793622036411509366387 2171690433054617264049581)
                    ·
                      refine ⟨814383912395481474018593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2171690433054617264049581 814383912395481474018593)
                      ·
                        rfl

theorem cell23_1586007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_1586007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586007 prefixEnd_1586007 := by exact prefixLift 1586007
  have htrace : WordTrace (prefixWord ++ tailWord_1586007) baseStart_1586007 baseEnd_1586007 := by
    simpa [prefixWord, tailWord_1586007, baseEnd_1586007] using wordTrace_append hprefix tailTrace_1586007
  have hstable : (prefixWord ++ tailWord_1586007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586007).length < 2 ^ (prefixWord ++ tailWord_1586007).sum := by decide
  have hdescent : baseEnd_1586007 < baseStart_1586007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586010 : List Nat := [3, 1, 1, 2, 1, 6, 2, 1, 1, 5]
def baseStart_1586010 : Nat := 118140960795 + 1586010 * 2 ^ 59
def prefixEnd_1586010 : Nat := 4983230072969 + 3 ^ 40 * 1586010 * 2
def baseEnd_1586010 : Nat := 271461817612481654093693

theorem tailTrace_1586010 : CollatzResearch.WordTrace tailWord_1586010 prefixEnd_1586010 271461817612481654093693 := by
  unfold tailWord_1586010
  simp only [CollatzResearch.WordTrace]
  refine ⟨14461634246041028447032871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38564357989442742525420989 14461634246041028447032871)
  ·
    refine ⟨21692451369061542670549307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14461634246041028447032871 21692451369061542670549307)
    ·
      refine ⟨32538677053592314005823961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21692451369061542670549307 32538677053592314005823961)
      ·
        refine ⟨24404007790194235504367971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32538677053592314005823961 24404007790194235504367971)
        ·
          refine ⟨36606011685291353256551957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24404007790194235504367971 36606011685291353256551957)
          ·
            refine ⟨1715906797748032183900873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36606011685291353256551957 1715906797748032183900873)
            ·
              refine ⟨1286930098311024137925655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1715906797748032183900873 1286930098311024137925655)
              ·
                refine ⟨1930395147466536206888483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1286930098311024137925655 1930395147466536206888483)
                ·
                  refine ⟨2895592721199804310332725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930395147466536206888483 2895592721199804310332725)
                  ·
                    refine ⟨271461817612481654093693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2895592721199804310332725 271461817612481654093693)
                    ·
                      rfl

theorem cell23_1586010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_1586010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586010 prefixEnd_1586010 := by exact prefixLift 1586010
  have htrace : WordTrace (prefixWord ++ tailWord_1586010) baseStart_1586010 baseEnd_1586010 := by
    simpa [prefixWord, tailWord_1586010, baseEnd_1586010] using wordTrace_append hprefix tailTrace_1586010
  have hstable : (prefixWord ++ tailWord_1586010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586010).length < 2 ^ (prefixWord ++ tailWord_1586010).sum := by decide
  have hdescent : baseEnd_1586010 < baseStart_1586010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586016 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 5]
def baseStart_1586016 : Nat := 118140960795 + 1586016 * 2 ^ 59
def prefixEnd_1586016 : Nat := 4983230072969 + 3 ^ 40 * 1586016 * 2
def baseEnd_1586016 : Nat := 814388533721371938806051

theorem tailTrace_1586016 : CollatzResearch.WordTrace tailWord_1586016 prefixEnd_1586016 814388533721371938806051 := by
  unfold tailWord_1586016
  simp only [CollatzResearch.WordTrace]
  refine ⟨28923377911071188406424951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38564503881428251208566601 28923377911071188406424951)
  ·
    refine ⟨43385066866606782609637427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28923377911071188406424951 43385066866606782609637427)
    ·
      refine ⟨65077600299910173914456141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43385066866606782609637427 65077600299910173914456141)
      ·
        refine ⟨24404100112466315217921053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65077600299910173914456141 24404100112466315217921053)
        ·
          refine ⟨9151537542174868206720395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24404100112466315217921053 9151537542174868206720395)
          ·
            refine ⟨13727306313262302310080593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9151537542174868206720395 13727306313262302310080593)
            ·
              refine ⟨10295479734946726732560445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13727306313262302310080593 10295479734946726732560445)
              ·
                refine ⟨3860804900605022524710167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10295479734946726732560445 3860804900605022524710167)
                ·
                  refine ⟨5791207350907533787065251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3860804900605022524710167 5791207350907533787065251)
                  ·
                    refine ⟨8686811026361300680597877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5791207350907533787065251 8686811026361300680597877)
                    ·
                      refine ⟨814388533721371938806051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8686811026361300680597877 814388533721371938806051)
                      ·
                        rfl

theorem cell23_1586016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_1586016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586016 prefixEnd_1586016 := by exact prefixLift 1586016
  have htrace : WordTrace (prefixWord ++ tailWord_1586016) baseStart_1586016 baseEnd_1586016 := by
    simpa [prefixWord, tailWord_1586016, baseEnd_1586016] using wordTrace_append hprefix tailTrace_1586016
  have hstable : (prefixWord ++ tailWord_1586016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586016).length < 2 ^ (prefixWord ++ tailWord_1586016).sum := by decide
  have hdescent : baseEnd_1586016 < baseStart_1586016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586023 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 4, 4]
def baseStart_1586023 : Nat := 118140960795 + 1586023 * 2 ^ 59
def prefixEnd_1586023 : Nat := 4983230072969 + 3 ^ 40 * 1586023 * 2
def baseEnd_1586023 : Nat := 271464042695317803806173

theorem tailTrace_1586023 : CollatzResearch.WordTrace tailWord_1586023 prefixEnd_1586023 271464042695317803806173 := by
  unfold tailWord_1586023
  simp only [CollatzResearch.WordTrace]
  refine ⟨57847011133117017008354723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38564674088744678005569815 57847011133117017008354723)
  ·
    refine ⟨86770516699675525512532085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57847011133117017008354723 86770516699675525512532085)
    ·
      refine ⟨8134735940594580516799883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86770516699675525512532085 8134735940594580516799883)
      ·
        refine ⟨12202103910891870775199825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8134735940594580516799883 12202103910891870775199825)
        ·
          refine ⟨9151577933168903081399869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12202103910891870775199825 9151577933168903081399869)
          ·
            refine ⟨3431841724938338655524951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9151577933168903081399869 3431841724938338655524951)
            ·
              refine ⟨5147762587407507983287427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3431841724938338655524951 5147762587407507983287427)
              ·
                refine ⟨7721643881111261974931141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147762587407507983287427 7721643881111261974931141)
                ·
                  refine ⟨1447808227708361620299589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7721643881111261974931141 1447808227708361620299589)
                  ·
                    refine ⟨271464042695317803806173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1447808227708361620299589 271464042695317803806173)
                    ·
                      rfl

theorem cell23_1586023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_1586023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586023 prefixEnd_1586023 := by exact prefixLift 1586023
  have htrace : WordTrace (prefixWord ++ tailWord_1586023) baseStart_1586023 baseEnd_1586023 := by
    simpa [prefixWord, tailWord_1586023, baseEnd_1586023] using wordTrace_append hprefix tailTrace_1586023
  have hstable : (prefixWord ++ tailWord_1586023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586023).length < 2 ^ (prefixWord ++ tailWord_1586023).sum := by decide
  have hdescent : baseEnd_1586023 < baseStart_1586023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586053 : List Nat := [1, 3, 1, 1, 3, 5, 2, 7]
def baseStart_1586053 : Nat := 118140960795 + 1586053 * 2 ^ 59
def prefixEnd_1586053 : Nat := 4983230072969 + 3 ^ 40 * 1586053 * 2
def baseEnd_1586053 : Nat := 30163241944651418297903

theorem tailTrace_1586053 : CollatzResearch.WordTrace tailWord_1586053 prefixEnd_1586053 30163241944651418297903 := by
  unfold tailWord_1586053
  simp only [CollatzResearch.WordTrace]
  refine ⟨57848105323008332131946813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38565403548672221421297875 57848105323008332131946813)
  ·
    refine ⟨21693039496128124549480055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57848105323008332131946813 21693039496128124549480055)
    ·
      refine ⟨32539559244192186824220083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21693039496128124549480055 32539559244192186824220083)
      ·
        refine ⟨48809338866288280236330125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32539559244192186824220083 48809338866288280236330125)
        ·
          refine ⟨18303502074858105088623797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48809338866288280236330125 18303502074858105088623797)
          ·
            refine ⟨1715953319517947352058481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18303502074858105088623797 1715953319517947352058481)
            ·
              refine ⟨1286964989638460514043861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1715953319517947352058481 1286964989638460514043861)
              ·
                refine ⟨30163241944651418297903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1286964989638460514043861 30163241944651418297903)
                ·
                  rfl

theorem cell23_1586053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 7].length) (baseStart_1586053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586053 prefixEnd_1586053 := by exact prefixLift 1586053
  have htrace : WordTrace (prefixWord ++ tailWord_1586053) baseStart_1586053 baseEnd_1586053 := by
    simpa [prefixWord, tailWord_1586053, baseEnd_1586053] using wordTrace_append hprefix tailTrace_1586053
  have hstable : (prefixWord ++ tailWord_1586053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586053).length < 2 ^ (prefixWord ++ tailWord_1586053).sum := by decide
  have hdescent : baseEnd_1586053 < baseStart_1586053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586070 : List Nat := [5, 3, 1, 1, 1, 1, 11]
def baseStart_1586070 : Nat := 118140960795 + 1586070 * 2 ^ 59
def prefixEnd_1586070 : Nat := 4983230072969 + 3 ^ 40 * 1586070 * 2
def baseEnd_1586070 : Nat := 10054521749095243549763

theorem tailTrace_1586070 : CollatzResearch.WordTrace tailWord_1586070 prefixEnd_1586070 10054521749095243549763 := by
  unfold tailWord_1586070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3615545335246671502207229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38565816909297829356877109 3615545335246671502207229)
  ·
    refine ⟨1355829500717501813327711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3615545335246671502207229 1355829500717501813327711)
    ·
      refine ⟨2033744251076252719991567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1355829500717501813327711 2033744251076252719991567)
      ·
        refine ⟨3050616376614379079987351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2033744251076252719991567 3050616376614379079987351)
        ·
          refine ⟨4575924564921568619981027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3050616376614379079987351 4575924564921568619981027)
          ·
            refine ⟨6863886847382352929971541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4575924564921568619981027 6863886847382352929971541)
            ·
              refine ⟨10054521749095243549763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6863886847382352929971541 10054521749095243549763)
              ·
                rfl

theorem cell23_1586070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 11].length) (baseStart_1586070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586070 prefixEnd_1586070 := by exact prefixLift 1586070
  have htrace : WordTrace (prefixWord ++ tailWord_1586070) baseStart_1586070 baseEnd_1586070 := by
    simpa [prefixWord, tailWord_1586070, baseEnd_1586070] using wordTrace_append hprefix tailTrace_1586070
  have hstable : (prefixWord ++ tailWord_1586070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586070).length < 2 ^ (prefixWord ++ tailWord_1586070).sum := by decide
  have hdescent : baseEnd_1586070 < baseStart_1586070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586073 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 5, 3, 2]
def baseStart_1586073 : Nat := 118140960795 + 1586073 * 2 ^ 59
def prefixEnd_1586073 : Nat := 4983230072969 + 3 ^ 40 * 1586073 * 2
def baseEnd_1586073 : Nat := 814417802118678215793289

theorem tailTrace_1586073 : CollatzResearch.WordTrace tailWord_1586073 prefixEnd_1586073 814417802118678215793289 := by
  unfold tailWord_1586073
  simp only [CollatzResearch.WordTrace]
  refine ⟨57848834782935875547674873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38565889855290583698449915 57848834782935875547674873)
  ·
    refine ⟨43386626087201906660756155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57848834782935875547674873 43386626087201906660756155)
    ·
      refine ⟨65079939130802859991134233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43386626087201906660756155 65079939130802859991134233)
      ·
        refine ⟨48809954348102144993350675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65079939130802859991134233 48809954348102144993350675)
        ·
          refine ⟨73214931522153217490026013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48809954348102144993350675 73214931522153217490026013)
          ·
            refine ⟨27455599320807456558759755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73214931522153217490026013 27455599320807456558759755)
            ·
              refine ⟨41183398981211184838139633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27455599320807456558759755 41183398981211184838139633)
              ·
                refine ⟨30887549235908388628604725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41183398981211184838139633 30887549235908388628604725)
                ·
                  refine ⟨2895707740866411433931693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30887549235908388628604725 2895707740866411433931693)
                  ·
                    refine ⟨1085890402824904287724385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2895707740866411433931693 1085890402824904287724385)
                    ·
                      refine ⟨814417802118678215793289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1085890402824904287724385 814417802118678215793289)
                      ·
                        rfl

theorem cell23_1586073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 3, 2].length) (baseStart_1586073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586073 prefixEnd_1586073 := by exact prefixLift 1586073
  have htrace : WordTrace (prefixWord ++ tailWord_1586073) baseStart_1586073 baseEnd_1586073 := by
    simpa [prefixWord, tailWord_1586073, baseEnd_1586073] using wordTrace_append hprefix tailTrace_1586073
  have hstable : (prefixWord ++ tailWord_1586073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586073).length < 2 ^ (prefixWord ++ tailWord_1586073).sum := by decide
  have hdescent : baseEnd_1586073 < baseStart_1586073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586081 : List Nat := [1, 2, 3, 4, 1, 2, 3, 2, 1, 2, 2]
def baseStart_1586081 : Nat := 118140960795 + 1586081 * 2 ^ 59
def prefixEnd_1586081 : Nat := 4983230072969 + 3 ^ 40 * 1586081 * 2
def baseEnd_1586081 : Nat := 814421909963914184493253

theorem tailTrace_1586081 : CollatzResearch.WordTrace tailWord_1586081 prefixEnd_1586081 814421909963914184493253 := by
  unfold tailWord_1586081
  simp only [CollatzResearch.WordTrace]
  refine ⟨57849126566906892913966097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38566084377937928609310731 57849126566906892913966097)
  ·
    refine ⟨43386844925180169685474573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57849126566906892913966097 43386844925180169685474573)
    ·
      refine ⟨16270066846942563632052965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43386844925180169685474573 16270066846942563632052965)
      ·
        refine ⟨3050637533801730681009931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16270066846942563632052965 3050637533801730681009931)
        ·
          refine ⟨4575956300702596021514897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3050637533801730681009931 4575956300702596021514897)
          ·
            refine ⟨3431967225526947016136173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4575956300702596021514897 3431967225526947016136173)
            ·
              refine ⟨1286987709572605131051065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3431967225526947016136173 1286987709572605131051065)
              ·
                refine ⟨965240782179453848288299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286987709572605131051065 965240782179453848288299)
                ·
                  refine ⟨1447861173269180772432449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965240782179453848288299 1447861173269180772432449)
                  ·
                    refine ⟨1085895879951885579324337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1447861173269180772432449 1085895879951885579324337)
                    ·
                      refine ⟨814421909963914184493253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1085895879951885579324337 814421909963914184493253)
                      ·
                        rfl

theorem cell23_1586081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_1586081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586081 prefixEnd_1586081 := by exact prefixLift 1586081
  have htrace : WordTrace (prefixWord ++ tailWord_1586081) baseStart_1586081 baseEnd_1586081 := by
    simpa [prefixWord, tailWord_1586081, baseEnd_1586081] using wordTrace_append hprefix tailTrace_1586081
  have hstable : (prefixWord ++ tailWord_1586081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586081).length < 2 ^ (prefixWord ++ tailWord_1586081).sum := by decide
  have hdescent : baseEnd_1586081 < baseStart_1586081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586097 : List Nat := [1, 2, 2, 4, 3, 1, 1, 3, 2, 1, 3]
def baseStart_1586097 : Nat := 118140960795 + 1586097 * 2 ^ 59
def prefixEnd_1586097 : Nat := 4983230072969 + 3 ^ 40 * 1586097 * 2
def baseEnd_1586097 : Nat := 814430125654386121893179

theorem tailTrace_1586097 : CollatzResearch.WordTrace tailWord_1586097 prefixEnd_1586097 814430125654386121893179 := by
  unfold tailWord_1586097
  simp only [CollatzResearch.WordTrace]
  refine ⟨57849710134848927646548545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38566473423232618431032363 57849710134848927646548545)
  ·
    refine ⟨43387282601136695734911409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57849710134848927646548545 43387282601136695734911409)
    ·
      refine ⟨32540461950852521801183557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43387282601136695734911409 32540461950852521801183557)
      ·
        refine ⟨6101336615784847837721917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32540461950852521801183557 6101336615784847837721917)
        ·
          refine ⟨2288001230919317939145719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6101336615784847837721917 2288001230919317939145719)
          ·
            refine ⟨3432001846378976908718579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288001230919317939145719 3432001846378976908718579)
            ·
              refine ⟨5148002769568465363077869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3432001846378976908718579 5148002769568465363077869)
              ·
                refine ⟨1930501038588174511154201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5148002769568465363077869 1930501038588174511154201)
                ·
                  refine ⟨1447875778941130883365651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1930501038588174511154201 1447875778941130883365651)
                  ·
                    refine ⟨2171813668411696325048477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1447875778941130883365651 2171813668411696325048477)
                    ·
                      refine ⟨814430125654386121893179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2171813668411696325048477 814430125654386121893179)
                      ·
                        rfl

theorem cell23_1586097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_1586097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586097 prefixEnd_1586097 := by exact prefixLift 1586097
  have htrace : WordTrace (prefixWord ++ tailWord_1586097) baseStart_1586097 baseEnd_1586097 := by
    simpa [prefixWord, tailWord_1586097, baseEnd_1586097] using wordTrace_append hprefix tailTrace_1586097
  have hstable : (prefixWord ++ tailWord_1586097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586097).length < 2 ^ (prefixWord ++ tailWord_1586097).sum := by decide
  have hdescent : baseEnd_1586097 < baseStart_1586097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586106 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_1586106 : Nat := 118140960795 + 1586106 * 2 ^ 59
def prefixEnd_1586106 : Nat := 4983230072969 + 3 ^ 40 * 1586106 * 2
def baseEnd_1586106 : Nat := 814434746980276586680637

theorem tailTrace_1586106 : CollatzResearch.WordTrace tailWord_1586106 prefixEnd_1586106 814434746980276586680637 := by
  unfold tailWord_1586106
  simp only [CollatzResearch.WordTrace]
  refine ⟨14462509597954080545906543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38566692261210881455750781 14462509597954080545906543)
  ·
    refine ⟨21693764396931120818859815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14462509597954080545906543 21693764396931120818859815)
    ·
      refine ⟨32540646595396681228289723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21693764396931120818859815 32540646595396681228289723)
      ·
        refine ⟨48810969893095021842434585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32540646595396681228289723 48810969893095021842434585)
        ·
          refine ⟨36608227419821266381825939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48810969893095021842434585 36608227419821266381825939)
          ·
            refine ⟨54912341129731899572738909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36608227419821266381825939 54912341129731899572738909)
            ·
              refine ⟨20592127923649462339777091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54912341129731899572738909 20592127923649462339777091)
              ·
                refine ⟨30888191885474193509665637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20592127923649462339777091 30888191885474193509665637)
                ·
                  refine ⟨5791535978526411283062307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30888191885474193509665637 5791535978526411283062307)
                  ·
                    refine ⟨8687303967789616924593461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5791535978526411283062307 8687303967789616924593461)
                    ·
                      refine ⟨814434746980276586680637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8687303967789616924593461 814434746980276586680637)
                      ·
                        rfl

theorem cell23_1586106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_1586106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586106 prefixEnd_1586106 := by exact prefixLift 1586106
  have htrace : WordTrace (prefixWord ++ tailWord_1586106) baseStart_1586106 baseEnd_1586106 := by
    simpa [prefixWord, tailWord_1586106, baseEnd_1586106] using wordTrace_append hprefix tailTrace_1586106
  have hstable : (prefixWord ++ tailWord_1586106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586106).length < 2 ^ (prefixWord ++ tailWord_1586106).sum := by decide
  have hdescent : baseEnd_1586106 < baseStart_1586106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586118 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_1586118 : Nat := 118140960795 + 1586118 * 2 ^ 59
def prefixEnd_1586118 : Nat := 4983230072969 + 3 ^ 40 * 1586118 * 2
def baseEnd_1586118 : Nat := 814440908748130539730583

theorem tailTrace_1586118 : CollatzResearch.WordTrace tailWord_1586118 prefixEnd_1586118 814440908748130539730583 := by
  unfold tailWord_1586118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1807827377117901507283219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38566984045181898822042005 1807827377117901507283219)
  ·
    refine ⟨2711741065676852260924829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1807827377117901507283219 2711741065676852260924829)
    ·
      refine ⟨1016902899628819597846811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2711741065676852260924829 1016902899628819597846811)
      ·
        refine ⟨1525354349443229396770217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016902899628819597846811 1525354349443229396770217)
        ·
          refine ⟨1144015762082422047577663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1525354349443229396770217 1144015762082422047577663)
          ·
            refine ⟨1716023643123633071366495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144015762082422047577663 1716023643123633071366495)
            ·
              refine ⟨2574035464685449607049743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1716023643123633071366495 2574035464685449607049743)
              ·
                refine ⟨3861053197028174410574615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574035464685449607049743 3861053197028174410574615)
                ·
                  refine ⟨5791579795542261615861923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3861053197028174410574615 5791579795542261615861923)
                  ·
                    refine ⟨8687369693313392423792885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5791579795542261615861923 8687369693313392423792885)
                    ·
                      refine ⟨814440908748130539730583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8687369693313392423792885 814440908748130539730583)
                      ·
                        rfl

theorem cell23_1586118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_1586118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586118 prefixEnd_1586118 := by exact prefixLift 1586118
  have htrace : WordTrace (prefixWord ++ tailWord_1586118) baseStart_1586118 baseEnd_1586118 := by
    simpa [prefixWord, tailWord_1586118, baseEnd_1586118] using wordTrace_append hprefix tailTrace_1586118
  have hstable : (prefixWord ++ tailWord_1586118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586118).length < 2 ^ (prefixWord ++ tailWord_1586118).sum := by decide
  have hdescent : baseEnd_1586118 < baseStart_1586118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586137 : List Nat := [1, 2, 1, 2, 5, 1, 1, 4, 2, 2, 2]
def baseStart_1586137 : Nat := 118140960795 + 1586137 * 2 ^ 59
def prefixEnd_1586137 : Nat := 4983230072969 + 3 ^ 40 * 1586137 * 2
def baseEnd_1586137 : Nat := 814450664880565965392995

theorem tailTrace_1586137 : CollatzResearch.WordTrace tailWord_1586137 prefixEnd_1586137 814450664880565965392995 := by
  unfold tailWord_1586137
  simp only [CollatzResearch.WordTrace]
  refine ⟨57851169054704014478004665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38567446036469342985336443 57851169054704014478004665)
  ·
    refine ⟨43388376791028010858503499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57851169054704014478004665 43388376791028010858503499)
    ·
      refine ⟨65082565186542016287755249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43388376791028010858503499 65082565186542016287755249)
      ·
        refine ⟨48811923889906512215816437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65082565186542016287755249 48811923889906512215816437)
        ·
          refine ⟨4576117864678735520232791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48811923889906512215816437 4576117864678735520232791)
          ·
            refine ⟨6864176797018103280349187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4576117864678735520232791 6864176797018103280349187)
            ·
              refine ⟨10296265195527154920523781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6864176797018103280349187 10296265195527154920523781)
              ·
                refine ⟨1930549724161341547598209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10296265195527154920523781 1930549724161341547598209)
                ·
                  refine ⟨1447912293121006160698657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1930549724161341547598209 1447912293121006160698657)
                  ·
                    refine ⟨1085934219840754620523993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1447912293121006160698657 1085934219840754620523993)
                    ·
                      refine ⟨814450664880565965392995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1085934219840754620523993 814450664880565965392995)
                      ·
                        rfl

theorem cell23_1586137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 2, 2].length) (baseStart_1586137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586137 prefixEnd_1586137 := by exact prefixLift 1586137
  have htrace : WordTrace (prefixWord ++ tailWord_1586137) baseStart_1586137 baseEnd_1586137 := by
    simpa [prefixWord, tailWord_1586137, baseEnd_1586137] using wordTrace_append hprefix tailTrace_1586137
  have hstable : (prefixWord ++ tailWord_1586137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586137).length < 2 ^ (prefixWord ++ tailWord_1586137).sum := by decide
  have hdescent : baseEnd_1586137 < baseStart_1586137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586193 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 4]
def baseStart_1586193 : Nat := 118140960795 + 1586193 * 2 ^ 59
def prefixEnd_1586193 : Nat := 4983230072969 + 3 ^ 40 * 1586193 * 2
def baseEnd_1586193 : Nat := 814479419797217746292737

theorem tailTrace_1586193 : CollatzResearch.WordTrace tailWord_1586193 prefixEnd_1586193 814479419797217746292737 := by
  unfold tailWord_1586193
  simp only [CollatzResearch.WordTrace]
  refine ⟨57853211542501136042043233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38568807695000757361362155 57853211542501136042043233)
  ·
    refine ⟨43389908656875852031532425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57853211542501136042043233 43389908656875852031532425)
    ·
      refine ⟨32542431492656889023649319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43389908656875852031532425 32542431492656889023649319)
      ·
        refine ⟨48813647238985333535473979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32542431492656889023649319 48813647238985333535473979)
        ·
          refine ⟨73220470858478000303210969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48813647238985333535473979 73220470858478000303210969)
          ·
            refine ⟨54915353143858500227408227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73220470858478000303210969 54915353143858500227408227)
            ·
              refine ⟨82373029715787750341112341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54915353143858500227408227 82373029715787750341112341)
              ·
                refine ⟨3861235767927550797239641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82373029715787750341112341 3861235767927550797239641)
                ·
                  refine ⟨2895926825945663097929731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3861235767927550797239641 2895926825945663097929731)
                  ·
                    refine ⟨4343890238918494646894597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2895926825945663097929731 4343890238918494646894597)
                    ·
                      refine ⟨814479419797217746292737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4343890238918494646894597 814479419797217746292737)
                      ·
                        rfl

theorem cell23_1586193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_1586193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586193 prefixEnd_1586193 := by exact prefixLift 1586193
  have htrace : WordTrace (prefixWord ++ tailWord_1586193) baseStart_1586193 baseEnd_1586193 := by
    simpa [prefixWord, tailWord_1586193, baseEnd_1586193] using wordTrace_append hprefix tailTrace_1586193
  have hstable : (prefixWord ++ tailWord_1586193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586193).length < 2 ^ (prefixWord ++ tailWord_1586193).sum := by decide
  have hdescent : baseEnd_1586193 < baseStart_1586193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586194 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 7]
def baseStart_1586194 : Nat := 118140960795 + 1586194 * 2 ^ 59
def prefixEnd_1586194 : Nat := 4983230072969 + 3 ^ 40 * 1586194 * 2
def baseEnd_1586194 : Nat := 90497770364208026931137

theorem tailTrace_1586194 : CollatzResearch.WordTrace tailWord_1586194 prefixEnd_1586194 90497770364208026931137 := by
  unfold tailWord_1586194
  simp only [CollatzResearch.WordTrace]
  refine ⟨14463312003874378303207409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38568832010331675475219757 14463312003874378303207409)
  ·
    refine ⟨10847484002905783727405557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14463312003874378303207409 10847484002905783727405557)
    ·
      refine ⟨1016951625272417224444271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10847484002905783727405557 1016951625272417224444271)
      ·
        refine ⟨1525427437908625836666407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016951625272417224444271 1525427437908625836666407)
        ·
          refine ⟨2288141156862938754999611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1525427437908625836666407 2288141156862938754999611)
          ·
            refine ⟨3432211735294408132499417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288141156862938754999611 3432211735294408132499417)
            ·
              refine ⟨2574158801470806099374563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3432211735294408132499417 2574158801470806099374563)
              ·
                refine ⟨3861238202206209149061845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574158801470806099374563 3861238202206209149061845)
                ·
                  refine ⟨90497770364208026931137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3861238202206209149061845 90497770364208026931137)
                  ·
                    rfl

theorem cell23_1586194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_1586194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586194 prefixEnd_1586194 := by exact prefixLift 1586194
  have htrace : WordTrace (prefixWord ++ tailWord_1586194) baseStart_1586194 baseEnd_1586194 := by
    simpa [prefixWord, tailWord_1586194, baseEnd_1586194] using wordTrace_append hprefix tailTrace_1586194
  have hstable : (prefixWord ++ tailWord_1586194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586194).length < 2 ^ (prefixWord ++ tailWord_1586194).sum := by decide
  have hdescent : baseEnd_1586194 < baseStart_1586194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586213 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 3, 4, 3]
def baseStart_1586213 : Nat := 118140960795 + 1586213 * 2 ^ 59
def prefixEnd_1586213 : Nat := 4983230072969 + 3 ^ 40 * 1586213 * 2
def baseEnd_1586213 : Nat := 814489689410307668042645

theorem tailTrace_1586213 : CollatzResearch.WordTrace tailWord_1586213 prefixEnd_1586213 814489689410307668042645 := by
  unfold tailWord_1586213
  simp only [CollatzResearch.WordTrace]
  refine ⟨57853941002428679457771293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38569294001619119638514195 57853941002428679457771293)
  ·
    refine ⟨21695227875910754796664235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57853941002428679457771293 21695227875910754796664235)
    ·
      refine ⟨32542841813866132194996353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21695227875910754796664235 32542841813866132194996353)
      ·
        refine ⟨24407131360399599146247265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32542841813866132194996353 24407131360399599146247265)
        ·
          refine ⟨18305348520299699359685449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24407131360399599146247265 18305348520299699359685449)
          ·
            refine ⟨13729011390224774519764087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18305348520299699359685449 13729011390224774519764087)
            ·
              refine ⟨20593517085337161779646131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13729011390224774519764087 20593517085337161779646131)
              ·
                refine ⟨30890275628005742669469197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20593517085337161779646131 30890275628005742669469197)
                ·
                  refine ⟨11583853360502153501050949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30890275628005742669469197 11583853360502153501050949)
                  ·
                    refine ⟨2171972505094153781447053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11583853360502153501050949 2171972505094153781447053)
                    ·
                      refine ⟨814489689410307668042645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2171972505094153781447053 814489689410307668042645)
                      ·
                        rfl

theorem cell23_1586213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_1586213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586213 prefixEnd_1586213 := by exact prefixLift 1586213
  have htrace : WordTrace (prefixWord ++ tailWord_1586213) baseStart_1586213 baseEnd_1586213 := by
    simpa [prefixWord, tailWord_1586213, baseEnd_1586213] using wordTrace_append hprefix tailTrace_1586213
  have hstable : (prefixWord ++ tailWord_1586213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586213).length < 2 ^ (prefixWord ++ tailWord_1586213).sum := by decide
  have hdescent : baseEnd_1586213 < baseStart_1586213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586233 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 8]
def baseStart_1586233 : Nat := 118140960795 + 1586233 * 2 ^ 59
def prefixEnd_1586233 : Nat := 4983230072969 + 3 ^ 40 * 1586233 * 2
def baseEnd_1586233 : Nat := 90499995447044176643617

theorem tailTrace_1586233 : CollatzResearch.WordTrace tailWord_1586233 prefixEnd_1586233 90499995447044176643617 := by
  unfold tailWord_1586233
  simp only [CollatzResearch.WordTrace]
  refine ⟨57854670462356222873499353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38569780308237481915666235 57854670462356222873499353)
  ·
    refine ⟨43391002846767167155124515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57854670462356222873499353 43391002846767167155124515)
    ·
      refine ⟨65086504270150750732686773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43391002846767167155124515 65086504270150750732686773)
      ·
        refine ⟨6101859775326632881189385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65086504270150750732686773 6101859775326632881189385)
        ·
          refine ⟨4576394831494974660892039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6101859775326632881189385 4576394831494974660892039)
          ·
            refine ⟨6864592247242461991338059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4576394831494974660892039 6864592247242461991338059)
            ·
              refine ⟨10296888370863692987007089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6864592247242461991338059 10296888370863692987007089)
              ·
                refine ⟨7722666278147769740255317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10296888370863692987007089 7722666278147769740255317)
                ·
                  refine ⟨90499995447044176643617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7722666278147769740255317 90499995447044176643617)
                  ·
                    rfl

theorem cell23_1586233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 8].length) (baseStart_1586233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586233 prefixEnd_1586233 := by exact prefixLift 1586233
  have htrace : WordTrace (prefixWord ++ tailWord_1586233) baseStart_1586233 baseEnd_1586233 := by
    simpa [prefixWord, tailWord_1586233, baseEnd_1586233] using wordTrace_append hprefix tailTrace_1586233
  have hstable : (prefixWord ++ tailWord_1586233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586233).length < 2 ^ (prefixWord ++ tailWord_1586233).sum := by decide
  have hdescent : baseEnd_1586233 < baseStart_1586233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586254 : List Nat := [4, 1, 1, 1, 1, 3, 5, 2, 1, 4]
def baseStart_1586254 : Nat := 118140960795 + 1586254 * 2 ^ 59
def prefixEnd_1586254 : Nat := 4983230072969 + 3 ^ 40 * 1586254 * 2
def baseEnd_1586254 : Nat := 271503580705714002543319

theorem tailTrace_1586254 : CollatzResearch.WordTrace tailWord_1586254 prefixEnd_1586254 271503580705714002543319 := by
  unfold tailWord_1586254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7231929549410017932501727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38570290930186762306675877 7231929549410017932501727)
  ·
    refine ⟨10847894324115026898752591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7231929549410017932501727 10847894324115026898752591)
    ·
      refine ⟨16271841486172540348128887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10847894324115026898752591 16271841486172540348128887)
      ·
        refine ⟨24407762229258810522193331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16271841486172540348128887 24407762229258810522193331)
        ·
          refine ⟨36611643343888215783289997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24407762229258810522193331 36611643343888215783289997)
          ·
            refine ⟨13729366253958080918733749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36611643343888215783289997 13729366253958080918733749)
            ·
              refine ⟨1287128086308570086131289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13729366253958080918733749 1287128086308570086131289)
              ·
                refine ⟨965346064731427564598467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1287128086308570086131289 965346064731427564598467)
                ·
                  refine ⟨1448019097097141346897701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965346064731427564598467 1448019097097141346897701)
                  ·
                    refine ⟨271503580705714002543319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1448019097097141346897701 271503580705714002543319)
                    ·
                      rfl

theorem cell23_1586254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_1586254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586254 prefixEnd_1586254 := by exact prefixLift 1586254
  have htrace : WordTrace (prefixWord ++ tailWord_1586254) baseStart_1586254 baseEnd_1586254 := by
    simpa [prefixWord, tailWord_1586254, baseEnd_1586254] using wordTrace_append hprefix tailTrace_1586254
  have hstable : (prefixWord ++ tailWord_1586254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586254).length < 2 ^ (prefixWord ++ tailWord_1586254).sum := by decide
  have hdescent : baseEnd_1586254 < baseStart_1586254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586263 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 3, 5]
def baseStart_1586263 : Nat := 118140960795 + 1586263 * 2 ^ 59
def prefixEnd_1586263 : Nat := 4983230072969 + 3 ^ 40 * 1586263 * 2
def baseEnd_1586263 : Nat := 271505121147677490805805

theorem tailTrace_1586263 : CollatzResearch.WordTrace tailWord_1586263 prefixEnd_1586263 271505121147677490805805 := by
  unfold tailWord_1586263
  simp only [CollatzResearch.WordTrace]
  refine ⟨57855764652247537997091443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38570509768165025331394295 57855764652247537997091443)
  ·
    refine ⟨86783646978371306995637165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57855764652247537997091443 86783646978371306995637165)
    ·
      refine ⟨32543867616889240123363937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86783646978371306995637165 32543867616889240123363937)
      ·
        refine ⟨24407900712666930092522953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32543867616889240123363937 24407900712666930092522953)
        ·
          refine ⟨18305925534500197569392215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24407900712666930092522953 18305925534500197569392215)
          ·
            refine ⟨27458888301750296354088323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18305925534500197569392215 27458888301750296354088323)
            ·
              refine ⟨41188332452625444531132485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27458888301750296354088323 41188332452625444531132485)
              ·
                refine ⟨7722812334867270849587341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41188332452625444531132485 7722812334867270849587341)
                ·
                  refine ⟨2896054625575226568595253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7722812334867270849587341 2896054625575226568595253)
                  ·
                    refine ⟨271505121147677490805805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2896054625575226568595253 271505121147677490805805)
                    ·
                      rfl

theorem cell23_1586263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_1586263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586263 prefixEnd_1586263 := by exact prefixLift 1586263
  have htrace : WordTrace (prefixWord ++ tailWord_1586263) baseStart_1586263 baseEnd_1586263 := by
    simpa [prefixWord, tailWord_1586263, baseEnd_1586263] using wordTrace_append hprefix tailTrace_1586263
  have hstable : (prefixWord ++ tailWord_1586263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586263).length < 2 ^ (prefixWord ++ tailWord_1586263).sum := by decide
  have hdescent : baseEnd_1586263 < baseStart_1586263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586287 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 2, 3, 2]
def baseStart_1586287 : Nat := 118140960795 + 1586287 * 2 ^ 59
def prefixEnd_1586287 : Nat := 4983230072969 + 3 ^ 40 * 1586287 * 2
def baseEnd_1586287 : Nat := 814527686978740378517305

theorem tailTrace_1586287 : CollatzResearch.WordTrace tailWord_1586287 prefixEnd_1586287 814527686978740378517305 := by
  unfold tailWord_1586287
  simp only [CollatzResearch.WordTrace]
  refine ⟨57856640004160590095965115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38571093336107060063976743 57856640004160590095965115)
  ·
    refine ⟨86784960006240885143947673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57856640004160590095965115 86784960006240885143947673)
    ·
      refine ⟨65088720004680663857960755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86784960006240885143947673 65088720004680663857960755)
      ·
        refine ⟨97633080007020995786941133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65088720004680663857960755 97633080007020995786941133)
        ·
          refine ⟨36612405002632873420102925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97633080007020995786941133 36612405002632873420102925)
          ·
            refine ⟨13729651875987327532538597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36612405002632873420102925 13729651875987327532538597)
            ·
              refine ⟨2574309726747623912350987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13729651875987327532538597 2574309726747623912350987)
              ·
                refine ⟨3861464590121435868526481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574309726747623912350987 3861464590121435868526481)
                ·
                  refine ⟨2896098442591076901394861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3861464590121435868526481 2896098442591076901394861)
                  ·
                    refine ⟨1086036915971653838023073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896098442591076901394861 1086036915971653838023073)
                    ·
                      refine ⟨814527686978740378517305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1086036915971653838023073 814527686978740378517305)
                      ·
                        rfl

theorem cell23_1586287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 3, 2].length) (baseStart_1586287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586287 prefixEnd_1586287 := by exact prefixLift 1586287
  have htrace : WordTrace (prefixWord ++ tailWord_1586287) baseStart_1586287 baseEnd_1586287 := by
    simpa [prefixWord, tailWord_1586287, baseEnd_1586287] using wordTrace_append hprefix tailTrace_1586287
  have hstable : (prefixWord ++ tailWord_1586287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586287).length < 2 ^ (prefixWord ++ tailWord_1586287).sum := by decide
  have hdescent : baseEnd_1586287 < baseStart_1586287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586323 : List Nat := [1, 1, 1, 2, 1, 2, 7, 8]
def baseStart_1586323 : Nat := 118140960795 + 1586323 * 2 ^ 59
def prefixEnd_1586323 : Nat := 4983230072969 + 3 ^ 40 * 1586323 * 2
def baseEnd_1586323 : Nat := 30168376751196379172857

theorem tailTrace_1586323 : CollatzResearch.WordTrace tailWord_1586323 prefixEnd_1586323 30168376751196379172857 := by
  unfold tailWord_1586323
  simp only [CollatzResearch.WordTrace]
  refine ⟨57857953032030168244275623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38571968688020112162850415 57857953032030168244275623)
  ·
    refine ⟨86786929548045252366413435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57857953032030168244275623 86786929548045252366413435)
    ·
      refine ⟨130180394322067878549620153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86786929548045252366413435 130180394322067878549620153)
      ·
        refine ⟨97635295741550908912215115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130180394322067878549620153 97635295741550908912215115)
        ·
          refine ⟨146452943612326363368322673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97635295741550908912215115 146452943612326363368322673)
          ·
            refine ⟨109839707709244772526242005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146452943612326363368322673 109839707709244772526242005)
            ·
              refine ⟨2574368149435424356083797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 109839707709244772526242005 2574368149435424356083797)
              ·
                refine ⟨30168376751196379172857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2574368149435424356083797 30168376751196379172857)
                ·
                  rfl

theorem cell23_1586323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 8].length) (baseStart_1586323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586323 prefixEnd_1586323 := by exact prefixLift 1586323
  have htrace : WordTrace (prefixWord ++ tailWord_1586323) baseStart_1586323 baseEnd_1586323 := by
    simpa [prefixWord, tailWord_1586323, baseEnd_1586323] using wordTrace_append hprefix tailTrace_1586323
  have hstable : (prefixWord ++ tailWord_1586323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586323).length < 2 ^ (prefixWord ++ tailWord_1586323).sum := by decide
  have hdescent : baseEnd_1586323 < baseStart_1586323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586327 : List Nat := [1, 1, 3, 3, 3, 1, 2, 3, 2, 4]
def baseStart_1586327 : Nat := 118140960795 + 1586327 * 2 ^ 59
def prefixEnd_1586327 : Nat := 4983230072969 + 3 ^ 40 * 1586327 * 2
def baseEnd_1586327 : Nat := 271516075401640074005707

theorem tailTrace_1586327 : CollatzResearch.WordTrace tailWord_1586327 prefixEnd_1586327 271516075401640074005707 := by
  unfold tailWord_1586327
  simp only [CollatzResearch.WordTrace]
  refine ⟨57858098924015676927421235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38572065949343784618280823 57858098924015676927421235)
  ·
    refine ⟨86787148386023515391131853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57858098924015676927421235 86787148386023515391131853)
    ·
      refine ⟨32545180644758818271674445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86787148386023515391131853 32545180644758818271674445)
      ·
        refine ⟨12204442741784556851877917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32545180644758818271674445 12204442741784556851877917)
        ·
          refine ⟨4576666028169208819454219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12204442741784556851877917 4576666028169208819454219)
          ·
            refine ⟨6864999042253813229181329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4576666028169208819454219 6864999042253813229181329)
            ·
              refine ⟨5148749281690359921885997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6864999042253813229181329 5148749281690359921885997)
              ·
                refine ⟨1930780980633884970707249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5148749281690359921885997 1930780980633884970707249)
                ·
                  refine ⟨1448085735475413728030437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1930780980633884970707249 1448085735475413728030437)
                  ·
                    refine ⟨271516075401640074005707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1448085735475413728030437 271516075401640074005707)
                    ·
                      rfl

theorem cell23_1586327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_1586327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586327 prefixEnd_1586327 := by exact prefixLift 1586327
  have htrace : WordTrace (prefixWord ++ tailWord_1586327) baseStart_1586327 baseEnd_1586327 := by
    simpa [prefixWord, tailWord_1586327, baseEnd_1586327] using wordTrace_append hprefix tailTrace_1586327
  have hstable : (prefixWord ++ tailWord_1586327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586327).length < 2 ^ (prefixWord ++ tailWord_1586327).sum := by decide
  have hdescent : baseEnd_1586327 < baseStart_1586327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586337 : List Nat := [1, 2, 3, 3, 1, 1, 2, 4, 1, 2, 3]
def baseStart_1586337 : Nat := 118140960795 + 1586337 * 2 ^ 59
def prefixEnd_1586337 : Nat := 4983230072969 + 3 ^ 40 * 1586337 * 2
def baseEnd_1586337 : Nat := 814553361011465182892075

theorem tailTrace_1586337 : CollatzResearch.WordTrace tailWord_1586337 prefixEnd_1586337 814553361011465182892075 := by
  unfold tailWord_1586337
  simp only [CollatzResearch.WordTrace]
  refine ⟨57858463653979448635285265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38572309102652965756856843 57858463653979448635285265)
  ·
    refine ⟨43393847740484586476463949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57858463653979448635285265 43393847740484586476463949)
    ·
      refine ⟨16272692902681719928673981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43393847740484586476463949 16272692902681719928673981)
      ·
        refine ⟨6102259838505644973252743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16272692902681719928673981 6102259838505644973252743)
        ·
          refine ⟨9153389757758467459879115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6102259838505644973252743 9153389757758467459879115)
          ·
            refine ⟨13730084636637701189818673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9153389757758467459879115 13730084636637701189818673)
            ·
              refine ⟨10297563477478275892364005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13730084636637701189818673 10297563477478275892364005)
              ·
                refine ⟨1930793152027176729818251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10297563477478275892364005 1930793152027176729818251)
                ·
                  refine ⟨2896189728040765094727377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930793152027176729818251 2896189728040765094727377)
                  ·
                    refine ⟨2172142296030573821045533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2896189728040765094727377 2172142296030573821045533)
                    ·
                      refine ⟨814553361011465182892075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2172142296030573821045533 814553361011465182892075)
                      ·
                        rfl

theorem cell23_1586337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_1586337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586337 prefixEnd_1586337 := by exact prefixLift 1586337
  have htrace : WordTrace (prefixWord ++ tailWord_1586337) baseStart_1586337 baseEnd_1586337 := by
    simpa [prefixWord, tailWord_1586337, baseEnd_1586337] using wordTrace_append hprefix tailTrace_1586337
  have hstable : (prefixWord ++ tailWord_1586337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586337).length < 2 ^ (prefixWord ++ tailWord_1586337).sum := by decide
  have hdescent : baseEnd_1586337 < baseStart_1586337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586338 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_1586338 : Nat := 118140960795 + 1586338 * 2 ^ 59
def prefixEnd_1586338 : Nat := 4983230072969 + 3 ^ 40 * 1586338 * 2
def baseEnd_1586338 : Nat := 814553874492119678979571

theorem tailTrace_1586338 : CollatzResearch.WordTrace tailWord_1586338 prefixEnd_1586338 814553874492119678979571 := by
  unfold tailWord_1586338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14464625031743956451517917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38572333417983883870714445 14464625031743956451517917)
  ·
    refine ⟨5424234386903983669319219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14464625031743956451517917 5424234386903983669319219)
    ·
      refine ⟨8136351580355975503978829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5424234386903983669319219 8136351580355975503978829)
      ·
        refine ⟨3051131842633490813992061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8136351580355975503978829 3051131842633490813992061)
        ·
          refine ⟨1144174440987559055247023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3051131842633490813992061 1144174440987559055247023)
          ·
            refine ⟨1716261661481338582870535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144174440987559055247023 1716261661481338582870535)
            ·
              refine ⟨2574392492222007874305803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1716261661481338582870535 2574392492222007874305803)
              ·
                refine ⟨3861588738333011811458705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574392492222007874305803 3861588738333011811458705)
                ·
                  refine ⟨2896191553749758858594029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3861588738333011811458705 2896191553749758858594029)
                  ·
                    refine ⟨1086071832656159571972761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896191553749758858594029 1086071832656159571972761)
                    ·
                      refine ⟨814553874492119678979571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1086071832656159571972761 814553874492119678979571)
                      ·
                        rfl

theorem cell23_1586338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_1586338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586338 prefixEnd_1586338 := by exact prefixLift 1586338
  have htrace : WordTrace (prefixWord ++ tailWord_1586338) baseStart_1586338 baseEnd_1586338 := by
    simpa [prefixWord, tailWord_1586338, baseEnd_1586338] using wordTrace_append hprefix tailTrace_1586338
  have hstable : (prefixWord ++ tailWord_1586338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586338).length < 2 ^ (prefixWord ++ tailWord_1586338).sum := by decide
  have hdescent : baseEnd_1586338 < baseStart_1586338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586354 : List Nat := [3, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3]
def baseStart_1586354 : Nat := 118140960795 + 1586354 * 2 ^ 59
def prefixEnd_1586354 : Nat := 4983230072969 + 3 ^ 40 * 1586354 * 2
def baseEnd_1586354 : Nat := 814562090182591616379497

theorem tailTrace_1586354 : CollatzResearch.WordTrace tailWord_1586354 prefixEnd_1586354 814562090182591616379497 := by
  unfold tailWord_1586354
  simp only [CollatzResearch.WordTrace]
  refine ⟨14464770923729465134663529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38572722463278573692436077 14464770923729465134663529)
  ·
    refine ⟨10848578192797098850997647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14464770923729465134663529 10848578192797098850997647)
    ·
      refine ⟨16272867289195648276496471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10848578192797098850997647 16272867289195648276496471)
      ·
        refine ⟨24409300933793472414744707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16272867289195648276496471 24409300933793472414744707)
        ·
          refine ⟨36613951400690208622117061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24409300933793472414744707 36613951400690208622117061)
          ·
            refine ⟨6865115887629414116646949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36613951400690208622117061 6865115887629414116646949)
            ·
              refine ⟨1287209228930515146871303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6865115887629414116646949 1287209228930515146871303)
              ·
                refine ⟨1930813843395772720306955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287209228930515146871303 1930813843395772720306955)
                ·
                  refine ⟨2896220765093659080460433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930813843395772720306955 2896220765093659080460433)
                  ·
                    refine ⟨2172165573820244310345325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2896220765093659080460433 2172165573820244310345325)
                    ·
                      refine ⟨814562090182591616379497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2172165573820244310345325 814562090182591616379497)
                      ·
                        rfl

theorem cell23_1586354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_1586354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586354 prefixEnd_1586354 := by exact prefixLift 1586354
  have htrace : WordTrace (prefixWord ++ tailWord_1586354) baseStart_1586354 baseEnd_1586354 := by
    simpa [prefixWord, tailWord_1586354, baseEnd_1586354] using wordTrace_append hprefix tailTrace_1586354
  have hstable : (prefixWord ++ tailWord_1586354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586354).length < 2 ^ (prefixWord ++ tailWord_1586354).sum := by decide
  have hdescent : baseEnd_1586354 < baseStart_1586354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586363 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 5]
def baseStart_1586363 : Nat := 118140960795 + 1586363 * 2 ^ 59
def prefixEnd_1586363 : Nat := 4983230072969 + 3 ^ 40 * 1586363 * 2
def baseEnd_1586363 : Nat := 814566711508482081166955

theorem tailTrace_1586363 : CollatzResearch.WordTrace tailWord_1586363 prefixEnd_1586363 814566711508482081166955 := by
  unfold tailWord_1586363
  simp only [CollatzResearch.WordTrace]
  refine ⟨57859411951885255075731743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38572941301256836717154495 57859411951885255075731743)
  ·
    refine ⟨86789117927827882613597615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57859411951885255075731743 86789117927827882613597615)
    ·
      refine ⟨130183676891741823920396423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86789117927827882613597615 130183676891741823920396423)
      ·
        refine ⟨195275515337612735880594635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130183676891741823920396423 195275515337612735880594635)
        ·
          refine ⟨292913273006419103820891953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195275515337612735880594635 292913273006419103820891953)
          ·
            refine ⟨219684954754814327865668965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292913273006419103820891953 219684954754814327865668965)
            ·
              refine ⟨41190929016527686474812931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 219684954754814327865668965 41190929016527686474812931)
              ·
                refine ⟨61786393524791529712219397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41190929016527686474812931 61786393524791529712219397)
                ·
                  refine ⟨11584948785898411821041137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61786393524791529712219397 11584948785898411821041137)
                  ·
                    refine ⟨8688711589423808865780853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11584948785898411821041137 8688711589423808865780853)
                    ·
                      refine ⟨814566711508482081166955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8688711589423808865780853 814566711508482081166955)
                      ·
                        rfl

theorem cell23_1586363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 5].length) (baseStart_1586363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586363 prefixEnd_1586363 := by exact prefixLift 1586363
  have htrace : WordTrace (prefixWord ++ tailWord_1586363) baseStart_1586363 baseEnd_1586363 := by
    simpa [prefixWord, tailWord_1586363, baseEnd_1586363] using wordTrace_append hprefix tailTrace_1586363
  have hstable : (prefixWord ++ tailWord_1586363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586363).length < 2 ^ (prefixWord ++ tailWord_1586363).sum := by decide
  have hdescent : baseEnd_1586363 < baseStart_1586363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586383 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 1, 8]
def baseStart_1586383 : Nat := 118140960795 + 1586383 * 2 ^ 59
def prefixEnd_1586383 : Nat := 4983230072969 + 3 ^ 40 * 1586383 * 2
def baseEnd_1586383 : Nat := 271525660373857334305621

theorem tailTrace_1586383 : CollatzResearch.WordTrace tailWord_1586383 prefixEnd_1586383 271525660373857334305621 := by
  unfold tailWord_1586383
  simp only [CollatzResearch.WordTrace]
  refine ⟨57860141411812798491459803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38573427607875198994306535 57860141411812798491459803)
  ·
    refine ⟨86790212117719197737189705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57860141411812798491459803 86790212117719197737189705)
    ·
      refine ⟨65092659088289398302892279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86790212117719197737189705 65092659088289398302892279)
      ·
        refine ⟨97638988632434097454338419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65092659088289398302892279 97638988632434097454338419)
        ·
          refine ⟨146458482948651146181507629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97638988632434097454338419 146458482948651146181507629)
          ·
            refine ⟨54921931105744179818065361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146458482948651146181507629 54921931105744179818065361)
            ·
              refine ⟨41191448329308134863549021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54921931105744179818065361 41191448329308134863549021)
              ·
                refine ⟨15446793123490550573830883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41191448329308134863549021 15446793123490550573830883)
                ·
                  refine ⟨23170189685235825860746325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15446793123490550573830883 23170189685235825860746325)
                  ·
                    refine ⟨271525660373857334305621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23170189685235825860746325 271525660373857334305621)
                    ·
                      rfl

theorem cell23_1586383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_1586383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586383 prefixEnd_1586383 := by exact prefixLift 1586383
  have htrace : WordTrace (prefixWord ++ tailWord_1586383) baseStart_1586383 baseEnd_1586383 := by
    simpa [prefixWord, tailWord_1586383, baseEnd_1586383] using wordTrace_append hprefix tailTrace_1586383
  have hstable : (prefixWord ++ tailWord_1586383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586383).length < 2 ^ (prefixWord ++ tailWord_1586383).sum := by decide
  have hdescent : baseEnd_1586383 < baseStart_1586383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586410 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_1586410 : Nat := 118140960795 + 1586410 * 2 ^ 59
def prefixEnd_1586410 : Nat := 4983230072969 + 3 ^ 40 * 1586410 * 2
def baseEnd_1586410 : Nat := 814590845099243397279239

theorem tailTrace_1586410 : CollatzResearch.WordTrace tailWord_1586410 prefixEnd_1586410 814590845099243397279239 := by
  unfold tailWord_1586410
  simp only [CollatzResearch.WordTrace]
  refine ⟨14465281545678745525673171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38574084121809988068461789 14465281545678745525673171)
  ·
    refine ⟨21697922318518118288509757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14465281545678745525673171 21697922318518118288509757)
    ·
      refine ⟨8136720869444294358191159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21697922318518118288509757 8136720869444294358191159)
      ·
        refine ⟨12205081304166441537286739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8136720869444294358191159 12205081304166441537286739)
        ·
          refine ⟨18307621956249662305930109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12205081304166441537286739 18307621956249662305930109)
          ·
            refine ⟨6865358233593623364723791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18307621956249662305930109 6865358233593623364723791)
            ·
              refine ⟨10298037350390435047085687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6865358233593623364723791 10298037350390435047085687)
              ·
                refine ⟨15447056025585652570628531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10298037350390435047085687 15447056025585652570628531)
                ·
                  refine ⟨23170584038378478855942797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15447056025585652570628531 23170584038378478855942797)
                  ·
                    refine ⟨8688969014391929570978549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23170584038378478855942797 8688969014391929570978549)
                    ·
                      refine ⟨814590845099243397279239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8688969014391929570978549 814590845099243397279239)
                      ·
                        rfl

theorem cell23_1586410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_1586410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586410 prefixEnd_1586410 := by exact prefixLift 1586410
  have htrace : WordTrace (prefixWord ++ tailWord_1586410) baseStart_1586410 baseEnd_1586410 := by
    simpa [prefixWord, tailWord_1586410, baseEnd_1586410] using wordTrace_append hprefix tailTrace_1586410
  have hstable : (prefixWord ++ tailWord_1586410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586410).length < 2 ^ (prefixWord ++ tailWord_1586410).sum := by decide
  have hdescent : baseEnd_1586410 < baseStart_1586410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586460 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 1, 7]
def baseStart_1586460 : Nat := 118140960795 + 1586460 * 2 ^ 59
def prefixEnd_1586460 : Nat := 4983230072969 + 3 ^ 40 * 1586460 * 2
def baseEnd_1586460 : Nat := 271538839710656067218003

theorem tailTrace_1586460 : CollatzResearch.WordTrace tailWord_1586460 prefixEnd_1586460 271538839710656067218003 := by
  unfold tailWord_1586460
  simp only [CollatzResearch.WordTrace]
  refine ⟨28931474916266920321006417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38575299888355893761341889 28931474916266920321006417)
  ·
    refine ⟨21698606187200190240754813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28931474916266920321006417 21698606187200190240754813)
    ·
      refine ⟨8136977320200071340283055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21698606187200190240754813 8136977320200071340283055)
      ·
        refine ⟨12205465980300107010424583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8136977320200071340283055 12205465980300107010424583)
        ·
          refine ⟨18308198970450160515636875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12205465980300107010424583 18308198970450160515636875)
          ·
            refine ⟨27462298455675240773455313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18308198970450160515636875 27462298455675240773455313)
            ·
              refine ⟨20596723841756430580091485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27462298455675240773455313 20596723841756430580091485)
              ·
                refine ⟨7723771440658661467534307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20596723841756430580091485 7723771440658661467534307)
                ·
                  refine ⟨11585657160987992201301461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7723771440658661467534307 11585657160987992201301461)
                  ·
                    refine ⟨271538839710656067218003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11585657160987992201301461 271538839710656067218003)
                    ·
                      rfl

theorem cell23_1586460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_1586460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586460 prefixEnd_1586460 := by exact prefixLift 1586460
  have htrace : WordTrace (prefixWord ++ tailWord_1586460) baseStart_1586460 baseEnd_1586460 := by
    simpa [prefixWord, tailWord_1586460, baseEnd_1586460] using wordTrace_append hprefix tailTrace_1586460
  have hstable : (prefixWord ++ tailWord_1586460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586460).length < 2 ^ (prefixWord ++ tailWord_1586460).sum := by decide
  have hdescent : baseEnd_1586460 < baseStart_1586460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586481 : List Nat := [1, 2, 2, 3, 3, 3, 2, 2, 5]
def baseStart_1586481 : Nat := 118140960795 + 1586481 * 2 ^ 59
def prefixEnd_1586481 : Nat := 4983230072969 + 3 ^ 40 * 1586481 * 2
def baseEnd_1586481 : Nat := 90514144691745846610157

theorem tailTrace_1586481 : CollatzResearch.WordTrace tailWord_1586481 prefixEnd_1586481 90514144691745846610157 := by
  unfold tailWord_1586481
  simp only [CollatzResearch.WordTrace]
  refine ⟨57863715765457761228527297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38575810510305174152351531 57863715765457761228527297)
  ·
    refine ⟨43397786824093320921395473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57863715765457761228527297 43397786824093320921395473)
    ·
      refine ⟨32548340118069990691046605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43397786824093320921395473 32548340118069990691046605)
      ·
        refine ⟨12205627544276246509142477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32548340118069990691046605 12205627544276246509142477)
        ·
          refine ⟨4577110329103592440928429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12205627544276246509142477 4577110329103592440928429)
          ·
            refine ⟨1716416373413847165348161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4577110329103592440928429 1716416373413847165348161)
            ·
              refine ⟨1287312280060385374011121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1716416373413847165348161 1287312280060385374011121)
              ·
                refine ⟨965484210045289030508341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1287312280060385374011121 965484210045289030508341)
                ·
                  refine ⟨90514144691745846610157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 965484210045289030508341 90514144691745846610157)
                  ·
                    rfl

theorem cell23_1586481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 5].length) (baseStart_1586481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586481 prefixEnd_1586481 := by exact prefixLift 1586481
  have htrace : WordTrace (prefixWord ++ tailWord_1586481) baseStart_1586481 baseEnd_1586481 := by
    simpa [prefixWord, tailWord_1586481, baseEnd_1586481] using wordTrace_append hprefix tailTrace_1586481
  have hstable : (prefixWord ++ tailWord_1586481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586481).length < 2 ^ (prefixWord ++ tailWord_1586481).sum := by decide
  have hdescent : baseEnd_1586481 < baseStart_1586481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586484 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_1586484 : Nat := 118140960795 + 1586484 * 2 ^ 59
def prefixEnd_1586484 : Nat := 4983230072969 + 3 ^ 40 * 1586484 * 2
def baseEnd_1586484 : Nat := 814628842667676107753899

theorem tailTrace_1586484 : CollatzResearch.WordTrace tailWord_1586484 prefixEnd_1586484 814628842667676107753899 := by
  unfold tailWord_1586484
  simp only [CollatzResearch.WordTrace]
  refine ⟨28931912592223446370443253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38575883456297928493924337 28931912592223446370443253)
  ·
    refine ⟨2712366805520948097229055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28931912592223446370443253 2712366805520948097229055)
    ·
      refine ⟨4068550208281422145843583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2712366805520948097229055 4068550208281422145843583)
      ·
        refine ⟨6102825312422133218765375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4068550208281422145843583 6102825312422133218765375)
        ·
          refine ⟨9154237968633199828148063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6102825312422133218765375 9154237968633199828148063)
          ·
            refine ⟨13731356952949799742222095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9154237968633199828148063 13731356952949799742222095)
            ·
              refine ⟨20597035429424699613333143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13731356952949799742222095 20597035429424699613333143)
              ·
                refine ⟨30895553144137049419999715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20597035429424699613333143 30895553144137049419999715)
                ·
                  refine ⟨46343329716205574129999573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30895553144137049419999715 46343329716205574129999573)
                  ·
                    refine ⟨1086171790223568143671865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46343329716205574129999573 1086171790223568143671865)
                    ·
                      refine ⟨814628842667676107753899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1086171790223568143671865 814628842667676107753899)
                      ·
                        rfl

theorem cell23_1586484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_1586484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586484 prefixEnd_1586484 := by exact prefixLift 1586484
  have htrace : WordTrace (prefixWord ++ tailWord_1586484) baseStart_1586484 baseEnd_1586484 := by
    simpa [prefixWord, tailWord_1586484, baseEnd_1586484] using wordTrace_append hprefix tailTrace_1586484
  have hstable : (prefixWord ++ tailWord_1586484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586484).length < 2 ^ (prefixWord ++ tailWord_1586484).sum := by decide
  have hdescent : baseEnd_1586484 < baseStart_1586484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586520 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 8]
def baseStart_1586520 : Nat := 118140960795 + 1586520 * 2 ^ 59
def prefixEnd_1586520 : Nat := 4983230072969 + 3 ^ 40 * 1586520 * 2
def baseEnd_1586520 : Nat := 90516369774581996322637

theorem tailTrace_1586520 : CollatzResearch.WordTrace tailWord_1586520 prefixEnd_1586520 90516369774581996322637 := by
  unfold tailWord_1586520
  simp only [CollatzResearch.WordTrace]
  refine ⟨28932569106158235444598507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38576758808210980592798009 28932569106158235444598507)
  ·
    refine ⟨43398853659237353166897761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28932569106158235444598507 43398853659237353166897761)
    ·
      refine ⟨32549140244428014875173321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43398853659237353166897761 32549140244428014875173321)
      ·
        refine ⟨24411855183321011156379991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32549140244428014875173321 24411855183321011156379991)
        ·
          refine ⟨36617782774981516734569987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24411855183321011156379991 36617782774981516734569987)
          ·
            refine ⟨54926674162472275101854981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36617782774981516734569987 54926674162472275101854981)
            ·
              refine ⟨10298751405463551581597809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54926674162472275101854981 10298751405463551581597809)
              ·
                refine ⟨7724063554097663686198357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10298751405463551581597809 7724063554097663686198357)
                ·
                  refine ⟨90516369774581996322637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7724063554097663686198357 90516369774581996322637)
                  ·
                    rfl

theorem cell23_1586520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 8].length) (baseStart_1586520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586520 prefixEnd_1586520 := by exact prefixLift 1586520
  have htrace : WordTrace (prefixWord ++ tailWord_1586520) baseStart_1586520 baseEnd_1586520 := by
    simpa [prefixWord, tailWord_1586520, baseEnd_1586520] using wordTrace_append hprefix tailTrace_1586520
  have hstable : (prefixWord ++ tailWord_1586520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586520).length < 2 ^ (prefixWord ++ tailWord_1586520).sum := by decide
  have hdescent : baseEnd_1586520 < baseStart_1586520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586541 : List Nat := [1, 5, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_1586541 : Nat := 118140960795 + 1586541 * 2 ^ 59
def prefixEnd_1586541 : Nat := 4983230072969 + 3 ^ 40 * 1586541 * 2
def baseEnd_1586541 : Nat := 271552703688327461580379

theorem tailTrace_1586541 : CollatzResearch.WordTrace tailWord_1586541 prefixEnd_1586541 271552703688327461580379 := by
  unfold tailWord_1586541
  simp only [CollatzResearch.WordTrace]
  refine ⟨57865904145240391475711477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38577269430160260983807651 57865904145240391475711477)
  ·
    refine ⟨5424928513616286700847951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57865904145240391475711477 5424928513616286700847951)
    ·
      refine ⟨8137392770424430051271927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5424928513616286700847951 8137392770424430051271927)
      ·
        refine ⟨12206089155636645076907891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8137392770424430051271927 12206089155636645076907891)
        ·
          refine ⟨18309133733454967615361837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12206089155636645076907891 18309133733454967615361837)
          ·
            refine ⟨6865925150045612855760689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18309133733454967615361837 6865925150045612855760689)
            ·
              refine ⟨5149443862534209641820517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6865925150045612855760689 5149443862534209641820517)
              ·
                refine ⟨965520724225164307841347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5149443862534209641820517 965520724225164307841347)
                ·
                  refine ⟨1448281086337746461762021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965520724225164307841347 1448281086337746461762021)
                  ·
                    refine ⟨271552703688327461580379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1448281086337746461762021 271552703688327461580379)
                    ·
                      rfl

theorem cell23_1586541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_1586541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586541 prefixEnd_1586541 := by exact prefixLift 1586541
  have htrace : WordTrace (prefixWord ++ tailWord_1586541) baseStart_1586541 baseEnd_1586541 := by
    simpa [prefixWord, tailWord_1586541, baseEnd_1586541] using wordTrace_append hprefix tailTrace_1586541
  have hstable : (prefixWord ++ tailWord_1586541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586541).length < 2 ^ (prefixWord ++ tailWord_1586541).sum := by decide
  have hdescent : baseEnd_1586541 < baseStart_1586541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586560 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 7]
def baseStart_1586560 : Nat := 118140960795 + 1586560 * 2 ^ 59
def prefixEnd_1586560 : Nat := 4983230072969 + 3 ^ 40 * 1586560 * 2
def baseEnd_1586560 : Nat := 814667867197417810403549

theorem tailTrace_1586560 : CollatzResearch.WordTrace tailWord_1586560 prefixEnd_1586560 814667867197417810403549 := by
  unfold tailWord_1586560
  simp only [CollatzResearch.WordTrace]
  refine ⟨28933298566085778860326567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38577731421447705147102089 28933298566085778860326567)
  ·
    refine ⟨43399947849128668290489851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28933298566085778860326567 43399947849128668290489851)
    ·
      refine ⟨65099921773693002435734777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43399947849128668290489851 65099921773693002435734777)
      ·
        refine ⟨48824941330269751826801083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65099921773693002435734777 48824941330269751826801083)
        ·
          refine ⟨73237411995404627740201625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48824941330269751826801083 73237411995404627740201625)
          ·
            refine ⟨54928058996553470805151219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73237411995404627740201625 54928058996553470805151219)
            ·
              refine ⟨82392088494830206207726829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54928058996553470805151219 82392088494830206207726829)
              ·
                refine ⟨30897033185561327327897561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82392088494830206207726829 30897033185561327327897561)
                ·
                  refine ⟨23172774889170995495923171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30897033185561327327897561 23172774889170995495923171)
                  ·
                    refine ⟨34759162333756493243884757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23172774889170995495923171 34759162333756493243884757)
                    ·
                      refine ⟨814667867197417810403549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34759162333756493243884757 814667867197417810403549)
                      ·
                        rfl

theorem cell23_1586560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_1586560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586560 prefixEnd_1586560 := by exact prefixLift 1586560
  have htrace : WordTrace (prefixWord ++ tailWord_1586560) baseStart_1586560 baseEnd_1586560 := by
    simpa [prefixWord, tailWord_1586560, baseEnd_1586560] using wordTrace_append hprefix tailTrace_1586560
  have hstable : (prefixWord ++ tailWord_1586560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586560).length < 2 ^ (prefixWord ++ tailWord_1586560).sum := by decide
  have hdescent : baseEnd_1586560 < baseStart_1586560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586591 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 2, 3, 2]
def baseStart_1586591 : Nat := 118140960795 + 1586591 * 2 ^ 59
def prefixEnd_1586591 : Nat := 4983230072969 + 3 ^ 40 * 1586591 * 2
def baseEnd_1586591 : Nat := 814683785097707189115907

theorem tailTrace_1586591 : CollatzResearch.WordTrace tailWord_1586591 prefixEnd_1586591 814683785097707189115907 := by
  unfold tailWord_1586591
  simp only [CollatzResearch.WordTrace]
  refine ⟨57867727795059250015031627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38578485196706166676687751 57867727795059250015031627)
  ·
    refine ⟨86801591692588875022547441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57867727795059250015031627 86801591692588875022547441)
    ·
      refine ⟨65101193769441656266910581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86801591692588875022547441 65101193769441656266910581)
      ·
        refine ⟨6103236915885155275022867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65101193769441656266910581 6103236915885155275022867)
        ·
          refine ⟨9154855373827732912534301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6103236915885155275022867 9154855373827732912534301)
          ·
            refine ⟨3433070765185399842200363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9154855373827732912534301 3433070765185399842200363)
            ·
              refine ⟨5149606147778099763300545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3433070765185399842200363 5149606147778099763300545)
              ·
                refine ⟨3862204610833574822475409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5149606147778099763300545 3862204610833574822475409)
                ·
                  refine ⟨2896653458125181116856557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3862204610833574822475409 2896653458125181116856557)
                  ·
                    refine ⟨1086245046796942918821209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896653458125181116856557 1086245046796942918821209)
                    ·
                      refine ⟨814683785097707189115907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1086245046796942918821209 814683785097707189115907)
                      ·
                        rfl

theorem cell23_1586591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_1586591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586591 prefixEnd_1586591 := by exact prefixLift 1586591
  have htrace : WordTrace (prefixWord ++ tailWord_1586591) baseStart_1586591 baseEnd_1586591 := by
    simpa [prefixWord, tailWord_1586591, baseEnd_1586591] using wordTrace_append hprefix tailTrace_1586591
  have hstable : (prefixWord ++ tailWord_1586591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586591).length < 2 ^ (prefixWord ++ tailWord_1586591).sum := by decide
  have hdescent : baseEnd_1586591 < baseStart_1586591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586621 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 5, 2, 2]
def baseStart_1586621 : Nat := 118140960795 + 1586621 * 2 ^ 59
def prefixEnd_1586621 : Nat := 4983230072969 + 3 ^ 40 * 1586621 * 2
def baseEnd_1586621 : Nat := 814699189517342071740769

theorem tailTrace_1586621 : CollatzResearch.WordTrace tailWord_1586621 prefixEnd_1586621 814699189517342071740769 := by
  unfold tailWord_1586621
  simp only [CollatzResearch.WordTrace]
  refine ⟨57868821984950565138623717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38579214656633710092415811 57868821984950565138623717)
  ·
    refine ⟨10850404122178230963491947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57868821984950565138623717 10850404122178230963491947)
    ·
      refine ⟨16275606183267346445237921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10850404122178230963491947 16275606183267346445237921)
      ·
        refine ⟨12206704637450509833928441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16275606183267346445237921 12206704637450509833928441)
        ·
          refine ⟨9155028478087882375446331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12206704637450509833928441 9155028478087882375446331)
          ·
            refine ⟨13732542717131823563169497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9155028478087882375446331 13732542717131823563169497)
            ·
              refine ⟨10299407037848867672377123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13732542717131823563169497 10299407037848867672377123)
              ·
                refine ⟨15449110556773301508565685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10299407037848867672377123 15449110556773301508565685)
                ·
                  refine ⟨1448354114697497016428033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15449110556773301508565685 1448354114697497016428033)
                  ·
                    refine ⟨1086265586023122762321025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1448354114697497016428033 1086265586023122762321025)
                    ·
                      refine ⟨814699189517342071740769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1086265586023122762321025 814699189517342071740769)
                      ·
                        rfl

theorem cell23_1586621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_1586621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586621 prefixEnd_1586621 := by exact prefixLift 1586621
  have htrace : WordTrace (prefixWord ++ tailWord_1586621) baseStart_1586621 baseEnd_1586621 := by
    simpa [prefixWord, tailWord_1586621, baseEnd_1586621] using wordTrace_append hprefix tailTrace_1586621
  have hstable : (prefixWord ++ tailWord_1586621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586621).length < 2 ^ (prefixWord ++ tailWord_1586621).sum := by decide
  have hdescent : baseEnd_1586621 < baseStart_1586621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586634 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_1586634 : Nat := 118140960795 + 1586634 * 2 ^ 59
def prefixEnd_1586634 : Nat := 4983230072969 + 3 ^ 40 * 1586634 * 2
def baseEnd_1586634 : Nat := 814705864765850520878209

theorem tailTrace_1586634 : CollatzResearch.WordTrace tailWord_1586634 prefixEnd_1586634 814705864765850520878209 := by
  unfold tailWord_1586634
  simp only [CollatzResearch.WordTrace]
  refine ⟨14467324033475867089711739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38579530755935645572564637 14467324033475867089711739)
  ·
    refine ⟨21700986050213800634567609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14467324033475867089711739 21700986050213800634567609)
    ·
      refine ⟨16275739537660350475925707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21700986050213800634567609 16275739537660350475925707)
      ·
        refine ⟨24413609306490525713888561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16275739537660350475925707 24413609306490525713888561)
        ·
          refine ⟨18310206979867894285416421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24413609306490525713888561 18310206979867894285416421)
          ·
            refine ⟨3433163808725230178515579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18310206979867894285416421 3433163808725230178515579)
            ·
              refine ⟨5149745713087845267773369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3433163808725230178515579 5149745713087845267773369)
              ·
                refine ⟨3862309284815883950830027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5149745713087845267773369 3862309284815883950830027)
                ·
                  refine ⟨5793463927223825926245041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3862309284815883950830027 5793463927223825926245041)
                  ·
                    refine ⟨4345097945417869444683781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5793463927223825926245041 4345097945417869444683781)
                    ·
                      refine ⟨814705864765850520878209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4345097945417869444683781 814705864765850520878209)
                      ·
                        rfl

theorem cell23_1586634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_1586634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586634 prefixEnd_1586634 := by exact prefixLift 1586634
  have htrace : WordTrace (prefixWord ++ tailWord_1586634) baseStart_1586634 baseEnd_1586634 := by
    simpa [prefixWord, tailWord_1586634, baseEnd_1586634] using wordTrace_append hprefix tailTrace_1586634
  have hstable : (prefixWord ++ tailWord_1586634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586634).length < 2 ^ (prefixWord ++ tailWord_1586634).sum := by decide
  have hdescent : baseEnd_1586634 < baseStart_1586634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586644 : List Nat := [2, 4, 1, 2, 4, 10]
def baseStart_1586644 : Nat := 118140960795 + 1586644 * 2 ^ 59
def prefixEnd_1586644 : Nat := 4983230072969 + 3 ^ 40 * 1586644 * 2
def baseEnd_1586644 : Nat := 3352720162849364122441

theorem tailTrace_1586644 : CollatzResearch.WordTrace tailWord_1586644 prefixEnd_1586644 3352720162849364122441 := by
  unfold tailWord_1586644
  simp only [CollatzResearch.WordTrace]
  refine ⟨28934830431933620033355493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38579773909244826711140657 28934830431933620033355493)
  ·
    refine ⟨5425280705987553756254155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28934830431933620033355493 5425280705987553756254155)
    ·
      refine ⟨8137921058981330634381233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5425280705987553756254155 8137921058981330634381233)
      ·
        refine ⟨6103440794235997975785925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8137921058981330634381233 6103440794235997975785925)
        ·
          refine ⟨1144395148919249620459861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6103440794235997975785925 1144395148919249620459861)
          ·
            refine ⟨3352720162849364122441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1144395148919249620459861 3352720162849364122441)
            ·
              rfl

theorem cell23_1586644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 10].length) (baseStart_1586644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586644 prefixEnd_1586644 := by exact prefixLift 1586644
  have htrace : WordTrace (prefixWord ++ tailWord_1586644) baseStart_1586644 baseEnd_1586644 := by
    simpa [prefixWord, tailWord_1586644, baseEnd_1586644] using wordTrace_append hprefix tailTrace_1586644
  have hstable : (prefixWord ++ tailWord_1586644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586644).length < 2 ^ (prefixWord ++ tailWord_1586644).sum := by decide
  have hdescent : baseEnd_1586644 < baseStart_1586644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586657 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 2, 7]
def baseStart_1586657 : Nat := 118140960795 + 1586657 * 2 ^ 59
def prefixEnd_1586657 : Nat := 4983230072969 + 3 ^ 40 * 1586657 * 2
def baseEnd_1586657 : Nat := 271572558273634643630201

theorem tailTrace_1586657 : CollatzResearch.WordTrace tailWord_1586657 prefixEnd_1586657 271572558273634643630201 := by
  unfold tailWord_1586657
  simp only [CollatzResearch.WordTrace]
  refine ⟨57870135012820143286934225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38580090008546762191289483 57870135012820143286934225)
  ·
    refine ⟨43402601259615107465200669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57870135012820143286934225 43402601259615107465200669)
    ·
      refine ⟨16275975472355665299450251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43402601259615107465200669 16275975472355665299450251)
      ·
        refine ⟨24413963208533497949175377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16275975472355665299450251 24413963208533497949175377)
        ·
          refine ⟨18310472406400123461881533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24413963208533497949175377 18310472406400123461881533)
          ·
            refine ⟨6866427152400046298205575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18310472406400123461881533 6866427152400046298205575)
            ·
              refine ⟨10299640728600069447308363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6866427152400046298205575 10299640728600069447308363)
              ·
                refine ⟨15449461092900104170962545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10299640728600069447308363 15449461092900104170962545)
                ·
                  refine ⟨11587095819675078128221909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15449461092900104170962545 11587095819675078128221909)
                  ·
                    refine ⟨271572558273634643630201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11587095819675078128221909 271572558273634643630201)
                    ·
                      rfl

theorem cell23_1586657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_1586657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586657 prefixEnd_1586657 := by exact prefixLift 1586657
  have htrace : WordTrace (prefixWord ++ tailWord_1586657) baseStart_1586657 baseEnd_1586657 := by
    simpa [prefixWord, tailWord_1586657, baseEnd_1586657] using wordTrace_append hprefix tailTrace_1586657
  have hstable : (prefixWord ++ tailWord_1586657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586657).length < 2 ^ (prefixWord ++ tailWord_1586657).sum := by decide
  have hdescent : baseEnd_1586657 < baseStart_1586657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586671 : List Nat := [1, 1, 2, 1, 4, 1, 4, 3, 2, 1, 3]
def baseStart_1586671 : Nat := 118140960795 + 1586671 * 2 ^ 59
def prefixEnd_1586671 : Nat := 4983230072969 + 3 ^ 40 * 1586671 * 2
def baseEnd_1586671 : Nat := 814724863550066876115539

theorem tailTrace_1586671 : CollatzResearch.WordTrace tailWord_1586671 prefixEnd_1586671 814724863550066876115539 := by
  unfold tailWord_1586671
  simp only [CollatzResearch.WordTrace]
  refine ⟨57870645634769423677943867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38580430423179615785295911 57870645634769423677943867)
  ·
    refine ⟨86805968452154135516915801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57870645634769423677943867 86805968452154135516915801)
    ·
      refine ⟨65104476339115601637686851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86805968452154135516915801 65104476339115601637686851)
      ·
        refine ⟨97656714508673402456530277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65104476339115601637686851 97656714508673402456530277)
        ·
          refine ⟨18310633970376262960599427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97656714508673402456530277 18310633970376262960599427)
          ·
            refine ⟨27465950955564394440899141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18310633970376262960599427 27465950955564394440899141)
            ·
              refine ⟨5149865804168323957668589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27465950955564394440899141 5149865804168323957668589)
              ·
                refine ⟨1931199676563121484125721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5149865804168323957668589 1931199676563121484125721)
                ·
                  refine ⟨1448399757422341113094291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1931199676563121484125721 1448399757422341113094291)
                  ·
                    refine ⟨2172599636133511669641437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1448399757422341113094291 2172599636133511669641437)
                    ·
                      refine ⟨814724863550066876115539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2172599636133511669641437 814724863550066876115539)
                      ·
                        rfl

theorem cell23_1586671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 1, 3].length) (baseStart_1586671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586671 prefixEnd_1586671 := by exact prefixLift 1586671
  have htrace : WordTrace (prefixWord ++ tailWord_1586671) baseStart_1586671 baseEnd_1586671 := by
    simpa [prefixWord, tailWord_1586671, baseEnd_1586671] using wordTrace_append hprefix tailTrace_1586671
  have hstable : (prefixWord ++ tailWord_1586671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586671).length < 2 ^ (prefixWord ++ tailWord_1586671).sum := by decide
  have hdescent : baseEnd_1586671 < baseStart_1586671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586681 : List Nat := [1, 2, 1, 3, 1, 2, 1, 6, 1, 3, 2]
def baseStart_1586681 : Nat := 118140960795 + 1586681 * 2 ^ 59
def prefixEnd_1586681 : Nat := 4983230072969 + 3 ^ 40 * 1586681 * 2
def baseEnd_1586681 : Nat := 814729998356611836990493

theorem tailTrace_1586681 : CollatzResearch.WordTrace tailWord_1586681 prefixEnd_1586681 814729998356611836990493 := by
  unfold tailWord_1586681
  simp only [CollatzResearch.WordTrace]
  refine ⟨57871010364733195385807897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38580673576488796923871931 57871010364733195385807897)
  ·
    refine ⟨43403257773549896539355923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57871010364733195385807897 43403257773549896539355923)
    ·
      refine ⟨65104886660324844809033885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43403257773549896539355923 65104886660324844809033885)
      ·
        refine ⟨24414332497621816803387707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65104886660324844809033885 24414332497621816803387707)
        ·
          refine ⟨36621498746432725205081561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24414332497621816803387707 36621498746432725205081561)
          ·
            refine ⟨27466124059824543903811171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36621498746432725205081561 27466124059824543903811171)
            ·
              refine ⟨41199186089736815855716757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27466124059824543903811171 41199186089736815855716757)
              ·
                refine ⟨1931211847956413243236723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41199186089736815855716757 1931211847956413243236723)
                ·
                  refine ⟨2896817771934619864855085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1931211847956413243236723 2896817771934619864855085)
                  ·
                    refine ⟨1086306664475482449320657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896817771934619864855085 1086306664475482449320657)
                    ·
                      refine ⟨814729998356611836990493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1086306664475482449320657 814729998356611836990493)
                      ·
                        rfl

theorem cell23_1586681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_1586681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586681 prefixEnd_1586681 := by exact prefixLift 1586681
  have htrace : WordTrace (prefixWord ++ tailWord_1586681) baseStart_1586681 baseEnd_1586681 := by
    simpa [prefixWord, tailWord_1586681, baseEnd_1586681] using wordTrace_append hprefix tailTrace_1586681
  have hstable : (prefixWord ++ tailWord_1586681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586681).length < 2 ^ (prefixWord ++ tailWord_1586681).sum := by decide
  have hdescent : baseEnd_1586681 < baseStart_1586681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586692 : List Nat := [2, 3, 2, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_1586692 : Nat := 118140960795 + 1586692 * 2 ^ 59
def prefixEnd_1586692 : Nat := 4983230072969 + 3 ^ 40 * 1586692 * 2
def baseEnd_1586692 : Nat := 814735646643811293952943

theorem tailTrace_1586692 : CollatzResearch.WordTrace tailWord_1586692 prefixEnd_1586692 814735646643811293952943 := by
  unfold tailWord_1586692
  simp only [CollatzResearch.WordTrace]
  refine ⟨28935705783846672132229165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38580941045128896176305553 28935705783846672132229165)
  ·
    refine ⟨10850889668942502049585937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28935705783846672132229165 10850889668942502049585937)
    ·
      refine ⟨8138167251706876537189453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10850889668942502049585937 8138167251706876537189453)
      ·
        refine ⟨3051812719390078701446045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8138167251706876537189453 3051812719390078701446045)
        ·
          refine ⟨1144429769771279513042267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3051812719390078701446045 1144429769771279513042267)
          ·
            refine ⟨1716644654656919269563401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144429769771279513042267 1716644654656919269563401)
            ·
              refine ⟨1287483490992689452172551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1716644654656919269563401 1287483490992689452172551)
              ·
                refine ⟨1931225236489034178258827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287483490992689452172551 1931225236489034178258827)
                ·
                  refine ⟨2896837854733551267388241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1931225236489034178258827 2896837854733551267388241)
                  ·
                    refine ⟨2172628391050163450541181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2896837854733551267388241 2172628391050163450541181)
                    ·
                      refine ⟨814735646643811293952943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2172628391050163450541181 814735646643811293952943)
                      ·
                        rfl

theorem cell23_1586692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_1586692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586692 prefixEnd_1586692 := by exact prefixLift 1586692
  have htrace : WordTrace (prefixWord ++ tailWord_1586692) baseStart_1586692 baseEnd_1586692 := by
    simpa [prefixWord, tailWord_1586692, baseEnd_1586692] using wordTrace_append hprefix tailTrace_1586692
  have hstable : (prefixWord ++ tailWord_1586692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586692).length < 2 ^ (prefixWord ++ tailWord_1586692).sum := by decide
  have hdescent : baseEnd_1586692 < baseStart_1586692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586697 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 1, 3, 5]
def baseStart_1586697 : Nat := 118140960795 + 1586697 * 2 ^ 59
def prefixEnd_1586697 : Nat := 4983230072969 + 3 ^ 40 * 1586697 * 2
def baseEnd_1586697 : Nat := 814738214047083774390419

theorem tailTrace_1586697 : CollatzResearch.WordTrace tailWord_1586697 prefixEnd_1586697 814738214047083774390419 := by
  unfold tailWord_1586697
  simp only [CollatzResearch.WordTrace]
  refine ⟨57871593932675230118390345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38581062621783486745593563 57871593932675230118390345)
  ·
    refine ⟨43403695449506422588792759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57871593932675230118390345 43403695449506422588792759)
    ·
      refine ⟨65105543174259633883189139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43403695449506422588792759 65105543174259633883189139)
      ·
        refine ⟨97658314761389450824783709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65105543174259633883189139 97658314761389450824783709)
        ·
          refine ⟨36621868035521044059293891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97658314761389450824783709 36621868035521044059293891)
          ·
            refine ⟨54932802053281566088940837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36621868035521044059293891 54932802053281566088940837)
            ·
              refine ⟨10299900384990293641676407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54932802053281566088940837 10299900384990293641676407)
              ·
                refine ⟨15449850577485440462514611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10299900384990293641676407 15449850577485440462514611)
                ·
                  refine ⟨23174775866228160693771917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15449850577485440462514611 23174775866228160693771917)
                  ·
                    refine ⟨8690540949835560260164469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23174775866228160693771917 8690540949835560260164469)
                    ·
                      refine ⟨814738214047083774390419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8690540949835560260164469 814738214047083774390419)
                      ·
                        rfl

theorem cell23_1586697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_1586697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586697 prefixEnd_1586697 := by exact prefixLift 1586697
  have htrace : WordTrace (prefixWord ++ tailWord_1586697) baseStart_1586697 baseEnd_1586697 := by
    simpa [prefixWord, tailWord_1586697, baseEnd_1586697] using wordTrace_append hprefix tailTrace_1586697
  have hstable : (prefixWord ++ tailWord_1586697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586697).length < 2 ^ (prefixWord ++ tailWord_1586697).sum := by decide
  have hdescent : baseEnd_1586697 < baseStart_1586697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586698 : List Nat := [3, 1, 2, 2, 2, 3, 1, 3, 1, 3, 2]
def baseStart_1586698 : Nat := 118140960795 + 1586698 * 2 ^ 59
def prefixEnd_1586698 : Nat := 4983230072969 + 3 ^ 40 * 1586698 * 2
def baseEnd_1586698 : Nat := 814738727527738270477915

theorem tailTrace_1586698 : CollatzResearch.WordTrace tailWord_1586698 prefixEnd_1586698 814738727527738270477915 := by
  unfold tailWord_1586698
  simp only [CollatzResearch.WordTrace]
  refine ⟨14467907601417901822294187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38581086937114404859451165 14467907601417901822294187)
  ·
    refine ⟨21701861402126852733441281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14467907601417901822294187 21701861402126852733441281)
    ·
      refine ⟨16276396051595139550080961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21701861402126852733441281 16276396051595139550080961)
      ·
        refine ⟨12207297038696354662560721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16276396051595139550080961 12207297038696354662560721)
        ·
          refine ⟨9155472779022265996920541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12207297038696354662560721 9155472779022265996920541)
          ·
            refine ⟨3433302292133349748845203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9155472779022265996920541 3433302292133349748845203)
            ·
              refine ⟨5149953438200024623267805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3433302292133349748845203 5149953438200024623267805)
              ·
                refine ⟨1931232539325009233725427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5149953438200024623267805 1931232539325009233725427)
                ·
                  refine ⟨2896848808987513850588141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1931232539325009233725427 2896848808987513850588141)
                  ·
                    refine ⟨1086318303370317693970553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2896848808987513850588141 1086318303370317693970553)
                    ·
                      refine ⟨814738727527738270477915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1086318303370317693970553 814738727527738270477915)
                      ·
                        rfl

theorem cell23_1586698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_1586698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586698 prefixEnd_1586698 := by exact prefixLift 1586698
  have htrace : WordTrace (prefixWord ++ tailWord_1586698) baseStart_1586698 baseEnd_1586698 := by
    simpa [prefixWord, tailWord_1586698, baseEnd_1586698] using wordTrace_append hprefix tailTrace_1586698
  have hstable : (prefixWord ++ tailWord_1586698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586698).length < 2 ^ (prefixWord ++ tailWord_1586698).sum := by decide
  have hdescent : baseEnd_1586698 < baseStart_1586698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586751 : List Nat := [1, 1, 2, 2, 3, 3, 3, 3, 5]
def baseStart_1586751 : Nat := 118140960795 + 1586751 * 2 ^ 59
def prefixEnd_1586751 : Nat := 4983230072969 + 3 ^ 40 * 1586751 * 2
def baseEnd_1586751 : Nat := 90529549111380729235019

theorem tailTrace_1586751 : CollatzResearch.WordTrace tailWord_1586751 prefixEnd_1586751 90529549111380729235019 := by
  unfold tailWord_1586751
  simp only [CollatzResearch.WordTrace]
  refine ⟨57873563474479597340856107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38582375649653064893904071 57873563474479597340856107)
  ·
    refine ⟨86810345211719396011284161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57873563474479597340856107 86810345211719396011284161)
    ·
      refine ⟨65107758908789547008463121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86810345211719396011284161 65107758908789547008463121)
      ·
        refine ⟨48830819181592160256347341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65107758908789547008463121 48830819181592160256347341)
        ·
          refine ⟨18311557193097060096130253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48830819181592160256347341 18311557193097060096130253)
          ·
            refine ⟨6866833947411397536048845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18311557193097060096130253 6866833947411397536048845)
            ·
              refine ⟨2575062730279274076018317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6866833947411397536048845 2575062730279274076018317)
              ·
                refine ⟨965648523854727778506869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2575062730279274076018317 965648523854727778506869)
                ·
                  refine ⟨90529549111380729235019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 965648523854727778506869 90529549111380729235019)
                  ·
                    rfl

theorem cell23_1586751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 5].length) (baseStart_1586751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586751 prefixEnd_1586751 := by exact prefixLift 1586751
  have htrace : WordTrace (prefixWord ++ tailWord_1586751) baseStart_1586751 baseEnd_1586751 := by
    simpa [prefixWord, tailWord_1586751, baseEnd_1586751] using wordTrace_append hprefix tailTrace_1586751
  have hstable : (prefixWord ++ tailWord_1586751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586751).length < 2 ^ (prefixWord ++ tailWord_1586751).sum := by decide
  have hdescent : baseEnd_1586751 < baseStart_1586751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586764 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 4, 5]
def baseStart_1586764 : Nat := 118140960795 + 1586764 * 2 ^ 59
def prefixEnd_1586764 : Nat := 4983230072969 + 3 ^ 40 * 1586764 * 2
def baseEnd_1586764 : Nat := 271590872416978337417537

theorem tailTrace_1586764 : CollatzResearch.WordTrace tailWord_1586764 prefixEnd_1586764 271590872416978337417537 := by
  unfold tailWord_1586764
  simp only [CollatzResearch.WordTrace]
  refine ⟨28937018811716250280539673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38582691748955000374052897 28937018811716250280539673)
  ·
    refine ⟨21702764108787187710404755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28937018811716250280539673 21702764108787187710404755)
    ·
      refine ⟨32554146163180781565607133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21702764108787187710404755 32554146163180781565607133)
      ·
        refine ⟨12207804811192793087102675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32554146163180781565607133 12207804811192793087102675)
        ·
          refine ⟨18311707216789189630654013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12207804811192793087102675 18311707216789189630654013)
          ·
            refine ⟨6866890206295946111495255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18311707216789189630654013 6866890206295946111495255)
            ·
              refine ⟨10300335309443919167242883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6866890206295946111495255 10300335309443919167242883)
              ·
                refine ⟨15450502964165878750864325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10300335309443919167242883 15450502964165878750864325)
                ·
                  refine ⟨2896969305781102265787061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15450502964165878750864325 2896969305781102265787061)
                  ·
                    refine ⟨271590872416978337417537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2896969305781102265787061 271590872416978337417537)
                    ·
                      rfl

theorem cell23_1586764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_1586764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586764 prefixEnd_1586764 := by exact prefixLift 1586764
  have htrace : WordTrace (prefixWord ++ tailWord_1586764) baseStart_1586764 baseEnd_1586764 := by
    simpa [prefixWord, tailWord_1586764, baseEnd_1586764] using wordTrace_append hprefix tailTrace_1586764
  have hstable : (prefixWord ++ tailWord_1586764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586764).length < 2 ^ (prefixWord ++ tailWord_1586764).sum := by decide
  have hdescent : baseEnd_1586764 < baseStart_1586764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586784 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 4]
def baseStart_1586784 : Nat := 118140960795 + 1586784 * 2 ^ 59
def prefixEnd_1586784 : Nat := 4983230072969 + 3 ^ 40 * 1586784 * 2
def baseEnd_1586784 : Nat := 814782886864024934002519

theorem tailTrace_1586784 : CollatzResearch.WordTrace tailWord_1586784 prefixEnd_1586784 814782886864024934002519 := by
  unfold tailWord_1586784
  simp only [CollatzResearch.WordTrace]
  refine ⟨28937383541680021988403703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38583178055573362651204937 28937383541680021988403703)
  ·
    refine ⟨43406075312520032982605555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28937383541680021988403703 43406075312520032982605555)
    ·
      refine ⟨65109112968780049473908333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43406075312520032982605555 65109112968780049473908333)
      ·
        refine ⟨24415917363292518552715625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65109112968780049473908333 24415917363292518552715625)
        ·
          refine ⟨18311938022469388914536719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24415917363292518552715625 18311938022469388914536719)
          ·
            refine ⟨27467907033704083371805079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18311938022469388914536719 27467907033704083371805079)
            ·
              refine ⟨41201860550556125057707619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27467907033704083371805079 41201860550556125057707619)
              ·
                refine ⟨61802790825834187586561429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41201860550556125057707619 61802790825834187586561429)
                ·
                  refine ⟨2897005819960977543120067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61802790825834187586561429 2897005819960977543120067)
                  ·
                    refine ⟨4345508729941466314680101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2897005819960977543120067 4345508729941466314680101)
                    ·
                      refine ⟨814782886864024934002519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4345508729941466314680101 814782886864024934002519)
                      ·
                        rfl

theorem cell23_1586784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_1586784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586784 prefixEnd_1586784 := by exact prefixLift 1586784
  have htrace : WordTrace (prefixWord ++ tailWord_1586784) baseStart_1586784 baseEnd_1586784 := by
    simpa [prefixWord, tailWord_1586784, baseEnd_1586784] using wordTrace_append hprefix tailTrace_1586784
  have hstable : (prefixWord ++ tailWord_1586784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586784).length < 2 ^ (prefixWord ++ tailWord_1586784).sum := by decide
  have hdescent : baseEnd_1586784 < baseStart_1586784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586798 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_1586798 : Nat := 118140960795 + 1586798 * 2 ^ 59
def prefixEnd_1586798 : Nat := 4983230072969 + 3 ^ 40 * 1586798 * 2
def baseEnd_1586798 : Nat := 271596691864395959742485

theorem tailTrace_1586798 : CollatzResearch.WordTrace tailWord_1586798 prefixEnd_1586798 271596691864395959742485 := by
  unfold tailWord_1586798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7234409713163665545977131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38583518470206216245211365 7234409713163665545977131)
  ·
    refine ⟨10851614569745498318965697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7234409713163665545977131 10851614569745498318965697)
    ·
      refine ⟨8138710927309123739224273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10851614569745498318965697 8138710927309123739224273)
      ·
        refine ⟨6104033195481842804418205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8138710927309123739224273 6104033195481842804418205)
        ·
          refine ⟨2289012448305691051656827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6104033195481842804418205 2289012448305691051656827)
          ·
            refine ⟨3433518672458536577485241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2289012448305691051656827 3433518672458536577485241)
            ·
              refine ⟨2575139004343902433113931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3433518672458536577485241 2575139004343902433113931)
              ·
                refine ⟨3862708506515853649670897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575139004343902433113931 3862708506515853649670897)
                ·
                  refine ⟨2897031379886890237253173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3862708506515853649670897 2897031379886890237253173)
                  ·
                    refine ⟨271596691864395959742485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2897031379886890237253173 271596691864395959742485)
                    ·
                      rfl

theorem cell23_1586798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_1586798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586798 prefixEnd_1586798 := by exact prefixLift 1586798
  have htrace : WordTrace (prefixWord ++ tailWord_1586798) baseStart_1586798 baseEnd_1586798 := by
    simpa [prefixWord, tailWord_1586798, baseEnd_1586798] using wordTrace_append hprefix tailTrace_1586798
  have hstable : (prefixWord ++ tailWord_1586798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586798).length < 2 ^ (prefixWord ++ tailWord_1586798).sum := by decide
  have hdescent : baseEnd_1586798 < baseStart_1586798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586821 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 2, 2, 3]
def baseStart_1586821 : Nat := 118140960795 + 1586821 * 2 ^ 59
def prefixEnd_1586821 : Nat := 4983230072969 + 3 ^ 40 * 1586821 * 2
def baseEnd_1586821 : Nat := 814801885648241289239849

theorem tailTrace_1586821 : CollatzResearch.WordTrace tailWord_1586821 prefixEnd_1586821 814801885648241289239849 := by
  unfold tailWord_1586821
  simp only [CollatzResearch.WordTrace]
  refine ⟨57876116584225999295904317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38584077722817332863936211 57876116584225999295904317)
  ·
    refine ⟨21703543719084749735964119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57876116584225999295904317 21703543719084749735964119)
    ·
      refine ⟨32555315578627124603946179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21703543719084749735964119 32555315578627124603946179)
      ·
        refine ⟨48832973367940686905919269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32555315578627124603946179 48832973367940686905919269)
        ·
          refine ⟨9156182506488878794859863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48832973367940686905919269 9156182506488878794859863)
          ·
            refine ⟨13734273759733318192289795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9156182506488878794859863 13734273759733318192289795)
            ·
              refine ⟨20601410639599977288434693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13734273759733318192289795 20601410639599977288434693)
              ·
                refine ⟨3862764494924995741581505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20601410639599977288434693 3862764494924995741581505)
                ·
                  refine ⟨2897073371193746806186129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3862764494924995741581505 2897073371193746806186129)
                  ·
                    refine ⟨2172805028395310104639597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2897073371193746806186129 2172805028395310104639597)
                    ·
                      refine ⟨814801885648241289239849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2172805028395310104639597 814801885648241289239849)
                      ·
                        rfl

theorem cell23_1586821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_1586821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586821 prefixEnd_1586821 := by exact prefixLift 1586821
  have htrace : WordTrace (prefixWord ++ tailWord_1586821) baseStart_1586821 baseEnd_1586821 := by
    simpa [prefixWord, tailWord_1586821, baseEnd_1586821] using wordTrace_append hprefix tailTrace_1586821
  have hstable : (prefixWord ++ tailWord_1586821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586821).length < 2 ^ (prefixWord ++ tailWord_1586821).sum := by decide
  have hdescent : baseEnd_1586821 < baseStart_1586821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586828 : List Nat := [2, 2, 1, 2, 1, 1, 5, 4, 1, 4]
def baseStart_1586828 : Nat := 118140960795 + 1586828 * 2 ^ 59
def prefixEnd_1586828 : Nat := 4983230072969 + 3 ^ 40 * 1586828 * 2
def baseEnd_1586828 : Nat := 271601826670940920617439

theorem tailTrace_1586828 : CollatzResearch.WordTrace tailWord_1586828 prefixEnd_1586828 271601826670940920617439 := by
  unfold tailWord_1586828
  simp only [CollatzResearch.WordTrace]
  refine ⟨28938185947600319745704569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38584247930133759660939425 28938185947600319745704569)
  ·
    refine ⟨21703639460700239809278427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28938185947600319745704569 21703639460700239809278427)
    ·
      refine ⟨32555459191050359713917641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21703639460700239809278427 32555459191050359713917641)
      ·
        refine ⟨24416594393287769785438231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32555459191050359713917641 24416594393287769785438231)
        ·
          refine ⟨36624891589931654678157347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24416594393287769785438231 36624891589931654678157347)
          ·
            refine ⟨54937337384897482017236021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36624891589931654678157347 54937337384897482017236021)
            ·
              refine ⟨5150375379834138939115877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54937337384897482017236021 5150375379834138939115877)
              ·
                refine ⟨965695383718901051084227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5150375379834138939115877 965695383718901051084227)
                ·
                  refine ⟨1448543075578351576626341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965695383718901051084227 1448543075578351576626341)
                  ·
                    refine ⟨271601826670940920617439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1448543075578351576626341 271601826670940920617439)
                    ·
                      rfl

theorem cell23_1586828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_1586828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586828 prefixEnd_1586828 := by exact prefixLift 1586828
  have htrace : WordTrace (prefixWord ++ tailWord_1586828) baseStart_1586828 baseEnd_1586828 := by
    simpa [prefixWord, tailWord_1586828, baseEnd_1586828] using wordTrace_append hprefix tailTrace_1586828
  have hstable : (prefixWord ++ tailWord_1586828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586828).length < 2 ^ (prefixWord ++ tailWord_1586828).sum := by decide
  have hdescent : baseEnd_1586828 < baseStart_1586828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586941 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_1586941 : Nat := 118140960795 + 1586941 * 2 ^ 59
def prefixEnd_1586941 : Nat := 4983230072969 + 3 ^ 40 * 1586941 * 2
def baseEnd_1586941 : Nat := 814863503326780819739297

theorem tailTrace_1586941 : CollatzResearch.WordTrace tailWord_1586941 prefixEnd_1586941 814863503326780819739297 := by
  unfold tailWord_1586941
  simp only [CollatzResearch.WordTrace]
  refine ⟨57880493343791259790272677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38586995562527506526848451 57880493343791259790272677)
  ·
    refine ⟨10852592501960861210676127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57880493343791259790272677 10852592501960861210676127)
    ·
      refine ⟨16278888752941291816014191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10852592501960861210676127 16278888752941291816014191)
      ·
        refine ⟨24418333129411937724021287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16278888752941291816014191 24418333129411937724021287)
        ·
          refine ⟨36627499694117906586031931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24418333129411937724021287 36627499694117906586031931)
          ·
            refine ⟨54941249541176859879047897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36627499694117906586031931 54941249541176859879047897)
            ·
              refine ⟨41205937155882644909285923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54941249541176859879047897 41205937155882644909285923)
              ·
                refine ⟨61808905733823967363928885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41205937155882644909285923 61808905733823967363928885)
                ·
                  refine ⟨5794584912545996940368333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61808905733823967363928885 5794584912545996940368333)
                  ·
                    refine ⟨2172969342204748852638125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5794584912545996940368333 2172969342204748852638125)
                    ·
                      refine ⟨814863503326780819739297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2172969342204748852638125 814863503326780819739297)
                      ·
                        rfl

theorem cell23_1586941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_1586941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586941 prefixEnd_1586941 := by exact prefixLift 1586941
  have htrace : WordTrace (prefixWord ++ tailWord_1586941) baseStart_1586941 baseEnd_1586941 := by
    simpa [prefixWord, tailWord_1586941, baseEnd_1586941] using wordTrace_append hprefix tailTrace_1586941
  have hstable : (prefixWord ++ tailWord_1586941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586941).length < 2 ^ (prefixWord ++ tailWord_1586941).sum := by decide
  have hdescent : baseEnd_1586941 < baseStart_1586941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586944 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 1, 9]
def baseStart_1586944 : Nat := 118140960795 + 1586944 * 2 ^ 59
def prefixEnd_1586944 : Nat := 4983230072969 + 3 ^ 40 * 1586944 * 2
def baseEnd_1586944 : Nat := 271621681256248102667261

theorem tailTrace_1586944 : CollatzResearch.WordTrace tailWord_1586944 prefixEnd_1586944 271621681256248102667261 := by
  unfold tailWord_1586944
  simp only [CollatzResearch.WordTrace]
  refine ⟨28940301381390195651315943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38587068508520260868421257 28940301381390195651315943)
  ·
    refine ⟨43410452072085293476973915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28940301381390195651315943 43410452072085293476973915)
    ·
      refine ⟨65115678108127940215460873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43410452072085293476973915 65115678108127940215460873)
      ·
        refine ⟨48836758581095955161595655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65115678108127940215460873 48836758581095955161595655)
        ·
          refine ⟨73255137871643932742393483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48836758581095955161595655 73255137871643932742393483)
          ·
            refine ⟨109882706807465899113590225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73255137871643932742393483 109882706807465899113590225)
            ·
              refine ⟨82412030105599424335192669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109882706807465899113590225 82412030105599424335192669)
              ·
                refine ⟨30904511289599784125697251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82412030105599424335192669 30904511289599784125697251)
                ·
                  refine ⟨46356766934399676188545877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30904511289599784125697251 46356766934399676188545877)
                  ·
                    refine ⟨271621681256248102667261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 46356766934399676188545877 271621681256248102667261)
                    ·
                      rfl

theorem cell23_1586944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_1586944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586944 prefixEnd_1586944 := by exact prefixLift 1586944
  have htrace : WordTrace (prefixWord ++ tailWord_1586944) baseStart_1586944 baseEnd_1586944 := by
    simpa [prefixWord, tailWord_1586944, baseEnd_1586944] using wordTrace_append hprefix tailTrace_1586944
  have hstable : (prefixWord ++ tailWord_1586944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586944).length < 2 ^ (prefixWord ++ tailWord_1586944).sum := by decide
  have hdescent : baseEnd_1586944 < baseStart_1586944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1586962 : List Nat := [3, 2, 4, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1586962 : Nat := 118140960795 + 1586962 * 2 ^ 59
def prefixEnd_1586962 : Nat := 4983230072969 + 3 ^ 40 * 1586962 * 2
def baseEnd_1586962 : Nat := 814874286420525237576701

theorem tailTrace_1586962 : CollatzResearch.WordTrace tailWord_1586962 prefixEnd_1586962 814874286420525237576701 := by
  unfold tailWord_1586962
  simp only [CollatzResearch.WordTrace]
  refine ⟨14470314819178795094196785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38587506184476786917858093 14470314819178795094196785)
  ·
    refine ⟨10852736114384096320647589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14470314819178795094196785 10852736114384096320647589)
    ·
      refine ⟨2034888021447018060121423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10852736114384096320647589 2034888021447018060121423)
      ·
        refine ⟨3052332032170527090182135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2034888021447018060121423 3052332032170527090182135)
        ·
          refine ⟨4578498048255790635273203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3052332032170527090182135 4578498048255790635273203)
          ·
            refine ⟨6867747072383685952909805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4578498048255790635273203 6867747072383685952909805)
            ·
              refine ⟨2575405152143882232341177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6867747072383685952909805 2575405152143882232341177)
              ·
                refine ⟨1931553864107911674255883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2575405152143882232341177 1931553864107911674255883)
                ·
                  refine ⟨2897330796161867511383825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1931553864107911674255883 2897330796161867511383825)
                  ·
                    refine ⟨2172998097121400633537869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2897330796161867511383825 2172998097121400633537869)
                    ·
                      refine ⟨814874286420525237576701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2172998097121400633537869 814874286420525237576701)
                      ·
                        rfl

theorem cell23_1586962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1586962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1586962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1586962 prefixEnd_1586962 := by exact prefixLift 1586962
  have htrace : WordTrace (prefixWord ++ tailWord_1586962) baseStart_1586962 baseEnd_1586962 := by
    simpa [prefixWord, tailWord_1586962, baseEnd_1586962] using wordTrace_append hprefix tailTrace_1586962
  have hstable : (prefixWord ++ tailWord_1586962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1586962).length < 2 ^ (prefixWord ++ tailWord_1586962).sum := by decide
  have hdescent : baseEnd_1586962 < baseStart_1586962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1586962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587011 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 4]
def baseStart_1587011 : Nat := 118140960795 + 1587011 * 2 ^ 59
def prefixEnd_1587011 : Nat := 4983230072969 + 3 ^ 40 * 1587011 * 2
def baseEnd_1587011 : Nat := 814899446972595545863975

theorem tailTrace_1587011 : CollatzResearch.WordTrace tailWord_1587011 prefixEnd_1587011 814899446972595545863975 := by
  unfold tailWord_1587011
  simp only [CollatzResearch.WordTrace]
  refine ⟨57883046453537661745320887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38588697635691774496880591 57883046453537661745320887)
  ·
    refine ⟨86824569680306492617981331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57883046453537661745320887 86824569680306492617981331)
    ·
      refine ⟨130236854520459738926971997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86824569680306492617981331 130236854520459738926971997)
      ·
        refine ⟨48838820445172402097614499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130236854520459738926971997 48838820445172402097614499)
        ·
          refine ⟨73258230667758603146421749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48838820445172402097614499 73258230667758603146421749)
          ·
            refine ⟨6867959125102369044977039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73258230667758603146421749 6867959125102369044977039)
            ·
              refine ⟨10301938687653553567465559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6867959125102369044977039 10301938687653553567465559)
              ·
                refine ⟨15452908031480330351198339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10301938687653553567465559 15452908031480330351198339)
                ·
                  refine ⟨23179362047220495526797509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15452908031480330351198339 23179362047220495526797509)
                  ·
                    refine ⟨4346130383853842911274533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23179362047220495526797509 4346130383853842911274533)
                    ·
                      refine ⟨814899446972595545863975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4346130383853842911274533 814899446972595545863975)
                      ·
                        rfl

theorem cell23_1587011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_1587011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587011 prefixEnd_1587011 := by exact prefixLift 1587011
  have htrace : WordTrace (prefixWord ++ tailWord_1587011) baseStart_1587011 baseEnd_1587011 := by
    simpa [prefixWord, tailWord_1587011, baseEnd_1587011] using wordTrace_append hprefix tailTrace_1587011
  have hstable : (prefixWord ++ tailWord_1587011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587011).length < 2 ^ (prefixWord ++ tailWord_1587011).sum := by decide
  have hdescent : baseEnd_1587011 < baseStart_1587011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587036 : List Nat := [2, 2, 4, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_1587036 : Nat := 118140960795 + 1587036 * 2 ^ 59
def prefixEnd_1587036 : Nat := 4983230072969 + 3 ^ 40 * 1587036 * 2
def baseEnd_1587036 : Nat := 814912283988957948051361

theorem tailTrace_1587036 : CollatzResearch.WordTrace tailWord_1587036 prefixEnd_1587036 814912283988957948051361 := by
  unfold tailWord_1587036
  simp only [CollatzResearch.WordTrace]
  refine ⟨28941979139223545507490481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38589305518964727343320641 28941979139223545507490481)
  ·
    refine ⟨21706484354417659130617861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28941979139223545507490481 21706484354417659130617861)
    ·
      refine ⟨4069965816453311086990849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21706484354417659130617861 4069965816453311086990849)
      ·
        refine ⟨3052474362339983315243137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4069965816453311086990849 3052474362339983315243137)
        ·
          refine ⟨2289355771754987486432353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3052474362339983315243137 2289355771754987486432353)
          ·
            refine ⟨1717016828816240614824265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2289355771754987486432353 1717016828816240614824265)
            ·
              refine ⟨1287762621612180461118199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1717016828816240614824265 1287762621612180461118199)
              ·
                refine ⟨1931643932418270691677299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287762621612180461118199 1931643932418270691677299)
                ·
                  refine ⟨2897465898627406037515949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1931643932418270691677299 2897465898627406037515949)
                  ·
                    refine ⟨1086549711985277264068481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2897465898627406037515949 1086549711985277264068481)
                    ·
                      refine ⟨814912283988957948051361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1086549711985277264068481 814912283988957948051361)
                      ·
                        rfl

theorem cell23_1587036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_1587036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587036 prefixEnd_1587036 := by exact prefixLift 1587036
  have htrace : WordTrace (prefixWord ++ tailWord_1587036) baseStart_1587036 baseEnd_1587036 := by
    simpa [prefixWord, tailWord_1587036, baseEnd_1587036] using wordTrace_append hprefix tailTrace_1587036
  have hstable : (prefixWord ++ tailWord_1587036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587036).length < 2 ^ (prefixWord ++ tailWord_1587036).sum := by decide
  have hdescent : baseEnd_1587036 < baseStart_1587036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587048 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_1587048 : Nat := 118140960795 + 1587048 * 2 ^ 59
def prefixEnd_1587048 : Nat := 4983230072969 + 3 ^ 40 * 1587048 * 2
def baseEnd_1587048 : Nat := 814918445756811901101305

theorem tailTrace_1587048 : CollatzResearch.WordTrace tailWord_1587048 prefixEnd_1587048 814918445756811901101305 := by
  unfold tailWord_1587048
  simp only [CollatzResearch.WordTrace]
  refine ⟨28942197977201808532208899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38589597302935744709611865 28942197977201808532208899)
  ·
    refine ⟨43413296965802712798313349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28942197977201808532208899 43413296965802712798313349)
    ·
      refine ⟨8139993181088008649683753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43413296965802712798313349 8139993181088008649683753)
      ·
        refine ⟨6104994885816006487262815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8139993181088008649683753 6104994885816006487262815)
        ·
          refine ⟨9157492328724009730894223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6104994885816006487262815 9157492328724009730894223)
          ·
            refine ⟨13736238493086014596341335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9157492328724009730894223 13736238493086014596341335)
            ·
              refine ⟨20604357739629021894512003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13736238493086014596341335 20604357739629021894512003)
              ·
                refine ⟨30906536609443532841768005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20604357739629021894512003 30906536609443532841768005)
                ·
                  refine ⟨5794975614270662407831501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30906536609443532841768005 5794975614270662407831501)
                  ·
                    refine ⟨2173115855351498402936813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5794975614270662407831501 2173115855351498402936813)
                    ·
                      refine ⟨814918445756811901101305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2173115855351498402936813 814918445756811901101305)
                      ·
                        rfl

theorem cell23_1587048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_1587048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587048 prefixEnd_1587048 := by exact prefixLift 1587048
  have htrace : WordTrace (prefixWord ++ tailWord_1587048) baseStart_1587048 baseEnd_1587048 := by
    simpa [prefixWord, tailWord_1587048, baseEnd_1587048] using wordTrace_append hprefix tailTrace_1587048
  have hstable : (prefixWord ++ tailWord_1587048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587048).length < 2 ^ (prefixWord ++ tailWord_1587048).sum := by decide
  have hdescent : baseEnd_1587048 < baseStart_1587048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587051 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 4, 5]
def baseStart_1587051 : Nat := 118140960795 + 1587051 * 2 ^ 59
def prefixEnd_1587051 : Nat := 4983230072969 + 3 ^ 40 * 1587051 * 2
def baseEnd_1587051 : Nat := 271639995399591796454597

theorem tailTrace_1587051 : CollatzResearch.WordTrace tailWord_1587051 prefixEnd_1587051 271639995399591796454597 := by
  unfold tailWord_1587051
  simp only [CollatzResearch.WordTrace]
  refine ⟨57884505373392748576777007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38589670248928499051184671 57884505373392748576777007)
  ·
    refine ⟨86826758060089122865165511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57884505373392748576777007 86826758060089122865165511)
    ·
      refine ⟨130240137090133684297748267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86826758060089122865165511 130240137090133684297748267)
      ·
        refine ⟨195360205635200526446622401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130240137090133684297748267 195360205635200526446622401)
        ·
          refine ⟨146520154226400394834966801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195360205635200526446622401 146520154226400394834966801)
          ·
            refine ⟨109890115669800296126225101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146520154226400394834966801 109890115669800296126225101)
            ·
              refine ⟨41208793376175111047334413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109890115669800296126225101 41208793376175111047334413)
              ·
                refine ⟨15453297516065666642750405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41208793376175111047334413 15453297516065666642750405)
                ·
                  refine ⟨2897493284262312495515701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15453297516065666642750405 2897493284262312495515701)
                  ·
                    refine ⟨271639995399591796454597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2897493284262312495515701 271639995399591796454597)
                    ·
                      rfl

theorem cell23_1587051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 5].length) (baseStart_1587051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587051 prefixEnd_1587051 := by exact prefixLift 1587051
  have htrace : WordTrace (prefixWord ++ tailWord_1587051) baseStart_1587051 baseEnd_1587051 := by
    simpa [prefixWord, tailWord_1587051, baseEnd_1587051] using wordTrace_append hprefix tailTrace_1587051
  have hstable : (prefixWord ++ tailWord_1587051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587051).length < 2 ^ (prefixWord ++ tailWord_1587051).sum := by decide
  have hdescent : baseEnd_1587051 < baseStart_1587051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587081 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 2, 8]
def baseStart_1587081 : Nat := 118140960795 + 1587081 * 2 ^ 59
def prefixEnd_1587081 : Nat := 4983230072969 + 3 ^ 40 * 1587081 * 2
def baseEnd_1587081 : Nat := 271645130206136757329551

theorem tailTrace_1587081 : CollatzResearch.WordTrace tailWord_1587081 prefixEnd_1587081 271645130206136757329551 := by
  unfold tailWord_1587081
  simp only [CollatzResearch.WordTrace]
  refine ⟨57885599563284063700369097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38590399708856042466912731 57885599563284063700369097)
  ·
    refine ⟨43414199672463047775276823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57885599563284063700369097 43414199672463047775276823)
    ·
      refine ⟨65121299508694571662915235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43414199672463047775276823 65121299508694571662915235)
      ·
        refine ⟨97681949263041857494372853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65121299508694571662915235 97681949263041857494372853)
        ·
          refine ⟨9157682743410174140097455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97681949263041857494372853 9157682743410174140097455)
          ·
            refine ⟨13736524115115261210146183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9157682743410174140097455 13736524115115261210146183)
            ·
              refine ⟨20604786172672891815219275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13736524115115261210146183 20604786172672891815219275)
              ·
                refine ⟨30907179259009337722828913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20604786172672891815219275 30907179259009337722828913)
                ·
                  refine ⟨23180384444257003292121685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30907179259009337722828913 23180384444257003292121685)
                  ·
                    refine ⟨271645130206136757329551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23180384444257003292121685 271645130206136757329551)
                    ·
                      rfl

theorem cell23_1587081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_1587081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587081 prefixEnd_1587081 := by exact prefixLift 1587081
  have htrace : WordTrace (prefixWord ++ tailWord_1587081) baseStart_1587081 baseEnd_1587081 := by
    simpa [prefixWord, tailWord_1587081, baseEnd_1587081] using wordTrace_append hprefix tailTrace_1587081
  have hstable : (prefixWord ++ tailWord_1587081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587081).length < 2 ^ (prefixWord ++ tailWord_1587081).sum := by decide
  have hdescent : baseEnd_1587081 < baseStart_1587081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587088 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 3, 6, 2]
def baseStart_1587088 : Nat := 118140960795 + 1587088 * 2 ^ 59
def prefixEnd_1587088 : Nat := 4983230072969 + 3 ^ 40 * 1587088 * 2
def baseEnd_1587088 : Nat := 814938984982991744601121

theorem tailTrace_1587088 : CollatzResearch.WordTrace tailWord_1587088 prefixEnd_1587088 814938984982991744601121 := by
  unfold tailWord_1587088
  simp only [CollatzResearch.WordTrace]
  refine ⟨28942927437129351947936959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38590569916172469263915945 28942927437129351947936959)
  ·
    refine ⟨43414391155694027921905439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28942927437129351947936959 43414391155694027921905439)
    ·
      refine ⟨65121586733541041882858159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43414391155694027921905439 65121586733541041882858159)
      ·
        refine ⟨97682380100311562824287239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65121586733541041882858159 97682380100311562824287239)
        ·
          refine ⟨146523570150467344236430859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97682380100311562824287239 146523570150467344236430859)
          ·
            refine ⟨219785355225701016354646289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146523570150467344236430859 219785355225701016354646289)
            ·
              refine ⟨164839016419275762265984717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219785355225701016354646289 164839016419275762265984717)
              ·
                refine ⟨61814631157228410849744269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164839016419275762265984717 61814631157228410849744269)
                ·
                  refine ⟨23180486683960654068654101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61814631157228410849744269 23180486683960654068654101)
                  ·
                    refine ⟨1086585313310655659468161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23180486683960654068654101 1086585313310655659468161)
                    ·
                      refine ⟨814938984982991744601121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1086585313310655659468161 814938984982991744601121)
                      ·
                        rfl

theorem cell23_1587088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 6, 2].length) (baseStart_1587088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587088 prefixEnd_1587088 := by exact prefixLift 1587088
  have htrace : WordTrace (prefixWord ++ tailWord_1587088) baseStart_1587088 baseEnd_1587088 := by
    simpa [prefixWord, tailWord_1587088, baseEnd_1587088] using wordTrace_append hprefix tailTrace_1587088
  have hstable : (prefixWord ++ tailWord_1587088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587088).length < 2 ^ (prefixWord ++ tailWord_1587088).sum := by decide
  have hdescent : baseEnd_1587088 < baseStart_1587088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587112 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1587112 : Nat := 118140960795 + 1587112 * 2 ^ 59
def prefixEnd_1587112 : Nat := 4983230072969 + 3 ^ 40 * 1587112 * 2
def baseEnd_1587112 : Nat := 814951308518699650701011

theorem tailTrace_1587112 : CollatzResearch.WordTrace tailWord_1587112 prefixEnd_1587112 814951308518699650701011 := by
  unfold tailWord_1587112
  simp only [CollatzResearch.WordTrace]
  refine ⟨28943365113085877997373795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38591153484114503996498393 28943365113085877997373795)
  ·
    refine ⟨43415047669628816996060693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28943365113085877997373795 43415047669628816996060693)
    ·
      refine ⟨2035080359513850796690345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43415047669628816996060693 2035080359513850796690345)
      ·
        refine ⟨1526310269635388097517759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2035080359513850796690345 1526310269635388097517759)
        ·
          refine ⟨2289465404453082146276639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526310269635388097517759 2289465404453082146276639)
          ·
            refine ⟨3434198106679623219414959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2289465404453082146276639 3434198106679623219414959)
            ·
              refine ⟨5151297160019434829122439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3434198106679623219414959 5151297160019434829122439)
              ·
                refine ⟨7726945740029152243683659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5151297160019434829122439 7726945740029152243683659)
                ·
                  refine ⟨11590418610043728365525489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7726945740029152243683659 11590418610043728365525489)
                  ·
                    refine ⟨8692813957532796274144117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11590418610043728365525489 8692813957532796274144117)
                    ·
                      refine ⟨814951308518699650701011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8692813957532796274144117 814951308518699650701011)
                      ·
                        rfl

theorem cell23_1587112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1587112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587112 prefixEnd_1587112 := by exact prefixLift 1587112
  have htrace : WordTrace (prefixWord ++ tailWord_1587112) baseStart_1587112 baseEnd_1587112 := by
    simpa [prefixWord, tailWord_1587112, baseEnd_1587112] using wordTrace_append hprefix tailTrace_1587112
  have hstable : (prefixWord ++ tailWord_1587112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587112).length < 2 ^ (prefixWord ++ tailWord_1587112).sum := by decide
  have hdescent : baseEnd_1587112 < baseStart_1587112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587128 : List Nat := [2, 1, 2, 1, 2, 3, 3, 3, 6]
def baseStart_1587128 : Nat := 118140960795 + 1587128 * 2 ^ 59
def prefixEnd_1587128 : Nat := 4983230072969 + 3 ^ 40 * 1587128 * 2
def baseEnd_1587128 : Nat := 90551058245463509788993

theorem tailTrace_1587128 : CollatzResearch.WordTrace tailWord_1587128 prefixEnd_1587128 90551058245463509788993 := by
  unfold tailWord_1587128
  simp only [CollatzResearch.WordTrace]
  refine ⟨28943656897056895363665019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38591542529409193818220025 28943656897056895363665019)
  ·
    refine ⟨43415485345585343045497529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28943656897056895363665019 43415485345585343045497529)
    ·
      refine ⟨32561614009189007284123147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43415485345585343045497529 32561614009189007284123147)
      ·
        refine ⟨48842421013783510926184721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32561614009189007284123147 48842421013783510926184721)
        ·
          refine ⟨36631815760337633194638541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48842421013783510926184721 36631815760337633194638541)
          ·
            refine ⟨13736930910126612447989453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36631815760337633194638541 13736930910126612447989453)
            ·
              refine ⟨5151349091297479667996045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13736930910126612447989453 5151349091297479667996045)
              ·
                refine ⟨1931755909236554875498517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5151349091297479667996045 1931755909236554875498517)
                ·
                  refine ⟨90551058245463509788993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1931755909236554875498517 90551058245463509788993)
                  ·
                    rfl

theorem cell23_1587128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 6].length) (baseStart_1587128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587128 prefixEnd_1587128 := by exact prefixLift 1587128
  have htrace : WordTrace (prefixWord ++ tailWord_1587128) baseStart_1587128 baseEnd_1587128 := by
    simpa [prefixWord, tailWord_1587128, baseEnd_1587128] using wordTrace_append hprefix tailTrace_1587128
  have hstable : (prefixWord ++ tailWord_1587128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587128).length < 2 ^ (prefixWord ++ tailWord_1587128).sum := by decide
  have hdescent : baseEnd_1587128 < baseStart_1587128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587131 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 6]
def baseStart_1587131 : Nat := 118140960795 + 1587131 * 2 ^ 59
def prefixEnd_1587131 : Nat := 4983230072969 + 3 ^ 40 * 1587131 * 2
def baseEnd_1587131 : Nat := 814961064651135076363423

theorem tailTrace_1587131 : CollatzResearch.WordTrace tailWord_1587131 prefixEnd_1587131 814961064651135076363423 := by
  unfold tailWord_1587131
  simp only [CollatzResearch.WordTrace]
  refine ⟨57887423213102922239689247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38591615475401948159792831 57887423213102922239689247)
  ·
    refine ⟨86831134819654383359533871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57887423213102922239689247 86831134819654383359533871)
    ·
      refine ⟨130246702229481575039300807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86831134819654383359533871 130246702229481575039300807)
      ·
        refine ⟨195370053344222362558951211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130246702229481575039300807 195370053344222362558951211)
        ·
          refine ⟨293055080016333543838426817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195370053344222362558951211 293055080016333543838426817)
          ·
            refine ⟨219791310012250157878820113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293055080016333543838426817 219791310012250157878820113)
            ·
              refine ⟨164843482509187618409115085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219791310012250157878820113 164843482509187618409115085)
              ·
                refine ⟨61816305940945356903418157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164843482509187618409115085 61816305940945356903418157)
                ·
                  refine ⟨23181114727854508838781809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61816305940945356903418157 23181114727854508838781809)
                  ·
                    refine ⟨17385836045890881629086357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23181114727854508838781809 17385836045890881629086357)
                    ·
                      refine ⟨814961064651135076363423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17385836045890881629086357 814961064651135076363423)
                      ·
                        rfl

theorem cell23_1587131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 6].length) (baseStart_1587131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587131 prefixEnd_1587131 := by exact prefixLift 1587131
  have htrace : WordTrace (prefixWord ++ tailWord_1587131) baseStart_1587131 baseEnd_1587131 := by
    simpa [prefixWord, tailWord_1587131, baseEnd_1587131] using wordTrace_append hprefix tailTrace_1587131
  have hstable : (prefixWord ++ tailWord_1587131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587131).length < 2 ^ (prefixWord ++ tailWord_1587131).sum := by decide
  have hdescent : baseEnd_1587131 < baseStart_1587131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587212 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 5, 2, 2]
def baseStart_1587212 : Nat := 118140960795 + 1587212 * 2 ^ 59
def prefixEnd_1587212 : Nat := 4983230072969 + 3 ^ 40 * 1587212 * 2
def baseEnd_1587212 : Nat := 815002656584149259450551

theorem tailTrace_1587212 : CollatzResearch.WordTrace tailWord_1587212 prefixEnd_1587212 815002656584149259450551 := by
  unfold tailWord_1587212
  simp only [CollatzResearch.WordTrace]
  refine ⟨28945188762904736536693945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38593585017206315382258593 28945188762904736536693945)
  ·
    refine ⟨21708891572178552402520459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28945188762904736536693945 21708891572178552402520459)
    ·
      refine ⟨32563337358267828603780689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21708891572178552402520459 32563337358267828603780689)
      ·
        refine ⟨24422503018700871452835517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32563337358267828603780689 24422503018700871452835517)
        ·
          refine ⟨9158438632012826794813319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24422503018700871452835517 9158438632012826794813319)
          ·
            refine ⟨13737657948019240192219979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9158438632012826794813319 13737657948019240192219979)
            ·
              refine ⟨20606486922028860288329969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13737657948019240192219979 20606486922028860288329969)
              ·
                refine ⟨15454865191521645216247477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20606486922028860288329969 15454865191521645216247477)
                ·
                  refine ⟨1448893611705154239023201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15454865191521645216247477 1448893611705154239023201)
                  ·
                    refine ⟨1086670208778865679267401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1448893611705154239023201 1086670208778865679267401)
                    ·
                      refine ⟨815002656584149259450551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1086670208778865679267401 815002656584149259450551)
                      ·
                        rfl

theorem cell23_1587212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_1587212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587212 prefixEnd_1587212 := by exact prefixLift 1587212
  have htrace : WordTrace (prefixWord ++ tailWord_1587212) baseStart_1587212 baseEnd_1587212 := by
    simpa [prefixWord, tailWord_1587212, baseEnd_1587212] using wordTrace_append hprefix tailTrace_1587212
  have hstable : (prefixWord ++ tailWord_1587212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587212).length < 2 ^ (prefixWord ++ tailWord_1587212).sum := by decide
  have hdescent : baseEnd_1587212 < baseStart_1587212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587213 : List Nat := [1, 7, 1, 2, 2, 1, 1, 2, 6]
def baseStart_1587213 : Nat := 118140960795 + 1587213 * 2 ^ 59
def prefixEnd_1587213 : Nat := 4983230072969 + 3 ^ 40 * 1587213 * 2
def baseEnd_1587213 : Nat := 90555907784978195059783

theorem tailTrace_1587213 : CollatzResearch.WordTrace tailWord_1587213 prefixEnd_1587213 90555907784978195059783 := by
  unfold tailWord_1587213
  simp only [CollatzResearch.WordTrace]
  refine ⟨57890413998805850244174293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38593609332537233496116195 57890413998805850244174293)
  ·
    refine ⟨1356806578097012115097835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 57890413998805850244174293 1356806578097012115097835)
    ·
      refine ⟨2035209867145518172646753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1356806578097012115097835 2035209867145518172646753)
      ·
        refine ⟨1526407400359138629485065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2035209867145518172646753 1526407400359138629485065)
        ·
          refine ⟨1144805550269353972113799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1526407400359138629485065 1144805550269353972113799)
          ·
            refine ⟨1717208325404030958170699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144805550269353972113799 1717208325404030958170699)
            ·
              refine ⟨2575812488106046437256049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717208325404030958170699 2575812488106046437256049)
              ·
                refine ⟨1931859366079534827942037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2575812488106046437256049 1931859366079534827942037)
                ·
                  refine ⟨90555907784978195059783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1931859366079534827942037 90555907784978195059783)
                  ·
                    rfl

theorem cell23_1587213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_1587213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587213 prefixEnd_1587213 := by exact prefixLift 1587213
  have htrace : WordTrace (prefixWord ++ tailWord_1587213) baseStart_1587213 baseEnd_1587213 := by
    simpa [prefixWord, tailWord_1587213, baseEnd_1587213] using wordTrace_append hprefix tailTrace_1587213
  have hstable : (prefixWord ++ tailWord_1587213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587213).length < 2 ^ (prefixWord ++ tailWord_1587213).sum := by decide
  have hdescent : baseEnd_1587213 < baseStart_1587213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587229 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_1587229 : Nat := 118140960795 + 1587229 * 2 ^ 59
def prefixEnd_1587229 : Nat := 4983230072969 + 3 ^ 40 * 1587229 * 2
def baseEnd_1587229 : Nat := 815011385755275692937973

theorem tailTrace_1587229 : CollatzResearch.WordTrace tailWord_1587229 prefixEnd_1587229 815011385755275692937973 := by
  unfold tailWord_1587229
  simp only [CollatzResearch.WordTrace]
  refine ⟨57890997566747884976756741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38593998377831923317837827 57890997566747884976756741)
  ·
    refine ⟨10854562043765228433141889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57890997566747884976756741 10854562043765228433141889)
    ·
      refine ⟨8140921532823921324856417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10854562043765228433141889 8140921532823921324856417)
      ·
        refine ⟨6105691149617940993642313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8140921532823921324856417 6105691149617940993642313)
        ·
          refine ⟨4579268362213455745231735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6105691149617940993642313 4579268362213455745231735)
          ·
            refine ⟨6868902543320183617847603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4579268362213455745231735 6868902543320183617847603)
            ·
              refine ⟨10303353814980275426771405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6868902543320183617847603 10303353814980275426771405)
              ·
                refine ⟨3863757680617603285039277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10303353814980275426771405 3863757680617603285039277)
                ·
                  refine ⟨1448909130231601231889729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3863757680617603285039277 1448909130231601231889729)
                  ·
                    refine ⟨1086681847673700923917297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1448909130231601231889729 1086681847673700923917297)
                    ·
                      refine ⟨815011385755275692937973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1086681847673700923917297 815011385755275692937973)
                      ·
                        rfl

theorem cell23_1587229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_1587229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587229 prefixEnd_1587229 := by exact prefixLift 1587229
  have htrace : WordTrace (prefixWord ++ tailWord_1587229) baseStart_1587229 baseEnd_1587229 := by
    simpa [prefixWord, tailWord_1587229, baseEnd_1587229] using wordTrace_append hprefix tailTrace_1587229
  have hstable : (prefixWord ++ tailWord_1587229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587229).length < 2 ^ (prefixWord ++ tailWord_1587229).sum := by decide
  have hdescent : baseEnd_1587229 < baseStart_1587229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587239 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1587239 : Nat := 118140960795 + 1587239 * 2 ^ 59
def prefixEnd_1587239 : Nat := 4983230072969 + 3 ^ 40 * 1587239 * 2
def baseEnd_1587239 : Nat := 271672173520606884604309

theorem tailTrace_1587239 : CollatzResearch.WordTrace tailWord_1587239 prefixEnd_1587239 271672173520606884604309 := by
  unfold tailWord_1587239
  simp only [CollatzResearch.WordTrace]
  refine ⟨57891362296711656684620771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38594241531141104456413847 57891362296711656684620771)
  ·
    refine ⟨86837043445067485026931157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57891362296711656684620771 86837043445067485026931157)
    ·
      refine ⟨2035243205743769180318699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 86837043445067485026931157 2035243205743769180318699)
      ·
        refine ⟨3052864808615653770478049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2035243205743769180318699 3052864808615653770478049)
        ·
          refine ⟨2289648606461740327858537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3052864808615653770478049 2289648606461740327858537)
          ·
            refine ⟨1717236454846305245893903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2289648606461740327858537 1717236454846305245893903)
            ·
              refine ⟨2575854682269457868840855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717236454846305245893903 2575854682269457868840855)
              ·
                refine ⟨3863782023404186803261283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575854682269457868840855 3863782023404186803261283)
                ·
                  refine ⟨5795673035106280204891925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3863782023404186803261283 5795673035106280204891925)
                  ·
                    refine ⟨271672173520606884604309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5795673035106280204891925 271672173520606884604309)
                    ·
                      rfl

theorem cell23_1587239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1587239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587239 prefixEnd_1587239 := by exact prefixLift 1587239
  have htrace : WordTrace (prefixWord ++ tailWord_1587239) baseStart_1587239 baseEnd_1587239 := by
    simpa [prefixWord, tailWord_1587239, baseEnd_1587239] using wordTrace_append hprefix tailTrace_1587239
  have hstable : (prefixWord ++ tailWord_1587239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587239).length < 2 ^ (prefixWord ++ tailWord_1587239).sum := by decide
  have hdescent : baseEnd_1587239 < baseStart_1587239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587242 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_1587242 : Nat := 118140960795 + 1587242 * 2 ^ 59
def prefixEnd_1587242 : Nat := 4983230072969 + 3 ^ 40 * 1587242 * 2
def baseEnd_1587242 : Nat := 815018061003784142075413

theorem tailTrace_1587242 : CollatzResearch.WordTrace tailWord_1587242 prefixEnd_1587242 815018061003784142075413 := by
  unfold tailWord_1587242
  simp only [CollatzResearch.WordTrace]
  refine ⟨14472867928925197049244995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38594314477133858797986653 14472867928925197049244995)
  ·
    refine ⟨21709301893387795573867493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14472867928925197049244995 21709301893387795573867493)
    ·
      refine ⟨4070494105010211670100155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21709301893387795573867493 4070494105010211670100155)
      ·
        refine ⟨6105741157515317505150233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4070494105010211670100155 6105741157515317505150233)
        ·
          refine ⟨4579305868136488128862675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6105741157515317505150233 4579305868136488128862675)
          ·
            refine ⟨6868958802204732193294013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4579305868136488128862675 6868958802204732193294013)
            ·
              refine ⟨2575859550826774572485255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6868958802204732193294013 2575859550826774572485255)
              ·
                refine ⟨3863789326240161858727883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575859550826774572485255 3863789326240161858727883)
                ·
                  refine ⟨5795683989360242788091825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3863789326240161858727883 5795683989360242788091825)
                  ·
                    refine ⟨4346762992020182091068869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5795683989360242788091825 4346762992020182091068869)
                    ·
                      refine ⟨815018061003784142075413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4346762992020182091068869 815018061003784142075413)
                      ·
                        rfl

theorem cell23_1587242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_1587242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587242 prefixEnd_1587242 := by exact prefixLift 1587242
  have htrace : WordTrace (prefixWord ++ tailWord_1587242) baseStart_1587242 baseEnd_1587242 := by
    simpa [prefixWord, tailWord_1587242, baseEnd_1587242] using wordTrace_append hprefix tailTrace_1587242
  have hstable : (prefixWord ++ tailWord_1587242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587242).length < 2 ^ (prefixWord ++ tailWord_1587242).sum := by decide
  have hdescent : baseEnd_1587242 < baseStart_1587242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587252 : List Nat := [2, 5, 1, 2, 2, 1, 1, 9]
def baseStart_1587252 : Nat := 118140960795 + 1587252 * 2 ^ 59
def prefixEnd_1587252 : Nat := 4983230072969 + 3 ^ 40 * 1587252 * 2
def baseEnd_1587252 : Nat := 30186044289271448257421

theorem tailTrace_1587252 : CollatzResearch.WordTrace tailWord_1587252 prefixEnd_1587252 30186044289271448257421 := by
  unfold tailWord_1587252
  simp only [CollatzResearch.WordTrace]
  refine ⟨28945918222832279952422005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38594557630443039936562673 28945918222832279952422005)
  ·
    refine ⟨2713679833390526245539563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28945918222832279952422005 2713679833390526245539563)
    ·
      refine ⟨4070519750085789368309345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2713679833390526245539563 4070519750085789368309345)
      ·
        refine ⟨3052889812564342026232009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4070519750085789368309345 3052889812564342026232009)
        ·
          refine ⟨2289667359423256519674007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3052889812564342026232009 2289667359423256519674007)
          ·
            refine ⟨3434501039134884779511011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2289667359423256519674007 3434501039134884779511011)
            ·
              refine ⟨5151751558702327169266517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3434501039134884779511011 5151751558702327169266517)
              ·
                refine ⟨30186044289271448257421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5151751558702327169266517 30186044289271448257421)
                ·
                  rfl

theorem cell23_1587252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 9].length) (baseStart_1587252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587252 prefixEnd_1587252 := by exact prefixLift 1587252
  have htrace : WordTrace (prefixWord ++ tailWord_1587252) baseStart_1587252 baseEnd_1587252 := by
    simpa [prefixWord, tailWord_1587252, baseEnd_1587252] using wordTrace_append hprefix tailTrace_1587252
  have hstable : (prefixWord ++ tailWord_1587252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587252).length < 2 ^ (prefixWord ++ tailWord_1587252).sum := by decide
  have hdescent : baseEnd_1587252 < baseStart_1587252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587296 : List Nat := [2, 1, 1, 3, 2, 5, 2, 1, 2, 1, 3]
def baseStart_1587296 : Nat := 118140960795 + 1587296 * 2 ^ 59
def prefixEnd_1587296 : Nat := 4983230072969 + 3 ^ 40 * 1587296 * 2
def baseEnd_1587296 : Nat := 815045788959126930800165

theorem tailTrace_1587296 : CollatzResearch.WordTrace tailWord_1587296 prefixEnd_1587296 815045788959126930800165 := by
  unfold tailWord_1587296
  simp only [CollatzResearch.WordTrace]
  refine ⟨28946720628752577709722871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38595627505003436946297161 28946720628752577709722871)
  ·
    refine ⟨43420080943128866564584307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28946720628752577709722871 43420080943128866564584307)
    ·
      refine ⟨65130121414693299846876461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43420080943128866564584307 65130121414693299846876461)
      ·
        refine ⟨24423795530509987442578673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65130121414693299846876461 24423795530509987442578673)
        ·
          refine ⟨18317846647882490581934005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24423795530509987442578673 18317846647882490581934005)
          ·
            refine ⟨1717298123238983492056313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18317846647882490581934005 1717298123238983492056313)
            ·
              refine ⟨1287973592429237619042235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1717298123238983492056313 1287973592429237619042235)
              ·
                refine ⟨1931960388643856428563353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287973592429237619042235 1931960388643856428563353)
                ·
                  refine ⟨1448970291482892321422515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1931960388643856428563353 1448970291482892321422515)
                  ·
                    refine ⟨2173455437224338482133773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1448970291482892321422515 2173455437224338482133773)
                    ·
                      refine ⟨815045788959126930800165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2173455437224338482133773 815045788959126930800165)
                      ·
                        rfl

theorem cell23_1587296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_1587296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587296 prefixEnd_1587296 := by exact prefixLift 1587296
  have htrace : WordTrace (prefixWord ++ tailWord_1587296) baseStart_1587296 baseEnd_1587296 := by
    simpa [prefixWord, tailWord_1587296, baseEnd_1587296] using wordTrace_append hprefix tailTrace_1587296
  have hstable : (prefixWord ++ tailWord_1587296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587296).length < 2 ^ (prefixWord ++ tailWord_1587296).sum := by decide
  have hdescent : baseEnd_1587296 < baseStart_1587296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587336 : List Nat := [2, 1, 3, 4, 1, 1, 1, 4, 2, 2, 2]
def baseStart_1587336 : Nat := 118140960795 + 1587336 * 2 ^ 59
def prefixEnd_1587336 : Nat := 4983230072969 + 3 ^ 40 * 1587336 * 2
def baseEnd_1587336 : Nat := 815066328185306774299981

theorem tailTrace_1587336 : CollatzResearch.WordTrace tailWord_1587336 prefixEnd_1587336 815066328185306774299981 := by
  unfold tailWord_1587336
  simp only [CollatzResearch.WordTrace]
  refine ⟨28947450088680121125450931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38596600118240161500601241 28947450088680121125450931)
  ·
    refine ⟨43421175133020181688176397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28947450088680121125450931 43421175133020181688176397)
    ·
      refine ⟨16282940674882568133066149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43421175133020181688176397 16282940674882568133066149)
      ·
        refine ⟨3053051376540481524949903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16282940674882568133066149 3053051376540481524949903)
        ·
          refine ⟨4579577064810722287424855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3053051376540481524949903 4579577064810722287424855)
          ·
            refine ⟨6869365597216083431137283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4579577064810722287424855 6869365597216083431137283)
            ·
              refine ⟨10304048395824125146705925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6869365597216083431137283 10304048395824125146705925)
              ·
                refine ⟨1932009074217023465007361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10304048395824125146705925 1932009074217023465007361)
                ·
                  refine ⟨1449006805662767598755521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1932009074217023465007361 1449006805662767598755521)
                  ·
                    refine ⟨1086755104247075699066641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1449006805662767598755521 1086755104247075699066641)
                    ·
                      refine ⟨815066328185306774299981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1086755104247075699066641 815066328185306774299981)
                      ·
                        rfl

theorem cell23_1587336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_1587336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587336 prefixEnd_1587336 := by exact prefixLift 1587336
  have htrace : WordTrace (prefixWord ++ tailWord_1587336) baseStart_1587336 baseEnd_1587336 := by
    simpa [prefixWord, tailWord_1587336, baseEnd_1587336] using wordTrace_append hprefix tailTrace_1587336
  have hstable : (prefixWord ++ tailWord_1587336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587336).length < 2 ^ (prefixWord ++ tailWord_1587336).sum := by decide
  have hdescent : baseEnd_1587336 < baseStart_1587336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587475 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 5, 6]
def baseStart_1587475 : Nat := 118140960795 + 1587475 * 2 ^ 59
def prefixEnd_1587475 : Nat := 4983230072969 + 3 ^ 40 * 1587475 * 2
def baseEnd_1587475 : Nat := 271712567332093910153947

theorem tailTrace_1587475 : CollatzResearch.WordTrace tailWord_1587475 prefixEnd_1587475 271712567332093910153947 := by
  unfold tailWord_1587475
  simp only [CollatzResearch.WordTrace]
  refine ⟨57899969923856668990211879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38599979949237779326807919 57899969923856668990211879)
  ·
    refine ⟨86849954885785003485317819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57899969923856668990211879 86849954885785003485317819)
    ·
      refine ⟨130274932328677505227976729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86849954885785003485317819 130274932328677505227976729)
      ·
        refine ⟨97706199246508128920982547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130274932328677505227976729 97706199246508128920982547)
        ·
          refine ⟨146559298869762193381473821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97706199246508128920982547 146559298869762193381473821)
          ·
            refine ⟨54959737076160822518052683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146559298869762193381473821 54959737076160822518052683)
            ·
              refine ⟨82439605614241233777079025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54959737076160822518052683 82439605614241233777079025)
              ·
                refine ⟨61829704210680925332809269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82439605614241233777079025 61829704210680925332809269)
                ·
                  refine ⟨5796534769751336749950869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61829704210680925332809269 5796534769751336749950869)
                  ·
                    refine ⟨271712567332093910153947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5796534769751336749950869 271712567332093910153947)
                    ·
                      rfl

theorem cell23_1587475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 6].length) (baseStart_1587475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587475 prefixEnd_1587475 := by exact prefixLift 1587475
  have htrace : WordTrace (prefixWord ++ tailWord_1587475) baseStart_1587475 baseEnd_1587475 := by
    simpa [prefixWord, tailWord_1587475, baseEnd_1587475] using wordTrace_append hprefix tailTrace_1587475
  have hstable : (prefixWord ++ tailWord_1587475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587475).length < 2 ^ (prefixWord ++ tailWord_1587475).sum := by decide
  have hdescent : baseEnd_1587475 < baseStart_1587475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587479 : List Nat := [1, 1, 3, 4, 1, 2, 3, 2, 1, 5]
def baseStart_1587479 : Nat := 118140960795 + 1587479 * 2 ^ 59
def prefixEnd_1587479 : Nat := 4983230072969 + 3 ^ 40 * 1587479 * 2
def baseEnd_1587479 : Nat := 271713251972966571603941

theorem tailTrace_1587479 : CollatzResearch.WordTrace tailWord_1587479 prefixEnd_1587479 271713251972966571603941 := by
  unfold tailWord_1587479
  simp only [CollatzResearch.WordTrace]
  refine ⟨57900115815842177673357491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38600077210561451782238327 57900115815842177673357491)
  ·
    refine ⟨86850173723763266510036237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57900115815842177673357491 86850173723763266510036237)
    ·
      refine ⟨32568815146411224941263589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86850173723763266510036237 32568815146411224941263589)
      ·
        refine ⟨6106652839952104676486923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32568815146411224941263589 6106652839952104676486923)
        ·
          refine ⟨9159979259928157014730385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6106652839952104676486923 9159979259928157014730385)
          ·
            refine ⟨6869984444946117761047789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9159979259928157014730385 6869984444946117761047789)
            ·
              refine ⟨2576244166854794160392921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6869984444946117761047789 2576244166854794160392921)
              ·
                refine ⟨1932183125141095620294691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2576244166854794160392921 1932183125141095620294691)
                ·
                  refine ⟨2898274687711643430442037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932183125141095620294691 2898274687711643430442037)
                  ·
                    refine ⟨271713251972966571603941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2898274687711643430442037 271713251972966571603941)
                    ·
                      rfl

theorem cell23_1587479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_1587479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587479 prefixEnd_1587479 := by exact prefixLift 1587479
  have htrace : WordTrace (prefixWord ++ tailWord_1587479) baseStart_1587479 baseEnd_1587479 := by
    simpa [prefixWord, tailWord_1587479, baseEnd_1587479] using wordTrace_append hprefix tailTrace_1587479
  have hstable : (prefixWord ++ tailWord_1587479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587479).length < 2 ^ (prefixWord ++ tailWord_1587479).sum := by decide
  have hdescent : baseEnd_1587479 < baseStart_1587479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587492 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_1587492 : Nat := 118140960795 + 1587492 * 2 ^ 59
def prefixEnd_1587492 : Nat := 4983230072969 + 3 ^ 40 * 1587492 * 2
def baseEnd_1587492 : Nat := 271715477055802721316421

theorem tailTrace_1587492 : CollatzResearch.WordTrace tailWord_1587492 prefixEnd_1587492 271715477055802721316421 := by
  unfold tailWord_1587492
  simp only [CollatzResearch.WordTrace]
  refine ⟨28950294982397540446790365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38600393309863387262387153 28950294982397540446790365)
  ·
    refine ⟨10856360618399077667546387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28950294982397540446790365 10856360618399077667546387)
    ·
      refine ⟨16284540927598616501319581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10856360618399077667546387 16284540927598616501319581)
      ·
        refine ⟨6106702847849481187994843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16284540927598616501319581 6106702847849481187994843)
        ·
          refine ⟨9160054271774221781992265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6106702847849481187994843 9160054271774221781992265)
          ·
            refine ⟨6870040703830666336494199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9160054271774221781992265 6870040703830666336494199)
            ·
              refine ⟨10305061055745999504741299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6870040703830666336494199 10305061055745999504741299)
              ·
                refine ⟨15457591583618999257111949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10305061055745999504741299 15457591583618999257111949)
                ·
                  refine ⟨5796596843857124721416981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15457591583618999257111949 5796596843857124721416981)
                  ·
                    refine ⟨271715477055802721316421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5796596843857124721416981 271715477055802721316421)
                    ·
                      rfl

theorem cell23_1587492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_1587492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587492 prefixEnd_1587492 := by exact prefixLift 1587492
  have htrace : WordTrace (prefixWord ++ tailWord_1587492) baseStart_1587492 baseEnd_1587492 := by
    simpa [prefixWord, tailWord_1587492, baseEnd_1587492] using wordTrace_append hprefix tailTrace_1587492
  have hstable : (prefixWord ++ tailWord_1587492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587492).length < 2 ^ (prefixWord ++ tailWord_1587492).sum := by decide
  have hdescent : baseEnd_1587492 < baseStart_1587492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587505 : List Nat := [1, 2, 2, 3, 15]
def baseStart_1587505 : Nat := 118140960795 + 1587505 * 2 ^ 59
def prefixEnd_1587505 : Nat := 4983230072969 + 3 ^ 40 * 1587505 * 2
def baseEnd_1587505 : Nat := 1118179844191929510407

theorem tailTrace_1587505 : CollatzResearch.WordTrace tailWord_1587505 prefixEnd_1587505 1118179844191929510407 := by
  unfold tailWord_1587505
  simp only [CollatzResearch.WordTrace]
  refine ⟨57901064113747984113803969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38600709409165322742535979 57901064113747984113803969)
  ·
    refine ⟨43425798085310988085352977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57901064113747984113803969 43425798085310988085352977)
    ·
      refine ⟨32569348563983241064014733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43425798085310988085352977 32569348563983241064014733)
      ·
        refine ⟨12213505711493715399005525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32569348563983241064014733 12213505711493715399005525)
        ·
          refine ⟨1118179844191929510407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 12213505711493715399005525 1118179844191929510407)
          ·
            rfl

theorem cell23_1587505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 15].length) (baseStart_1587505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587505 prefixEnd_1587505 := by exact prefixLift 1587505
  have htrace : WordTrace (prefixWord ++ tailWord_1587505) baseStart_1587505 baseEnd_1587505 := by
    simpa [prefixWord, tailWord_1587505, baseEnd_1587505] using wordTrace_append hprefix tailTrace_1587505
  have hstable : (prefixWord ++ tailWord_1587505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587505).length < 2 ^ (prefixWord ++ tailWord_1587505).sum := by decide
  have hdescent : baseEnd_1587505 < baseStart_1587505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587516 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 3, 2, 2]
def baseStart_1587516 : Nat := 118140960795 + 1587516 * 2 ^ 59
def prefixEnd_1587516 : Nat := 4983230072969 + 3 ^ 40 * 1587516 * 2
def baseEnd_1587516 : Nat := 815158754703116070049153

theorem tailTrace_1587516 : CollatzResearch.WordTrace tailWord_1587516 prefixEnd_1587516 815158754703116070049153 := by
  unfold tailWord_1587516
  simp only [CollatzResearch.WordTrace]
  refine ⟨28950732658354066496227201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38600976877805421994969601 28950732658354066496227201)
  ·
    refine ⟨21713049493765549872170401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28950732658354066496227201 21713049493765549872170401)
    ·
      refine ⟨16284787120324162404127801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21713049493765549872170401 16284787120324162404127801)
      ·
        refine ⟨12213590340243121803095851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16284787120324162404127801 12213590340243121803095851)
        ·
          refine ⟨18320385510364682704643777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12213590340243121803095851 18320385510364682704643777)
          ·
            refine ⟨13740289132773512028482833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18320385510364682704643777 13740289132773512028482833)
            ·
              refine ⟨10305216849580134021362125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13740289132773512028482833 10305216849580134021362125)
              ·
                refine ⟨3864456318592550258010797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10305216849580134021362125 3864456318592550258010797)
                ·
                  refine ⟨1449171119472206346754049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3864456318592550258010797 1449171119472206346754049)
                  ·
                    refine ⟨1086878339604154760065537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1449171119472206346754049 1086878339604154760065537)
                    ·
                      refine ⟨815158754703116070049153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1086878339604154760065537 815158754703116070049153)
                      ·
                        rfl

theorem cell23_1587516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_1587516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587516 prefixEnd_1587516 := by exact prefixLift 1587516
  have htrace : WordTrace (prefixWord ++ tailWord_1587516) baseStart_1587516 baseEnd_1587516 := by
    simpa [prefixWord, tailWord_1587516, baseEnd_1587516] using wordTrace_append hprefix tailTrace_1587516
  have hstable : (prefixWord ++ tailWord_1587516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587516).length < 2 ^ (prefixWord ++ tailWord_1587516).sum := by decide
  have hdescent : baseEnd_1587516 < baseStart_1587516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587593 : List Nat := [1, 2, 1, 1, 6, 2, 2, 2, 1, 3, 2]
def baseStart_1587593 : Nat := 118140960795 + 1587593 * 2 ^ 59
def prefixEnd_1587593 : Nat := 4983230072969 + 3 ^ 40 * 1587593 * 2
def baseEnd_1587593 : Nat := 815198292713512268786299

theorem tailTrace_1587593 : CollatzResearch.WordTrace tailWord_1587593 prefixEnd_1587593 815198292713512268786299 := by
  unfold tailWord_1587593
  simp only [CollatzResearch.WordTrace]
  refine ⟨57904273737429175143007433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38602849158286116762004955 57904273737429175143007433)
  ·
    refine ⟨43428205303071881357255575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57904273737429175143007433 43428205303071881357255575)
    ·
      refine ⟨65142307954607822035883363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43428205303071881357255575 65142307954607822035883363)
      ·
        refine ⟨97713461931911733053825045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65142307954607822035883363 97713461931911733053825045)
        ·
          refine ⟨4580318528058362486898049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97713461931911733053825045 4580318528058362486898049)
          ·
            refine ⟨3435238896043771865173537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4580318528058362486898049 3435238896043771865173537)
            ·
              refine ⟨2576429172032828898880153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3435238896043771865173537 2576429172032828898880153)
              ·
                refine ⟨1932321879024621674160115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2576429172032828898880153 1932321879024621674160115)
                ·
                  refine ⟨2898482818536932511240173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932321879024621674160115 2898482818536932511240173)
                  ·
                    refine ⟨1086931056951349691715065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2898482818536932511240173 1086931056951349691715065)
                    ·
                      refine ⟨815198292713512268786299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1086931056951349691715065 815198292713512268786299)
                      ·
                        rfl

theorem cell23_1587593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 3, 2].length) (baseStart_1587593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587593 prefixEnd_1587593 := by exact prefixLift 1587593
  have htrace : WordTrace (prefixWord ++ tailWord_1587593) baseStart_1587593 baseEnd_1587593 := by
    simpa [prefixWord, tailWord_1587593, baseEnd_1587593] using wordTrace_append hprefix tailTrace_1587593
  have hstable : (prefixWord ++ tailWord_1587593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587593).length < 2 ^ (prefixWord ++ tailWord_1587593).sum := by decide
  have hdescent : baseEnd_1587593 < baseStart_1587593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587623 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_1587623 : Nat := 118140960795 + 1587623 * 2 ^ 59
def prefixEnd_1587623 : Nat := 4983230072969 + 3 ^ 40 * 1587623 * 2
def baseEnd_1587623 : Nat := 815213697133147151411161

theorem tailTrace_1587623 : CollatzResearch.WordTrace tailWord_1587623 prefixEnd_1587623 815213697133147151411161 := by
  unfold tailWord_1587623
  simp only [CollatzResearch.WordTrace]
  refine ⟨57905367927320490266599523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38603578618213660177733015 57905367927320490266599523)
  ·
    refine ⟨86858051890980735399899285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57905367927320490266599523 86858051890980735399899285)
    ·
      refine ⟨4071471182389721971870279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86858051890980735399899285 4071471182389721971870279)
      ·
        refine ⟨6107206773584582957805419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4071471182389721971870279 6107206773584582957805419)
        ·
          refine ⟨9160810160376874436708129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6107206773584582957805419 9160810160376874436708129)
          ·
            refine ⟨6870607620282655827531097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9160810160376874436708129 6870607620282655827531097)
            ·
              refine ⟨5152955715211991870648323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6870607620282655827531097 5152955715211991870648323)
              ·
                refine ⟨7729433572817987805972485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5152955715211991870648323 7729433572817987805972485)
                ·
                  refine ⟨1449268794903372713619841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7729433572817987805972485 1449268794903372713619841)
                  ·
                    refine ⟨1086951596177529535214881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1449268794903372713619841 1086951596177529535214881)
                    ·
                      refine ⟨815213697133147151411161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1086951596177529535214881 815213697133147151411161)
                      ·
                        rfl

theorem cell23_1587623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_1587623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587623 prefixEnd_1587623 := by exact prefixLift 1587623
  have htrace : WordTrace (prefixWord ++ tailWord_1587623) baseStart_1587623 baseEnd_1587623 := by
    simpa [prefixWord, tailWord_1587623, baseEnd_1587623] using wordTrace_append hprefix tailTrace_1587623
  have hstable : (prefixWord ++ tailWord_1587623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587623).length < 2 ^ (prefixWord ++ tailWord_1587623).sum := by decide
  have hdescent : baseEnd_1587623 < baseStart_1587623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587642 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 3, 7]
def baseStart_1587642 : Nat := 118140960795 + 1587642 * 2 ^ 59
def prefixEnd_1587642 : Nat := 4983230072969 + 3 ^ 40 * 1587642 * 2
def baseEnd_1587642 : Nat := 271741151088527525691191

theorem tailTrace_1587642 : CollatzResearch.WordTrace tailWord_1587642 prefixEnd_1587642 271741151088527525691191 := by
  unfold tailWord_1587642
  simp only [CollatzResearch.WordTrace]
  refine ⟨14476515228562914127885295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38604040609501104341027453 14476515228562914127885295)
  ·
    refine ⟨21714772842844371191827943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14476515228562914127885295 21714772842844371191827943)
    ·
      refine ⟨32572159264266556787741915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21714772842844371191827943 32572159264266556787741915)
      ·
        refine ⟨48858238896399835181612873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32572159264266556787741915 48858238896399835181612873)
        ·
          refine ⟨36643679172299876386209655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48858238896399835181612873 36643679172299876386209655)
          ·
            refine ⟨54965518758449814579314483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36643679172299876386209655 54965518758449814579314483)
            ·
              refine ⟨82448278137674721868971725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54965518758449814579314483 82448278137674721868971725)
              ·
                refine ⟨30918104301628020700864397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82448278137674721868971725 30918104301628020700864397)
                ·
                  refine ⟨11594289113110507762824149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30918104301628020700864397 11594289113110507762824149)
                  ·
                    refine ⟨271741151088527525691191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11594289113110507762824149 271741151088527525691191)
                    ·
                      rfl

theorem cell23_1587642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_1587642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587642 prefixEnd_1587642 := by exact prefixLift 1587642
  have htrace : WordTrace (prefixWord ++ tailWord_1587642) baseStart_1587642 baseEnd_1587642 := by
    simpa [prefixWord, tailWord_1587642, baseEnd_1587642] using wordTrace_append hprefix tailTrace_1587642
  have hstable : (prefixWord ++ tailWord_1587642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587642).length < 2 ^ (prefixWord ++ tailWord_1587642).sum := by decide
  have hdescent : baseEnd_1587642 < baseStart_1587642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587669 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_1587669 : Nat := 118140960795 + 1587669 * 2 ^ 59
def prefixEnd_1587669 : Nat := 4983230072969 + 3 ^ 40 * 1587669 * 2
def baseEnd_1587669 : Nat := 815237317243253971435949

theorem tailTrace_1587669 : CollatzResearch.WordTrace tailWord_1587669 prefixEnd_1587669 815237317243253971435949 := by
  unfold tailWord_1587669
  simp only [CollatzResearch.WordTrace]
  refine ⟨57907045685153840122774061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38604697123435893415182707 57907045685153840122774061)
  ·
    refine ⟨21715142131932690046040273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57907045685153840122774061 21715142131932690046040273)
    ·
      refine ⟨16286356598949517534530205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21715142131932690046040273 16286356598949517534530205)
      ·
        refine ⟨6107383724606069075448827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16286356598949517534530205 6107383724606069075448827)
        ·
          refine ⟨9161075586909103613173241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6107383724606069075448827 9161075586909103613173241)
          ·
            refine ⟨6870806690181827709879931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9161075586909103613173241 6870806690181827709879931)
            ·
              refine ⟨10306210035272741564819897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6870806690181827709879931 10306210035272741564819897)
              ·
                refine ⟨7729657526454556173614923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10306210035272741564819897 7729657526454556173614923)
                ·
                  refine ⟨11594486289681834260422385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7729657526454556173614923 11594486289681834260422385)
                  ·
                    refine ⟨8695864717261375695316789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11594486289681834260422385 8695864717261375695316789)
                    ·
                      refine ⟨815237317243253971435949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8695864717261375695316789 815237317243253971435949)
                      ·
                        rfl

theorem cell23_1587669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_1587669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587669 prefixEnd_1587669 := by exact prefixLift 1587669
  have htrace : WordTrace (prefixWord ++ tailWord_1587669) baseStart_1587669 baseEnd_1587669 := by
    simpa [prefixWord, tailWord_1587669, baseEnd_1587669] using wordTrace_append hprefix tailTrace_1587669
  have hstable : (prefixWord ++ tailWord_1587669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587669).length < 2 ^ (prefixWord ++ tailWord_1587669).sum := by decide
  have hdescent : baseEnd_1587669 < baseStart_1587669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587696 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 2, 4, 2]
def baseStart_1587696 : Nat := 118140960795 + 1587696 * 2 ^ 59
def prefixEnd_1587696 : Nat := 4983230072969 + 3 ^ 40 * 1587696 * 2
def baseEnd_1587696 : Nat := 815251181220925365798325

theorem tailTrace_1587696 : CollatzResearch.WordTrace tailWord_1587696 prefixEnd_1587696 815251181220925365798325 := by
  unfold tailWord_1587696
  simp only [CollatzResearch.WordTrace]
  refine ⟨28954015228028011867003471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38605353637370682489337961 28954015228028011867003471)
  ·
    refine ⟨43431022842042017800505207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28954015228028011867003471 43431022842042017800505207)
    ·
      refine ⟨65146534263063026700757811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43431022842042017800505207 65146534263063026700757811)
      ·
        refine ⟨97719801394594540051136717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65146534263063026700757811 97719801394594540051136717)
        ·
          refine ⟨36644925522972952519176269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97719801394594540051136717 36644925522972952519176269)
          ·
            refine ⟨13741847071114857194691101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36644925522972952519176269 13741847071114857194691101)
            ·
              refine ⟨5153192651668071448009163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13741847071114857194691101 5153192651668071448009163)
              ·
                refine ⟨7729788977502107172013745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5153192651668071448009163 7729788977502107172013745)
                ·
                  refine ⟨5797341733126580379010309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7729788977502107172013745 5797341733126580379010309)
                  ·
                    refine ⟨1087001574961233821064433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5797341733126580379010309 1087001574961233821064433)
                    ·
                      refine ⟨815251181220925365798325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1087001574961233821064433 815251181220925365798325)
                      ·
                        rfl

theorem cell23_1587696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 2, 4, 2].length) (baseStart_1587696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587696 prefixEnd_1587696 := by exact prefixLift 1587696
  have htrace : WordTrace (prefixWord ++ tailWord_1587696) baseStart_1587696 baseEnd_1587696 := by
    simpa [prefixWord, tailWord_1587696, baseEnd_1587696] using wordTrace_append hprefix tailTrace_1587696
  have hstable : (prefixWord ++ tailWord_1587696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587696).length < 2 ^ (prefixWord ++ tailWord_1587696).sum := by decide
  have hdescent : baseEnd_1587696 < baseStart_1587696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587699 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 3]
def baseStart_1587699 : Nat := 118140960795 + 1587699 * 2 ^ 59
def prefixEnd_1587699 : Nat := 4983230072969 + 3 ^ 40 * 1587699 * 2
def baseEnd_1587699 : Nat := 815252721662888854060811

theorem tailTrace_1587699 : CollatzResearch.WordTrace tailWord_1587699 prefixEnd_1587699 815252721662888854060811 := by
  unfold tailWord_1587699
  simp only [CollatzResearch.WordTrace]
  refine ⟨57908139875045155246366151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38605426583363436830910767 57908139875045155246366151)
  ·
    refine ⟨86862209812567732869549227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57908139875045155246366151 86862209812567732869549227)
    ·
      refine ⟨130293314718851599304323841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86862209812567732869549227 130293314718851599304323841)
      ·
        refine ⟨97719986039138699478242881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130293314718851599304323841 97719986039138699478242881)
        ·
          refine ⟨73289989529354024608682161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97719986039138699478242881 73289989529354024608682161)
          ·
            refine ⟨54967492147015518456511621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73289989529354024608682161 54967492147015518456511621)
            ·
              refine ⟨10306404777565409710595929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54967492147015518456511621 10306404777565409710595929)
              ·
                refine ⟨7729803583174057282946947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10306404777565409710595929 7729803583174057282946947)
                ·
                  refine ⟨11594705374761085924420421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7729803583174057282946947 11594705374761085924420421)
                  ·
                    refine ⟨2174007257767703610828829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11594705374761085924420421 2174007257767703610828829)
                    ·
                      refine ⟨815252721662888854060811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2174007257767703610828829 815252721662888854060811)
                      ·
                        rfl

theorem cell23_1587699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 3].length) (baseStart_1587699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587699 prefixEnd_1587699 := by exact prefixLift 1587699
  have htrace : WordTrace (prefixWord ++ tailWord_1587699) baseStart_1587699 baseEnd_1587699 := by
    simpa [prefixWord, tailWord_1587699, baseEnd_1587699] using wordTrace_append hprefix tailTrace_1587699
  have hstable : (prefixWord ++ tailWord_1587699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587699).length < 2 ^ (prefixWord ++ tailWord_1587699).sum := by decide
  have hdescent : baseEnd_1587699 < baseStart_1587699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587713 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_1587713 : Nat := 118140960795 + 1587713 * 2 ^ 59
def prefixEnd_1587713 : Nat := 4983230072969 + 3 ^ 40 * 1587713 * 2
def baseEnd_1587713 : Nat := 815259910392051799285747

theorem tailTrace_1587713 : CollatzResearch.WordTrace tailWord_1587713 prefixEnd_1587713 815259910392051799285747 := by
  unfold tailWord_1587713
  simp only [CollatzResearch.WordTrace]
  refine ⟨57908650496994435637375793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38605766997996290424917195 57908650496994435637375793)
  ·
    refine ⟨43431487872745826728031845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57908650496994435637375793 43431487872745826728031845)
    ·
      refine ⟨8143403976139842511505971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43431487872745826728031845 8143403976139842511505971)
      ·
        refine ⟨12215105964209763767258957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8143403976139842511505971 12215105964209763767258957)
        ·
          refine ⟨4580664736578661412722109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12215105964209763767258957 4580664736578661412722109)
          ·
            refine ⟨1717749276216998029770791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4580664736578661412722109 1717749276216998029770791)
            ·
              refine ⟨2576623914325497044656187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717749276216998029770791 2576623914325497044656187)
              ·
                refine ⟨3864935871488245566984281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2576623914325497044656187 3864935871488245566984281)
                ·
                  refine ⟨2898701903616184175238211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3864935871488245566984281 2898701903616184175238211)
                  ·
                    refine ⟨4348052855424276262857317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2898701903616184175238211 4348052855424276262857317)
                    ·
                      refine ⟨815259910392051799285747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4348052855424276262857317 815259910392051799285747)
                      ·
                        rfl

theorem cell23_1587713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_1587713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587713 prefixEnd_1587713 := by exact prefixLift 1587713
  have htrace : WordTrace (prefixWord ++ tailWord_1587713) baseStart_1587713 baseEnd_1587713 := by
    simpa [prefixWord, tailWord_1587713, baseEnd_1587713] using wordTrace_append hprefix tailTrace_1587713
  have hstable : (prefixWord ++ tailWord_1587713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587713).length < 2 ^ (prefixWord ++ tailWord_1587713).sum := by decide
  have hdescent : baseEnd_1587713 < baseStart_1587713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587723 : List Nat := [1, 1, 1, 1, 7, 1, 1, 5, 1, 4]
def baseStart_1587723 : Nat := 118140960795 + 1587723 * 2 ^ 59
def prefixEnd_1587723 : Nat := 4983230072969 + 3 ^ 40 * 1587723 * 2
def baseEnd_1587723 : Nat := 271755015066198920053567

theorem tailTrace_1587723 : CollatzResearch.WordTrace tailWord_1587723 prefixEnd_1587723 271755015066198920053567 := by
  unfold tailWord_1587723
  simp only [CollatzResearch.WordTrace]
  refine ⟨57909015226958207345239823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38606010151305471563493215 57909015226958207345239823)
  ·
    refine ⟨86863522840437311017859735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57909015226958207345239823 86863522840437311017859735)
    ·
      refine ⟨130295284260655966526789603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86863522840437311017859735 130295284260655966526789603)
      ·
        refine ⟨195442926390983949790184405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130295284260655966526789603 195442926390983949790184405)
        ·
          refine ⟨4580693587288686323207447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 195442926390983949790184405 4580693587288686323207447)
          ·
            refine ⟨6871040380933029484811171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4580693587288686323207447 6871040380933029484811171)
            ·
              refine ⟨10306560571399544227216757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6871040380933029484811171 10306560571399544227216757)
              ·
                refine ⟨966240053568707271301571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10306560571399544227216757 966240053568707271301571)
                ·
                  refine ⟨1449360080353060906952357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966240053568707271301571 1449360080353060906952357)
                  ·
                    refine ⟨271755015066198920053567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1449360080353060906952357 271755015066198920053567)
                    ·
                      rfl

theorem cell23_1587723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 1, 4].length) (baseStart_1587723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587723 prefixEnd_1587723 := by exact prefixLift 1587723
  have htrace : WordTrace (prefixWord ++ tailWord_1587723) baseStart_1587723 baseEnd_1587723 := by
    simpa [prefixWord, tailWord_1587723, baseEnd_1587723] using wordTrace_append hprefix tailTrace_1587723
  have hstable : (prefixWord ++ tailWord_1587723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587723).length < 2 ^ (prefixWord ++ tailWord_1587723).sum := by decide
  have hdescent : baseEnd_1587723 < baseStart_1587723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587736 : List Nat := [2, 1, 2, 3, 3, 1, 3, 2, 6]
def baseStart_1587736 : Nat := 118140960795 + 1587736 * 2 ^ 59
def prefixEnd_1587736 : Nat := 4983230072969 + 3 ^ 40 * 1587736 * 2
def baseEnd_1587736 : Nat := 90585746716345023255349

theorem tailTrace_1587736 : CollatzResearch.WordTrace tailWord_1587736 prefixEnd_1587736 90585746716345023255349 := by
  unfold tailWord_1587736
  simp only [CollatzResearch.WordTrace]
  refine ⟨28954744687955555282731531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38606326250607407043642041 28954744687955555282731531)
  ·
    refine ⟨43432117031933332924097297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28954744687955555282731531 43432117031933332924097297)
    ·
      refine ⟨32574087773949999693072973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43432117031933332924097297 32574087773949999693072973)
      ·
        refine ⟨12215282915231249884902365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32574087773949999693072973 12215282915231249884902365)
        ·
          refine ⟨4580731093211718706838387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12215282915231249884902365 4580731093211718706838387)
          ·
            refine ⟨6871096639817578060257581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4580731093211718706838387 6871096639817578060257581)
            ·
              refine ⟨2576661239931591772596593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6871096639817578060257581 2576661239931591772596593)
              ·
                refine ⟨1932495929948693829447445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2576661239931591772596593 1932495929948693829447445)
                ·
                  refine ⟨90585746716345023255349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1932495929948693829447445 90585746716345023255349)
                  ·
                    rfl

theorem cell23_1587736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 6].length) (baseStart_1587736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587736 prefixEnd_1587736 := by exact prefixLift 1587736
  have htrace : WordTrace (prefixWord ++ tailWord_1587736) baseStart_1587736 baseEnd_1587736 := by
    simpa [prefixWord, tailWord_1587736, baseEnd_1587736] using wordTrace_append hprefix tailTrace_1587736
  have hstable : (prefixWord ++ tailWord_1587736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587736).length < 2 ^ (prefixWord ++ tailWord_1587736).sum := by decide
  have hdescent : baseEnd_1587736 < baseStart_1587736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587749 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 5, 5]
def baseStart_1587749 : Nat := 118140960795 + 1587749 * 2 ^ 59
def prefixEnd_1587749 : Nat := 4983230072969 + 3 ^ 40 * 1587749 * 2
def baseEnd_1587749 : Nat := 271759465231871219478527

theorem tailTrace_1587749 : CollatzResearch.WordTrace tailWord_1587749 prefixEnd_1587749 271759465231871219478527 := by
  unfold tailWord_1587749
  simp only [CollatzResearch.WordTrace]
  refine ⟨57909963524864013785686301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38606642349909342523790867 57909963524864013785686301)
  ·
    refine ⟨21716236321824005169632363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57909963524864013785686301 21716236321824005169632363)
    ·
      refine ⟨32574354482736007754448545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21716236321824005169632363 32574354482736007754448545)
      ·
        refine ⟨24430765862052005815836409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32574354482736007754448545 24430765862052005815836409)
        ·
          refine ⟨18323074396539004361877307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24430765862052005815836409 18323074396539004361877307)
          ·
            refine ⟨27484611594808506542815961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18323074396539004361877307 27484611594808506542815961)
            ·
              refine ⟨20613458696106379907111971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27484611594808506542815961 20613458696106379907111971)
              ·
                refine ⟨30920188044159569860667957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20613458696106379907111971 30920188044159569860667957)
                ·
                  refine ⟨2898767629139959674437621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30920188044159569860667957 2898767629139959674437621)
                  ·
                    refine ⟨271759465231871219478527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2898767629139959674437621 271759465231871219478527)
                    ·
                      rfl

theorem cell23_1587749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_1587749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587749 prefixEnd_1587749 := by exact prefixLift 1587749
  have htrace : WordTrace (prefixWord ++ tailWord_1587749) baseStart_1587749 baseEnd_1587749 := by
    simpa [prefixWord, tailWord_1587749, baseEnd_1587749] using wordTrace_append hprefix tailTrace_1587749
  have hstable : (prefixWord ++ tailWord_1587749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587749).length < 2 ^ (prefixWord ++ tailWord_1587749).sum := by decide
  have hdescent : baseEnd_1587749 < baseStart_1587749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587773 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 1, 5, 2]
def baseStart_1587773 : Nat := 118140960795 + 1587773 * 2 ^ 59
def prefixEnd_1587773 : Nat := 4983230072969 + 3 ^ 40 * 1587773 * 2
def baseEnd_1587773 : Nat := 815290719231321564535471

theorem tailTrace_1587773 : CollatzResearch.WordTrace tailWord_1587773 prefixEnd_1587773 815290719231321564535471 := by
  unfold tailWord_1587773
  simp only [CollatzResearch.WordTrace]
  refine ⟨57910838876777065884559973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38607225917851377256373315 57910838876777065884559973)
  ·
    refine ⟨10858282289395699853354995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57910838876777065884559973 10858282289395699853354995)
    ·
      refine ⟨16287423434093549780032493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10858282289395699853354995 16287423434093549780032493)
      ·
        refine ⟨6107783787785081167512185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16287423434093549780032493 6107783787785081167512185)
        ·
          refine ⟨4580837840838810875634139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6107783787785081167512185 4580837840838810875634139)
          ·
            refine ⟨6871256761258216313451209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4580837840838810875634139 6871256761258216313451209)
            ·
              refine ⟨5153442570943662235088407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6871256761258216313451209 5153442570943662235088407)
              ·
                refine ⟨7730163856415493352632611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5153442570943662235088407 7730163856415493352632611)
                ·
                  refine ⟨11595245784623240028948917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7730163856415493352632611 11595245784623240028948917)
                  ·
                    refine ⟨1087054292308428752713961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11595245784623240028948917 1087054292308428752713961)
                    ·
                      refine ⟨815290719231321564535471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1087054292308428752713961 815290719231321564535471)
                      ·
                        rfl

theorem cell23_1587773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_1587773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587773 prefixEnd_1587773 := by exact prefixLift 1587773
  have htrace : WordTrace (prefixWord ++ tailWord_1587773) baseStart_1587773 baseEnd_1587773 := by
    simpa [prefixWord, tailWord_1587773, baseEnd_1587773] using wordTrace_append hprefix tailTrace_1587773
  have hstable : (prefixWord ++ tailWord_1587773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587773).length < 2 ^ (prefixWord ++ tailWord_1587773).sum := by decide
  have hdescent : baseEnd_1587773 < baseStart_1587773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587774 : List Nat := [4, 2, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_1587774 : Nat := 118140960795 + 1587774 * 2 ^ 59
def prefixEnd_1587774 : Nat := 4983230072969 + 3 ^ 40 * 1587774 * 2
def baseEnd_1587774 : Nat := 271763744237325353540989

theorem tailTrace_1587774 : CollatzResearch.WordTrace tailWord_1587774 prefixEnd_1587774 271763744237325353540989 := by
  unfold tailWord_1587774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7238859418721680381918297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38607250233182295370230917 7238859418721680381918297)
  ·
    refine ⟨5429144564041260286438723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7238859418721680381918297 5429144564041260286438723)
    ·
      refine ⟨8143716846061890429658085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5429144564041260286438723 8143716846061890429658085)
      ·
        refine ⟨1526946908636604455560891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8143716846061890429658085 1526946908636604455560891)
        ·
          refine ⟨2290420362954906683341337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526946908636604455560891 2290420362954906683341337)
          ·
            refine ⟨1717815272216180012506003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2290420362954906683341337 1717815272216180012506003)
            ·
              refine ⟨2576722908324270018759005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717815272216180012506003 2576722908324270018759005)
              ·
                refine ⟨966271090621601257034627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2576722908324270018759005 966271090621601257034627)
                ·
                  refine ⟨1449406635932401885551941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966271090621601257034627 1449406635932401885551941)
                  ·
                    refine ⟨271763744237325353540989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1449406635932401885551941 271763744237325353540989)
                    ·
                      rfl

theorem cell23_1587774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_1587774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587774 prefixEnd_1587774 := by exact prefixLift 1587774
  have htrace : WordTrace (prefixWord ++ tailWord_1587774) baseStart_1587774 baseEnd_1587774 := by
    simpa [prefixWord, tailWord_1587774, baseEnd_1587774] using wordTrace_append hprefix tailTrace_1587774
  have hstable : (prefixWord ++ tailWord_1587774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587774).length < 2 ^ (prefixWord ++ tailWord_1587774).sum := by decide
  have hdescent : baseEnd_1587774 < baseStart_1587774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587779 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 1, 6]
def baseStart_1587779 : Nat := 118140960795 + 1587779 * 2 ^ 59
def prefixEnd_1587779 : Nat := 4983230072969 + 3 ^ 40 * 1587779 * 2
def baseEnd_1587779 : Nat := 271764600038416180353481

theorem tailTrace_1587779 : CollatzResearch.WordTrace tailWord_1587779 prefixEnd_1587779 271764600038416180353481 := by
  unfold tailWord_1587779
  simp only [CollatzResearch.WordTrace]
  refine ⟨57911057714755328909278391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38607371809836885939518927 57911057714755328909278391)
  ·
    refine ⟨86866586572132993363917587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57911057714755328909278391 86866586572132993363917587)
    ·
      refine ⟨130299879858199490045876381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86866586572132993363917587 130299879858199490045876381)
      ·
        refine ⟨48862454946824808767203643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130299879858199490045876381 48862454946824808767203643)
        ·
          refine ⟨73293682420237213150805465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48862454946824808767203643 73293682420237213150805465)
          ·
            refine ⟨54970261815177909863104099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73293682420237213150805465 54970261815177909863104099)
            ·
              refine ⟨82455392722766864794656149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54970261815177909863104099 82455392722766864794656149)
              ·
                refine ⟨3865096533879696787249507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82455392722766864794656149 3865096533879696787249507)
                ·
                  refine ⟨5797644800819545180874261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3865096533879696787249507 5797644800819545180874261)
                  ·
                    refine ⟨271764600038416180353481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5797644800819545180874261 271764600038416180353481)
                    ·
                      rfl

theorem cell23_1587779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 6].length) (baseStart_1587779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587779 prefixEnd_1587779 := by exact prefixLift 1587779
  have htrace : WordTrace (prefixWord ++ tailWord_1587779) baseStart_1587779 baseEnd_1587779 := by
    simpa [prefixWord, tailWord_1587779, baseEnd_1587779] using wordTrace_append hprefix tailTrace_1587779
  have hstable : (prefixWord ++ tailWord_1587779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587779).length < 2 ^ (prefixWord ++ tailWord_1587779).sum := by decide
  have hdescent : baseEnd_1587779 < baseStart_1587779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587799 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_1587799 : Nat := 118140960795 + 1587799 * 2 ^ 59
def prefixEnd_1587799 : Nat := 4983230072969 + 3 ^ 40 * 1587799 * 2
def baseEnd_1587799 : Nat := 815304069728338462810351

theorem tailTrace_1587799 : CollatzResearch.WordTrace tailWord_1587799 prefixEnd_1587799 815304069728338462810351 := by
  unfold tailWord_1587799
  simp only [CollatzResearch.WordTrace]
  refine ⟨57911787174682872325006451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38607858116455248216670967 57911787174682872325006451)
  ·
    refine ⟨86867680762024308487509677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57911787174682872325006451 86867680762024308487509677)
    ·
      refine ⟨32575380285759115682816129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86867680762024308487509677 32575380285759115682816129)
      ·
        refine ⟨24431535214319336762112097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32575380285759115682816129 24431535214319336762112097)
        ·
          refine ⟨18323651410739502571584073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24431535214319336762112097 18323651410739502571584073)
          ·
            refine ⟨13742738558054626928688055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18323651410739502571584073 13742738558054626928688055)
            ·
              refine ⟨20614107837081940393032083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13742738558054626928688055 20614107837081940393032083)
              ·
                refine ⟨30921161755622910589548125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20614107837081940393032083 30921161755622910589548125)
                ·
                  refine ⟨11595435658358591471080547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30921161755622910589548125 11595435658358591471080547)
                  ·
                    refine ⟨17393153487537887206620821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11595435658358591471080547 17393153487537887206620821)
                    ·
                      refine ⟨815304069728338462810351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17393153487537887206620821 815304069728338462810351)
                      ·
                        rfl

theorem cell23_1587799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_1587799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587799 prefixEnd_1587799 := by exact prefixLift 1587799
  have htrace : WordTrace (prefixWord ++ tailWord_1587799) baseStart_1587799 baseEnd_1587799 := by
    simpa [prefixWord, tailWord_1587799, baseEnd_1587799] using wordTrace_append hprefix tailTrace_1587799
  have hstable : (prefixWord ++ tailWord_1587799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587799).length < 2 ^ (prefixWord ++ tailWord_1587799).sum := by decide
  have hdescent : baseEnd_1587799 < baseStart_1587799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587809 : List Nat := [1, 2, 3, 1, 1, 4, 1, 10]
def baseStart_1587809 : Nat := 118140960795 + 1587809 * 2 ^ 59
def prefixEnd_1587809 : Nat := 4983230072969 + 3 ^ 40 * 1587809 * 2
def baseEnd_1587809 : Nat := 30196637204995682358715

theorem tailTrace_1587809 : CollatzResearch.WordTrace tailWord_1587809 prefixEnd_1587809 30196637204995682358715 := by
  unfold tailWord_1587809
  simp only [CollatzResearch.WordTrace]
  refine ⟨57912151904646644032870481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38608101269764429355246987 57912151904646644032870481)
  ·
    refine ⟨43434113928484983024652861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57912151904646644032870481 43434113928484983024652861)
    ·
      refine ⟨16287792723181868634244823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43434113928484983024652861 16287792723181868634244823)
      ·
        refine ⟨24431689084772802951367235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16287792723181868634244823 24431689084772802951367235)
        ·
          refine ⟨36647533627159204427050853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24431689084772802951367235 36647533627159204427050853)
          ·
            refine ⟨6871412555092350830072035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36647533627159204427050853 6871412555092350830072035)
            ·
              refine ⟨10307118832638526245108053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6871412555092350830072035 10307118832638526245108053)
              ·
                refine ⟨30196637204995682358715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10307118832638526245108053 30196637204995682358715)
                ·
                  rfl

theorem cell23_1587809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 10].length) (baseStart_1587809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587809 prefixEnd_1587809 := by exact prefixLift 1587809
  have htrace : WordTrace (prefixWord ++ tailWord_1587809) baseStart_1587809 baseEnd_1587809 := by
    simpa [prefixWord, tailWord_1587809, baseEnd_1587809] using wordTrace_append hprefix tailTrace_1587809
  have hstable : (prefixWord ++ tailWord_1587809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587809).length < 2 ^ (prefixWord ++ tailWord_1587809).sum := by decide
  have hdescent : baseEnd_1587809 < baseStart_1587809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587823 : List Nat := [1, 1, 2, 1, 3, 2, 5, 2, 1, 2, 3]
def baseStart_1587823 : Nat := 118140960795 + 1587823 * 2 ^ 59
def prefixEnd_1587823 : Nat := 4983230072969 + 3 ^ 40 * 1587823 * 2
def baseEnd_1587823 : Nat := 815316393264046368910241

theorem tailTrace_1587823 : CollatzResearch.WordTrace tailWord_1587823 prefixEnd_1587823 815316393264046368910241 := by
  unfold tailWord_1587823
  simp only [CollatzResearch.WordTrace]
  refine ⟨57912662526595924423880123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38608441684397282949253415 57912662526595924423880123)
  ·
    refine ⟨86868993789893886635820185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57912662526595924423880123 86868993789893886635820185)
    ·
      refine ⟨65151745342420414976865139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86868993789893886635820185 65151745342420414976865139)
      ·
        refine ⟨97727618013630622465297709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65151745342420414976865139 97727618013630622465297709)
        ·
          refine ⟨36647856755111483424486641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97727618013630622465297709 36647856755111483424486641)
          ·
            refine ⟨27485892566333612568364981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36647856755111483424486641 27485892566333612568364981)
            ·
              refine ⟨2576802428093776178284217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27485892566333612568364981 2576802428093776178284217)
              ·
                refine ⟨1932601821070332133713163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2576802428093776178284217 1932601821070332133713163)
                ·
                  refine ⟨2898902731605498200569745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932601821070332133713163 2898902731605498200569745)
                  ·
                    refine ⟨2174177048704123650427309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2898902731605498200569745 2174177048704123650427309)
                    ·
                      refine ⟨815316393264046368910241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2174177048704123650427309 815316393264046368910241)
                      ·
                        rfl

theorem cell23_1587823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 2, 3].length) (baseStart_1587823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587823 prefixEnd_1587823 := by exact prefixLift 1587823
  have htrace : WordTrace (prefixWord ++ tailWord_1587823) baseStart_1587823 baseEnd_1587823 := by
    simpa [prefixWord, tailWord_1587823, baseEnd_1587823] using wordTrace_append hprefix tailTrace_1587823
  have hstable : (prefixWord ++ tailWord_1587823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587823).length < 2 ^ (prefixWord ++ tailWord_1587823).sum := by decide
  have hdescent : baseEnd_1587823 < baseStart_1587823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587836 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_1587836 : Nat := 118140960795 + 1587836 * 2 ^ 59
def prefixEnd_1587836 : Nat := 4983230072969 + 3 ^ 40 * 1587836 * 2
def baseEnd_1587836 : Nat := 815323068512554818047681

theorem tailTrace_1587836 : CollatzResearch.WordTrace tailWord_1587836 prefixEnd_1587836 815323068512554818047681 := by
  unfold tailWord_1587836
  simp only [CollatzResearch.WordTrace]
  refine ⟨28956568337774413822051681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38608757783699218429402241 28956568337774413822051681)
  ·
    refine ⟨21717426253330810366538761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28956568337774413822051681 21717426253330810366538761)
    ·
      refine ⟨16288069689998107774904071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21717426253330810366538761 16288069689998107774904071)
      ·
        refine ⟨24432104534997161662356107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16288069689998107774904071 24432104534997161662356107)
        ·
          refine ⟨36648156802495742493534161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24432104534997161662356107 36648156802495742493534161)
          ·
            refine ⟨27486117601871806870150621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36648156802495742493534161 27486117601871806870150621)
            ·
              refine ⟨10307294100701927576306483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27486117601871806870150621 10307294100701927576306483)
              ·
                refine ⟨15460941151052891364459725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10307294100701927576306483 15460941151052891364459725)
                ·
                  refine ⟨5797852931644834261672397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15460941151052891364459725 5797852931644834261672397)
                  ·
                    refine ⟨2174194849366812848127149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5797852931644834261672397 2174194849366812848127149)
                    ·
                      refine ⟨815323068512554818047681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2174194849366812848127149 815323068512554818047681)
                      ·
                        rfl

theorem cell23_1587836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_1587836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587836 prefixEnd_1587836 := by exact prefixLift 1587836
  have htrace : WordTrace (prefixWord ++ tailWord_1587836) baseStart_1587836 baseEnd_1587836 := by
    simpa [prefixWord, tailWord_1587836, baseEnd_1587836] using wordTrace_append hprefix tailTrace_1587836
  have hstable : (prefixWord ++ tailWord_1587836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587836).length < 2 ^ (prefixWord ++ tailWord_1587836).sum := by decide
  have hdescent : baseEnd_1587836 < baseStart_1587836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587840 : List Nat := [2, 1, 1, 2, 1, 6, 3, 1, 1, 2, 3]
def baseStart_1587840 : Nat := 118140960795 + 1587840 * 2 ^ 59
def prefixEnd_1587840 : Nat := 4983230072969 + 3 ^ 40 * 1587840 * 2
def baseEnd_1587840 : Nat := 815325122435172802397663

theorem tailTrace_1587840 : CollatzResearch.WordTrace tailWord_1587840 prefixEnd_1587840 815325122435172802397663 := by
  unfold tailWord_1587840
  simp only [CollatzResearch.WordTrace]
  refine ⟨28956641283767168163624487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38608855045022890884832649 28956641283767168163624487)
  ·
    refine ⟨43434961925650752245436731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28956641283767168163624487 43434961925650752245436731)
    ·
      refine ⟨65152442888476128368155097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43434961925650752245436731 65152442888476128368155097)
      ·
        refine ⟨48864332166357096276116323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65152442888476128368155097 48864332166357096276116323)
        ·
          refine ⟨73296498249535644414174485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48864332166357096276116323 73296498249535644414174485)
          ·
            refine ⟨3435773355446983331914429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73296498249535644414174485 3435773355446983331914429)
            ·
              refine ⟨1288415008292618749467911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3435773355446983331914429 1288415008292618749467911)
              ·
                refine ⟨1932622512438928124201867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1288415008292618749467911 1932622512438928124201867)
                ·
                  refine ⟨2898933768658392186302801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932622512438928124201867 2898933768658392186302801)
                  ·
                    refine ⟨2174200326493794139727101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2898933768658392186302801 2174200326493794139727101)
                    ·
                      refine ⟨815325122435172802397663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2174200326493794139727101 815325122435172802397663)
                      ·
                        rfl

theorem cell23_1587840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 1, 2, 3].length) (baseStart_1587840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587840 prefixEnd_1587840 := by exact prefixLift 1587840
  have htrace : WordTrace (prefixWord ++ tailWord_1587840) baseStart_1587840 baseEnd_1587840 := by
    simpa [prefixWord, tailWord_1587840, baseEnd_1587840] using wordTrace_append hprefix tailTrace_1587840
  have hstable : (prefixWord ++ tailWord_1587840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587840).length < 2 ^ (prefixWord ++ tailWord_1587840).sum := by decide
  have hdescent : baseEnd_1587840 < baseStart_1587840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587863 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 5, 3, 2]
def baseStart_1587863 : Nat := 118140960795 + 1587863 * 2 ^ 59
def prefixEnd_1587863 : Nat := 4983230072969 + 3 ^ 40 * 1587863 * 2
def baseEnd_1587863 : Nat := 815336932490226212410057

theorem tailTrace_1587863 : CollatzResearch.WordTrace tailWord_1587863 prefixEnd_1587863 815336932490226212410057 := by
  unfold tailWord_1587863
  simp only [CollatzResearch.WordTrace]
  refine ⟨57914121446451011255336243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38609414297634007503557495 57914121446451011255336243)
  ·
    refine ⟨86871182169676516883004365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57914121446451011255336243 86871182169676516883004365)
    ·
      refine ⟨32576693313628693831126637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86871182169676516883004365 32576693313628693831126637)
      ·
        refine ⟨12216259992610760186672489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32576693313628693831126637 12216259992610760186672489)
        ·
          refine ⟨9162194994458070140004367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12216259992610760186672489 9162194994458070140004367)
          ·
            refine ⟨13743292491687105210006551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9162194994458070140004367 13743292491687105210006551)
            ·
              refine ⟨20614938737530657815009827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13743292491687105210006551 20614938737530657815009827)
              ·
                refine ⟨30922408106295986722514741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20614938737530657815009827 30922408106295986722514741)
                ·
                  refine ⟨2898975759965248755235757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30922408106295986722514741 2898975759965248755235757)
                  ·
                    refine ⟨1087115909986968283213409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2898975759965248755235757 1087115909986968283213409)
                    ·
                      refine ⟨815336932490226212410057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1087115909986968283213409 815336932490226212410057)
                      ·
                        rfl

theorem cell23_1587863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_1587863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587863 prefixEnd_1587863 := by exact prefixLift 1587863
  have htrace : WordTrace (prefixWord ++ tailWord_1587863) baseStart_1587863 baseEnd_1587863 := by
    simpa [prefixWord, tailWord_1587863, baseEnd_1587863] using wordTrace_append hprefix tailTrace_1587863
  have hstable : (prefixWord ++ tailWord_1587863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587863).length < 2 ^ (prefixWord ++ tailWord_1587863).sum := by decide
  have hdescent : baseEnd_1587863 < baseStart_1587863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587870 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_1587870 : Nat := 118140960795 + 1587870 * 2 ^ 59
def prefixEnd_1587870 : Nat := 4983230072969 + 3 ^ 40 * 1587870 * 2
def baseEnd_1587870 : Nat := 815340526854807685022525

theorem tailTrace_1587870 : CollatzResearch.WordTrace tailWord_1587870 prefixEnd_1587870 815340526854807685022525 := by
  unfold tailWord_1587870
  simp only [CollatzResearch.WordTrace]
  refine ⟨7239297094678206431355133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38609584504950434300560709 7239297094678206431355133)
  ·
    refine ⟨2714736410504327411758175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7239297094678206431355133 2714736410504327411758175)
    ·
      refine ⟨4072104615756491117637263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2714736410504327411758175 4072104615756491117637263)
      ·
        refine ⟨6108156923634736676455895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4072104615756491117637263 6108156923634736676455895)
        ·
          refine ⟨9162235385452105014683843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6108156923634736676455895 9162235385452105014683843)
          ·
            refine ⟨13743353078178157522025765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9162235385452105014683843 13743353078178157522025765)
            ·
              refine ⟨2576878702158404535379831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13743353078178157522025765 2576878702158404535379831)
              ·
                refine ⟨3865318053237606803069747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2576878702158404535379831 3865318053237606803069747)
                ·
                  refine ⟨5797977079856410204604621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3865318053237606803069747 5797977079856410204604621)
                  ·
                    refine ⟨2174241404946153826726733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5797977079856410204604621 2174241404946153826726733)
                    ·
                      refine ⟨815340526854807685022525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2174241404946153826726733 815340526854807685022525)
                      ·
                        rfl

theorem cell23_1587870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_1587870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587870 prefixEnd_1587870 := by exact prefixLift 1587870
  have htrace : WordTrace (prefixWord ++ tailWord_1587870) baseStart_1587870 baseEnd_1587870 := by
    simpa [prefixWord, tailWord_1587870, baseEnd_1587870] using wordTrace_append hprefix tailTrace_1587870
  have hstable : (prefixWord ++ tailWord_1587870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587870).length < 2 ^ (prefixWord ++ tailWord_1587870).sum := by decide
  have hdescent : baseEnd_1587870 < baseStart_1587870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587876 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_1587876 : Nat := 118140960795 + 1587876 * 2 ^ 59
def prefixEnd_1587876 : Nat := 4983230072969 + 3 ^ 40 * 1587876 * 2
def baseEnd_1587876 : Nat := 815343607738734661547497

theorem tailTrace_1587876 : CollatzResearch.WordTrace tailWord_1587876 prefixEnd_1587876 815343607738734661547497 := by
  unfold tailWord_1587876
  simp only [CollatzResearch.WordTrace]
  refine ⟨28957297797701957237779741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38609730396935942983706321 28957297797701957237779741)
  ·
    refine ⟨10858986674138233964167403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28957297797701957237779741 10858986674138233964167403)
    ·
      refine ⟨16288480011207350946251105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10858986674138233964167403 16288480011207350946251105)
      ·
        refine ⟨12216360008405513209688329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16288480011207350946251105 12216360008405513209688329)
        ·
          refine ⟨9162270006304134907266247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12216360008405513209688329 9162270006304134907266247)
          ·
            refine ⟨13743405009456202360899371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9162270006304134907266247 13743405009456202360899371)
            ·
              refine ⟨20615107514184303541349057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13743405009456202360899371 20615107514184303541349057)
              ·
                refine ⟨15461330635638227656011793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20615107514184303541349057 15461330635638227656011793)
                ·
                  refine ⟨11595997976728670742008845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15461330635638227656011793 11595997976728670742008845)
                  ·
                    refine ⟨4348499241273251528253317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11595997976728670742008845 4348499241273251528253317)
                    ·
                      refine ⟨815343607738734661547497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4348499241273251528253317 815343607738734661547497)
                      ·
                        rfl

theorem cell23_1587876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_1587876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587876 prefixEnd_1587876 := by exact prefixLift 1587876
  have htrace : WordTrace (prefixWord ++ tailWord_1587876) baseStart_1587876 baseEnd_1587876 := by
    simpa [prefixWord, tailWord_1587876, baseEnd_1587876] using wordTrace_append hprefix tailTrace_1587876
  have hstable : (prefixWord ++ tailWord_1587876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587876).length < 2 ^ (prefixWord ++ tailWord_1587876).sum := by decide
  have hdescent : baseEnd_1587876 < baseStart_1587876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587950 : List Nat := [4, 1, 2, 1, 1, 3, 3, 3, 5]
def baseStart_1587950 : Nat := 118140960795 + 1587950 * 2 ^ 59
def prefixEnd_1587950 : Nat := 4983230072969 + 3 ^ 40 * 1587950 * 2
def baseEnd_1587950 : Nat := 90597956145240819113573

theorem tailTrace_1587950 : CollatzResearch.WordTrace tailWord_1587950 prefixEnd_1587950 90597956145240819113573 := by
  unfold tailWord_1587950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7239661824641978139219163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38611529731423883409168869 7239661824641978139219163)
  ·
    refine ⟨10859492736962967208828745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7239661824641978139219163 10859492736962967208828745)
    ·
      refine ⟨8144619552722225406621559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10859492736962967208828745 8144619552722225406621559)
      ·
        refine ⟨12216929329083338109932339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8144619552722225406621559 12216929329083338109932339)
        ·
          refine ⟨18325393993625007164898509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12216929329083338109932339 18325393993625007164898509)
          ·
            refine ⟨6872022747609377686836941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18325393993625007164898509 6872022747609377686836941)
            ·
              refine ⟨2577008530353516632563853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6872022747609377686836941 2577008530353516632563853)
              ·
                refine ⟨966378198882568737211445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2577008530353516632563853 966378198882568737211445)
                ·
                  refine ⟨90597956145240819113573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 966378198882568737211445 90597956145240819113573)
                  ·
                    rfl

theorem cell23_1587950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_1587950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587950 prefixEnd_1587950 := by exact prefixLift 1587950
  have htrace : WordTrace (prefixWord ++ tailWord_1587950) baseStart_1587950 baseEnd_1587950 := by
    simpa [prefixWord, tailWord_1587950, baseEnd_1587950] using wordTrace_append hprefix tailTrace_1587950
  have hstable : (prefixWord ++ tailWord_1587950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587950).length < 2 ^ (prefixWord ++ tailWord_1587950).sum := by decide
  have hdescent : baseEnd_1587950 < baseStart_1587950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587983 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 1, 6, 2]
def baseStart_1587983 : Nat := 118140960795 + 1587983 * 2 ^ 59
def prefixEnd_1587983 : Nat := 4983230072969 + 3 ^ 40 * 1587983 * 2
def baseEnd_1587983 : Nat := 815398550168765742909505

theorem tailTrace_1587983 : CollatzResearch.WordTrace tailWord_1587983 prefixEnd_1587983 815398550168765742909505 := by
  unfold tailWord_1587983
  simp only [CollatzResearch.WordTrace]
  refine ⟨57918498206016271749704603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38612332137344181166469735 57918498206016271749704603)
  ·
    refine ⟨86877747309024407624556905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57918498206016271749704603 86877747309024407624556905)
    ·
      refine ⟨65158310481768305718417679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86877747309024407624556905 65158310481768305718417679)
      ·
        refine ⟨97737465722652458577626519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65158310481768305718417679 97737465722652458577626519)
        ·
          refine ⟨146606198583978687866439779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97737465722652458577626519 146606198583978687866439779)
          ·
            refine ⟨219909297875968031799659669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146606198583978687866439779 219909297875968031799659669)
            ·
              refine ⟨10308248337936001490609047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 219909297875968031799659669 10308248337936001490609047)
              ·
                refine ⟨15462372506904002235913571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10308248337936001490609047 15462372506904002235913571)
                ·
                  refine ⟨23193558760356003353870357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15462372506904002235913571 23193558760356003353870357)
                  ·
                    refine ⟨1087198066891687657212673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23193558760356003353870357 1087198066891687657212673)
                    ·
                      refine ⟨815398550168765742909505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1087198066891687657212673 815398550168765742909505)
                      ·
                        rfl

theorem cell23_1587983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 6, 2].length) (baseStart_1587983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587983 prefixEnd_1587983 := by exact prefixLift 1587983
  have htrace : WordTrace (prefixWord ++ tailWord_1587983) baseStart_1587983 baseEnd_1587983 := by
    simpa [prefixWord, tailWord_1587983, baseEnd_1587983] using wordTrace_append hprefix tailTrace_1587983
  have hstable : (prefixWord ++ tailWord_1587983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587983).length < 2 ^ (prefixWord ++ tailWord_1587983).sum := by decide
  have hdescent : baseEnd_1587983 < baseStart_1587983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1587997 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_1587997 : Nat := 118140960795 + 1587997 * 2 ^ 59
def prefixEnd_1587997 : Nat := 4983230072969 + 3 ^ 40 * 1587997 * 2
def baseEnd_1587997 : Nat := 271801912965976229378147

theorem tailTrace_1587997 : CollatzResearch.WordTrace tailWord_1587997 prefixEnd_1587997 271801912965976229378147 := by
  unfold tailWord_1587997
  simp only [CollatzResearch.WordTrace]
  refine ⟨57919008827965552140714245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38612672551977034760476163 57919008827965552140714245)
  ·
    refine ⟨10859814155243541026383921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57919008827965552140714245 10859814155243541026383921)
    ·
      refine ⟨8144860616432655769787941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10859814155243541026383921 8144860616432655769787941)
      ·
        refine ⟨1527161365581122956835239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8144860616432655769787941 1527161365581122956835239)
        ·
          refine ⟨2290742048371684435252859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527161365581122956835239 2290742048371684435252859)
          ·
            refine ⟨3436113072557526652879289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2290742048371684435252859 3436113072557526652879289)
            ·
              refine ⟨2577084804418144989659467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3436113072557526652879289 2577084804418144989659467)
              ·
                refine ⟨3865627206627217484489201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577084804418144989659467 3865627206627217484489201)
                ·
                  refine ⟨2899220404970413113366901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3865627206627217484489201 2899220404970413113366901)
                  ·
                    refine ⟨271801912965976229378147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2899220404970413113366901 271801912965976229378147)
                    ·
                      rfl

theorem cell23_1587997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_1587997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1587997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1587997 prefixEnd_1587997 := by exact prefixLift 1587997
  have htrace : WordTrace (prefixWord ++ tailWord_1587997) baseStart_1587997 baseEnd_1587997 := by
    simpa [prefixWord, tailWord_1587997, baseEnd_1587997] using wordTrace_append hprefix tailTrace_1587997
  have hstable : (prefixWord ++ tailWord_1587997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1587997).length < 2 ^ (prefixWord ++ tailWord_1587997).sum := by decide
  have hdescent : baseEnd_1587997 < baseStart_1587997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1587997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588000 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1588000 : Nat := 118140960795 + 1588000 * 2 ^ 59
def prefixEnd_1588000 : Nat := 4983230072969 + 3 ^ 40 * 1588000 * 2
def baseEnd_1588000 : Nat := 815407279339892176396927

theorem tailTrace_1588000 : CollatzResearch.WordTrace tailWord_1588000 prefixEnd_1588000 815407279339892176396927 := by
  unfold tailWord_1588000
  simp only [CollatzResearch.WordTrace]
  refine ⟨28959559123477341826536727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38612745497969789102048969 28959559123477341826536727)
  ·
    refine ⟨43439338685216012739805091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28959559123477341826536727 43439338685216012739805091)
    ·
      refine ⟨65159008027824019109707637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43439338685216012739805091 65159008027824019109707637)
      ·
        refine ⟨6108657002608501791535091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65159008027824019109707637 6108657002608501791535091)
        ·
          refine ⟨9162985503912752687302637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6108657002608501791535091 9162985503912752687302637)
          ·
            refine ⟨3436119563967282257738489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9162985503912752687302637 3436119563967282257738489)
            ·
              refine ⟨2577089672975461693303867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3436119563967282257738489 2577089672975461693303867)
              ·
                refine ⟨3865634509463192539955801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577089672975461693303867 3865634509463192539955801)
                ·
                  refine ⟨2899225882097394404966851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3865634509463192539955801 2899225882097394404966851)
                  ·
                    refine ⟨4348838823146091607450277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2899225882097394404966851 4348838823146091607450277)
                    ·
                      refine ⟨815407279339892176396927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4348838823146091607450277 815407279339892176396927)
                      ·
                        rfl

theorem cell23_1588000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1588000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588000 prefixEnd_1588000 := by exact prefixLift 1588000
  have htrace : WordTrace (prefixWord ++ tailWord_1588000) baseStart_1588000 baseEnd_1588000 := by
    simpa [prefixWord, tailWord_1588000, baseEnd_1588000] using wordTrace_append hprefix tailTrace_1588000
  have hstable : (prefixWord ++ tailWord_1588000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588000).length < 2 ^ (prefixWord ++ tailWord_1588000).sum := by decide
  have hdescent : baseEnd_1588000 < baseStart_1588000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588023 : List Nat := [1, 1, 3, 1, 2, 1, 6, 2, 6]
def baseStart_1588023 : Nat := 118140960795 + 1588023 * 2 ^ 59
def prefixEnd_1588023 : Nat := 4983230072969 + 3 ^ 40 * 1588023 * 2
def baseEnd_1588023 : Nat := 90602121043882842934369

theorem tailTrace_1588023 : CollatzResearch.WordTrace tailWord_1588023 prefixEnd_1588023 90602121043882842934369 := by
  unfold tailWord_1588023
  simp only [CollatzResearch.WordTrace]
  refine ⟨57919957125871358581160723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38613304750580905720773815 57919957125871358581160723)
  ·
    refine ⟨86879935688807037871741085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57919957125871358581160723 86879935688807037871741085)
    ·
      refine ⟨32579975883302639201902907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86879935688807037871741085 32579975883302639201902907)
      ·
        refine ⟨48869963824953958802854361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32579975883302639201902907 48869963824953958802854361)
        ·
          refine ⟨36652472868715469102140771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48869963824953958802854361 36652472868715469102140771)
          ·
            refine ⟨54978709303073203653211157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36652472868715469102140771 54978709303073203653211157)
            ·
              refine ⟨2577126998581556421244273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54978709303073203653211157 2577126998581556421244273)
              ·
                refine ⟨1932845248936167315933205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2577126998581556421244273 1932845248936167315933205)
                ·
                  refine ⟨90602121043882842934369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1932845248936167315933205 90602121043882842934369)
                  ·
                    rfl

theorem cell23_1588023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 6].length) (baseStart_1588023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588023 prefixEnd_1588023 := by exact prefixLift 1588023
  have htrace : WordTrace (prefixWord ++ tailWord_1588023) baseStart_1588023 baseEnd_1588023 := by
    simpa [prefixWord, tailWord_1588023, baseEnd_1588023] using wordTrace_append hprefix tailTrace_1588023
  have hstable : (prefixWord ++ tailWord_1588023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588023).length < 2 ^ (prefixWord ++ tailWord_1588023).sum := by decide
  have hdescent : baseEnd_1588023 < baseStart_1588023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588053 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 3, 5]
def baseStart_1588053 : Nat := 118140960795 + 1588053 * 2 ^ 59
def prefixEnd_1588053 : Nat := 4983230072969 + 3 ^ 40 * 1588053 * 2
def baseEnd_1588053 : Nat := 271811497938193489678061

theorem tailTrace_1588053 : CollatzResearch.WordTrace tailWord_1588053 prefixEnd_1588053 271811497938193489678061 := by
  unfold tailWord_1588053
  simp only [CollatzResearch.WordTrace]
  refine ⟨57921051315762673704752813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38614034210508449136501875 57921051315762673704752813)
  ·
    refine ⟨21720394243411002639282305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57921051315762673704752813 21720394243411002639282305)
    ·
      refine ⟨16290295682558251979461729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21720394243411002639282305 16290295682558251979461729)
      ·
        refine ⟨12217721761918688984596297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16290295682558251979461729 12217721761918688984596297)
        ·
          refine ⟨9163291321439016738447223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12217721761918688984596297 9163291321439016738447223)
          ·
            refine ⟨13744936982158525107670835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9163291321439016738447223 13744936982158525107670835)
            ·
              refine ⟨20617405473237787661506253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13744936982158525107670835 20617405473237787661506253)
              ·
                refine ⟨7731527052464170373064845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20617405473237787661506253 7731527052464170373064845)
                ·
                  refine ⟨2899322644674063889899317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7731527052464170373064845 2899322644674063889899317)
                  ·
                    refine ⟨271811497938193489678061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2899322644674063889899317 271811497938193489678061)
                    ·
                      rfl

theorem cell23_1588053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_1588053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588053 prefixEnd_1588053 := by exact prefixLift 1588053
  have htrace : WordTrace (prefixWord ++ tailWord_1588053) baseStart_1588053 baseEnd_1588053 := by
    simpa [prefixWord, tailWord_1588053, baseEnd_1588053] using wordTrace_append hprefix tailTrace_1588053
  have hstable : (prefixWord ++ tailWord_1588053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588053).length < 2 ^ (prefixWord ++ tailWord_1588053).sum := by decide
  have hdescent : baseEnd_1588053 < baseStart_1588053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588093 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_1588093 : Nat := 118140960795 + 1588093 * 2 ^ 59
def prefixEnd_1588093 : Nat := 4983230072969 + 3 ^ 40 * 1588093 * 2
def baseEnd_1588093 : Nat := 815455033040760312533999

theorem tailTrace_1588093 : CollatzResearch.WordTrace tailWord_1588093 prefixEnd_1588093 815455033040760312533999 := by
  unfold tailWord_1588093
  simp only [CollatzResearch.WordTrace]
  refine ⟨57922510235617760536208933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38615006823745173690805955 57922510235617760536208933)
  ·
    refine ⟨10860470669178330100539175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57922510235617760536208933 10860470669178330100539175)
    ·
      refine ⟨16290706003767495150808763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10860470669178330100539175 16290706003767495150808763)
      ·
        refine ⟨24436059005651242726213145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16290706003767495150808763 24436059005651242726213145)
        ·
          refine ⟨18327044254238432044659859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24436059005651242726213145 18327044254238432044659859)
          ·
            refine ⟨27490566381357648066989789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18327044254238432044659859 27490566381357648066989789)
            ·
              refine ⟨10308962393009118025121171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27490566381357648066989789 10308962393009118025121171)
              ·
                refine ⟨15463443589513677037681757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10308962393009118025121171 15463443589513677037681757)
                ·
                  refine ⟨5798791346067628889130659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15463443589513677037681757 5798791346067628889130659)
                  ·
                    refine ⟨8698187019101443333695989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5798791346067628889130659 8698187019101443333695989)
                    ·
                      refine ⟨815455033040760312533999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8698187019101443333695989 815455033040760312533999)
                      ·
                        rfl

theorem cell23_1588093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_1588093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588093 prefixEnd_1588093 := by exact prefixLift 1588093
  have htrace : WordTrace (prefixWord ++ tailWord_1588093) baseStart_1588093 baseEnd_1588093 := by
    simpa [prefixWord, tailWord_1588093, baseEnd_1588093] using wordTrace_append hprefix tailTrace_1588093
  have hstable : (prefixWord ++ tailWord_1588093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588093).length < 2 ^ (prefixWord ++ tailWord_1588093).sum := by decide
  have hdescent : baseEnd_1588093 < baseStart_1588093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588107 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 3, 2, 2]
def baseStart_1588107 : Nat := 118140960795 + 1588107 * 2 ^ 59
def prefixEnd_1588107 : Nat := 4983230072969 + 3 ^ 40 * 1588107 * 2
def baseEnd_1588107 : Nat := 815462221769923257758935

theorem tailTrace_1588107 : CollatzResearch.WordTrace tailWord_1588107 prefixEnd_1588107 815462221769923257758935 := by
  unfold tailWord_1588107
  simp only [CollatzResearch.WordTrace]
  refine ⟨57923020857567040927218575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38615347238378027284812383 57923020857567040927218575)
  ·
    refine ⟨86884531286350561390827863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57923020857567040927218575 86884531286350561390827863)
    ·
      refine ⟨130326796929525842086241795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86884531286350561390827863 130326796929525842086241795)
      ·
        refine ⟨195490195394288763129362693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130326796929525842086241795 195490195394288763129362693)
        ·
          refine ⟨36654411636429143086755505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195490195394288763129362693 36654411636429143086755505)
          ·
            refine ⟨27490808727321857315066629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36654411636429143086755505 27490808727321857315066629)
            ·
              refine ⟨5154526636372848246574993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27490808727321857315066629 5154526636372848246574993)
              ·
                refine ⟨3865894977279636184931245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5154526636372848246574993 3865894977279636184931245)
                ·
                  refine ⟨1449710616479863569349217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3865894977279636184931245 1449710616479863569349217)
                  ·
                    refine ⟨1087282962359897677011913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1449710616479863569349217 1087282962359897677011913)
                    ·
                      refine ⟨815462221769923257758935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1087282962359897677011913 815462221769923257758935)
                      ·
                        rfl

theorem cell23_1588107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 2, 2].length) (baseStart_1588107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588107 prefixEnd_1588107 := by exact prefixLift 1588107
  have htrace : WordTrace (prefixWord ++ tailWord_1588107) baseStart_1588107 baseEnd_1588107 := by
    simpa [prefixWord, tailWord_1588107, baseEnd_1588107] using wordTrace_append hprefix tailTrace_1588107
  have hstable : (prefixWord ++ tailWord_1588107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588107).length < 2 ^ (prefixWord ++ tailWord_1588107).sum := by decide
  have hdescent : baseEnd_1588107 < baseStart_1588107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588127 : List Nat := [1, 1, 2, 5, 2, 1, 2, 3, 1, 2, 3]
def baseStart_1588127 : Nat := 118140960795 + 1588127 * 2 ^ 59
def prefixEnd_1588127 : Nat := 4983230072969 + 3 ^ 40 * 1588127 * 2
def baseEnd_1588127 : Nat := 815472491383013179508843

theorem tailTrace_1588127 : CollatzResearch.WordTrace tailWord_1588127 prefixEnd_1588127 815472491383013179508843 := by
  unfold tailWord_1588127
  simp only [CollatzResearch.WordTrace]
  refine ⟨57923750317494584342946635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38615833544996389561964423 57923750317494584342946635)
  ·
    refine ⟨86885625476241876514419953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57923750317494584342946635 86885625476241876514419953)
    ·
      refine ⟨65164219107181407385814965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86885625476241876514419953 65164219107181407385814965)
      ·
        refine ⟨6109145541298256942420153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65164219107181407385814965 6109145541298256942420153)
        ·
          refine ⟨4581859155973692706815115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6109145541298256942420153 4581859155973692706815115)
          ·
            refine ⟨6872788733960539060222673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4581859155973692706815115 6872788733960539060222673)
            ·
              refine ⟨5154591550470404295167005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6872788733960539060222673 5154591550470404295167005)
              ·
                refine ⟨1932971831426401610687627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5154591550470404295167005 1932971831426401610687627)
                ·
                  refine ⟨2899457747139602416031441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1932971831426401610687627 2899457747139602416031441)
                  ·
                    refine ⟨2174593310354701812023581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2899457747139602416031441 2174593310354701812023581)
                    ·
                      refine ⟨815472491383013179508843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2174593310354701812023581 815472491383013179508843)
                      ·
                        rfl

theorem cell23_1588127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_1588127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588127 prefixEnd_1588127 := by exact prefixLift 1588127
  have htrace : WordTrace (prefixWord ++ tailWord_1588127) baseStart_1588127 baseEnd_1588127 := by
    simpa [prefixWord, tailWord_1588127, baseEnd_1588127] using wordTrace_append hprefix tailTrace_1588127
  have hstable : (prefixWord ++ tailWord_1588127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588127).length < 2 ^ (prefixWord ++ tailWord_1588127).sum := by decide
  have hdescent : baseEnd_1588127 < baseStart_1588127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588130 : List Nat := [3, 3, 1, 2, 2, 3, 9]
def baseStart_1588130 : Nat := 118140960795 + 1588130 * 2 ^ 59
def prefixEnd_1588130 : Nat := 4983230072969 + 3 ^ 40 * 1588130 * 2
def baseEnd_1588130 : Nat := 10067580639814526762609

theorem tailTrace_1588130 : CollatzResearch.WordTrace tailWord_1588130 prefixEnd_1588130 10067580639814526762609 := by
  unfold tailWord_1588130
  simp only [CollatzResearch.WordTrace]
  refine ⟨14480964934120928963826461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38615906490989143903537229 14480964934120928963826461)
  ·
    refine ⟨5430361850295348361434923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14480964934120928963826461 5430361850295348361434923)
    ·
      refine ⟨8145542775443022542152385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5430361850295348361434923 8145542775443022542152385)
      ·
        refine ⟨6109157081582266906614289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8145542775443022542152385 6109157081582266906614289)
        ·
          refine ⟨4581867811186700179960717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6109157081582266906614289 4581867811186700179960717)
          ·
            refine ⟨1718200429195012567485269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4581867811186700179960717 1718200429195012567485269)
            ·
              refine ⟨10067580639814526762609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1718200429195012567485269 10067580639814526762609)
              ·
                rfl

theorem cell23_1588130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 9].length) (baseStart_1588130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588130 prefixEnd_1588130 := by exact prefixLift 1588130
  have htrace : WordTrace (prefixWord ++ tailWord_1588130) baseStart_1588130 baseEnd_1588130 := by
    simpa [prefixWord, tailWord_1588130, baseEnd_1588130] using wordTrace_append hprefix tailTrace_1588130
  have hstable : (prefixWord ++ tailWord_1588130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588130).length < 2 ^ (prefixWord ++ tailWord_1588130).sum := by decide
  have hdescent : baseEnd_1588130 < baseStart_1588130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588163 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 4]
def baseStart_1588163 : Nat := 118140960795 + 1588163 * 2 ^ 59
def prefixEnd_1588163 : Nat := 4983230072969 + 3 ^ 40 * 1588163 * 2
def baseEnd_1588163 : Nat := 815490976686575038658677

theorem tailTrace_1588163 : CollatzResearch.WordTrace tailWord_1588163 prefixEnd_1588163 815490976686575038658677 := by
  unfold tailWord_1588163
  simp only [CollatzResearch.WordTrace]
  refine ⟨57925063345364162491257143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38616708896909441660838095 57925063345364162491257143)
  ·
    refine ⟨86887595018046243736885715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57925063345364162491257143 86887595018046243736885715)
    ·
      refine ⟨130331392527069365605328573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86887595018046243736885715 130331392527069365605328573)
      ·
        refine ⟨48874272197651012101998215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130331392527069365605328573 48874272197651012101998215)
        ·
          refine ⟨73311408296476518152997323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48874272197651012101998215 73311408296476518152997323)
          ·
            refine ⟨109967112444714777229495985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73311408296476518152997323 109967112444714777229495985)
            ·
              refine ⟨82475334333536082922121989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109967112444714777229495985 82475334333536082922121989)
              ·
                refine ⟨15464125187538015547897873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82475334333536082922121989 15464125187538015547897873)
                ·
                  refine ⟨11598093890653511660923405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15464125187538015547897873 11598093890653511660923405)
                  ·
                    refine ⟨4349285208995066872846277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11598093890653511660923405 4349285208995066872846277)
                    ·
                      refine ⟨815490976686575038658677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4349285208995066872846277 815490976686575038658677)
                      ·
                        rfl

theorem cell23_1588163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_1588163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588163 prefixEnd_1588163 := by exact prefixLift 1588163
  have htrace : WordTrace (prefixWord ++ tailWord_1588163) baseStart_1588163 baseEnd_1588163 := by
    simpa [prefixWord, tailWord_1588163, baseEnd_1588163] using wordTrace_append hprefix tailTrace_1588163
  have hstable : (prefixWord ++ tailWord_1588163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588163).length < 2 ^ (prefixWord ++ tailWord_1588163).sum := by decide
  have hdescent : baseEnd_1588163 < baseStart_1588163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588183 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_1588183 : Nat := 118140960795 + 1588183 * 2 ^ 59
def prefixEnd_1588183 : Nat := 4983230072969 + 3 ^ 40 * 1588183 * 2
def baseEnd_1588183 : Nat := 815501246299664960408585

theorem tailTrace_1588183 : CollatzResearch.WordTrace tailWord_1588183 prefixEnd_1588183 815501246299664960408585 := by
  unfold tailWord_1588183
  simp only [CollatzResearch.WordTrace]
  refine ⟨57925792805291705906985203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38617195203527803937990135 57925792805291705906985203)
  ·
    refine ⟨86888689207937558860477805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57925792805291705906985203 86888689207937558860477805)
    ·
      refine ⟨32583258452976584572679177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86888689207937558860477805 32583258452976584572679177)
      ·
        refine ⟨24437443839732438429509383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32583258452976584572679177 24437443839732438429509383)
        ·
          refine ⟨36656165759598657644264075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24437443839732438429509383 36656165759598657644264075)
          ·
            refine ⟨54984248639397986466396113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36656165759598657644264075 54984248639397986466396113)
            ·
              refine ⟨41238186479548489849797085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54984248639397986466396113 41238186479548489849797085)
              ·
                refine ⟨15464319929830683693673907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41238186479548489849797085 15464319929830683693673907)
                ·
                  refine ⟨23196479894746025540510861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15464319929830683693673907 23196479894746025540510861)
                  ·
                    refine ⟨8698679960529759577691573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23196479894746025540510861 8698679960529759577691573)
                    ·
                      refine ⟨815501246299664960408585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8698679960529759577691573 815501246299664960408585)
                      ·
                        rfl

theorem cell23_1588183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_1588183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588183 prefixEnd_1588183 := by exact prefixLift 1588183
  have htrace : WordTrace (prefixWord ++ tailWord_1588183) baseStart_1588183 baseEnd_1588183 := by
    simpa [prefixWord, tailWord_1588183, baseEnd_1588183] using wordTrace_append hprefix tailTrace_1588183
  have hstable : (prefixWord ++ tailWord_1588183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588183).length < 2 ^ (prefixWord ++ tailWord_1588183).sum := by decide
  have hdescent : baseEnd_1588183 < baseStart_1588183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588193 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_1588193 : Nat := 118140960795 + 1588193 * 2 ^ 59
def prefixEnd_1588193 : Nat := 4983230072969 + 3 ^ 40 * 1588193 * 2
def baseEnd_1588193 : Nat := 815506381106209921283539

theorem tailTrace_1588193 : CollatzResearch.WordTrace tailWord_1588193 prefixEnd_1588193 815506381106209921283539 := by
  unfold tailWord_1588193
  simp only [CollatzResearch.WordTrace]
  refine ⟨57926157535255477614849233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38617438356836985076566155 57926157535255477614849233)
  ·
    refine ⟨43444618151441608211136925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57926157535255477614849233 43444618151441608211136925)
    ·
      refine ⟨16291731806790603079176347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43444618151441608211136925 16291731806790603079176347)
      ·
        refine ⟨24437597710185904618764521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16291731806790603079176347 24437597710185904618764521)
        ·
          refine ⟨18328198282639428464073391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24437597710185904618764521 18328198282639428464073391)
          ·
            refine ⟨27492297423959142696110087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18328198282639428464073391 27492297423959142696110087)
            ·
              refine ⟨41238446135938714044165131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27492297423959142696110087 41238446135938714044165131)
              ·
                refine ⟨61857669203908071066247697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41238446135938714044165131 61857669203908071066247697)
                ·
                  refine ⟨46393251902931053299685773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61857669203908071066247697 46393251902931053299685773)
                  ·
                    refine ⟨17397469463599144987382165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46393251902931053299685773 17397469463599144987382165)
                    ·
                      refine ⟨815506381106209921283539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17397469463599144987382165 815506381106209921283539)
                      ·
                        rfl

theorem cell23_1588193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_1588193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588193 prefixEnd_1588193 := by exact prefixLift 1588193
  have htrace : WordTrace (prefixWord ++ tailWord_1588193) baseStart_1588193 baseEnd_1588193 := by
    simpa [prefixWord, tailWord_1588193, baseEnd_1588193] using wordTrace_append hprefix tailTrace_1588193
  have hstable : (prefixWord ++ tailWord_1588193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588193).length < 2 ^ (prefixWord ++ tailWord_1588193).sum := by decide
  have hdescent : baseEnd_1588193 < baseStart_1588193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588200 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_1588200 : Nat := 118140960795 + 1588200 * 2 ^ 59
def prefixEnd_1588200 : Nat := 4983230072969 + 3 ^ 40 * 1588200 * 2
def baseEnd_1588200 : Nat := 815509975470791393896007

theorem tailTrace_1588200 : CollatzResearch.WordTrace tailWord_1588200 prefixEnd_1588200 815509975470791393896007 := by
  unfold tailWord_1588200
  simp only [CollatzResearch.WordTrace]
  refine ⟨28963206423115058905177027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38617608564153411873569369 28963206423115058905177027)
  ·
    refine ⟨43444809634672588357765541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28963206423115058905177027 43444809634672588357765541)
    ·
      refine ⟨8145901806501110317081039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43444809634672588357765541 8145901806501110317081039)
      ·
        refine ⟨12218852709751665475621559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8145901806501110317081039 12218852709751665475621559)
        ·
          refine ⟨18328279064627498213432339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12218852709751665475621559 18328279064627498213432339)
          ·
            refine ⟨27492418596941247320148509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18328279064627498213432339 27492418596941247320148509)
            ·
              refine ⟨10309656973852967745055691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27492418596941247320148509 10309656973852967745055691)
              ·
                refine ⟨15464485460779451617583537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10309656973852967745055691 15464485460779451617583537)
                ·
                  refine ⟨11598364095584588713187653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15464485460779451617583537 11598364095584588713187653)
                  ·
                    refine ⟨2174693267922110383722685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11598364095584588713187653 2174693267922110383722685)
                    ·
                      refine ⟨815509975470791393896007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2174693267922110383722685 815509975470791393896007)
                      ·
                        rfl

theorem cell23_1588200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_1588200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588200 prefixEnd_1588200 := by exact prefixLift 1588200
  have htrace : WordTrace (prefixWord ++ tailWord_1588200) baseStart_1588200 baseEnd_1588200 := by
    simpa [prefixWord, tailWord_1588200, baseEnd_1588200] using wordTrace_append hprefix tailTrace_1588200
  have hstable : (prefixWord ++ tailWord_1588200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588200).length < 2 ^ (prefixWord ++ tailWord_1588200).sum := by decide
  have hdescent : baseEnd_1588200 < baseStart_1588200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588214 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_1588214 : Nat := 118140960795 + 1588214 * 2 ^ 59
def prefixEnd_1588214 : Nat := 4983230072969 + 3 ^ 40 * 1588214 * 2
def baseEnd_1588214 : Nat := 815517164199954339120943

theorem tailTrace_1588214 : CollatzResearch.WordTrace tailWord_1588214 prefixEnd_1588214 815517164199954339120943 := by
  unfold tailWord_1588214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3620432716761212387585231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38617948978786265467575797 3620432716761212387585231)
  ·
    refine ⟨5430649075141818581377847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3620432716761212387585231 5430649075141818581377847)
    ·
      refine ⟨8145973612712727872066771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5430649075141818581377847 8145973612712727872066771)
      ·
        refine ⟨12218960419069091808100157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8145973612712727872066771 12218960419069091808100157)
        ·
          refine ⟨4582110157150909428037559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12218960419069091808100157 4582110157150909428037559)
          ·
            refine ⟨6873165235726364142056339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4582110157150909428037559 6873165235726364142056339)
            ·
              refine ⟨10309747853589546213084509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6873165235726364142056339 10309747853589546213084509)
              ·
                refine ⟨3866155445096079829906691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10309747853589546213084509 3866155445096079829906691)
                ·
                  refine ⟨5799233167644119744860037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3866155445096079829906691 5799233167644119744860037)
                  ·
                    refine ⟨1087356218933272452161257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5799233167644119744860037 1087356218933272452161257)
                    ·
                      refine ⟨815517164199954339120943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1087356218933272452161257 815517164199954339120943)
                      ·
                        rfl

theorem cell23_1588214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_1588214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588214 prefixEnd_1588214 := by exact prefixLift 1588214
  have htrace : WordTrace (prefixWord ++ tailWord_1588214) baseStart_1588214 baseEnd_1588214 := by
    simpa [prefixWord, tailWord_1588214, baseEnd_1588214] using wordTrace_append hprefix tailTrace_1588214
  have hstable : (prefixWord ++ tailWord_1588214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588214).length < 2 ^ (prefixWord ++ tailWord_1588214).sum := by decide
  have hdescent : baseEnd_1588214 < baseStart_1588214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588220 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 7]
def baseStart_1588220 : Nat := 118140960795 + 1588220 * 2 ^ 59
def prefixEnd_1588220 : Nat := 4983230072969 + 3 ^ 40 * 1588220 * 2
def baseEnd_1588220 : Nat := 90613360564875701738435

theorem tailTrace_1588220 : CollatzResearch.WordTrace tailWord_1588220 prefixEnd_1588220 90613360564875701738435 := by
  unfold tailWord_1588220
  simp only [CollatzResearch.WordTrace]
  refine ⟨28963571153078830613041057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38618094870771774150721409 28963571153078830613041057)
  ·
    refine ⟨21722678364809122959780793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28963571153078830613041057 21722678364809122959780793)
    ·
      refine ⟨16292008773606842219835595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21722678364809122959780793 16292008773606842219835595)
      ·
        refine ⟨24438013160410263329753393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16292008773606842219835595 24438013160410263329753393)
        ·
          refine ⟨18328509870307697497315045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24438013160410263329753393 18328509870307697497315045)
          ·
            refine ⟨3436595600682693280746571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18328509870307697497315045 3436595600682693280746571)
            ·
              refine ⟨5154893401024039921119857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3436595600682693280746571 5154893401024039921119857)
              ·
                refine ⟨3866170050768029940839893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5154893401024039921119857 3866170050768029940839893)
                ·
                  refine ⟨90613360564875701738435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3866170050768029940839893 90613360564875701738435)
                  ·
                    rfl

theorem cell23_1588220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_1588220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588220 prefixEnd_1588220 := by exact prefixLift 1588220
  have htrace : WordTrace (prefixWord ++ tailWord_1588220) baseStart_1588220 baseEnd_1588220 := by
    simpa [prefixWord, tailWord_1588220, baseEnd_1588220] using wordTrace_append hprefix tailTrace_1588220
  have hstable : (prefixWord ++ tailWord_1588220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588220).length < 2 ^ (prefixWord ++ tailWord_1588220).sum := by decide
  have hdescent : baseEnd_1588220 < baseStart_1588220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588242 : List Nat := [3, 2, 5, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_1588242 : Nat := 118140960795 + 1588242 * 2 ^ 59
def prefixEnd_1588242 : Nat := 4983230072969 + 3 ^ 40 * 1588242 * 2
def baseEnd_1588242 : Nat := 815531541658280229570815

theorem tailTrace_1588242 : CollatzResearch.WordTrace tailWord_1588242 prefixEnd_1588242 815531541658280229570815 := by
  unfold tailWord_1588242
  simp only [CollatzResearch.WordTrace]
  refine ⟨14481986178019489745845745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38618629808051972655588653 14481986178019489745845745)
  ·
    refine ⟨10861489633514617309384309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14481986178019489745845745 10861489633514617309384309)
    ·
      refine ⟨1018264653141995372754779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10861489633514617309384309 1018264653141995372754779)
      ·
        refine ⟨1527396979712993059132169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1018264653141995372754779 1527396979712993059132169)
        ·
          refine ⟨1145547734784744794349127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1527396979712993059132169 1145547734784744794349127)
          ·
            refine ⟨1718321602177117191523691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145547734784744794349127 1718321602177117191523691)
            ·
              refine ⟨2577482403265675787285537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718321602177117191523691 2577482403265675787285537)
              ·
                refine ⟨1933111802449256840464153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2577482403265675787285537 1933111802449256840464153)
                ·
                  refine ⟨1449833851836942630348115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1933111802449256840464153 1449833851836942630348115)
                  ·
                    refine ⟨2174750777755413945522173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1449833851836942630348115 2174750777755413945522173)
                    ·
                      refine ⟨815531541658280229570815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2174750777755413945522173 815531541658280229570815)
                      ·
                        rfl

theorem cell23_1588242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_1588242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588242 prefixEnd_1588242 := by exact prefixLift 1588242
  have htrace : WordTrace (prefixWord ++ tailWord_1588242) baseStart_1588242 baseEnd_1588242 := by
    simpa [prefixWord, tailWord_1588242, baseEnd_1588242] using wordTrace_append hprefix tailTrace_1588242
  have hstable : (prefixWord ++ tailWord_1588242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588242).length < 2 ^ (prefixWord ++ tailWord_1588242).sum := by decide
  have hdescent : baseEnd_1588242 < baseStart_1588242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588247 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1588247 : Nat := 118140960795 + 1588247 * 2 ^ 59
def prefixEnd_1588247 : Nat := 4983230072969 + 3 ^ 40 * 1588247 * 2
def baseEnd_1588247 : Nat := 815534109061552710008291

theorem tailTrace_1588247 : CollatzResearch.WordTrace tailWord_1588247 prefixEnd_1588247 815534109061552710008291 := by
  unfold tailWord_1588247
  simp only [CollatzResearch.WordTrace]
  refine ⟨57928127077059844837314995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38618751384706563224876663 57928127077059844837314995)
  ·
    refine ⟨86892190615589767255972493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57928127077059844837314995 86892190615589767255972493)
    ·
      refine ⟨32584571480846162720989685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86892190615589767255972493 32584571480846162720989685)
      ·
        refine ⟨3054803576329327755092783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32584571480846162720989685 3054803576329327755092783)
        ·
          refine ⟨4582205364493991632639175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3054803576329327755092783 4582205364493991632639175)
          ·
            refine ⟨6873308046740987448958763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4582205364493991632639175 6873308046740987448958763)
            ·
              refine ⟨10309962070111481173438145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6873308046740987448958763 10309962070111481173438145)
              ·
                refine ⟨7732471552583610880078609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10309962070111481173438145 7732471552583610880078609)
                ·
                  refine ⟨5799353664437708160058957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7732471552583610880078609 5799353664437708160058957)
                  ·
                    refine ⟨2174757624164140560022109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5799353664437708160058957 2174757624164140560022109)
                    ·
                      refine ⟨815534109061552710008291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2174757624164140560022109 815534109061552710008291)
                      ·
                        rfl

theorem cell23_1588247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1588247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588247 prefixEnd_1588247 := by exact prefixLift 1588247
  have htrace : WordTrace (prefixWord ++ tailWord_1588247) baseStart_1588247 baseEnd_1588247 := by
    simpa [prefixWord, tailWord_1588247, baseEnd_1588247] using wordTrace_append hprefix tailTrace_1588247
  have hstable : (prefixWord ++ tailWord_1588247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588247).length < 2 ^ (prefixWord ++ tailWord_1588247).sum := by decide
  have hdescent : baseEnd_1588247 < baseStart_1588247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588250 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 4, 5]
def baseStart_1588250 : Nat := 118140960795 + 1588250 * 2 ^ 59
def prefixEnd_1588250 : Nat := 4983230072969 + 3 ^ 40 * 1588250 * 2
def baseEnd_1588250 : Nat := 271845216501172066090259

theorem tailTrace_1588250 : CollatzResearch.WordTrace tailWord_1588250 prefixEnd_1588250 271845216501172066090259 := by
  unfold tailWord_1588250
  simp only [CollatzResearch.WordTrace]
  refine ⟨14482059124012244087418551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38618824330699317566449469 14482059124012244087418551)
  ·
    refine ⟨21723088686018366131127827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14482059124012244087418551 21723088686018366131127827)
    ·
      refine ⟨32584633029027549196691741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21723088686018366131127827 32584633029027549196691741)
      ·
        refine ⟨12219237385885330948759403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32584633029027549196691741 12219237385885330948759403)
        ·
          refine ⟨18328856078827996423139105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12219237385885330948759403 18328856078827996423139105)
          ·
            refine ⟨13746642059120997317354329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18328856078827996423139105 13746642059120997317354329)
            ·
              refine ⟨10309981544340747988015747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13746642059120997317354329 10309981544340747988015747)
              ·
                refine ⟨15464972316511121982023621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10309981544340747988015747 15464972316511121982023621)
                ·
                  refine ⟨2899682309345835371629429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15464972316511121982023621 2899682309345835371629429)
                  ·
                    refine ⟨271845216501172066090259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2899682309345835371629429 271845216501172066090259)
                    ·
                      rfl

theorem cell23_1588250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_1588250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588250 prefixEnd_1588250 := by exact prefixLift 1588250
  have htrace : WordTrace (prefixWord ++ tailWord_1588250) baseStart_1588250 baseEnd_1588250 := by
    simpa [prefixWord, tailWord_1588250, baseEnd_1588250] using wordTrace_append hprefix tailTrace_1588250
  have hstable : (prefixWord ++ tailWord_1588250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588250).length < 2 ^ (prefixWord ++ tailWord_1588250).sum := by decide
  have hdescent : baseEnd_1588250 < baseStart_1588250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588327 : List Nat := [1, 1, 5, 1, 1, 4, 1, 3, 6]
def baseStart_1588327 : Nat := 118140960795 + 1588327 * 2 ^ 59
def prefixEnd_1588327 : Nat := 4983230072969 + 3 ^ 40 * 1588327 * 2
def baseEnd_1588327 : Nat := 90619465279323599667547

theorem tailTrace_1588327 : CollatzResearch.WordTrace tailWord_1588327 prefixEnd_1588327 90619465279323599667547 := by
  unfold tailWord_1588327
  simp only [CollatzResearch.WordTrace]
  refine ⟨57931044916770018500227235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38620696611180012333484823 57931044916770018500227235)
  ·
    refine ⟨86896567375155027750340853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57931044916770018500227235 86896567375155027750340853)
    ·
      refine ⟨8146553191420783851594455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86896567375155027750340853 8146553191420783851594455)
      ·
        refine ⟨12219829787131175777391683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8146553191420783851594455 12219829787131175777391683)
        ·
          refine ⟨18329744680696763666087525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12219829787131175777391683 18329744680696763666087525)
          ·
            refine ⟨3436827127630643187391411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18329744680696763666087525 3436827127630643187391411)
            ·
              refine ⟨5155240691445964781087117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3436827127630643187391411 5155240691445964781087117)
              ·
                refine ⟨1933215259292236792907669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5155240691445964781087117 1933215259292236792907669)
                ·
                  refine ⟨90619465279323599667547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1933215259292236792907669 90619465279323599667547)
                  ·
                    rfl

theorem cell23_1588327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 6].length) (baseStart_1588327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588327 prefixEnd_1588327 := by exact prefixLift 1588327
  have htrace : WordTrace (prefixWord ++ tailWord_1588327) baseStart_1588327 baseEnd_1588327 := by
    simpa [prefixWord, tailWord_1588327, baseEnd_1588327] using wordTrace_append hprefix tailTrace_1588327
  have hstable : (prefixWord ++ tailWord_1588327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588327).length < 2 ^ (prefixWord ++ tailWord_1588327).sum := by decide
  have hdescent : baseEnd_1588327 < baseStart_1588327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588347 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 1, 5, 2]
def baseStart_1588347 : Nat := 118140960795 + 1588347 * 2 ^ 59
def prefixEnd_1588347 : Nat := 4983230072969 + 3 ^ 40 * 1588347 * 2
def baseEnd_1588347 : Nat := 815585457127002318757831

theorem tailTrace_1588347 : CollatzResearch.WordTrace tailWord_1588347 prefixEnd_1588347 815585457127002318757831 := by
  unfold tailWord_1588347
  simp only [CollatzResearch.WordTrace]
  refine ⟨57931774376697561915955295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38621182917798374610636863 57931774376697561915955295)
  ·
    refine ⟨86897661565046342873932943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57931774376697561915955295 86897661565046342873932943)
    ·
      refine ⟨130346492347569514310899415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86897661565046342873932943 130346492347569514310899415)
      ·
        refine ⟨195519738521354271466349123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130346492347569514310899415 195519738521354271466349123)
        ·
          refine ⟨293279607782031407199523685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195519738521354271466349123 293279607782031407199523685)
          ·
            refine ⟨54989926459130888849910691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 293279607782031407199523685 54989926459130888849910691)
            ·
              refine ⟨82484889688696333274866037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54989926459130888849910691 82484889688696333274866037)
              ·
                refine ⟨7732958408315281244518691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82484889688696333274866037 7732958408315281244518691)
                ·
                  refine ⟨11599437612472921866778037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7732958408315281244518691 11599437612472921866778037)
                  ·
                    refine ⟨1087447276169336425010441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11599437612472921866778037 1087447276169336425010441)
                    ·
                      refine ⟨815585457127002318757831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1087447276169336425010441 815585457127002318757831)
                      ·
                        rfl

theorem cell23_1588347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 5, 2].length) (baseStart_1588347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588347 prefixEnd_1588347 := by exact prefixLift 1588347
  have htrace : WordTrace (prefixWord ++ tailWord_1588347) baseStart_1588347 baseEnd_1588347 := by
    simpa [prefixWord, tailWord_1588347, baseEnd_1588347] using wordTrace_append hprefix tailTrace_1588347
  have hstable : (prefixWord ++ tailWord_1588347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588347).length < 2 ^ (prefixWord ++ tailWord_1588347).sum := by decide
  have hdescent : baseEnd_1588347 < baseStart_1588347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588377 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 4, 6, 2]
def baseStart_1588377 : Nat := 118140960795 + 1588377 * 2 ^ 59
def prefixEnd_1588377 : Nat := 4983230072969 + 3 ^ 40 * 1588377 * 2
def baseEnd_1588377 : Nat := 815600861546637201382693

theorem tailTrace_1588377 : CollatzResearch.WordTrace tailWord_1588377 prefixEnd_1588377 815600861546637201382693 := by
  unfold tailWord_1588377
  simp only [CollatzResearch.WordTrace]
  refine ⟨57932868566588877039547385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38621912377725918026364923 57932868566588877039547385)
  ·
    refine ⟨43449651424941657779660539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57932868566588877039547385 43449651424941657779660539)
    ·
      refine ⟨65174477137412486669490809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43449651424941657779660539 65174477137412486669490809)
      ·
        refine ⟨48880857853059365002118107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65174477137412486669490809 48880857853059365002118107)
        ·
          refine ⟨73321286779589047503177161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48880857853059365002118107 73321286779589047503177161)
          ·
            refine ⟨54990965084691785627382871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73321286779589047503177161 54990965084691785627382871)
            ·
              refine ⟨82486447627037678441074307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54990965084691785627382871 82486447627037678441074307)
              ·
                refine ⟨123729671440556517661611461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82486447627037678441074307 123729671440556517661611461)
                ·
                  refine ⟨23199313395104347061552149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123729671440556517661611461 23199313395104347061552149)
                  ·
                    refine ⟨1087467815395516268510257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23199313395104347061552149 1087467815395516268510257)
                    ·
                      refine ⟨815600861546637201382693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1087467815395516268510257 815600861546637201382693)
                      ·
                        rfl

theorem cell23_1588377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 6, 2].length) (baseStart_1588377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588377 prefixEnd_1588377 := by exact prefixLift 1588377
  have htrace : WordTrace (prefixWord ++ tailWord_1588377) baseStart_1588377 baseEnd_1588377 := by
    simpa [prefixWord, tailWord_1588377, baseEnd_1588377] using wordTrace_append hprefix tailTrace_1588377
  have hstable : (prefixWord ++ tailWord_1588377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588377).length < 2 ^ (prefixWord ++ tailWord_1588377).sum := by decide
  have hdescent : baseEnd_1588377 < baseStart_1588377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588407 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 4]
def baseStart_1588407 : Nat := 118140960795 + 1588407 * 2 ^ 59
def prefixEnd_1588407 : Nat := 4983230072969 + 3 ^ 40 * 1588407 * 2
def baseEnd_1588407 : Nat := 815616265966272084007555

theorem tailTrace_1588407 : CollatzResearch.WordTrace tailWord_1588407 prefixEnd_1588407 815616265966272084007555 := by
  unfold tailWord_1588407
  simp only [CollatzResearch.WordTrace]
  refine ⟨57933962756480192163139475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38622641837653461442092983 57933962756480192163139475)
  ·
    refine ⟨86900944134720288244709213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57933962756480192163139475 86900944134720288244709213)
    ·
      refine ⟨32587854050520108091765955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86900944134720288244709213 32587854050520108091765955)
      ·
        refine ⟨48881781075780162137648933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32587854050520108091765955 48881781075780162137648933)
        ·
          refine ⟨9165333951708780400809175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48881781075780162137648933 9165333951708780400809175)
          ·
            refine ⟨13748000927563170601213763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9165333951708780400809175 13748000927563170601213763)
            ·
              refine ⟨20622001391344755901820645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13748000927563170601213763 20622001391344755901820645)
              ·
                refine ⟨3866625260877141731591371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20622001391344755901820645 3866625260877141731591371)
                ·
                  refine ⟨5799937891315712597387057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3866625260877141731591371 5799937891315712597387057)
                  ·
                    refine ⟨4349953418486784448040293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5799937891315712597387057 4349953418486784448040293)
                    ·
                      refine ⟨815616265966272084007555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4349953418486784448040293 815616265966272084007555)
                      ·
                        rfl

theorem cell23_1588407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_1588407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588407 prefixEnd_1588407 := by exact prefixLift 1588407
  have htrace : WordTrace (prefixWord ++ tailWord_1588407) baseStart_1588407 baseEnd_1588407 := by
    simpa [prefixWord, tailWord_1588407, baseEnd_1588407] using wordTrace_append hprefix tailTrace_1588407
  have hstable : (prefixWord ++ tailWord_1588407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588407).length < 2 ^ (prefixWord ++ tailWord_1588407).sum := by decide
  have hdescent : baseEnd_1588407 < baseStart_1588407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588422 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1588422 : Nat := 118140960795 + 1588422 * 2 ^ 59
def prefixEnd_1588422 : Nat := 4983230072969 + 3 ^ 40 * 1588422 * 2
def baseEnd_1588422 : Nat := 815623968176089525319987

theorem tailTrace_1588422 : CollatzResearch.WordTrace tailWord_1588422 prefixEnd_1588422 815623968176089525319987 := by
  unfold tailWord_1588422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1810453432857057803904235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38623006567617233149957013 1810453432857057803904235)
  ·
    refine ⟨2715680149285586705856353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1810453432857057803904235 2715680149285586705856353)
    ·
      refine ⟨2036760111964190029392265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2715680149285586705856353 2036760111964190029392265)
      ·
        refine ⟨1527570083973142522044199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2036760111964190029392265 1527570083973142522044199)
        ·
          refine ⟨2291355125959713783066299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527570083973142522044199 2291355125959713783066299)
          ·
            refine ⟨3437032688939570674599449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291355125959713783066299 3437032688939570674599449)
            ·
              refine ⟨2577774516704678005949587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3437032688939570674599449 2577774516704678005949587)
              ·
                refine ⟨3866661775057017008924381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577774516704678005949587 3866661775057017008924381)
                ·
                  refine ⟨1449998165646381378346643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3866661775057017008924381 1449998165646381378346643)
                  ·
                    refine ⟨2174997248469572067519965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1449998165646381378346643 2174997248469572067519965)
                    ·
                      refine ⟨815623968176089525319987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2174997248469572067519965 815623968176089525319987)
                      ·
                        rfl

theorem cell23_1588422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1588422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588422 prefixEnd_1588422 := by exact prefixLift 1588422
  have htrace : WordTrace (prefixWord ++ tailWord_1588422) baseStart_1588422 baseEnd_1588422 := by
    simpa [prefixWord, tailWord_1588422, baseEnd_1588422] using wordTrace_append hprefix tailTrace_1588422
  have hstable : (prefixWord ++ tailWord_1588422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588422).length < 2 ^ (prefixWord ++ tailWord_1588422).sum := by decide
  have hdescent : baseEnd_1588422 < baseStart_1588422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588438 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_1588438 : Nat := 118140960795 + 1588438 * 2 ^ 59
def prefixEnd_1588438 : Nat := 4983230072969 + 3 ^ 40 * 1588438 * 2
def baseEnd_1588438 : Nat := 271877394622187154239971

theorem tailTrace_1588438 : CollatzResearch.WordTrace tailWord_1588438 prefixEnd_1588438 271877394622187154239971 := by
  unfold tailWord_1588438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3620943338710492778594873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38623395612911922971678645 3620943338710492778594873)
  ·
    refine ⟨2715707504032869583946155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3620943338710492778594873 2715707504032869583946155)
    ·
      refine ⟨4073561256049304375919233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2715707504032869583946155 4073561256049304375919233)
      ·
        refine ⟨3055170942036978281939425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4073561256049304375919233 3055170942036978281939425)
        ·
          refine ⟨2291378206527733711454569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3055170942036978281939425 2291378206527733711454569)
          ·
            refine ⟨1718533654895800283590927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2291378206527733711454569 1718533654895800283590927)
            ·
              refine ⟨2577800482343700425386391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718533654895800283590927 2577800482343700425386391)
              ·
                refine ⟨3866700723515550638079587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577800482343700425386391 3866700723515550638079587)
                ·
                  refine ⟨5800051085273325957119381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3866700723515550638079587 5800051085273325957119381)
                  ·
                    refine ⟨271877394622187154239971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5800051085273325957119381 271877394622187154239971)
                    ·
                      rfl

theorem cell23_1588438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_1588438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588438 prefixEnd_1588438 := by exact prefixLift 1588438
  have htrace : WordTrace (prefixWord ++ tailWord_1588438) baseStart_1588438 baseEnd_1588438 := by
    simpa [prefixWord, tailWord_1588438, baseEnd_1588438] using wordTrace_append hprefix tailTrace_1588438
  have hstable : (prefixWord ++ tailWord_1588438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588438).length < 2 ^ (prefixWord ++ tailWord_1588438).sum := by decide
  have hdescent : baseEnd_1588438 < baseStart_1588438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588461 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_1588461 : Nat := 118140960795 + 1588461 * 2 ^ 59
def prefixEnd_1588461 : Nat := 4983230072969 + 3 ^ 40 * 1588461 * 2
def baseEnd_1588461 : Nat := 815643993921614872732307

theorem tailTrace_1588461 : CollatzResearch.WordTrace tailWord_1588461 prefixEnd_1588461 815643993921614872732307 := by
  unfold tailWord_1588461
  simp only [CollatzResearch.WordTrace]
  refine ⟨57935932298284559385605237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38623954865523039590403491 57935932298284559385605237)
  ·
    refine ⟨5431493652964177442400491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57935932298284559385605237 5431493652964177442400491)
    ·
      refine ⟨8147240479446266163600737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5431493652964177442400491 8147240479446266163600737)
      ·
        refine ⟨6110430359584699622700553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8147240479446266163600737 6110430359584699622700553)
        ·
          refine ⟨4582822769688524717025415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6110430359584699622700553 4582822769688524717025415)
          ·
            refine ⟨6874234154532787075538123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4582822769688524717025415 6874234154532787075538123)
            ·
              refine ⟨10311351231799180613307185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6874234154532787075538123 10311351231799180613307185)
              ·
                refine ⟨7733513423849385459980389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10311351231799180613307185 7733513423849385459980389)
                ·
                  refine ⟨1450033766971759773746323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7733513423849385459980389 1450033766971759773746323)
                  ·
                    refine ⟨2175050650457639660619485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1450033766971759773746323 2175050650457639660619485)
                    ·
                      refine ⟨815643993921614872732307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2175050650457639660619485 815643993921614872732307)
                      ·
                        rfl

theorem cell23_1588461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_1588461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588461 prefixEnd_1588461 := by exact prefixLift 1588461
  have htrace : WordTrace (prefixWord ++ tailWord_1588461) baseStart_1588461 baseEnd_1588461 := by
    simpa [prefixWord, tailWord_1588461, baseEnd_1588461] using wordTrace_append hprefix tailTrace_1588461
  have hstable : (prefixWord ++ tailWord_1588461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588461).length < 2 ^ (prefixWord ++ tailWord_1588461).sum := by decide
  have hdescent : baseEnd_1588461 < baseStart_1588461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588468 : List Nat := [2, 6, 1, 2, 1, 2, 9]
def baseStart_1588468 : Nat := 118140960795 + 1588468 * 2 ^ 59
def prefixEnd_1588468 : Nat := 4983230072969 + 3 ^ 40 * 1588468 * 2
def baseEnd_1588468 : Nat := 10069723312175263522775

theorem tailTrace_1588468 : CollatzResearch.WordTrace tailWord_1588468 prefixEnd_1588468 10069723312175263522775 := by
  unfold tailWord_1588468
  simp only [CollatzResearch.WordTrace]
  refine ⟨28968093804629599790555029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38624125072839466387406705 28968093804629599790555029)
  ·
    refine ⟨1357879397092012490182267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28968093804629599790555029 1357879397092012490182267)
    ·
      refine ⟨2036819095638018735273401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1357879397092012490182267 2036819095638018735273401)
      ·
        refine ⟨1527614321728514051455051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2036819095638018735273401 1527614321728514051455051)
        ·
          refine ⟨2291421482592771077182577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527614321728514051455051 2291421482592771077182577)
          ·
            refine ⟨1718566111944578307886933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2291421482592771077182577 1718566111944578307886933)
            ·
              refine ⟨10069723312175263522775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1718566111944578307886933 10069723312175263522775)
              ·
                rfl

theorem cell23_1588468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 9].length) (baseStart_1588468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588468 prefixEnd_1588468 := by exact prefixLift 1588468
  have htrace : WordTrace (prefixWord ++ tailWord_1588468) baseStart_1588468 baseEnd_1588468 := by
    simpa [prefixWord, tailWord_1588468, baseEnd_1588468] using wordTrace_append hprefix tailTrace_1588468
  have hstable : (prefixWord ++ tailWord_1588468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588468).length < 2 ^ (prefixWord ++ tailWord_1588468).sum := by decide
  have hdescent : baseEnd_1588468 < baseStart_1588468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588497 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_1588497 : Nat := 118140960795 + 1588497 * 2 ^ 59
def prefixEnd_1588497 : Nat := 4983230072969 + 3 ^ 40 * 1588497 * 2
def baseEnd_1588497 : Nat := 815662479225176731882141

theorem tailTrace_1588497 : CollatzResearch.WordTrace tailWord_1588497 prefixEnd_1588497 815662479225176731882141 := by
  unfold tailWord_1588497
  simp only [CollatzResearch.WordTrace]
  refine ⟨57937245326154137533915745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38624830217436091689277163 57937245326154137533915745)
  ·
    refine ⟨43452933994615603150436809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57937245326154137533915745 43452933994615603150436809)
    ·
      refine ⟨32589700495961702362827607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43452933994615603150436809 32589700495961702362827607)
      ·
        refine ⟨48884550743942553544241411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32589700495961702362827607 48884550743942553544241411)
        ·
          refine ⟨73326826115913830316362117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48884550743942553544241411 73326826115913830316362117)
          ·
            refine ⟨13748779896733843184317897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73326826115913830316362117 13748779896733843184317897)
            ·
              refine ⟨10311584922550382388238423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13748779896733843184317897 10311584922550382388238423)
              ·
                refine ⟨15467377383825573582357635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10311584922550382388238423 15467377383825573582357635)
                ·
                  refine ⟨23201066075738360373536453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15467377383825573582357635 23201066075738360373536453)
                  ·
                    refine ⟨4350199889200942570038085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23201066075738360373536453 4350199889200942570038085)
                    ·
                      refine ⟨815662479225176731882141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4350199889200942570038085 815662479225176731882141)
                      ·
                        rfl

theorem cell23_1588497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_1588497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588497 prefixEnd_1588497 := by exact prefixLift 1588497
  have htrace : WordTrace (prefixWord ++ tailWord_1588497) baseStart_1588497 baseEnd_1588497 := by
    simpa [prefixWord, tailWord_1588497, baseEnd_1588497] using wordTrace_append hprefix tailTrace_1588497
  have hstable : (prefixWord ++ tailWord_1588497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588497).length < 2 ^ (prefixWord ++ tailWord_1588497).sum := by decide
  have hdescent : baseEnd_1588497 < baseStart_1588497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588524 : List Nat := [2, 2, 1, 1, 1, 3, 1, 7, 5]
def baseStart_1588524 : Nat := 118140960795 + 1588524 * 2 ^ 59
def prefixEnd_1588524 : Nat := 4983230072969 + 3 ^ 40 * 1588524 * 2
def baseEnd_1588524 : Nat := 90630704800316458471613

theorem tailTrace_1588524 : CollatzResearch.WordTrace tailWord_1588524 prefixEnd_1588524 90630704800316458471613 := by
  unfold tailWord_1588524
  simp only [CollatzResearch.WordTrace]
  refine ⟨28969115048528160572574313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38625486731370880763432417 28969115048528160572574313)
  ·
    refine ⟨21726836286396120429430735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28969115048528160572574313 21726836286396120429430735)
    ·
      refine ⟨32590254429594180644146103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21726836286396120429430735 32590254429594180644146103)
      ·
        refine ⟨48885381644391270966219155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32590254429594180644146103 48885381644391270966219155)
        ·
          refine ⟨73328072466586906449328733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48885381644391270966219155 73328072466586906449328733)
          ·
            refine ⟨27498027174970089918498275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73328072466586906449328733 27498027174970089918498275)
            ·
              refine ⟨41247040762455134877747413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27498027174970089918498275 41247040762455134877747413)
              ·
                refine ⟨966727517870042223697205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41247040762455134877747413 966727517870042223697205)
                ·
                  refine ⟨90630704800316458471613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 966727517870042223697205 90630704800316458471613)
                  ·
                    rfl

theorem cell23_1588524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 5].length) (baseStart_1588524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588524 prefixEnd_1588524 := by exact prefixLift 1588524
  have htrace : WordTrace (prefixWord ++ tailWord_1588524) baseStart_1588524 baseEnd_1588524 := by
    simpa [prefixWord, tailWord_1588524, baseEnd_1588524] using wordTrace_append hprefix tailTrace_1588524
  have hstable : (prefixWord ++ tailWord_1588524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588524).length < 2 ^ (prefixWord ++ tailWord_1588524).sum := by decide
  have hdescent : baseEnd_1588524 < baseStart_1588524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588544 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 1, 7, 2]
def baseStart_1588544 : Nat := 118140960795 + 1588544 * 2 ^ 59
def prefixEnd_1588544 : Nat := 4983230072969 + 3 ^ 40 * 1588544 * 2
def baseEnd_1588544 : Nat := 815686612815938047994425

theorem tailTrace_1588544 : CollatzResearch.WordTrace tailWord_1588544 prefixEnd_1588544 815686612815938047994425 := by
  unfold tailWord_1588544
  simp only [CollatzResearch.WordTrace]
  refine ⟨28969479778491932280438343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38625973037989243040584457 28969479778491932280438343)
  ·
    refine ⟨43454219667737898420657515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28969479778491932280438343 43454219667737898420657515)
    ·
      refine ⟨65181329501606847630986273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43454219667737898420657515 65181329501606847630986273)
      ·
        refine ⟨48885997126205135723239705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65181329501606847630986273 48885997126205135723239705)
        ·
          refine ⟨36664497844653851792429779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48885997126205135723239705 36664497844653851792429779)
          ·
            refine ⟨54996746766980777688644669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36664497844653851792429779 54996746766980777688644669)
            ·
              refine ⟨20623780037617791633241751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54996746766980777688644669 20623780037617791633241751)
              ·
                refine ⟨30935670056426687449862627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20623780037617791633241751 30935670056426687449862627)
                ·
                  refine ⟨46403505084640031174793941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30935670056426687449862627 46403505084640031174793941)
                  ·
                    refine ⟨1087582150421250730659233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46403505084640031174793941 1087582150421250730659233)
                    ·
                      refine ⟨815686612815938047994425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1087582150421250730659233 815686612815938047994425)
                      ·
                        rfl

theorem cell23_1588544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 7, 2].length) (baseStart_1588544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588544 prefixEnd_1588544 := by exact prefixLift 1588544
  have htrace : WordTrace (prefixWord ++ tailWord_1588544) baseStart_1588544 baseEnd_1588544 := by
    simpa [prefixWord, tailWord_1588544, baseEnd_1588544] using wordTrace_append hprefix tailTrace_1588544
  have hstable : (prefixWord ++ tailWord_1588544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588544).length < 2 ^ (prefixWord ++ tailWord_1588544).sum := by decide
  have hdescent : baseEnd_1588544 < baseStart_1588544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588627 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 4, 9]
def baseStart_1588627 : Nat := 118140960795 + 1588627 * 2 ^ 59
def prefixEnd_1588627 : Nat := 4983230072969 + 3 ^ 40 * 1588627 * 2
def baseEnd_1588627 : Nat := 271909743903420407752181

theorem tailTrace_1588627 : CollatzResearch.WordTrace tailWord_1588627 prefixEnd_1588627 271909743903420407752181 := by
  unfold tailWord_1588627
  simp only [CollatzResearch.WordTrace]
  refine ⟨57941986815683169736148135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38627991210455446490765423 57941986815683169736148135)
  ·
    refine ⟨86912980223524754604222203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57941986815683169736148135 86912980223524754604222203)
    ·
      refine ⟨130369470335287131906333305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86912980223524754604222203 130369470335287131906333305)
      ·
        refine ⟨97777102751465348929749979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130369470335287131906333305 97777102751465348929749979)
        ·
          refine ⟨146665654127198023394624969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97777102751465348929749979 146665654127198023394624969)
          ·
            refine ⟨109999240595398517545968727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146665654127198023394624969 109999240595398517545968727)
            ·
              refine ⟨164998860893097776318953091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109999240595398517545968727 164998860893097776318953091)
              ·
                refine ⟨247498291339646664478429637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164998860893097776318953091 247498291339646664478429637)
                ·
                  refine ⟨46405929626183749589705557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 247498291339646664478429637 46405929626183749589705557)
                  ·
                    refine ⟨271909743903420407752181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 46405929626183749589705557 271909743903420407752181)
                    ·
                      rfl

theorem cell23_1588627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 9].length) (baseStart_1588627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588627 prefixEnd_1588627 := by exact prefixLift 1588627
  have htrace : WordTrace (prefixWord ++ tailWord_1588627) baseStart_1588627 baseEnd_1588627 := by
    simpa [prefixWord, tailWord_1588627, baseEnd_1588627] using wordTrace_append hprefix tailTrace_1588627
  have hstable : (prefixWord ++ tailWord_1588627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588627).length < 2 ^ (prefixWord ++ tailWord_1588627).sum := by decide
  have hdescent : baseEnd_1588627 < baseStart_1588627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588644 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_1588644 : Nat := 118140960795 + 1588644 * 2 ^ 59
def prefixEnd_1588644 : Nat := 4983230072969 + 3 ^ 40 * 1588644 * 2
def baseEnd_1588644 : Nat := 271912653627129218914655

theorem tailTrace_1588644 : CollatzResearch.WordTrace tailWord_1588644 prefixEnd_1588644 271912653627129218914655 := by
  unfold tailWord_1588644
  simp only [CollatzResearch.WordTrace]
  refine ⟨28971303428310790819758493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38628404571081054426344657 28971303428310790819758493)
  ·
    refine ⟨10864238785616546557409435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28971303428310790819758493 10864238785616546557409435)
    ·
      refine ⟨16296358178424819836114153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10864238785616546557409435 16296358178424819836114153)
      ·
        refine ⟨12222268633818614877085615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16296358178424819836114153 12222268633818614877085615)
        ·
          refine ⟨18333402950727922315628423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12222268633818614877085615 18333402950727922315628423)
          ·
            refine ⟨27500104426091883473442635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18333402950727922315628423 27500104426091883473442635)
            ·
              refine ⟨41250156639137825210163953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27500104426091883473442635 41250156639137825210163953)
              ·
                refine ⟨30937617479353368907622965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41250156639137825210163953 30937617479353368907622965)
                ·
                  refine ⟨2900401638689378335089653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30937617479353368907622965 2900401638689378335089653)
                  ·
                    refine ⟨271912653627129218914655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2900401638689378335089653 271912653627129218914655)
                    ·
                      rfl

theorem cell23_1588644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_1588644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588644 prefixEnd_1588644 := by exact prefixLift 1588644
  have htrace : WordTrace (prefixWord ++ tailWord_1588644) baseStart_1588644 baseEnd_1588644 := by
    simpa [prefixWord, tailWord_1588644, baseEnd_1588644] using wordTrace_append hprefix tailTrace_1588644
  have hstable : (prefixWord ++ tailWord_1588644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588644).length < 2 ^ (prefixWord ++ tailWord_1588644).sum := by decide
  have hdescent : baseEnd_1588644 < baseStart_1588644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588665 : List Nat := [1, 2, 1, 4, 5, 1, 2, 1, 6]
def baseStart_1588665 : Nat := 118140960795 + 1588665 * 2 ^ 59
def prefixEnd_1588665 : Nat := 4983230072969 + 3 ^ 40 * 1588665 * 2
def baseEnd_1588665 : Nat := 90638749330570230509041

theorem tailTrace_1588665 : CollatzResearch.WordTrace tailWord_1588665 prefixEnd_1588665 90638749330570230509041 := by
  unfold tailWord_1588665
  simp only [CollatzResearch.WordTrace]
  refine ⟨57943372789545502226031449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38628915193030334817354299 57943372789545502226031449)
  ·
    refine ⟨43457529592159126669523587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57943372789545502226031449 43457529592159126669523587)
    ·
      refine ⟨65186294388238690004285381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43457529592159126669523587 65186294388238690004285381)
      ·
        refine ⟨12222430197794754375803509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65186294388238690004285381 12222430197794754375803509)
        ·
          refine ⟨1145852831043258222731579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12222430197794754375803509 1145852831043258222731579)
          ·
            refine ⟨1718779246564887334097369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145852831043258222731579 1718779246564887334097369)
            ·
              refine ⟨1289084434923665500573027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1718779246564887334097369 1289084434923665500573027)
              ·
                refine ⟨1933626652385498250859541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289084434923665500573027 1933626652385498250859541)
                ·
                  refine ⟨90638749330570230509041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1933626652385498250859541 90638749330570230509041)
                  ·
                    rfl

theorem cell23_1588665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 6].length) (baseStart_1588665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588665 prefixEnd_1588665 := by exact prefixLift 1588665
  have htrace : WordTrace (prefixWord ++ tailWord_1588665) baseStart_1588665 baseEnd_1588665 := by
    simpa [prefixWord, tailWord_1588665, baseEnd_1588665] using wordTrace_append hprefix tailTrace_1588665
  have hstable : (prefixWord ++ tailWord_1588665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588665).length < 2 ^ (prefixWord ++ tailWord_1588665).sum := by decide
  have hdescent : baseEnd_1588665 < baseStart_1588665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588709 : List Nat := [1, 3, 1, 5, 1, 3, 2, 2, 1, 1, 3]
def baseStart_1588709 : Nat := 118140960795 + 1588709 * 2 ^ 59
def prefixEnd_1588709 : Nat := 4983230072969 + 3 ^ 40 * 1588709 * 2
def baseEnd_1588709 : Nat := 815771337123929902431167

theorem tailTrace_1588709 : CollatzResearch.WordTrace tailWord_1588709 prefixEnd_1588709 815771337123929902431167 := by
  unfold tailWord_1588709
  simp only [CollatzResearch.WordTrace]
  refine ⟨57944977601386097740633181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38629985067590731827088787 57944977601386097740633181)
  ·
    refine ⟨21729366600519786652737443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57944977601386097740633181 21729366600519786652737443)
    ·
      refine ⟨32594049900779679979106165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21729366600519786652737443 32594049900779679979106165)
      ·
        refine ⟨3055692178198094998041203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32594049900779679979106165 3055692178198094998041203)
        ·
          refine ⟨4583538267297142497061805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055692178198094998041203 4583538267297142497061805)
          ·
            refine ⟨1718826850236428436398177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4583538267297142497061805 1718826850236428436398177)
            ·
              refine ⟨1289120137677321327298633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1718826850236428436398177 1289120137677321327298633)
              ·
                refine ⟨966840103257990995473975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1289120137677321327298633 966840103257990995473975)
                ·
                  refine ⟨1450260154886986493210963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966840103257990995473975 1450260154886986493210963)
                  ·
                    refine ⟨2175390232330479739816445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1450260154886986493210963 2175390232330479739816445)
                    ·
                      refine ⟨815771337123929902431167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2175390232330479739816445 815771337123929902431167)
                      ·
                        rfl

theorem cell23_1588709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_1588709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588709 prefixEnd_1588709 := by exact prefixLift 1588709
  have htrace : WordTrace (prefixWord ++ tailWord_1588709) baseStart_1588709 baseEnd_1588709 := by
    simpa [prefixWord, tailWord_1588709, baseEnd_1588709] using wordTrace_append hprefix tailTrace_1588709
  have hstable : (prefixWord ++ tailWord_1588709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588709).length < 2 ^ (prefixWord ++ tailWord_1588709).sum := by decide
  have hdescent : baseEnd_1588709 < baseStart_1588709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588721 : List Nat := [1, 2, 2, 2, 3, 4, 1, 8]
def baseStart_1588721 : Nat := 118140960795 + 1588721 * 2 ^ 59
def prefixEnd_1588721 : Nat := 4983230072969 + 3 ^ 40 * 1588721 * 2
def baseEnd_1588721 : Nat := 30213981440436439091893

theorem tailTrace_1588721 : CollatzResearch.WordTrace tailWord_1588721 prefixEnd_1588721 30213981440436439091893 := by
  unfold tailWord_1588721
  simp only [CollatzResearch.WordTrace]
  refine ⟨57945415277342623790070017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38630276851561749193380011 57945415277342623790070017)
  ·
    refine ⟨43459061458006967842552513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57945415277342623790070017 43459061458006967842552513)
    ·
      refine ⟨32594296093505225881914385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43459061458006967842552513 32594296093505225881914385)
      ·
        refine ⟨24445722070128919411435789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32594296093505225881914385 24445722070128919411435789)
        ·
          refine ⟨9167145776298344779288421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24445722070128919411435789 9167145776298344779288421)
          ·
            refine ⟨1718839833055939646116579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9167145776298344779288421 1718839833055939646116579)
            ·
              refine ⟨2578259749583909469174869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718839833055939646116579 2578259749583909469174869)
              ·
                refine ⟨30213981440436439091893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2578259749583909469174869 30213981440436439091893)
                ·
                  rfl

theorem cell23_1588721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 8].length) (baseStart_1588721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588721 prefixEnd_1588721 := by exact prefixLift 1588721
  have htrace : WordTrace (prefixWord ++ tailWord_1588721) baseStart_1588721 baseEnd_1588721 := by
    simpa [prefixWord, tailWord_1588721, baseEnd_1588721] using wordTrace_append hprefix tailTrace_1588721
  have hstable : (prefixWord ++ tailWord_1588721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588721).length < 2 ^ (prefixWord ++ tailWord_1588721).sum := by decide
  have hdescent : baseEnd_1588721 < baseStart_1588721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588725 : List Nat := [1, 3, 5, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1588725 : Nat := 118140960795 + 1588725 * 2 ^ 59
def prefixEnd_1588725 : Nat := 4983230072969 + 3 ^ 40 * 1588725 * 2
def baseEnd_1588725 : Nat := 271926517604800613277031

theorem tailTrace_1588725 : CollatzResearch.WordTrace tailWord_1588725 prefixEnd_1588725 271926517604800613277031 := by
  unfold tailWord_1588725
  simp only [CollatzResearch.WordTrace]
  refine ⟨57945561169328132473215629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38630374112885421648810419 57945561169328132473215629)
  ·
    refine ⟨21729585438498049677455861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57945561169328132473215629 21729585438498049677455861)
    ·
      refine ⟨2037148634859192157261487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21729585438498049677455861 2037148634859192157261487)
      ·
        refine ⟨3055722952288788235892231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2037148634859192157261487 3055722952288788235892231)
        ·
          refine ⟨4583584428433182353838347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055722952288788235892231 4583584428433182353838347)
          ·
            refine ⟨6875376642649773530757521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583584428433182353838347 6875376642649773530757521)
            ·
              refine ⟨5156532481987330148068141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6875376642649773530757521 5156532481987330148068141)
              ·
                refine ⟨1933699680745248805525553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5156532481987330148068141 1933699680745248805525553)
                ·
                  refine ⟨1450274760558936604144165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1933699680745248805525553 1450274760558936604144165)
                  ·
                    refine ⟨271926517604800613277031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1450274760558936604144165 271926517604800613277031)
                    ·
                      rfl

theorem cell23_1588725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1588725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588725 prefixEnd_1588725 := by exact prefixLift 1588725
  have htrace : WordTrace (prefixWord ++ tailWord_1588725) baseStart_1588725 baseEnd_1588725 := by
    simpa [prefixWord, tailWord_1588725, baseEnd_1588725] using wordTrace_append hprefix tailTrace_1588725
  have hstable : (prefixWord ++ tailWord_1588725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588725).length < 2 ^ (prefixWord ++ tailWord_1588725).sum := by decide
  have hdescent : baseEnd_1588725 < baseStart_1588725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588828 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 7]
def baseStart_1588828 : Nat := 118140960795 + 1588828 * 2 ^ 59
def prefixEnd_1588828 : Nat := 4983230072969 + 3 ^ 40 * 1588828 * 2
def baseEnd_1588828 : Nat := 90648049035757215204791

theorem tailTrace_1588828 : CollatzResearch.WordTrace tailWord_1588828 prefixEnd_1588828 90648049035757215204791 := by
  unfold tailWord_1588828
  simp only [CollatzResearch.WordTrace]
  refine ⟨28974658943977490532107569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38632878591969987376143425 28974658943977490532107569)
  ·
    refine ⟨21730994207983117899080677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28974658943977490532107569 21730994207983117899080677)
    ·
      refine ⟨4074561413996834606077627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21730994207983117899080677 4074561413996834606077627)
      ·
        refine ⟨6111842120995251909116441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4074561413996834606077627 6111842120995251909116441)
        ·
          refine ⟨4583881590746438931837331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6111842120995251909116441 4583881590746438931837331)
          ·
            refine ⟨6875822386119658397755997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583881590746438931837331 6875822386119658397755997)
            ·
              refine ⟨2578433394794871899158499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6875822386119658397755997 2578433394794871899158499)
              ·
                refine ⟨3867650092192307848737749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2578433394794871899158499 3867650092192307848737749)
                ·
                  refine ⟨90648049035757215204791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3867650092192307848737749 90648049035757215204791)
                  ·
                    rfl

theorem cell23_1588828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 7].length) (baseStart_1588828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588828 prefixEnd_1588828 := by exact prefixLift 1588828
  have htrace : WordTrace (prefixWord ++ tailWord_1588828) baseStart_1588828 baseEnd_1588828 := by
    simpa [prefixWord, tailWord_1588828, baseEnd_1588828] using wordTrace_append hprefix tailTrace_1588828
  have hstable : (prefixWord ++ tailWord_1588828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588828).length < 2 ^ (prefixWord ++ tailWord_1588828).sum := by decide
  have hdescent : baseEnd_1588828 < baseStart_1588828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588922 : List Nat := [3, 1, 1, 1, 2, 5, 2, 3, 1, 4]
def baseStart_1588922 : Nat := 118140960795 + 1588922 * 2 ^ 59
def prefixEnd_1588922 : Nat := 4983230072969 + 3 ^ 40 * 1588922 * 2
def baseEnd_1588922 : Nat := 271960236167779189689229

theorem tailTrace_1588922 : CollatzResearch.WordTrace tailWord_1588922 prefixEnd_1588922 271960236167779189689229 := by
  unfold tailWord_1588922
  simp only [CollatzResearch.WordTrace]
  refine ⟨14488186587403608779534255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38635164233076290078758013 14488186587403608779534255)
  ·
    refine ⟨21732279881105413169301383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14488186587403608779534255 21732279881105413169301383)
    ·
      refine ⟨32598419821658119753952075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21732279881105413169301383 32598419821658119753952075)
      ·
        refine ⟨48897629732487179630928113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32598419821658119753952075 48897629732487179630928113)
        ·
          refine ⟨36673222299365384723196085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48897629732487179630928113 36673222299365384723196085)
          ·
            refine ⟨3438114590565504817799633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36673222299365384723196085 3438114590565504817799633)
            ·
              refine ⟨2578585942924128613349725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3438114590565504817799633 2578585942924128613349725)
              ·
                refine ⟨966969728596548230006147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2578585942924128613349725 966969728596548230006147)
                ·
                  refine ⟨1450454592894822345009221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966969728596548230006147 1450454592894822345009221)
                  ·
                    refine ⟨271960236167779189689229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1450454592894822345009221 271960236167779189689229)
                    ·
                      rfl

theorem cell23_1588922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_1588922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588922 prefixEnd_1588922 := by exact prefixLift 1588922
  have htrace : WordTrace (prefixWord ++ tailWord_1588922) baseStart_1588922 baseEnd_1588922 := by
    simpa [prefixWord, tailWord_1588922, baseEnd_1588922] using wordTrace_append hprefix tailTrace_1588922
  have hstable : (prefixWord ++ tailWord_1588922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588922).length < 2 ^ (prefixWord ++ tailWord_1588922).sum := by decide
  have hdescent : baseEnd_1588922 < baseStart_1588922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588945 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 3, 1, 3]
def baseStart_1588945 : Nat := 118140960795 + 1588945 * 2 ^ 59
def prefixEnd_1588945 : Nat := 4983230072969 + 3 ^ 40 * 1588945 * 2
def baseEnd_1588945 : Nat := 815892518558390979080081

theorem tailTrace_1588945 : CollatzResearch.WordTrace tailWord_1588945 prefixEnd_1588945 815892518558390979080081 := by
  unfold tailWord_1588945
  simp only [CollatzResearch.WordTrace]
  refine ⟨57953585228531110046224289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38635723485687406697482859 57953585228531110046224289)
  ·
    refine ⟨43465188921398332534668217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57953585228531110046224289 43465188921398332534668217)
    ·
      refine ⟨32598891691048749401001163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43465188921398332534668217 32598891691048749401001163)
      ·
        refine ⟨48898337536573124101501745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32598891691048749401001163 48898337536573124101501745)
        ·
          refine ⟨36673753152429843076126309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48898337536573124101501745 36673753152429843076126309)
          ·
            refine ⟨6876328716080595576773683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36673753152429843076126309 6876328716080595576773683)
            ·
              refine ⟨10314493074120893365160525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6876328716080595576773683 10314493074120893365160525)
              ·
                refine ⟨3867934902795335011935197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10314493074120893365160525 3867934902795335011935197)
                ·
                  refine ⟨1450475588548250629475699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3867934902795335011935197 1450475588548250629475699)
                  ·
                    refine ⟨2175713382822375944213549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1450475588548250629475699 2175713382822375944213549)
                    ·
                      refine ⟨815892518558390979080081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2175713382822375944213549 815892518558390979080081)
                      ·
                        rfl

theorem cell23_1588945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_1588945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588945 prefixEnd_1588945 := by exact prefixLift 1588945
  have htrace : WordTrace (prefixWord ++ tailWord_1588945) baseStart_1588945 baseEnd_1588945 := by
    simpa [prefixWord, tailWord_1588945, baseEnd_1588945] using wordTrace_append hprefix tailTrace_1588945
  have hstable : (prefixWord ++ tailWord_1588945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588945).length < 2 ^ (prefixWord ++ tailWord_1588945).sum := by decide
  have hdescent : baseEnd_1588945 < baseStart_1588945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588965 : List Nat := [1, 3, 1, 4, 1, 1, 4, 2, 1, 5]
def baseStart_1588965 : Nat := 118140960795 + 1588965 * 2 ^ 59
def prefixEnd_1588965 : Nat := 4983230072969 + 3 ^ 40 * 1588965 * 2
def baseEnd_1588965 : Nat := 271967596057160300276663

theorem tailTrace_1588965 : CollatzResearch.WordTrace tailWord_1588965 prefixEnd_1588965 271967596057160300276663 := by
  unfold tailWord_1588965
  simp only [CollatzResearch.WordTrace]
  refine ⟨57954314688458653461952349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38636209792305768974634899 57954314688458653461952349)
  ·
    refine ⟨21732868008171995048232131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57954314688458653461952349 21732868008171995048232131)
    ·
      refine ⟨32599302012257992572348197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21732868008171995048232131 32599302012257992572348197)
      ·
        refine ⟨6112369127298373607315287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32599302012257992572348197 6112369127298373607315287)
        ·
          refine ⟨9168553690947560410972931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6112369127298373607315287 9168553690947560410972931)
          ·
            refine ⟨13752830536421340616459397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9168553690947560410972931 13752830536421340616459397)
            ·
              refine ⟨2578655725579001365586137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13752830536421340616459397 2578655725579001365586137)
              ·
                refine ⟨1933991794184251024189603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2578655725579001365586137 1933991794184251024189603)
                ·
                  refine ⟨2900987691276376536284405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933991794184251024189603 2900987691276376536284405)
                  ·
                    refine ⟨271967596057160300276663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2900987691276376536284405 271967596057160300276663)
                    ·
                      rfl

theorem cell23_1588965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_1588965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588965 prefixEnd_1588965 := by exact prefixLift 1588965
  have htrace : WordTrace (prefixWord ++ tailWord_1588965) baseStart_1588965 baseEnd_1588965 := by
    simpa [prefixWord, tailWord_1588965, baseEnd_1588965] using wordTrace_append hprefix tailTrace_1588965
  have hstable : (prefixWord ++ tailWord_1588965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588965).length < 2 ^ (prefixWord ++ tailWord_1588965).sum := by decide
  have hdescent : baseEnd_1588965 < baseStart_1588965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588978 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_1588978 : Nat := 118140960795 + 1588978 * 2 ^ 59
def prefixEnd_1588978 : Nat := 4983230072969 + 3 ^ 40 * 1588978 * 2
def baseEnd_1588978 : Nat := 271969821139996449989143

theorem tailTrace_1588978 : CollatzResearch.WordTrace tailWord_1588978 prefixEnd_1588978 271969821139996449989143 := by
  unfold tailWord_1588978
  simp only [CollatzResearch.WordTrace]
  refine ⟨14488697209352889170543897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38636525891607704454783725 14488697209352889170543897)
  ·
    refine ⟨10866522907014666877907923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14488697209352889170543897 10866522907014666877907923)
    ·
      refine ⟨16299784360522000316861885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10866522907014666877907923 16299784360522000316861885)
      ·
        refine ⟨6112419135195750118823207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16299784360522000316861885 6112419135195750118823207)
        ·
          refine ⟨9168628702793625178234811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6112419135195750118823207 9168628702793625178234811)
          ·
            refine ⟨13752943054190437767352217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9168628702793625178234811 13752943054190437767352217)
            ·
              refine ⟨10314707290642828325514163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13752943054190437767352217 10314707290642828325514163)
              ·
                refine ⟨15472060935964242488271245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10314707290642828325514163 15472060935964242488271245)
                ·
                  refine ⟨5802022850986590933101717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15472060935964242488271245 5802022850986590933101717)
                  ·
                    refine ⟨271969821139996449989143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5802022850986590933101717 271969821139996449989143)
                    ·
                      rfl

theorem cell23_1588978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_1588978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588978 prefixEnd_1588978 := by exact prefixLift 1588978
  have htrace : WordTrace (prefixWord ++ tailWord_1588978) baseStart_1588978 baseEnd_1588978 := by
    simpa [prefixWord, tailWord_1588978, baseEnd_1588978] using wordTrace_append hprefix tailTrace_1588978
  have hstable : (prefixWord ++ tailWord_1588978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588978).length < 2 ^ (prefixWord ++ tailWord_1588978).sum := by decide
  have hdescent : baseEnd_1588978 < baseStart_1588978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588991 : List Nat := [1, 1, 2, 2, 1, 3, 13]
def baseStart_1588991 : Nat := 118140960795 + 1588991 * 2 ^ 59
def prefixEnd_1588991 : Nat := 4983230072969 + 3 ^ 40 * 1588991 * 2
def baseEnd_1588991 : Nat := 10073038748993799988949

theorem tailTrace_1588991 : CollatzResearch.WordTrace tailWord_1588991 prefixEnd_1588991 10073038748993799988949 := by
  unfold tailWord_1588991
  simp only [CollatzResearch.WordTrace]
  refine ⟨57955262986364459902398827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38636841990909639934932551 57955262986364459902398827)
  ·
    refine ⟨86932894479546689853598241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57955262986364459902398827 86932894479546689853598241)
    ·
      refine ⟨65199670859660017390198681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86932894479546689853598241 65199670859660017390198681)
      ·
        refine ⟨48899753144745013042649011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65199670859660017390198681 48899753144745013042649011)
        ·
          refine ⟨73349629717117519563973517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48899753144745013042649011 73349629717117519563973517)
          ·
            refine ⟨27506111143919069836490069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73349629717117519563973517 27506111143919069836490069)
            ·
              refine ⟨10073038748993799988949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 27506111143919069836490069 10073038748993799988949)
              ·
                rfl

theorem cell23_1588991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 13].length) (baseStart_1588991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588991 prefixEnd_1588991 := by exact prefixLift 1588991
  have htrace : WordTrace (prefixWord ++ tailWord_1588991) baseStart_1588991 baseEnd_1588991 := by
    simpa [prefixWord, tailWord_1588991, baseEnd_1588991] using wordTrace_append hprefix tailTrace_1588991
  have hstable : (prefixWord ++ tailWord_1588991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588991).length < 2 ^ (prefixWord ++ tailWord_1588991).sum := by decide
  have hdescent : baseEnd_1588991 < baseStart_1588991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1588996 : List Nat := [2, 3, 2, 2, 1, 3, 3, 2, 1, 1, 3]
def baseStart_1588996 : Nat := 118140960795 + 1588996 * 2 ^ 59
def prefixEnd_1588996 : Nat := 4983230072969 + 3 ^ 40 * 1588996 * 2
def baseEnd_1588996 : Nat := 815918706071770279542347

theorem tailTrace_1588996 : CollatzResearch.WordTrace tailWord_1588996 prefixEnd_1588996 815918706071770279542347 := by
  unfold tailWord_1588996
  simp only [CollatzResearch.WordTrace]
  refine ⟨28977722675673172878165421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38636963567564230504220561 28977722675673172878165421)
  ·
    refine ⟨10866646003377439829312033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28977722675673172878165421 10866646003377439829312033)
    ·
      refine ⟨8149984502533079871984025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10866646003377439829312033 8149984502533079871984025)
      ·
        refine ⟨6112488376899809903988019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8149984502533079871984025 6112488376899809903988019)
        ·
          refine ⟨9168732565349714855982029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6112488376899809903988019 9168732565349714855982029)
          ·
            refine ⟨3438274712006143070993261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9168732565349714855982029 3438274712006143070993261)
            ·
              refine ⟨1289353017002303651622473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3438274712006143070993261 1289353017002303651622473)
              ·
                refine ⟨967014762751727738716855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1289353017002303651622473 967014762751727738716855)
                ·
                  refine ⟨1450522144127591608075283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967014762751727738716855 1450522144127591608075283)
                  ·
                    refine ⟨2175783216191387412112925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1450522144127591608075283 2175783216191387412112925)
                    ·
                      refine ⟨815918706071770279542347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2175783216191387412112925 815918706071770279542347)
                      ·
                        rfl

theorem cell23_1588996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_1588996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1588996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1588996 prefixEnd_1588996 := by exact prefixLift 1588996
  have htrace : WordTrace (prefixWord ++ tailWord_1588996) baseStart_1588996 baseEnd_1588996 := by
    simpa [prefixWord, tailWord_1588996, baseEnd_1588996] using wordTrace_append hprefix tailTrace_1588996
  have hstable : (prefixWord ++ tailWord_1588996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1588996).length < 2 ^ (prefixWord ++ tailWord_1588996).sum := by decide
  have hdescent : baseEnd_1588996 < baseStart_1588996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1588996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589052 : List Nat := [2, 2, 2, 2, 1, 1, 3, 4, 2, 1, 3]
def baseStart_1589052 : Nat := 118140960795 + 1589052 * 2 ^ 59
def prefixEnd_1589052 : Nat := 4983230072969 + 3 ^ 40 * 1589052 * 2
def baseEnd_1589052 : Nat := 815947460988422060442089

theorem tailTrace_1589052 : CollatzResearch.WordTrace tailWord_1589052 prefixEnd_1589052 815947460988422060442089 := by
  unfold tailWord_1589052
  simp only [CollatzResearch.WordTrace]
  refine ⟨28978743919571733660184705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38638325226095644880246273 28978743919571733660184705)
  ·
    refine ⟨21734057939678800245138529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28978743919571733660184705 21734057939678800245138529)
    ·
      refine ⟨16300543454759100183853897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21734057939678800245138529 16300543454759100183853897)
      ·
        refine ⟨12225407591069325137890423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16300543454759100183853897 12225407591069325137890423)
        ·
          refine ⟨18338111386603987706835635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12225407591069325137890423 18338111386603987706835635)
          ·
            refine ⟨27507167079905981560253453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18338111386603987706835635 27507167079905981560253453)
            ·
              refine ⟨10315187654964743085095045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27507167079905981560253453 10315187654964743085095045)
              ·
                refine ⟨1934097685305889328455321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10315187654964743085095045 1934097685305889328455321)
                ·
                  refine ⟨1450573263979416996341491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1934097685305889328455321 1450573263979416996341491)
                  ·
                    refine ⟨2175859895969125494512237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1450573263979416996341491 2175859895969125494512237)
                    ·
                      refine ⟨815947460988422060442089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2175859895969125494512237 815947460988422060442089)
                      ·
                        rfl

theorem cell23_1589052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_1589052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589052 prefixEnd_1589052 := by exact prefixLift 1589052
  have htrace : WordTrace (prefixWord ++ tailWord_1589052) baseStart_1589052 baseEnd_1589052 := by
    simpa [prefixWord, tailWord_1589052, baseEnd_1589052] using wordTrace_append hprefix tailTrace_1589052
  have hstable : (prefixWord ++ tailWord_1589052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589052).length < 2 ^ (prefixWord ++ tailWord_1589052).sum := by decide
  have hdescent : baseEnd_1589052 < baseStart_1589052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589053 : List Nat := [1, 4, 1, 4, 1, 1, 4, 2, 1, 2, 2]
def baseStart_1589053 : Nat := 118140960795 + 1589053 * 2 ^ 59
def prefixEnd_1589053 : Nat := 4983230072969 + 3 ^ 40 * 1589053 * 2
def baseEnd_1589053 : Nat := 815947974469076556529585

theorem tailTrace_1589053 : CollatzResearch.WordTrace tailWord_1589053 prefixEnd_1589053 815947974469076556529585 := by
  unfold tailWord_1589053
  simp only [CollatzResearch.WordTrace]
  refine ⟨57957524312139844491155813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38638349541426562994103875 57957524312139844491155813)
  ·
    refine ⟨10867035808526220842091715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57957524312139844491155813 10867035808526220842091715)
    ·
      refine ⟨16300553712789331263137573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10867035808526220842091715 16300553712789331263137573)
      ·
        refine ⟨3056353821147999611838295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16300553712789331263137573 3056353821147999611838295)
        ·
          refine ⟨4584530731721999417757443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3056353821147999611838295 4584530731721999417757443)
          ·
            refine ⟨6876796097582999126636165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4584530731721999417757443 6876796097582999126636165)
            ·
              refine ⟨1289399268296812336244281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6876796097582999126636165 1289399268296812336244281)
              ·
                refine ⟨967049451222609252183211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1289399268296812336244281 967049451222609252183211)
                ·
                  refine ⟨1450574176833913878274817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967049451222609252183211 1450574176833913878274817)
                  ·
                    refine ⟨1087930632625435408706113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1450574176833913878274817 1087930632625435408706113)
                    ·
                      refine ⟨815947974469076556529585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1087930632625435408706113 815947974469076556529585)
                      ·
                        rfl

theorem cell23_1589053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_1589053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589053 prefixEnd_1589053 := by exact prefixLift 1589053
  have htrace : WordTrace (prefixWord ++ tailWord_1589053) baseStart_1589053 baseEnd_1589053 := by
    simpa [prefixWord, tailWord_1589053, baseEnd_1589053] using wordTrace_append hprefix tailTrace_1589053
  have hstable : (prefixWord ++ tailWord_1589053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589053).length < 2 ^ (prefixWord ++ tailWord_1589053).sum := by decide
  have hdescent : baseEnd_1589053 < baseStart_1589053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589069 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1589069 : Nat := 118140960795 + 1589069 * 2 ^ 59
def prefixEnd_1589069 : Nat := 4983230072969 + 3 ^ 40 * 1589069 * 2
def baseEnd_1589069 : Nat := 815956190159548493929511

theorem tailTrace_1589069 : CollatzResearch.WordTrace tailWord_1589069 prefixEnd_1589069 815956190159548493929511 := by
  unfold tailWord_1589069
  simp only [CollatzResearch.WordTrace]
  refine ⟨57958107880081879223738261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38638738586721252815825507 57958107880081879223738261)
  ·
    refine ⟨2716786306878838088612731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57958107880081879223738261 2716786306878838088612731)
    ·
      refine ⟨4075179460318257132919097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2716786306878838088612731 4075179460318257132919097)
      ·
        refine ⟨3056384595238692849689323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4075179460318257132919097 3056384595238692849689323)
        ·
          refine ⟨4584576892858039274533985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3056384595238692849689323 4584576892858039274533985)
          ·
            refine ⟨3438432669643529455900489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4584576892858039274533985 3438432669643529455900489)
            ·
              refine ⟨2578824502232647091925367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3438432669643529455900489 2578824502232647091925367)
              ·
                refine ⟨3868236753348970637888051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2578824502232647091925367 3868236753348970637888051)
                ·
                  refine ⟨5802355130023455956832077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3868236753348970637888051 5802355130023455956832077)
                  ·
                    refine ⟨2175883173758795983812029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5802355130023455956832077 2175883173758795983812029)
                    ·
                      refine ⟨815956190159548493929511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2175883173758795983812029 815956190159548493929511)
                      ·
                        rfl

theorem cell23_1589069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1589069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589069 prefixEnd_1589069 := by exact prefixLift 1589069
  have htrace : WordTrace (prefixWord ++ tailWord_1589069) baseStart_1589069 baseEnd_1589069 := by
    simpa [prefixWord, tailWord_1589069, baseEnd_1589069] using wordTrace_append hprefix tailTrace_1589069
  have hstable : (prefixWord ++ tailWord_1589069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589069).length < 2 ^ (prefixWord ++ tailWord_1589069).sum := by decide
  have hdescent : baseEnd_1589069 < baseStart_1589069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589109 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_1589109 : Nat := 118140960795 + 1589109 * 2 ^ 59
def prefixEnd_1589109 : Nat := 4983230072969 + 3 ^ 40 * 1589109 * 2
def baseEnd_1589109 : Nat := 815976729385728337429327

theorem tailTrace_1589109 : CollatzResearch.WordTrace tailWord_1589109 prefixEnd_1589109 815976729385728337429327 := by
  unfold tailWord_1589109
  simp only [CollatzResearch.WordTrace]
  refine ⟨57959566799936966055194381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38639711199957977370129587 57959566799936966055194381)
  ·
    refine ⟨21734837549976362270697893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57959566799936966055194381 21734837549976362270697893)
    ·
      refine ⟨4075282040620567925755855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21734837549976362270697893 4075282040620567925755855)
      ·
        refine ⟨6112923060930851888633783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4075282040620567925755855 6112923060930851888633783)
        ·
          refine ⟨9169384591396277832950675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6112923060930851888633783 9169384591396277832950675)
          ·
            refine ⟨13754076887094416749426013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9169384591396277832950675 13754076887094416749426013)
            ·
              refine ⟨5157778832660406281034755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13754076887094416749426013 5157778832660406281034755)
              ·
                refine ⟨7736668248990609421552133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5157778832660406281034755 7736668248990609421552133)
                ·
                  refine ⟨1450625296685739266541025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7736668248990609421552133 1450625296685739266541025)
                  ·
                    refine ⟨1087968972514304449905769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1450625296685739266541025 1087968972514304449905769)
                    ·
                      refine ⟨815976729385728337429327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1087968972514304449905769 815976729385728337429327)
                      ·
                        rfl

theorem cell23_1589109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_1589109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589109 prefixEnd_1589109 := by exact prefixLift 1589109
  have htrace : WordTrace (prefixWord ++ tailWord_1589109) baseStart_1589109 baseEnd_1589109 := by
    simpa [prefixWord, tailWord_1589109, baseEnd_1589109] using wordTrace_append hprefix tailTrace_1589109
  have hstable : (prefixWord ++ tailWord_1589109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589109).length < 2 ^ (prefixWord ++ tailWord_1589109).sum := by decide
  have hdescent : baseEnd_1589109 < baseStart_1589109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589125 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 2, 3, 3]
def baseStart_1589125 : Nat := 118140960795 + 1589125 * 2 ^ 59
def prefixEnd_1589125 : Nat := 4983230072969 + 3 ^ 40 * 1589125 * 2
def baseEnd_1589125 : Nat := 815984945076200274829253

theorem tailTrace_1589125 : CollatzResearch.WordTrace tailWord_1589125 prefixEnd_1589125 815984945076200274829253 := by
  unfold tailWord_1589125
  simp only [CollatzResearch.WordTrace]
  refine ⟨57960150367879000787776829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38640100245252667191851219 57960150367879000787776829)
  ·
    refine ⟨21735056387954625295416311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57960150367879000787776829 21735056387954625295416311)
    ·
      refine ⟨32602584581931937943124467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21735056387954625295416311 32602584581931937943124467)
      ·
        refine ⟨48903876872897906914686701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32602584581931937943124467 48903876872897906914686701)
        ·
          refine ⟨18338953827336715093007513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48903876872897906914686701 18338953827336715093007513)
          ·
            refine ⟨13754215370502536319755635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18338953827336715093007513 13754215370502536319755635)
            ·
              refine ⟨20631323055753804479633453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13754215370502536319755635 20631323055753804479633453)
              ·
                refine ⟨7736746145907676679862545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20631323055753804479633453 7736746145907676679862545)
                ·
                  refine ⟨5802559609430757509896909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7736746145907676679862545 5802559609430757509896909)
                  ·
                    refine ⟨2175959853536534066211341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5802559609430757509896909 2175959853536534066211341)
                    ·
                      refine ⟨815984945076200274829253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2175959853536534066211341 815984945076200274829253)
                      ·
                        rfl

theorem cell23_1589125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_1589125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589125 prefixEnd_1589125 := by exact prefixLift 1589125
  have htrace : WordTrace (prefixWord ++ tailWord_1589125) baseStart_1589125 baseEnd_1589125 := by
    simpa [prefixWord, tailWord_1589125, baseEnd_1589125] using wordTrace_append hprefix tailTrace_1589125
  have hstable : (prefixWord ++ tailWord_1589125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589125).length < 2 ^ (prefixWord ++ tailWord_1589125).sum := by decide
  have hdescent : baseEnd_1589125 < baseStart_1589125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589135 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 5, 7, 2]
def baseStart_1589135 : Nat := 118140960795 + 1589135 * 2 ^ 59
def prefixEnd_1589135 : Nat := 4983230072969 + 3 ^ 40 * 1589135 * 2
def baseEnd_1589135 : Nat := 815990079882745235704207

theorem tailTrace_1589135 : CollatzResearch.WordTrace tailWord_1589135 prefixEnd_1589135 815990079882745235704207 := by
  unfold tailWord_1589135
  simp only [CollatzResearch.WordTrace]
  refine ⟨57960515097842772495640859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38640343398561848330427239 57960515097842772495640859)
  ·
    refine ⟨86940772646764158743461289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57960515097842772495640859 86940772646764158743461289)
    ·
      refine ⟨65205579485073119057595967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86940772646764158743461289 65205579485073119057595967)
      ·
        refine ⟨97808369227609678586393951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65205579485073119057595967 97808369227609678586393951)
        ·
          refine ⟨146712553841414517879590927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97808369227609678586393951 146712553841414517879590927)
          ·
            refine ⟨220068830762121776819386391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146712553841414517879590927 220068830762121776819386391)
            ·
              refine ⟨330103246143182665229079587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220068830762121776819386391 330103246143182665229079587)
              ·
                refine ⟨495154869214773997843619381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330103246143182665229079587 495154869214773997843619381)
                ·
                  refine ⟨46420768988885062297839317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 495154869214773997843619381 46420768988885062297839317)
                  ·
                    refine ⟨1087986773176993647605609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46420768988885062297839317 1087986773176993647605609)
                    ·
                      refine ⟨815990079882745235704207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1087986773176993647605609 815990079882745235704207)
                      ·
                        rfl

theorem cell23_1589135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 7, 2].length) (baseStart_1589135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589135 prefixEnd_1589135 := by exact prefixLift 1589135
  have htrace : WordTrace (prefixWord ++ tailWord_1589135) baseStart_1589135 baseEnd_1589135 := by
    simpa [prefixWord, tailWord_1589135, baseEnd_1589135] using wordTrace_append hprefix tailTrace_1589135
  have hstable : (prefixWord ++ tailWord_1589135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589135).length < 2 ^ (prefixWord ++ tailWord_1589135).sum := by decide
  have hdescent : baseEnd_1589135 < baseStart_1589135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589149 : List Nat := [1, 4, 2, 1, 2, 4, 1, 3, 5]
def baseStart_1589149 : Nat := 118140960795 + 1589149 * 2 ^ 59
def prefixEnd_1589149 : Nat := 4983230072969 + 3 ^ 40 * 1589149 * 2
def baseEnd_1589149 : Nat := 90666363179100908992127

theorem tailTrace_1589149 : CollatzResearch.WordTrace tailWord_1589149 prefixEnd_1589149 90666363179100908992127 := by
  unfold tailWord_1589149
  simp only [CollatzResearch.WordTrace]
  refine ⟨57961025719792052886650501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38640683813194701924433667 57961025719792052886650501)
  ·
    refine ⟨10867692322461009916246969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57961025719792052886650501 10867692322461009916246969)
    ·
      refine ⟨8150769241845757437185227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10867692322461009916246969 8150769241845757437185227)
      ·
        refine ⟨12226153862768636155777841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8150769241845757437185227 12226153862768636155777841)
        ·
          refine ⟨9169615397076477116833381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12226153862768636155777841 9169615397076477116833381)
          ·
            refine ⟨1719302886951839459406259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9169615397076477116833381 1719302886951839459406259)
            ·
              refine ⟨2578954330427759189109389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1719302886951839459406259 2578954330427759189109389)
              ·
                refine ⟨967107873910409695916021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2578954330427759189109389 967107873910409695916021)
                ·
                  refine ⟨90666363179100908992127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 967107873910409695916021 90666363179100908992127)
                  ·
                    rfl

theorem cell23_1589149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_1589149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589149 prefixEnd_1589149 := by exact prefixLift 1589149
  have htrace : WordTrace (prefixWord ++ tailWord_1589149) baseStart_1589149 baseEnd_1589149 := by
    simpa [prefixWord, tailWord_1589149, baseEnd_1589149] using wordTrace_append hprefix tailTrace_1589149
  have hstable : (prefixWord ++ tailWord_1589149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589149).length < 2 ^ (prefixWord ++ tailWord_1589149).sum := by decide
  have hdescent : baseEnd_1589149 < baseStart_1589149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589249 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_1589249 : Nat := 118140960795 + 1589249 * 2 ^ 59
def prefixEnd_1589249 : Nat := 4983230072969 + 3 ^ 40 * 1589249 * 2
def baseEnd_1589249 : Nat := 816048616677357789678683

theorem tailTrace_1589249 : CollatzResearch.WordTrace tailWord_1589249 prefixEnd_1589249 816048616677357789678683 := by
  unfold tailWord_1589249
  simp only [CollatzResearch.WordTrace]
  refine ⟨57964673019429769965290801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38643115346286513310193867 57964673019429769965290801)
  ·
    refine ⟨43473504764572327473968101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57964673019429769965290801 43473504764572327473968101)
    ·
      refine ⟨8151282143357311401369019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43473504764572327473968101 8151282143357311401369019)
      ·
        refine ⟨12226923215035967102053529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8151282143357311401369019 12226923215035967102053529)
        ·
          refine ⟨9170192411276975326540147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12226923215035967102053529 9170192411276975326540147)
          ·
            refine ⟨13755288616915462989810221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9170192411276975326540147 13755288616915462989810221)
            ·
              refine ⟨5158233231343298621178833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13755288616915462989810221 5158233231343298621178833)
              ·
                refine ⟨3868674923507473965884125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5158233231343298621178833 3868674923507473965884125)
                ·
                  refine ⟨1450753096315302737206547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3868674923507473965884125 1450753096315302737206547)
                  ·
                    refine ⟨2176129644472954105809821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1450753096315302737206547 2176129644472954105809821)
                    ·
                      refine ⟨816048616677357789678683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2176129644472954105809821 816048616677357789678683)
                      ·
                        rfl

theorem cell23_1589249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_1589249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589249 prefixEnd_1589249 := by exact prefixLift 1589249
  have htrace : WordTrace (prefixWord ++ tailWord_1589249) baseStart_1589249 baseEnd_1589249 := by
    simpa [prefixWord, tailWord_1589249, baseEnd_1589249] using wordTrace_append hprefix tailTrace_1589249
  have hstable : (prefixWord ++ tailWord_1589249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589249).length < 2 ^ (prefixWord ++ tailWord_1589249).sum := by decide
  have hdescent : baseEnd_1589249 < baseStart_1589249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589269 : List Nat := [1, 3, 2, 1, 5, 1, 1, 3, 1, 5]
def baseStart_1589269 : Nat := 118140960795 + 1589269 * 2 ^ 59
def prefixEnd_1589269 : Nat := 4983230072969 + 3 ^ 40 * 1589269 * 2
def baseEnd_1589269 : Nat := 272019628763482570476197

theorem tailTrace_1589269 : CollatzResearch.WordTrace tailWord_1589269 prefixEnd_1589269 272019628763482570476197 := by
  unfold tailWord_1589269
  simp only [CollatzResearch.WordTrace]
  refine ⟨57965402479357313381018861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38643601652904875587345907 57965402479357313381018861)
  ·
    refine ⟨21737025929758992517882073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57965402479357313381018861 21737025929758992517882073)
    ·
      refine ⟨16302769447319244388411555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21737025929758992517882073 16302769447319244388411555)
      ·
        refine ⟨24454154170978866582617333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16302769447319244388411555 24454154170978866582617333)
        ·
          refine ⟨2292576953529268742120375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24454154170978866582617333 2292576953529268742120375)
          ·
            refine ⟨3438865430293903113180563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2292576953529268742120375 3438865430293903113180563)
            ·
              refine ⟨5158298145440854669770845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3438865430293903113180563 5158298145440854669770845)
              ·
                refine ⟨1934361804540320501164067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5158298145440854669770845 1934361804540320501164067)
                ·
                  refine ⟨2901542706810480751746101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934361804540320501164067 2901542706810480751746101)
                  ·
                    refine ⟨272019628763482570476197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2901542706810480751746101 272019628763482570476197)
                    ·
                      rfl

theorem cell23_1589269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_1589269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589269 prefixEnd_1589269 := by exact prefixLift 1589269
  have htrace : WordTrace (prefixWord ++ tailWord_1589269) baseStart_1589269 baseEnd_1589269 := by
    simpa [prefixWord, tailWord_1589269, baseEnd_1589269] using wordTrace_append hprefix tailTrace_1589269
  have hstable : (prefixWord ++ tailWord_1589269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589269).length < 2 ^ (prefixWord ++ tailWord_1589269).sum := by decide
  have hdescent : baseEnd_1589269 < baseStart_1589269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589292 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 3]
def baseStart_1589292 : Nat := 118140960795 + 1589292 * 2 ^ 59
def prefixEnd_1589292 : Nat := 4983230072969 + 3 ^ 40 * 1589292 * 2
def baseEnd_1589292 : Nat := 816070696345501121440985

theorem tailTrace_1589292 : CollatzResearch.WordTrace tailWord_1589292 prefixEnd_1589292 816070696345501121440985 := by
  unfold tailWord_1589292
  simp only [CollatzResearch.WordTrace]
  refine ⟨28983120679136994154553065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38644160905515992206070753 28983120679136994154553065)
  ·
    refine ⟨21737340509352745615914799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28983120679136994154553065 21737340509352745615914799)
    ·
      refine ⟨32606010764029118423872199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21737340509352745615914799 32606010764029118423872199)
      ·
        refine ⟨48909016146043677635808299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32606010764029118423872199 48909016146043677635808299)
        ·
          refine ⟨73363524219065516453712449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48909016146043677635808299 73363524219065516453712449)
          ·
            refine ⟨55022643164299137340284337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73363524219065516453712449 55022643164299137340284337)
            ·
              refine ⟨41266982373224353005213253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55022643164299137340284337 41266982373224353005213253)
              ·
                refine ⟨7737559194979566188477485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41266982373224353005213253 7737559194979566188477485)
                ·
                  refine ⟨2901584698117337320679057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7737559194979566188477485 2901584698117337320679057)
                  ·
                    refine ⟨2176188523588002990509293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2901584698117337320679057 2176188523588002990509293)
                    ·
                      refine ⟨816070696345501121440985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2176188523588002990509293 816070696345501121440985)
                      ·
                        rfl

theorem cell23_1589292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_1589292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589292 prefixEnd_1589292 := by exact prefixLift 1589292
  have htrace : WordTrace (prefixWord ++ tailWord_1589292) baseStart_1589292 baseEnd_1589292 := by
    simpa [prefixWord, tailWord_1589292, baseEnd_1589292] using wordTrace_append hprefix tailTrace_1589292
  have hstable : (prefixWord ++ tailWord_1589292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589292).length < 2 ^ (prefixWord ++ tailWord_1589292).sum := by decide
  have hdescent : baseEnd_1589292 < baseStart_1589292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589312 : List Nat := [2, 1, 1, 2, 2, 4, 4, 7]
def baseStart_1589312 : Nat := 118140960795 + 1589312 * 2 ^ 59
def prefixEnd_1589312 : Nat := 4983230072969 + 3 ^ 40 * 1589312 * 2
def baseEnd_1589312 : Nat := 30225220961429297895959

theorem tailTrace_1589312 : CollatzResearch.WordTrace tailWord_1589312 prefixEnd_1589312 30225220961429297895959 := by
  unfold tailWord_1589312
  simp only [CollatzResearch.WordTrace]
  refine ⟨28983485409100765862417095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38644647212134354483222793 28983485409100765862417095)
  ·
    refine ⟨43475228113651148793625643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28983485409100765862417095 43475228113651148793625643)
    ·
      refine ⟨65212842170476723190438465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43475228113651148793625643 65212842170476723190438465)
      ·
        refine ⟨48909631627857542392828849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65212842170476723190438465 48909631627857542392828849)
        ·
          refine ⟨36682223720893156794621637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48909631627857542392828849 36682223720893156794621637)
          ·
            refine ⟨6877916947667466898991557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36682223720893156794621637 6877916947667466898991557)
            ·
              refine ⟨1289609427687650043560917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6877916947667466898991557 1289609427687650043560917)
              ·
                refine ⟨30225220961429297895959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1289609427687650043560917 30225220961429297895959)
                ·
                  rfl

theorem cell23_1589312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 7].length) (baseStart_1589312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589312 prefixEnd_1589312 := by exact prefixLift 1589312
  have htrace : WordTrace (prefixWord ++ tailWord_1589312) baseStart_1589312 baseEnd_1589312 := by
    simpa [prefixWord, tailWord_1589312, baseEnd_1589312] using wordTrace_append hprefix tailTrace_1589312
  have hstable : (prefixWord ++ tailWord_1589312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589312).length < 2 ^ (prefixWord ++ tailWord_1589312).sum := by decide
  have hdescent : baseEnd_1589312 < baseStart_1589312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589322 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_1589322 : Nat := 118140960795 + 1589322 * 2 ^ 59
def prefixEnd_1589322 : Nat := 4983230072969 + 3 ^ 40 * 1589322 * 2
def baseEnd_1589322 : Nat := 816086100765136004065847

theorem tailTrace_1589322 : CollatzResearch.WordTrace tailWord_1589322 prefixEnd_1589322 816086100765136004065847 := by
  unfold tailWord_1589322
  simp only [CollatzResearch.WordTrace]
  refine ⟨14491833887041325858174555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38644890365443535621798813 14491833887041325858174555)
  ·
    refine ⟨21737750830561988787261833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14491833887041325858174555 21737750830561988787261833)
    ·
      refine ⟨16303313122921491590446375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21737750830561988787261833 16303313122921491590446375)
      ·
        refine ⟨24454969684382237385669563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16303313122921491590446375 24454969684382237385669563)
        ·
          refine ⟨36682454526573356078504345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24454969684382237385669563 36682454526573356078504345)
          ·
            refine ⟨27511840894930017058878259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36682454526573356078504345 27511840894930017058878259)
            ·
              refine ⟨41267761342395025588317389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27511840894930017058878259 41267761342395025588317389)
              ·
                refine ⟨15475410503398134595619021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41267761342395025588317389 15475410503398134595619021)
                ·
                  refine ⟨5803278938774300473357133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15475410503398134595619021 5803278938774300473357133)
                  ·
                    refine ⟨2176229602040362677508925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5803278938774300473357133 2176229602040362677508925)
                    ·
                      refine ⟨816086100765136004065847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2176229602040362677508925 816086100765136004065847)
                      ·
                        rfl

theorem cell23_1589322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_1589322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589322 prefixEnd_1589322 := by exact prefixLift 1589322
  have htrace : WordTrace (prefixWord ++ tailWord_1589322) baseStart_1589322 baseEnd_1589322 := by
    simpa [prefixWord, tailWord_1589322, baseEnd_1589322] using wordTrace_append hprefix tailTrace_1589322
  have hstable : (prefixWord ++ tailWord_1589322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589322).length < 2 ^ (prefixWord ++ tailWord_1589322).sum := by decide
  have hdescent : baseEnd_1589322 < baseStart_1589322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589356 : List Nat := [2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 3]
def baseStart_1589356 : Nat := 118140960795 + 1589356 * 2 ^ 59
def prefixEnd_1589356 : Nat := 4983230072969 + 3 ^ 40 * 1589356 * 2
def baseEnd_1589356 : Nat := 816103559107388871040691

theorem tailTrace_1589356 : CollatzResearch.WordTrace tailWord_1589356 prefixEnd_1589356 816103559107388871040691 := by
  unfold tailWord_1589356
  simp only [CollatzResearch.WordTrace]
  refine ⟨28984287815021063619717961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38645717086694751492957281 28984287815021063619717961)
  ·
    refine ⟨21738215861265797714788471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28984287815021063619717961 21738215861265797714788471)
    ·
      refine ⟨32607323791898696572182707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21738215861265797714788471 32607323791898696572182707)
      ·
        refine ⟨48910985687848044858274061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32607323791898696572182707 48910985687848044858274061)
        ·
          refine ⟨18341619632943016821852773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48910985687848044858274061 18341619632943016821852773)
          ·
            refine ⟨3439053681176815654097395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18341619632943016821852773 3439053681176815654097395)
            ·
              refine ⟨5158580521765223481146093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3439053681176815654097395 5158580521765223481146093)
              ·
                refine ⟨1934467695661958805429785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5158580521765223481146093 1934467695661958805429785)
                ·
                  refine ⟨1450850771746469104072339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1934467695661958805429785 1450850771746469104072339)
                  ·
                    refine ⟨2176276157619703656108509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1450850771746469104072339 2176276157619703656108509)
                    ·
                      refine ⟨816103559107388871040691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2176276157619703656108509 816103559107388871040691)
                      ·
                        rfl

theorem cell23_1589356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_1589356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589356 prefixEnd_1589356 := by exact prefixLift 1589356
  have htrace : WordTrace (prefixWord ++ tailWord_1589356) baseStart_1589356 baseEnd_1589356 := by
    simpa [prefixWord, tailWord_1589356, baseEnd_1589356] using wordTrace_append hprefix tailTrace_1589356
  have hstable : (prefixWord ++ tailWord_1589356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589356).length < 2 ^ (prefixWord ++ tailWord_1589356).sum := by decide
  have hdescent : baseEnd_1589356 < baseStart_1589356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589379 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 3, 4, 2]
def baseStart_1589379 : Nat := 118140960795 + 1589379 * 2 ^ 59
def prefixEnd_1589379 : Nat := 4983230072969 + 3 ^ 40 * 1589379 * 2
def baseEnd_1589379 : Nat := 816115369162442281053085

theorem tailTrace_1589379 : CollatzResearch.WordTrace tailWord_1589379 prefixEnd_1589379 816115369162442281053085 := by
  unfold tailWord_1589379
  simp only [CollatzResearch.WordTrace]
  refine ⟨57969414508958802167523191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38646276339305868111682127 57969414508958802167523191)
  ·
    refine ⟨86954121763438203251284787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57969414508958802167523191 86954121763438203251284787)
    ·
      refine ⟨130431182645157304876927181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86954121763438203251284787 130431182645157304876927181)
      ·
        refine ⟨48911693491933989328847693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130431182645157304876927181 48911693491933989328847693)
        ·
          refine ⟨18341885059475245998317885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48911693491933989328847693 18341885059475245998317885)
          ·
            refine ⟨6878206897303217249369207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18341885059475245998317885 6878206897303217249369207)
            ·
              refine ⟨10317310345954825874053811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6878206897303217249369207 10317310345954825874053811)
              ·
                refine ⟨15475965518932238811080717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10317310345954825874053811 15475965518932238811080717)
                ·
                  refine ⟨5803487069599589554155269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15475965518932238811080717 5803487069599589554155269)
                  ·
                    refine ⟨1088153825549923041404113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5803487069599589554155269 1088153825549923041404113)
                    ·
                      refine ⟨816115369162442281053085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1088153825549923041404113 816115369162442281053085)
                      ·
                        rfl

theorem cell23_1589379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 4, 2].length) (baseStart_1589379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589379 prefixEnd_1589379 := by exact prefixLift 1589379
  have htrace : WordTrace (prefixWord ++ tailWord_1589379) baseStart_1589379 baseEnd_1589379 := by
    simpa [prefixWord, tailWord_1589379, baseEnd_1589379] using wordTrace_append hprefix tailTrace_1589379
  have hstable : (prefixWord ++ tailWord_1589379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589379).length < 2 ^ (prefixWord ++ tailWord_1589379).sum := by decide
  have hdescent : baseEnd_1589379 < baseStart_1589379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589392 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 4]
def baseStart_1589392 : Nat := 118140960795 + 1589392 * 2 ^ 59
def prefixEnd_1589392 : Nat := 4983230072969 + 3 ^ 40 * 1589392 * 2
def baseEnd_1589392 : Nat := 816122044410950730190525

theorem tailTrace_1589392 : CollatzResearch.WordTrace tailWord_1589392 prefixEnd_1589392 816122044410950730190525 := by
  unfold tailWord_1589392
  simp only [CollatzResearch.WordTrace]
  refine ⟨28984944328955852693873215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38646592438607803591830953 28984944328955852693873215)
  ·
    refine ⟨43477416493433779040809823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28984944328955852693873215 43477416493433779040809823)
    ·
      refine ⟨65216124740150668561214735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43477416493433779040809823 65216124740150668561214735)
      ·
        refine ⟨97824187110226002841822103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65216124740150668561214735 97824187110226002841822103)
        ·
          refine ⟨146736280665339004262733155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97824187110226002841822103 146736280665339004262733155)
          ·
            refine ⟨220104420998008506394099733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146736280665339004262733155 220104420998008506394099733)
            ·
              refine ⟨10317394734281648737223425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220104420998008506394099733 10317394734281648737223425)
              ·
                refine ⟨7738046050711236552917569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10317394734281648737223425 7738046050711236552917569)
                ·
                  refine ⟨5803534538033427414688177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7738046050711236552917569 5803534538033427414688177)
                  ·
                    refine ⟨4352650903525070561016133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5803534538033427414688177 4352650903525070561016133)
                    ·
                      refine ⟨816122044410950730190525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4352650903525070561016133 816122044410950730190525)
                      ·
                        rfl

theorem cell23_1589392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_1589392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589392 prefixEnd_1589392 := by exact prefixLift 1589392
  have htrace : WordTrace (prefixWord ++ tailWord_1589392) baseStart_1589392 baseEnd_1589392 := by
    simpa [prefixWord, tailWord_1589392, baseEnd_1589392] using wordTrace_append hprefix tailTrace_1589392
  have hstable : (prefixWord ++ tailWord_1589392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589392).length < 2 ^ (prefixWord ++ tailWord_1589392).sum := by decide
  have hdescent : baseEnd_1589392 < baseStart_1589392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589406 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1589406 : Nat := 118140960795 + 1589406 * 2 ^ 59
def prefixEnd_1589406 : Nat := 4983230072969 + 3 ^ 40 * 1589406 * 2
def baseEnd_1589406 : Nat := 272043077713371225138487

theorem tailTrace_1589406 : CollatzResearch.WordTrace tailWord_1589406 prefixEnd_1589406 272043077713371225138487 := by
  unfold tailWord_1589406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7246299909982623222344509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38646932853240657185837381 7246299909982623222344509)
  ·
    refine ⟨2717362466243483708379191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7246299909982623222344509 2717362466243483708379191)
    ·
      refine ⟨4076043699365225562568787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2717362466243483708379191 4076043699365225562568787)
      ·
        refine ⟨6114065549047838343853181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4076043699365225562568787 6114065549047838343853181)
        ·
          refine ⟨2292774580892939378944943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6114065549047838343853181 2292774580892939378944943)
          ·
            refine ⟨3439161871339409068417415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2292774580892939378944943 3439161871339409068417415)
            ·
              refine ⟨5158742807009113602626123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3439161871339409068417415 5158742807009113602626123)
              ·
                refine ⟨7738114210513670403939185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5158742807009113602626123 7738114210513670403939185)
                ·
                  refine ⟨5803585657885252802954389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7738114210513670403939185 5803585657885252802954389)
                  ·
                    refine ⟨272043077713371225138487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5803585657885252802954389 272043077713371225138487)
                    ·
                      rfl

theorem cell23_1589406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1589406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589406 prefixEnd_1589406 := by exact prefixLift 1589406
  have htrace : WordTrace (prefixWord ++ tailWord_1589406) baseStart_1589406 baseEnd_1589406 := by
    simpa [prefixWord, tailWord_1589406, baseEnd_1589406] using wordTrace_append hprefix tailTrace_1589406
  have hstable : (prefixWord ++ tailWord_1589406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589406).length < 2 ^ (prefixWord ++ tailWord_1589406).sum := by decide
  have hdescent : baseEnd_1589406 < baseStart_1589406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589409 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1589409 : Nat := 118140960795 + 1589409 * 2 ^ 59
def prefixEnd_1589409 : Nat := 4983230072969 + 3 ^ 40 * 1589409 * 2
def baseEnd_1589409 : Nat := 816130773582077163677947

theorem tailTrace_1589409 : CollatzResearch.WordTrace tailWord_1589409 prefixEnd_1589409 816130773582077163677947 := by
  unfold tailWord_1589409
  simp only [CollatzResearch.WordTrace]
  refine ⟨57970508698850117291115281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38647005799233411527410187 57970508698850117291115281)
  ·
    refine ⟨43477881524137587968336461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57970508698850117291115281 43477881524137587968336461)
    ·
      refine ⟨16304205571551595488126173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43477881524137587968336461 16304205571551595488126173)
      ·
        refine ⟨6114077089331848308047315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16304205571551595488126173 6114077089331848308047315)
        ·
          refine ⟨9171115633997772462070973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6114077089331848308047315 9171115633997772462070973)
          ·
            refine ⟨3439168362749164673276615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9171115633997772462070973 3439168362749164673276615)
            ·
              refine ⟨5158752544123747009914923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3439168362749164673276615 5158752544123747009914923)
              ·
                refine ⟨7738128816185620514872385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5158752544123747009914923 7738128816185620514872385)
                ·
                  refine ⟨5803596612139215386154289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7738128816185620514872385 5803596612139215386154289)
                  ·
                    refine ⟨4352697459104411539615717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5803596612139215386154289 4352697459104411539615717)
                    ·
                      refine ⟨816130773582077163677947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4352697459104411539615717 816130773582077163677947)
                      ·
                        rfl

theorem cell23_1589409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1589409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589409 prefixEnd_1589409 := by exact prefixLift 1589409
  have htrace : WordTrace (prefixWord ++ tailWord_1589409) baseStart_1589409 baseEnd_1589409 := by
    simpa [prefixWord, tailWord_1589409, baseEnd_1589409] using wordTrace_append hprefix tailTrace_1589409
  have hstable : (prefixWord ++ tailWord_1589409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589409).length < 2 ^ (prefixWord ++ tailWord_1589409).sum := by decide
  have hdescent : baseEnd_1589409 < baseStart_1589409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589432 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 1, 7]
def baseStart_1589432 : Nat := 118140960795 + 1589432 * 2 ^ 59
def prefixEnd_1589432 : Nat := 4983230072969 + 3 ^ 40 * 1589432 * 2
def baseEnd_1589432 : Nat := 272047527879043524563447

theorem tailTrace_1589432 : CollatzResearch.WordTrace tailWord_1589432 prefixEnd_1589432 272047527879043524563447 := by
  unfold tailWord_1589432
  simp only [CollatzResearch.WordTrace]
  refine ⟨28985673788883396109601275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38647565051844528146135033 28985673788883396109601275)
  ·
    refine ⟨43478510683325094164401913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28985673788883396109601275 43478510683325094164401913)
    ·
      refine ⟨32608883012493820623301435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43478510683325094164401913 32608883012493820623301435)
      ·
        refine ⟨48913324518740730934952153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32608883012493820623301435 48913324518740730934952153)
        ·
          refine ⟨36684993389055548201214115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48913324518740730934952153 36684993389055548201214115)
          ·
            refine ⟨55027490083583322301821173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36684993389055548201214115 55027490083583322301821173)
            ·
              refine ⟨5158827195335936465795735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55027490083583322301821173 5158827195335936465795735)
              ·
                refine ⟨7738240793003904698693603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5158827195335936465795735 7738240793003904698693603)
                ·
                  refine ⟨11607361189505857048040405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7738240793003904698693603 11607361189505857048040405)
                  ·
                    refine ⟨272047527879043524563447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11607361189505857048040405 272047527879043524563447)
                    ·
                      rfl

theorem cell23_1589432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_1589432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589432 prefixEnd_1589432 := by exact prefixLift 1589432
  have htrace : WordTrace (prefixWord ++ tailWord_1589432) baseStart_1589432 baseEnd_1589432 := by
    simpa [prefixWord, tailWord_1589432, baseEnd_1589432] using wordTrace_append hprefix tailTrace_1589432
  have hstable : (prefixWord ++ tailWord_1589432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589432).length < 2 ^ (prefixWord ++ tailWord_1589432).sum := by decide
  have hdescent : baseEnd_1589432 < baseStart_1589432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589489 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 1, 4, 3]
def baseStart_1589489 : Nat := 118140960795 + 1589489 * 2 ^ 59
def prefixEnd_1589489 : Nat := 4983230072969 + 3 ^ 40 * 1589489 * 2
def baseEnd_1589489 : Nat := 816171852034436850677579

theorem tailTrace_1589489 : CollatzResearch.WordTrace tailWord_1589489 prefixEnd_1589489 816171852034436850677579 := by
  unfold tailWord_1589489
  simp only [CollatzResearch.WordTrace]
  refine ⟨57973426538560290954027521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38648951025706860636018347 57973426538560290954027521)
  ·
    refine ⟨43480069903920218215520641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57973426538560290954027521 43480069903920218215520641)
    ·
      refine ⟨32610052427940163661640481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43480069903920218215520641 32610052427940163661640481)
      ·
        refine ⟨24457539320955122746230361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32610052427940163661640481 24457539320955122746230361)
        ·
          refine ⟨18343154490716342059672771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24457539320955122746230361 18343154490716342059672771)
          ·
            refine ⟨27514731736074513089509157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18343154490716342059672771 27514731736074513089509157)
            ·
              refine ⟨5159012200513971204282967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27514731736074513089509157 5159012200513971204282967)
              ·
                refine ⟨7738518300770956806424451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5159012200513971204282967 7738518300770956806424451)
                ·
                  refine ⟨11607777451156435209636677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7738518300770956806424451 11607777451156435209636677)
                  ·
                    refine ⟨2176458272091831601806877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11607777451156435209636677 2176458272091831601806877)
                    ·
                      refine ⟨816171852034436850677579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2176458272091831601806877 816171852034436850677579)
                      ·
                        rfl

theorem cell23_1589489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_1589489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589489 prefixEnd_1589489 := by exact prefixLift 1589489
  have htrace : WordTrace (prefixWord ++ tailWord_1589489) baseStart_1589489 baseEnd_1589489 := by
    simpa [prefixWord, tailWord_1589489, baseEnd_1589489] using wordTrace_append hprefix tailTrace_1589489
  have hstable : (prefixWord ++ tailWord_1589489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589489).length < 2 ^ (prefixWord ++ tailWord_1589489).sum := by decide
  have hdescent : baseEnd_1589489 < baseStart_1589489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589539 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 3, 5]
def baseStart_1589539 : Nat := 118140960795 + 1589539 * 2 ^ 59
def prefixEnd_1589539 : Nat := 4983230072969 + 3 ^ 40 * 1589539 * 2
def baseEnd_1589539 : Nat := 272065842022387218350783

theorem tailTrace_1589539 : CollatzResearch.WordTrace tailWord_1589539 prefixEnd_1589539 272065842022387218350783 := by
  unfold tailWord_1589539
  simp only [CollatzResearch.WordTrace]
  refine ⟨57975250188379149493347671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38650166792252766328898447 57975250188379149493347671)
  ·
    refine ⟨86962875282568724240021507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57975250188379149493347671 86962875282568724240021507)
    ·
      refine ⟨130444312923853086360032261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86962875282568724240021507 130444312923853086360032261)
      ·
        refine ⟨24458308673222453692506049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130444312923853086360032261 24458308673222453692506049)
        ·
          refine ⟨18343731504916840269379537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24458308673222453692506049 18343731504916840269379537)
          ·
            refine ⟨13757798628687630202034653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18343731504916840269379537 13757798628687630202034653)
            ·
              refine ⟨5159174485757861325762995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13757798628687630202034653 5159174485757861325762995)
              ·
                refine ⟨7738761728636791988644493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5159174485757861325762995 7738761728636791988644493)
                ·
                  refine ⟨2902035648238796995741685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7738761728636791988644493 2902035648238796995741685)
                  ·
                    refine ⟨272065842022387218350783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2902035648238796995741685 272065842022387218350783)
                    ·
                      rfl

theorem cell23_1589539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 5].length) (baseStart_1589539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589539 prefixEnd_1589539 := by exact prefixLift 1589539
  have htrace : WordTrace (prefixWord ++ tailWord_1589539) baseStart_1589539 baseEnd_1589539 := by
    simpa [prefixWord, tailWord_1589539, baseEnd_1589539] using wordTrace_append hprefix tailTrace_1589539
  have hstable : (prefixWord ++ tailWord_1589539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589539).length < 2 ^ (prefixWord ++ tailWord_1589539).sum := by decide
  have hdescent : baseEnd_1589539 < baseStart_1589539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589610 : List Nat := [3, 1, 3, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_1589610 : Nat := 118140960795 + 1589610 * 2 ^ 59
def prefixEnd_1589610 : Nat := 4983230072969 + 3 ^ 40 * 1589610 * 2
def baseEnd_1589610 : Nat := 816233983193630877264523

theorem tailTrace_1589610 : CollatzResearch.WordTrace tailWord_1589610 prefixEnd_1589610 816233983193630877264523 := by
  unfold tailWord_1589610
  simp only [CollatzResearch.WordTrace]
  refine ⟨14494459942780482154795571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38651893180747952412788189 14494459942780482154795571)
  ·
    refine ⟨21741689914170723232193357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14494459942780482154795571 21741689914170723232193357)
    ·
      refine ⟨8153133717814021212072509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21741689914170723232193357 8153133717814021212072509)
      ·
        refine ⟨3057425144180257954527191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8153133717814021212072509 3057425144180257954527191)
        ·
          refine ⟨4586137716270386931790787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3057425144180257954527191 4586137716270386931790787)
          ·
            refine ⟨6879206574405580397686181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4586137716270386931790787 6879206574405580397686181)
            ·
              refine ⟨1289851232701046324566159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6879206574405580397686181 1289851232701046324566159)
              ·
                refine ⟨1934776849051569486849239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289851232701046324566159 1934776849051569486849239)
                ·
                  refine ⟨2902165273577354230273859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934776849051569486849239 2902165273577354230273859)
                  ·
                    refine ⟨4353247910366031345410789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2902165273577354230273859 4353247910366031345410789)
                    ·
                      refine ⟨816233983193630877264523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4353247910366031345410789 816233983193630877264523)
                      ·
                        rfl

theorem cell23_1589610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_1589610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589610 prefixEnd_1589610 := by exact prefixLift 1589610
  have htrace : WordTrace (prefixWord ++ tailWord_1589610) baseStart_1589610 baseEnd_1589610 := by
    simpa [prefixWord, tailWord_1589610, baseEnd_1589610] using wordTrace_append hprefix tailTrace_1589610
  have hstable : (prefixWord ++ tailWord_1589610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589610).length < 2 ^ (prefixWord ++ tailWord_1589610).sum := by decide
  have hdescent : baseEnd_1589610 < baseStart_1589610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589613 : List Nat := [1, 5, 1, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_1589613 : Nat := 118140960795 + 1589613 * 2 ^ 59
def prefixEnd_1589613 : Nat := 4983230072969 + 3 ^ 40 * 1589613 * 2
def baseEnd_1589613 : Nat := 816235523635594365527009

theorem tailTrace_1589613 : CollatzResearch.WordTrace tailWord_1589613 prefixEnd_1589613 816235523635594365527009 := by
  unfold tailWord_1589613
  simp only [CollatzResearch.WordTrace]
  refine ⟨57977949190111060131541493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38651966126740706754360995 57977949190111060131541493)
  ·
    refine ⟨5435432736572911887332015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57977949190111060131541493 5435432736572911887332015)
    ·
      refine ⟨8153149104859367830998023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5435432736572911887332015 8153149104859367830998023)
      ·
        refine ⟨12229723657289051746497035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8153149104859367830998023 12229723657289051746497035)
        ·
          refine ⟨18344585485933577619745553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12229723657289051746497035 18344585485933577619745553)
          ·
            refine ⟨13758439114450183214809165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18344585485933577619745553 13758439114450183214809165)
            ·
              refine ⟨5159414667918818705553437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13758439114450183214809165 5159414667918818705553437)
              ·
                refine ⟨1934780500469557014582539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5159414667918818705553437 1934780500469557014582539)
                ·
                  refine ⟨2902170750704335521873809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934780500469557014582539 2902170750704335521873809)
                  ·
                    refine ⟨2176628063028251641405357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2902170750704335521873809 2176628063028251641405357)
                    ·
                      refine ⟨816235523635594365527009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2176628063028251641405357 816235523635594365527009)
                      ·
                        rfl

theorem cell23_1589613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_1589613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589613 prefixEnd_1589613 := by exact prefixLift 1589613
  have htrace : WordTrace (prefixWord ++ tailWord_1589613) baseStart_1589613 baseEnd_1589613 := by
    simpa [prefixWord, tailWord_1589613, baseEnd_1589613] using wordTrace_append hprefix tailTrace_1589613
  have hstable : (prefixWord ++ tailWord_1589613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589613).length < 2 ^ (prefixWord ++ tailWord_1589613).sum := by decide
  have hdescent : baseEnd_1589613 < baseStart_1589613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589643 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 1, 3, 3]
def baseStart_1589643 : Nat := 118140960795 + 1589643 * 2 ^ 59
def prefixEnd_1589643 : Nat := 4983230072969 + 3 ^ 40 * 1589643 * 2
def baseEnd_1589643 : Nat := 816250928055229248151871

theorem tailTrace_1589643 : CollatzResearch.WordTrace tailWord_1589643 prefixEnd_1589643 816250928055229248151871 := by
  unfold tailWord_1589643
  simp only [CollatzResearch.WordTrace]
  refine ⟨57979043380002375255133583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38652695586668250170089055 57979043380002375255133583)
  ·
    refine ⟨86968565070003562882700375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57979043380002375255133583 86968565070003562882700375)
    ·
      refine ⟨130452847605005344324050563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86968565070003562882700375 130452847605005344324050563)
      ·
        refine ⟨195679271407508016486075845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130452847605005344324050563 195679271407508016486075845)
        ·
          refine ⟨36689863388907753091139221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195679271407508016486075845 36689863388907753091139221)
          ·
            refine ⟨1719837346355050926147151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36689863388907753091139221 1719837346355050926147151)
            ·
              refine ⟨2579756019532576389220727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1719837346355050926147151 2579756019532576389220727)
              ·
                refine ⟨3869634029298864583831091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2579756019532576389220727 3869634029298864583831091)
                ·
                  refine ⟨5804451043948296875746637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3869634029298864583831091 5804451043948296875746637)
                  ·
                    refine ⟨2176669141480611328404989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5804451043948296875746637 2176669141480611328404989)
                    ·
                      refine ⟨816250928055229248151871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2176669141480611328404989 816250928055229248151871)
                      ·
                        rfl

theorem cell23_1589643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 3, 3].length) (baseStart_1589643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589643 prefixEnd_1589643 := by exact prefixLift 1589643
  have htrace : WordTrace (prefixWord ++ tailWord_1589643) baseStart_1589643 baseEnd_1589643 := by
    simpa [prefixWord, tailWord_1589643, baseEnd_1589643] using wordTrace_append hprefix tailTrace_1589643
  have hstable : (prefixWord ++ tailWord_1589643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589643).length < 2 ^ (prefixWord ++ tailWord_1589643).sum := by decide
  have hdescent : baseEnd_1589643 < baseStart_1589643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589656 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1589656 : Nat := 118140960795 + 1589656 * 2 ^ 59
def prefixEnd_1589656 : Nat := 4983230072969 + 3 ^ 40 * 1589656 * 2
def baseEnd_1589656 : Nat := 816257603303737697289311

theorem tailTrace_1589656 : CollatzResearch.WordTrace tailWord_1589656 prefixEnd_1589656 816257603303737697289311 := by
  unfold tailWord_1589656
  simp only [CollatzResearch.WordTrace]
  refine ⟨28989758764477639237678411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38653011685970185650237881 28989758764477639237678411)
  ·
    refine ⟨43484638146716458856517617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28989758764477639237678411 43484638146716458856517617)
    ·
      refine ⟨32613478610037344142388213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43484638146716458856517617 32613478610037344142388213)
      ·
        refine ⟨3057513619691001013348895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32613478610037344142388213 3057513619691001013348895)
        ·
          refine ⟨4586270429536501520023343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3057513619691001013348895 4586270429536501520023343)
          ·
            refine ⟨6879405644304752280035015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4586270429536501520023343 6879405644304752280035015)
            ·
              refine ⟨10319108466457128420052523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6879405644304752280035015 10319108466457128420052523)
              ·
                refine ⟨15478662699685692630078785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10319108466457128420052523 15478662699685692630078785)
                ·
                  refine ⟨11608997024764269472559089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15478662699685692630078785 11608997024764269472559089)
                  ·
                    refine ⟨8706747768573202104419317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11608997024764269472559089 8706747768573202104419317)
                    ·
                      refine ⟨816257603303737697289311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8706747768573202104419317 816257603303737697289311)
                      ·
                        rfl

theorem cell23_1589656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1589656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589656 prefixEnd_1589656 := by exact prefixLift 1589656
  have htrace : WordTrace (prefixWord ++ tailWord_1589656) baseStart_1589656 baseEnd_1589656 := by
    simpa [prefixWord, tailWord_1589656, baseEnd_1589656] using wordTrace_append hprefix tailTrace_1589656
  have hstable : (prefixWord ++ tailWord_1589656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589656).length < 2 ^ (prefixWord ++ tailWord_1589656).sum := by decide
  have hdescent : baseEnd_1589656 < baseStart_1589656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589661 : List Nat := [1, 4, 2, 1, 5, 1, 1, 3, 1, 2, 2]
def baseStart_1589661 : Nat := 118140960795 + 1589661 * 2 ^ 59
def prefixEnd_1589661 : Nat := 4983230072969 + 3 ^ 40 * 1589661 * 2
def baseEnd_1589661 : Nat := 816260170707010177726789

theorem tailTrace_1589661 : CollatzResearch.WordTrace tailWord_1589661 prefixEnd_1589661 816260170707010177726789 := by
  unfold tailWord_1589661
  simp only [CollatzResearch.WordTrace]
  refine ⟨57979699893937164329288837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38653133262624776219525891 57979699893937164329288837)
  ·
    refine ⟨10871193730113218311741657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57979699893937164329288837 10871193730113218311741657)
    ·
      refine ⟨8153395297584913733806243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10871193730113218311741657 8153395297584913733806243)
      ·
        refine ⟨12230092946377370600709365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8153395297584913733806243 12230092946377370600709365)
        ·
          refine ⟨1146571213722878493816503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12230092946377370600709365 1146571213722878493816503)
          ·
            refine ⟨1719856820584317740724755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146571213722878493816503 1719856820584317740724755)
            ·
              refine ⟨2579785230876476611087133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1719856820584317740724755 2579785230876476611087133)
              ·
                refine ⟨967419461578678729157675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2579785230876476611087133 967419461578678729157675)
                ·
                  refine ⟨1451129192368018093736513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967419461578678729157675 1451129192368018093736513)
                  ·
                    refine ⟨1088346894276013570302385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1451129192368018093736513 1088346894276013570302385)
                    ·
                      refine ⟨816260170707010177726789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1088346894276013570302385 816260170707010177726789)
                      ·
                        rfl

theorem cell23_1589661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_1589661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589661 prefixEnd_1589661 := by exact prefixLift 1589661
  have htrace : WordTrace (prefixWord ++ tailWord_1589661) baseStart_1589661 baseEnd_1589661 := by
    simpa [prefixWord, tailWord_1589661, baseEnd_1589661] using wordTrace_append hprefix tailTrace_1589661
  have hstable : (prefixWord ++ tailWord_1589661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589661).length < 2 ^ (prefixWord ++ tailWord_1589661).sum := by decide
  have hdescent : baseEnd_1589661 < baseStart_1589661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589756 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_1589756 : Nat := 118140960795 + 1589756 * 2 ^ 59
def prefixEnd_1589756 : Nat := 4983230072969 + 3 ^ 40 * 1589756 * 2
def baseEnd_1589756 : Nat := 816308951369187306038851

theorem tailTrace_1589756 : CollatzResearch.WordTrace tailWord_1589756 prefixEnd_1589756 816308951369187306038851 := by
  unfold tailWord_1589756
  simp only [CollatzResearch.WordTrace]
  refine ⟨28991582414296497776998561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38655443219061997035998081 28991582414296497776998561)
  ·
    refine ⟨21743686810722373332748921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28991582414296497776998561 21743686810722373332748921)
    ·
      refine ⟨16307765108041779999561691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21743686810722373332748921 16307765108041779999561691)
      ·
        refine ⟨24461647662062669999342537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16307765108041779999561691 24461647662062669999342537)
        ·
          refine ⟨18346235746547002499506903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24461647662062669999342537 18346235746547002499506903)
          ·
            refine ⟨27519353619820503749260355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18346235746547002499506903 27519353619820503749260355)
            ·
              refine ⟨41279030429730755623890533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27519353619820503749260355 41279030429730755623890533)
              ·
                refine ⟨7739818205574516679479475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41279030429730755623890533 7739818205574516679479475)
                ·
                  refine ⟨11609727308361775019219213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7739818205574516679479475 11609727308361775019219213)
                  ·
                    refine ⟨4353647740635665632207205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11609727308361775019219213 4353647740635665632207205)
                    ·
                      refine ⟨816308951369187306038851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4353647740635665632207205 816308951369187306038851)
                      ·
                        rfl

theorem cell23_1589756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_1589756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589756 prefixEnd_1589756 := by exact prefixLift 1589756
  have htrace : WordTrace (prefixWord ++ tailWord_1589756) baseStart_1589756 baseEnd_1589756 := by
    simpa [prefixWord, tailWord_1589756, baseEnd_1589756] using wordTrace_append hprefix tailTrace_1589756
  have hstable : (prefixWord ++ tailWord_1589756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589756).length < 2 ^ (prefixWord ++ tailWord_1589756).sum := by decide
  have hdescent : baseEnd_1589756 < baseStart_1589756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589786 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_1589786 : Nat := 118140960795 + 1589786 * 2 ^ 59
def prefixEnd_1589786 : Nat := 4983230072969 + 3 ^ 40 * 1589786 * 2
def baseEnd_1589786 : Nat := 816324355788822188663713

theorem tailTrace_1589786 : CollatzResearch.WordTrace tailWord_1589786 prefixEnd_1589786 816324355788822188663713 := by
  unfold tailWord_1589786
  simp only [CollatzResearch.WordTrace]
  refine ⟨14496064754621077669397303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38656172678989540451726141 14496064754621077669397303)
  ·
    refine ⟨21744097131931616504095955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14496064754621077669397303 21744097131931616504095955)
    ·
      refine ⟨32616145697897424756143933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21744097131931616504095955 32616145697897424756143933)
      ·
        refine ⟨12231054636711534283553975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32616145697897424756143933 12231054636711534283553975)
        ·
          refine ⟨18346581955067301425330963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12231054636711534283553975 18346581955067301425330963)
          ·
            refine ⟨27519872932600952137996445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18346581955067301425330963 27519872932600952137996445)
            ·
              refine ⟨10319952349725357051748667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27519872932600952137996445 10319952349725357051748667)
              ·
                refine ⟨15479928524588035577623001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10319952349725357051748667 15479928524588035577623001)
                ·
                  refine ⟨11609946393441026683217251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15479928524588035577623001 11609946393441026683217251)
                  ·
                    refine ⟨17414919590161540024825877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11609946393441026683217251 17414919590161540024825877)
                    ·
                      refine ⟨816324355788822188663713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17414919590161540024825877 816324355788822188663713)
                      ·
                        rfl

theorem cell23_1589786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_1589786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589786 prefixEnd_1589786 := by exact prefixLift 1589786
  have htrace : WordTrace (prefixWord ++ tailWord_1589786) baseStart_1589786 baseEnd_1589786 := by
    simpa [prefixWord, tailWord_1589786, baseEnd_1589786] using wordTrace_append hprefix tailTrace_1589786
  have hstable : (prefixWord ++ tailWord_1589786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589786).length < 2 ^ (prefixWord ++ tailWord_1589786).sum := by decide
  have hdescent : baseEnd_1589786 < baseStart_1589786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589793 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_1589793 : Nat := 118140960795 + 1589793 * 2 ^ 59
def prefixEnd_1589793 : Nat := 4983230072969 + 3 ^ 40 * 1589793 * 2
def baseEnd_1589793 : Nat := 816327950153403661276181

theorem tailTrace_1589793 : CollatzResearch.WordTrace tailWord_1589793 prefixEnd_1589793 816327950153403661276181 := by
  unfold tailWord_1589793
  simp only [CollatzResearch.WordTrace]
  refine ⟨57984514329458950873094033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38656342886305967248729355 57984514329458950873094033)
  ·
    refine ⟨43488385747094213154820525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57984514329458950873094033 43488385747094213154820525)
    ·
      refine ⟨16308144655160329933057697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43488385747094213154820525 16308144655160329933057697)
      ·
        refine ⟨12231108491370247449793273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16308144655160329933057697 12231108491370247449793273)
        ·
          refine ⟨9173331368527685587344955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12231108491370247449793273 9173331368527685587344955)
          ·
            refine ⟨13759997052791528381017433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9173331368527685587344955 13759997052791528381017433)
            ·
              refine ⟨10319997789593646285763075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13759997052791528381017433 10319997789593646285763075)
              ·
                refine ⟨15479996684390469428644613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10319997789593646285763075 15479996684390469428644613)
                ·
                  refine ⟨2902499378323213017870865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15479996684390469428644613 2902499378323213017870865)
                  ·
                    refine ⟨2176874533742409763403149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2902499378323213017870865 2176874533742409763403149)
                    ·
                      refine ⟨816327950153403661276181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2176874533742409763403149 816327950153403661276181)
                      ·
                        rfl

theorem cell23_1589793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_1589793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589793 prefixEnd_1589793 := by exact prefixLift 1589793
  have htrace : WordTrace (prefixWord ++ tailWord_1589793) baseStart_1589793 baseEnd_1589793 := by
    simpa [prefixWord, tailWord_1589793, baseEnd_1589793] using wordTrace_append hprefix tailTrace_1589793
  have hstable : (prefixWord ++ tailWord_1589793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589793).length < 2 ^ (prefixWord ++ tailWord_1589793).sum := by decide
  have hdescent : baseEnd_1589793 < baseStart_1589793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589800 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1589800 : Nat := 118140960795 + 1589800 * 2 ^ 59
def prefixEnd_1589800 : Nat := 4983230072969 + 3 ^ 40 * 1589800 * 2
def baseEnd_1589800 : Nat := 272110514839328377962883

theorem tailTrace_1589800 : CollatzResearch.WordTrace tailWord_1589800 prefixEnd_1589800 272110514839328377962883 := by
  unfold tailWord_1589800
  simp only [CollatzResearch.WordTrace]
  refine ⟨28992384820216795534299427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38656513093622394045732569 28992384820216795534299427)
  ·
    refine ⟨43488577230325193301449141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28992384820216795534299427 43488577230325193301449141)
    ·
      refine ⟨4077054115342986872010857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43488577230325193301449141 4077054115342986872010857)
      ·
        refine ⟨3057790586507240154008143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4077054115342986872010857 3057790586507240154008143)
        ·
          refine ⟨4586685879760860231012215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3057790586507240154008143 4586685879760860231012215)
          ·
            refine ⟨6880028819641290346518323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4586685879760860231012215 6880028819641290346518323)
            ·
              refine ⟨10320043229461935519777485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6880028819641290346518323 10320043229461935519777485)
              ·
                refine ⟨3870016211048225819916557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10320043229461935519777485 3870016211048225819916557)
                ·
                  refine ⟨1451256079143084682468709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3870016211048225819916557 1451256079143084682468709)
                  ·
                    refine ⟨272110514839328377962883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1451256079143084682468709 272110514839328377962883)
                    ·
                      rfl

theorem cell23_1589800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1589800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589800 prefixEnd_1589800 := by exact prefixLift 1589800
  have htrace : WordTrace (prefixWord ++ tailWord_1589800) baseStart_1589800 baseEnd_1589800 := by
    simpa [prefixWord, tailWord_1589800, baseEnd_1589800] using wordTrace_append hprefix tailTrace_1589800
  have hstable : (prefixWord ++ tailWord_1589800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589800).length < 2 ^ (prefixWord ++ tailWord_1589800).sum := by decide
  have hdescent : baseEnd_1589800 < baseStart_1589800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589816 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_1589816 : Nat := 118140960795 + 1589816 * 2 ^ 59
def prefixEnd_1589816 : Nat := 4983230072969 + 3 ^ 40 * 1589816 * 2
def baseEnd_1589816 : Nat := 816339760208457071288575

theorem tailTrace_1589816 : CollatzResearch.WordTrace tailWord_1589816 prefixEnd_1589816 816339760208457071288575 := by
  unfold tailWord_1589816
  simp only [CollatzResearch.WordTrace]
  refine ⟨28992676604187812900590651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38656902138917083867454201 28992676604187812900590651)
  ·
    refine ⟨43489014906281719350885977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28992676604187812900590651 43489014906281719350885977)
    ·
      refine ⟨32616761179711289513164483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43489014906281719350885977 32616761179711289513164483)
      ·
        refine ⟨48925141769566934269746725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32616761179711289513164483 48925141769566934269746725)
        ·
          refine ⟨9173464081793800175577511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48925141769566934269746725 9173464081793800175577511)
          ·
            refine ⟨13760196122690700263366267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9173464081793800175577511 13760196122690700263366267)
            ·
              refine ⟨20640294184036050395049401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13760196122690700263366267 20640294184036050395049401)
              ·
                refine ⟨15480220638027037796287051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20640294184036050395049401 15480220638027037796287051)
                ·
                  refine ⟨23220330957040556694430577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15480220638027037796287051 23220330957040556694430577)
                  ·
                    refine ⟨17415248217780417520822933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23220330957040556694430577 17415248217780417520822933)
                    ·
                      refine ⟨816339760208457071288575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17415248217780417520822933 816339760208457071288575)
                      ·
                        rfl

theorem cell23_1589816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_1589816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589816 prefixEnd_1589816 := by exact prefixLift 1589816
  have htrace : WordTrace (prefixWord ++ tailWord_1589816) baseStart_1589816 baseEnd_1589816 := by
    simpa [prefixWord, tailWord_1589816, baseEnd_1589816] using wordTrace_append hprefix tailTrace_1589816
  have hstable : (prefixWord ++ tailWord_1589816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589816).length < 2 ^ (prefixWord ++ tailWord_1589816).sum := by decide
  have hdescent : baseEnd_1589816 < baseStart_1589816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589830 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_1589830 : Nat := 118140960795 + 1589830 * 2 ^ 59
def prefixEnd_1589830 : Nat := 4983230072969 + 3 ^ 40 * 1589830 * 2
def baseEnd_1589830 : Nat := 90705216548624446279279

theorem tailTrace_1589830 : CollatzResearch.WordTrace tailWord_1589830 prefixEnd_1589830 90705216548624446279279 := by
  unfold tailWord_1589830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1812058244697653318505967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38657242553549937461460629 1812058244697653318505967)
  ·
    refine ⟨2718087367046479977758951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1812058244697653318505967 2718087367046479977758951)
    ·
      refine ⟨4077131050569719966638427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2718087367046479977758951 4077131050569719966638427)
      ·
        refine ⟨6115696575854579949957641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4077131050569719966638427 6115696575854579949957641)
        ·
          refine ⟨4586772431890934962468231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6115696575854579949957641 4586772431890934962468231)
          ·
            refine ⟨6880158647836402443702347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4586772431890934962468231 6880158647836402443702347)
            ·
              refine ⟨10320237971754603665553521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6880158647836402443702347 10320237971754603665553521)
              ·
                refine ⟨7740178478815952749165141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10320237971754603665553521 7740178478815952749165141)
                ·
                  refine ⟨90705216548624446279279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7740178478815952749165141 90705216548624446279279)
                  ·
                    rfl

theorem cell23_1589830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_1589830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589830 prefixEnd_1589830 := by exact prefixLift 1589830
  have htrace : WordTrace (prefixWord ++ tailWord_1589830) baseStart_1589830 baseEnd_1589830 := by
    simpa [prefixWord, tailWord_1589830, baseEnd_1589830] using wordTrace_append hprefix tailTrace_1589830
  have hstable : (prefixWord ++ tailWord_1589830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589830).length < 2 ^ (prefixWord ++ tailWord_1589830).sum := by decide
  have hdescent : baseEnd_1589830 < baseStart_1589830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589857 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 3, 1, 3]
def baseStart_1589857 : Nat := 118140960795 + 1589857 * 2 ^ 59
def prefixEnd_1589857 : Nat := 4983230072969 + 3 ^ 40 * 1589857 * 2
def baseEnd_1589857 : Nat := 816360812915291410875887

theorem tailTrace_1589857 : CollatzResearch.WordTrace tailWord_1589857 prefixEnd_1589857 816360812915291410875887 := by
  unfold tailWord_1589857
  simp only [CollatzResearch.WordTrace]
  refine ⟨57986848601227089803423825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38657899067484726535615883 57986848601227089803423825)
  ·
    refine ⟨43490136450920317352567869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57986848601227089803423825 43490136450920317352567869)
    ·
      refine ⟨16308801169095119007212951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43490136450920317352567869 16308801169095119007212951)
      ·
        refine ⟨24463201753642678510819427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16308801169095119007212951 24463201753642678510819427)
        ·
          refine ⟨36694802630464017766229141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24463201753642678510819427 36694802630464017766229141)
          ·
            refine ⟨1720068873303000832791991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36694802630464017766229141 1720068873303000832791991)
            ·
              refine ⟨2580103309954501249187987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1720068873303000832791991 2580103309954501249187987)
              ·
                refine ⟨3870154964931751873781981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2580103309954501249187987 3870154964931751873781981)
                ·
                  refine ⟨1451308111849406952668243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3870154964931751873781981 1451308111849406952668243)
                  ·
                    refine ⟨2176962167774110429002365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1451308111849406952668243 2176962167774110429002365)
                    ·
                      refine ⟨816360812915291410875887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2176962167774110429002365 816360812915291410875887)
                      ·
                        rfl

theorem cell23_1589857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_1589857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589857 prefixEnd_1589857 := by exact prefixLift 1589857
  have htrace : WordTrace (prefixWord ++ tailWord_1589857) baseStart_1589857 baseEnd_1589857 := by
    simpa [prefixWord, tailWord_1589857, baseEnd_1589857] using wordTrace_append hprefix tailTrace_1589857
  have hstable : (prefixWord ++ tailWord_1589857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589857).length < 2 ^ (prefixWord ++ tailWord_1589857).sum := by decide
  have hdescent : baseEnd_1589857 < baseStart_1589857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589863 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1589863 : Nat := 118140960795 + 1589863 * 2 ^ 59
def prefixEnd_1589863 : Nat := 4983230072969 + 3 ^ 40 * 1589863 * 2
def baseEnd_1589863 : Nat := 816363893799218387400859

theorem tailTrace_1589863 : CollatzResearch.WordTrace tailWord_1589863 prefixEnd_1589863 816363893799218387400859 := by
  unfold tailWord_1589863
  simp only [CollatzResearch.WordTrace]
  refine ⟨57987067439205352828142243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38658044959470235218761495 57987067439205352828142243)
  ·
    refine ⟨86980601158808029242213365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57987067439205352828142243 86980601158808029242213365)
    ·
      refine ⟨8154431358638252741457503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86980601158808029242213365 8154431358638252741457503)
      ·
        refine ⟨12231647037957379112186255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8154431358638252741457503 12231647037957379112186255)
        ·
          refine ⟨18347470556936068668279383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12231647037957379112186255 18347470556936068668279383)
          ·
            refine ⟨27521205835404103002419075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18347470556936068668279383 27521205835404103002419075)
            ·
              refine ⟨41281808753106154503628613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27521205835404103002419075 41281808753106154503628613)
              ·
                refine ⟨7740339141207403969430365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41281808753106154503628613 7740339141207403969430365)
                ·
                  refine ⟨2902627177952776488536387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7740339141207403969430365 2902627177952776488536387)
                  ·
                    refine ⟨4353940766929164732804581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2902627177952776488536387 4353940766929164732804581)
                    ·
                      refine ⟨816363893799218387400859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4353940766929164732804581 816363893799218387400859)
                      ·
                        rfl

theorem cell23_1589863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1589863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589863 prefixEnd_1589863 := by exact prefixLift 1589863
  have htrace : WordTrace (prefixWord ++ tailWord_1589863) baseStart_1589863 baseEnd_1589863 := by
    simpa [prefixWord, tailWord_1589863, baseEnd_1589863] using wordTrace_append hprefix tailTrace_1589863
  have hstable : (prefixWord ++ tailWord_1589863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589863).length < 2 ^ (prefixWord ++ tailWord_1589863).sum := by decide
  have hdescent : baseEnd_1589863 < baseStart_1589863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589864 : List Nat := [2, 1, 4, 3, 3, 1, 2, 1, 6]
def baseStart_1589864 : Nat := 118140960795 + 1589864 * 2 ^ 59
def prefixEnd_1589864 : Nat := 4983230072969 + 3 ^ 40 * 1589864 * 2
def baseEnd_1589864 : Nat := 90707156364430320387595

theorem tailTrace_1589864 : CollatzResearch.WordTrace tailWord_1589864 prefixEnd_1589864 90707156364430320387595 := by
  unfold tailWord_1589864
  simp only [CollatzResearch.WordTrace]
  refine ⟨28993551956100864999464323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38658069274801153332619097 28993551956100864999464323)
  ·
    refine ⟨43490327934151297499196485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28993551956100864999464323 43490327934151297499196485)
    ·
      refine ⟨8154436487653368281099341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43490327934151297499196485 8154436487653368281099341)
      ·
        refine ⟨3057913682870013105412253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8154436487653368281099341 3057913682870013105412253)
        ·
          refine ⟨1146717631076254914529595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3057913682870013105412253 1146717631076254914529595)
          ·
            refine ⟨1720076446614382371794393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146717631076254914529595 1720076446614382371794393)
            ·
              refine ⟨1290057334960786778845795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1720076446614382371794393 1290057334960786778845795)
              ·
                refine ⟨1935086002441180168268693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290057334960786778845795 1935086002441180168268693)
                ·
                  refine ⟨90707156364430320387595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1935086002441180168268693 90707156364430320387595)
                  ·
                    rfl

theorem cell23_1589864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 6].length) (baseStart_1589864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589864 prefixEnd_1589864 := by exact prefixLift 1589864
  have htrace : WordTrace (prefixWord ++ tailWord_1589864) baseStart_1589864 baseEnd_1589864 := by
    simpa [prefixWord, tailWord_1589864, baseEnd_1589864] using wordTrace_append hprefix tailTrace_1589864
  have hstable : (prefixWord ++ tailWord_1589864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589864).length < 2 ^ (prefixWord ++ tailWord_1589864).sum := by decide
  have hdescent : baseEnd_1589864 < baseStart_1589864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589893 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_1589893 : Nat := 118140960795 + 1589893 * 2 ^ 59
def prefixEnd_1589893 : Nat := 4983230072969 + 3 ^ 40 * 1589893 * 2
def baseEnd_1589893 : Nat := 816379298218853270025721

theorem tailTrace_1589893 : CollatzResearch.WordTrace tailWord_1589893 prefixEnd_1589893 816379298218853270025721 := by
  unfold tailWord_1589893
  simp only [CollatzResearch.WordTrace]
  refine ⟨57988161629096667951734333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38658774419397778634489555 57988161629096667951734333)
  ·
    refine ⟨21745560610911250481900375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57988161629096667951734333 21745560610911250481900375)
    ·
      refine ⟨32618340916366875722850563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21745560610911250481900375 32618340916366875722850563)
      ·
        refine ⟨48927511374550313584275845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32618340916366875722850563 48927511374550313584275845)
        ·
          refine ⟨9173908382728183797051721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48927511374550313584275845 9173908382728183797051721)
          ·
            refine ⟨6880431287046137847788791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9173908382728183797051721 6880431287046137847788791)
            ·
              refine ⟨10320646930569206771683187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6880431287046137847788791 10320646930569206771683187)
              ·
                refine ⟨15480970395853810157524781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10320646930569206771683187 15480970395853810157524781)
                ·
                  refine ⟨5805363898445178809071793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15480970395853810157524781 5805363898445178809071793)
                  ·
                    refine ⟨4354022923833884106803845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5805363898445178809071793 4354022923833884106803845)
                    ·
                      refine ⟨816379298218853270025721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4354022923833884106803845 816379298218853270025721)
                      ·
                        rfl

theorem cell23_1589893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_1589893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589893 prefixEnd_1589893 := by exact prefixLift 1589893
  have htrace : WordTrace (prefixWord ++ tailWord_1589893) baseStart_1589893 baseEnd_1589893 := by
    simpa [prefixWord, tailWord_1589893, baseEnd_1589893] using wordTrace_append hprefix tailTrace_1589893
  have hstable : (prefixWord ++ tailWord_1589893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589893).length < 2 ^ (prefixWord ++ tailWord_1589893).sum := by decide
  have hdescent : baseEnd_1589893 < baseStart_1589893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589908 : List Nat := [2, 4, 2, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_1589908 : Nat := 118140960795 + 1589908 * 2 ^ 59
def prefixEnd_1589908 : Nat := 4983230072969 + 3 ^ 40 * 1589908 * 2
def baseEnd_1589908 : Nat := 816387000428670711338153

theorem tailTrace_1589908 : CollatzResearch.WordTrace tailWord_1589908 prefixEnd_1589908 816387000428670711338153 := by
  unfold tailWord_1589908
  simp only [CollatzResearch.WordTrace]
  refine ⟨28994354362021162756765189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38659139149361550342353585 28994354362021162756765189)
  ·
    refine ⟨5436441442878968016893473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28994354362021162756765189 5436441442878968016893473)
    ·
      refine ⟨4077331082159226012670105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5436441442878968016893473 4077331082159226012670105)
      ·
        refine ⟨3057998311619419509502579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4077331082159226012670105 3057998311619419509502579)
        ·
          refine ⟨4586997467429129264253869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3057998311619419509502579 4586997467429129264253869)
          ·
            refine ⟨1720124050285923474095201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4586997467429129264253869 1720124050285923474095201)
            ·
              refine ⟨1290093037714442605571401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1720124050285923474095201 1290093037714442605571401)
              ·
                refine ⟨967569778285831954178551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290093037714442605571401 967569778285831954178551)
                ·
                  refine ⟨1451354667428747931267827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967569778285831954178551 1451354667428747931267827)
                  ·
                    refine ⟨2177032001143121896901741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1451354667428747931267827 2177032001143121896901741)
                    ·
                      refine ⟨816387000428670711338153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2177032001143121896901741 816387000428670711338153)
                      ·
                        rfl

theorem cell23_1589908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_1589908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589908 prefixEnd_1589908 := by exact prefixLift 1589908
  have htrace : WordTrace (prefixWord ++ tailWord_1589908) baseStart_1589908 baseEnd_1589908 := by
    simpa [prefixWord, tailWord_1589908, baseEnd_1589908] using wordTrace_append hprefix tailTrace_1589908
  have hstable : (prefixWord ++ tailWord_1589908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589908).length < 2 ^ (prefixWord ++ tailWord_1589908).sum := by decide
  have hdescent : baseEnd_1589908 < baseStart_1589908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589913 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 3, 3, 3]
def baseStart_1589913 : Nat := 118140960795 + 1589913 * 2 ^ 59
def prefixEnd_1589913 : Nat := 4983230072969 + 3 ^ 40 * 1589913 * 2
def baseEnd_1589913 : Nat := 816389567831943191775629

theorem tailTrace_1589913 : CollatzResearch.WordTrace tailWord_1589913 prefixEnd_1589913 816389567831943191775629 := by
  unfold tailWord_1589913
  simp only [CollatzResearch.WordTrace]
  refine ⟨57988891089024211367462393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38659260726016140911641595 57988891089024211367462393)
  ·
    refine ⟨43491668316768158525596795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57988891089024211367462393 43491668316768158525596795)
    ·
      refine ⟨65237502475152237788395193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43491668316768158525596795 65237502475152237788395193)
      ·
        refine ⟨48928126856364178341296395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65237502475152237788395193 48928126856364178341296395)
        ·
          refine ⟨73392190284546267511944593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48928126856364178341296395 73392190284546267511944593)
          ·
            refine ⟨55044142713409700633958445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73392190284546267511944593 55044142713409700633958445)
            ·
              refine ⟨20641553517528637737734417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55044142713409700633958445 20641553517528637737734417)
              ·
                refine ⟨15481165138146478303300813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20641553517528637737734417 15481165138146478303300813)
                ·
                  refine ⟨5805436926804929363737805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15481165138146478303300813 5805436926804929363737805)
                  ·
                    refine ⟨2177038847551848511401677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5805436926804929363737805 2177038847551848511401677)
                    ·
                      refine ⟨816389567831943191775629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2177038847551848511401677 816389567831943191775629)
                      ·
                        rfl

theorem cell23_1589913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_1589913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589913 prefixEnd_1589913 := by exact prefixLift 1589913
  have htrace : WordTrace (prefixWord ++ tailWord_1589913) baseStart_1589913 baseEnd_1589913 := by
    simpa [prefixWord, tailWord_1589913, baseEnd_1589913] using wordTrace_append hprefix tailTrace_1589913
  have hstable : (prefixWord ++ tailWord_1589913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589913).length < 2 ^ (prefixWord ++ tailWord_1589913).sum := by decide
  have hdescent : baseEnd_1589913 < baseStart_1589913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589920 : List Nat := [2, 1, 1, 4, 4, 2, 1, 8]
def baseStart_1589920 : Nat := 118140960795 + 1589920 * 2 ^ 59
def prefixEnd_1589920 : Nat := 4983230072969 + 3 ^ 40 * 1589920 * 2
def baseEnd_1589920 : Nat := 30236783785056469051411

theorem tailTrace_1589920 : CollatzResearch.WordTrace tailWord_1589920 prefixEnd_1589920 30236783785056469051411 := by
  unfold tailWord_1589920
  simp only [CollatzResearch.WordTrace]
  refine ⟨28994573199999425781483607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38659430933332567708644809 28994573199999425781483607)
  ·
    refine ⟨43491859799999138672225411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28994573199999425781483607 43491859799999138672225411)
    ·
      refine ⟨65237789699998708008338117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43491859799999138672225411 65237789699998708008338117)
      ·
        refine ⟨12232085568749757751563397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65237789699998708008338117 12232085568749757751563397)
        ·
          refine ⟨2293516044140579578418137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12232085568749757751563397 2293516044140579578418137)
          ·
            refine ⟨1720137033105434683813603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2293516044140579578418137 1720137033105434683813603)
            ·
              refine ⟨2580205549658152025720405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1720137033105434683813603 2580205549658152025720405)
              ·
                refine ⟨30236783785056469051411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2580205549658152025720405 30236783785056469051411)
                ·
                  rfl

theorem cell23_1589920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 8].length) (baseStart_1589920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589920 prefixEnd_1589920 := by exact prefixLift 1589920
  have htrace : WordTrace (prefixWord ++ tailWord_1589920) baseStart_1589920 baseEnd_1589920 := by
    simpa [prefixWord, tailWord_1589920, baseEnd_1589920] using wordTrace_append hprefix tailTrace_1589920
  have hstable : (prefixWord ++ tailWord_1589920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589920).length < 2 ^ (prefixWord ++ tailWord_1589920).sum := by decide
  have hdescent : baseEnd_1589920 < baseStart_1589920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589937 : List Nat := [1, 2, 2, 6, 1, 1, 3, 7]
def baseStart_1589937 : Nat := 118140960795 + 1589937 * 2 ^ 59
def prefixEnd_1589937 : Nat := 4983230072969 + 3 ^ 40 * 1589937 * 2
def baseEnd_1589937 : Nat := 30237107087690781402797

theorem tailTrace_1589937 : CollatzResearch.WordTrace tailWord_1589937 prefixEnd_1589937 30237107087690781402797 := by
  unfold tailWord_1589937
  simp only [CollatzResearch.WordTrace]
  refine ⟨57989766440937263466336065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38659844293958175644224043 57989766440937263466336065)
  ·
    refine ⟨43492324830702947599752049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57989766440937263466336065 43492324830702947599752049)
    ·
      refine ⟨32619243623027210699814037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43492324830702947599752049 32619243623027210699814037)
      ·
        refine ⟨1529027044829400501553783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32619243623027210699814037 1529027044829400501553783)
        ·
          refine ⟨2293540567244100752330675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529027044829400501553783 2293540567244100752330675)
          ·
            refine ⟨3440310850866151128496013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293540567244100752330675 3440310850866151128496013)
            ·
              refine ⟨1290116569074806673186005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3440310850866151128496013 1290116569074806673186005)
              ·
                refine ⟨30237107087690781402797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1290116569074806673186005 30237107087690781402797)
                ·
                  rfl

theorem cell23_1589937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 7].length) (baseStart_1589937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589937 prefixEnd_1589937 := by exact prefixLift 1589937
  have htrace : WordTrace (prefixWord ++ tailWord_1589937) baseStart_1589937 baseEnd_1589937 := by
    simpa [prefixWord, tailWord_1589937, baseEnd_1589937] using wordTrace_append hprefix tailTrace_1589937
  have hstable : (prefixWord ++ tailWord_1589937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589937).length < 2 ^ (prefixWord ++ tailWord_1589937).sum := by decide
  have hdescent : baseEnd_1589937 < baseStart_1589937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589958 : List Nat := [6, 1, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1589958 : Nat := 118140960795 + 1589958 * 2 ^ 59
def prefixEnd_1589958 : Nat := 4983230072969 + 3 ^ 40 * 1589958 * 2
def baseEnd_1589958 : Nat := 272137558153798505237641

theorem tailTrace_1589958 : CollatzResearch.WordTrace tailWord_1589958 prefixEnd_1589958 272137558153798505237641 := by
  unfold tailWord_1589958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1812204136683162001651579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38660354915907456035233685 1812204136683162001651579)
  ·
    refine ⟨2718306205024743002477369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1812204136683162001651579 2718306205024743002477369)
    ·
      refine ⟨2038729653768557251858027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2718306205024743002477369 2038729653768557251858027)
      ·
        refine ⟨3058094480652835877787041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2038729653768557251858027 3058094480652835877787041)
        ·
          refine ⟨2293570860489626908340281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3058094480652835877787041 2293570860489626908340281)
          ·
            refine ⟨1720178145367220181255211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2293570860489626908340281 1720178145367220181255211)
            ·
              refine ⟨2580267218050830271882817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1720178145367220181255211 2580267218050830271882817)
              ·
                refine ⟨1935200413538122703912113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2580267218050830271882817 1935200413538122703912113)
                ·
                  refine ⟨1451400310153592027934085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1935200413538122703912113 1451400310153592027934085)
                  ·
                    refine ⟨272137558153798505237641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1451400310153592027934085 272137558153798505237641)
                    ·
                      rfl

theorem cell23_1589958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1589958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589958 prefixEnd_1589958 := by exact prefixLift 1589958
  have htrace : WordTrace (prefixWord ++ tailWord_1589958) baseStart_1589958 baseEnd_1589958 := by
    simpa [prefixWord, tailWord_1589958, baseEnd_1589958] using wordTrace_append hprefix tailTrace_1589958
  have hstable : (prefixWord ++ tailWord_1589958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589958).length < 2 ^ (prefixWord ++ tailWord_1589958).sum := by decide
  have hdescent : baseEnd_1589958 < baseStart_1589958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589964 : List Nat := [2, 2, 1, 5, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1589964 : Nat := 118140960795 + 1589964 * 2 ^ 59
def prefixEnd_1589964 : Nat := 4983230072969 + 3 ^ 40 * 1589964 * 2
def baseEnd_1589964 : Nat := 816415755345322492237895

theorem tailTrace_1589964 : CollatzResearch.WordTrace tailWord_1589964 prefixEnd_1589964 816415755345322492237895 := by
  unfold tailWord_1589964
  simp only [CollatzResearch.WordTrace]
  refine ⟨28995375605919723538784473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38660500807892964718379297 28995375605919723538784473)
  ·
    refine ⟨21746531704439792654088355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28995375605919723538784473 21746531704439792654088355)
    ·
      refine ⟨32619797556659688981132533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21746531704439792654088355 32619797556659688981132533)
      ·
        refine ⟨3058106020936845841981175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32619797556659688981132533 3058106020936845841981175)
        ·
          refine ⟨4587159031405268762971763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058106020936845841981175 4587159031405268762971763)
          ·
            refine ⟨6880738547107903144457645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4587159031405268762971763 6880738547107903144457645)
            ·
              refine ⟨2580276955165463679171617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6880738547107903144457645 2580276955165463679171617)
              ·
                refine ⟨1935207716374097759378713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2580276955165463679171617 1935207716374097759378713)
                ·
                  refine ⟨1451405787280573319534035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1935207716374097759378713 1451405787280573319534035)
                  ·
                    refine ⟨2177108680920859979301053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1451405787280573319534035 2177108680920859979301053)
                    ·
                      refine ⟨816415755345322492237895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2177108680920859979301053 816415755345322492237895)
                      ·
                        rfl

theorem cell23_1589964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1589964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589964 prefixEnd_1589964 := by exact prefixLift 1589964
  have htrace : WordTrace (prefixWord ++ tailWord_1589964) baseStart_1589964 baseEnd_1589964 := by
    simpa [prefixWord, tailWord_1589964, baseEnd_1589964] using wordTrace_append hprefix tailTrace_1589964
  have hstable : (prefixWord ++ tailWord_1589964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589964).length < 2 ^ (prefixWord ++ tailWord_1589964).sum := by decide
  have hdescent : baseEnd_1589964 < baseStart_1589964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1589993 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 7]
def baseStart_1589993 : Nat := 118140960795 + 1589993 * 2 ^ 59
def prefixEnd_1589993 : Nat := 4983230072969 + 3 ^ 40 * 1589993 * 2
def baseEnd_1589993 : Nat := 90714516253811430975029

theorem tailTrace_1589993 : CollatzResearch.WordTrace tailWord_1589993 prefixEnd_1589993 90714516253811430975029 := by
  unfold tailWord_1589993
  simp only [CollatzResearch.WordTrace]
  refine ⟨57991808928734385030374633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38661205952489590020249755 57991808928734385030374633)
  ·
    refine ⟨43493856696550788772780975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57991808928734385030374633 43493856696550788772780975)
    ·
      refine ⟨65240785044826183159171463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43493856696550788772780975 65240785044826183159171463)
      ·
        refine ⟨97861177567239274738757195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65240785044826183159171463 97861177567239274738757195)
        ·
          refine ⟨146791766350858912108135793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97861177567239274738757195 146791766350858912108135793)
          ·
            refine ⟨110093824763144184081101845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146791766350858912108135793 110093824763144184081101845)
            ·
              refine ⟨5160648035772383628801649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110093824763144184081101845 5160648035772383628801649)
              ·
                refine ⟨3870486026829287721601237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5160648035772383628801649 3870486026829287721601237)
                ·
                  refine ⟨90714516253811430975029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3870486026829287721601237 90714516253811430975029)
                  ·
                    rfl

theorem cell23_1589993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 7].length) (baseStart_1589993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1589993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1589993 prefixEnd_1589993 := by exact prefixLift 1589993
  have htrace : WordTrace (prefixWord ++ tailWord_1589993) baseStart_1589993 baseEnd_1589993 := by
    simpa [prefixWord, tailWord_1589993, baseEnd_1589993] using wordTrace_append hprefix tailTrace_1589993
  have hstable : (prefixWord ++ tailWord_1589993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1589993).length < 2 ^ (prefixWord ++ tailWord_1589993).sum := by decide
  have hdescent : baseEnd_1589993 < baseStart_1589993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1589993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590033 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_1590033 : Nat := 118140960795 + 1590033 * 2 ^ 59
def prefixEnd_1590033 : Nat := 4983230072969 + 3 ^ 40 * 1590033 * 2
def baseEnd_1590033 : Nat := 816451185510482722275077

theorem tailTrace_1590033 : CollatzResearch.WordTrace tailWord_1590033 prefixEnd_1590033 816451185510482722275077 := by
  unfold tailWord_1590033
  simp only [CollatzResearch.WordTrace]
  refine ⟨57993267848589471861830753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38662178565726314574553835 57993267848589471861830753)
  ·
    refine ⟨43494950886442103896373065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57993267848589471861830753 43494950886442103896373065)
    ·
      refine ⟨32621213164831577922279799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43494950886442103896373065 32621213164831577922279799)
      ·
        refine ⟨48931819747247366883419699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32621213164831577922279799 48931819747247366883419699)
        ·
          refine ⟨73397729620871050325129549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48931819747247366883419699 73397729620871050325129549)
          ·
            refine ⟨27524148607826643871923581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73397729620871050325129549 27524148607826643871923581)
            ·
              refine ⟨10321555727934991451971343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27524148607826643871923581 10321555727934991451971343)
              ·
                refine ⟨15482333591902487177957015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10321555727934991451971343 15482333591902487177957015)
                ·
                  refine ⟨23223500387853730766935523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15482333591902487177957015 23223500387853730766935523)
                  ·
                    refine ⟨34835250581780596150403285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23223500387853730766935523 34835250581780596150403285)
                    ·
                      refine ⟨816451185510482722275077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34835250581780596150403285 816451185510482722275077)
                      ·
                        rfl

theorem cell23_1590033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_1590033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590033 prefixEnd_1590033 := by exact prefixLift 1590033
  have htrace : WordTrace (prefixWord ++ tailWord_1590033) baseStart_1590033 baseEnd_1590033 := by
    simpa [prefixWord, tailWord_1590033, baseEnd_1590033] using wordTrace_append hprefix tailTrace_1590033
  have hstable : (prefixWord ++ tailWord_1590033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590033).length < 2 ^ (prefixWord ++ tailWord_1590033).sum := by decide
  have hdescent : baseEnd_1590033 < baseStart_1590033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590063 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 5]
def baseStart_1590063 : Nat := 118140960795 + 1590063 * 2 ^ 59
def prefixEnd_1590063 : Nat := 4983230072969 + 3 ^ 40 * 1590063 * 2
def baseEnd_1590063 : Nat := 816466589930117604899939

theorem tailTrace_1590063 : CollatzResearch.WordTrace tailWord_1590063 prefixEnd_1590063 816466589930117604899939 := by
  unfold tailWord_1590063
  simp only [CollatzResearch.WordTrace]
  refine ⟨57994362038480786985422843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38662908025653857990281895 57994362038480786985422843)
  ·
    refine ⟨86991543057721180478134265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57994362038480786985422843 86991543057721180478134265)
    ·
      refine ⟨65243657293290885358600699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86991543057721180478134265 65243657293290885358600699)
      ·
        refine ⟨97865485939936328037901049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65243657293290885358600699 97865485939936328037901049)
        ·
          refine ⟨73399114454952246028425787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97865485939936328037901049 73399114454952246028425787)
          ·
            refine ⟨110098671682428369042638681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73399114454952246028425787 110098671682428369042638681)
            ·
              refine ⟨82574003761821276781979011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110098671682428369042638681 82574003761821276781979011)
              ·
                refine ⟨123861005642731915172968517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82574003761821276781979011 123861005642731915172968517)
                ·
                  refine ⟨23223938558012234094931597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123861005642731915172968517 23223938558012234094931597)
                  ·
                    refine ⟨8708976959254587785599349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23223938558012234094931597 8708976959254587785599349)
                    ·
                      refine ⟨816466589930117604899939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8708976959254587785599349 816466589930117604899939)
                      ·
                        rfl

theorem cell23_1590063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_1590063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590063 prefixEnd_1590063 := by exact prefixLift 1590063
  have htrace : WordTrace (prefixWord ++ tailWord_1590063) baseStart_1590063 baseEnd_1590063 := by
    simpa [prefixWord, tailWord_1590063, baseEnd_1590063] using wordTrace_append hprefix tailTrace_1590063
  have hstable : (prefixWord ++ tailWord_1590063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590063).length < 2 ^ (prefixWord ++ tailWord_1590063).sum := by decide
  have hdescent : baseEnd_1590063 < baseStart_1590063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590078 : List Nat := [4, 2, 1, 2, 4, 1, 2, 2, 5]
def baseStart_1590078 : Nat := 118140960795 + 1590078 * 2 ^ 59
def prefixEnd_1590078 : Nat := 4983230072969 + 3 ^ 40 * 1590078 * 2
def baseEnd_1590078 : Nat := 90719365793326116245819

theorem tailTrace_1590078 : CollatzResearch.WordTrace tailWord_1590078 prefixEnd_1590078 90719365793326116245819 := by
  unfold tailWord_1590078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7249363641678305568402361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38663272755617629698145925 7249363641678305568402361)
  ·
    refine ⟨5437022731258729176301771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7249363641678305568402361 5437022731258729176301771)
    ·
      refine ⟨8155534096888093764452657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5437022731258729176301771 8155534096888093764452657)
      ·
        refine ⟨6116650572666070323339493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8155534096888093764452657 6116650572666070323339493)
        ·
          refine ⟨1146871982374888185626155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6116650572666070323339493 1146871982374888185626155)
          ·
            refine ⟨1720307973562332278439233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146871982374888185626155 1720307973562332278439233)
            ·
              refine ⟨1290230980171749208829425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1720307973562332278439233 1290230980171749208829425)
              ·
                refine ⟨967673235128811906622069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290230980171749208829425 967673235128811906622069)
                ·
                  refine ⟨90719365793326116245819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 967673235128811906622069 90719365793326116245819)
                  ·
                    rfl

theorem cell23_1590078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_1590078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590078 prefixEnd_1590078 := by exact prefixLift 1590078
  have htrace : WordTrace (prefixWord ++ tailWord_1590078) baseStart_1590078 baseEnd_1590078 := by
    simpa [prefixWord, tailWord_1590078, baseEnd_1590078] using wordTrace_append hprefix tailTrace_1590078
  have hstable : (prefixWord ++ tailWord_1590078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590078).length < 2 ^ (prefixWord ++ tailWord_1590078).sum := by decide
  have hdescent : baseEnd_1590078 < baseStart_1590078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590114 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1590114 : Nat := 118140960795 + 1590114 * 2 ^ 59
def prefixEnd_1590114 : Nat := 4983230072969 + 3 ^ 40 * 1590114 * 2
def baseEnd_1590114 : Nat := 816492777443496905362205

theorem tailTrace_1590114 : CollatzResearch.WordTrace tailWord_1590114 prefixEnd_1590114 816492777443496905362205 := by
  unfold tailWord_1590114
  simp only [CollatzResearch.WordTrace]
  refine ⟨14499055540324005673882349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38664148107530681797019597 14499055540324005673882349)
  ·
    refine ⟨5437145827621502127705881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14499055540324005673882349 5437145827621502127705881)
    ·
      refine ⟨4077859370716126595779411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5437145827621502127705881 4077859370716126595779411)
      ·
        refine ⟨6116789056074189893669117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4077859370716126595779411 6116789056074189893669117)
        ·
          refine ⟨2293795896027821210125919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6116789056074189893669117 2293795896027821210125919)
          ·
            refine ⟨3440693844041731815188879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293795896027821210125919 3440693844041731815188879)
            ·
              refine ⟨5161040766062597722783319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3440693844041731815188879 5161040766062597722783319)
              ·
                refine ⟨7741561149093896584174979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5161040766062597722783319 7741561149093896584174979)
                ·
                  refine ⟨11612341723640844876262469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7741561149093896584174979 11612341723640844876262469)
                  ·
                    refine ⟨2177314073182658414299213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11612341723640844876262469 2177314073182658414299213)
                    ·
                      refine ⟨816492777443496905362205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2177314073182658414299213 816492777443496905362205)
                      ·
                        rfl

theorem cell23_1590114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1590114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590114 prefixEnd_1590114 := by exact prefixLift 1590114
  have htrace : WordTrace (prefixWord ++ tailWord_1590114) baseStart_1590114 baseEnd_1590114 := by
    simpa [prefixWord, tailWord_1590114, baseEnd_1590114] using wordTrace_append hprefix tailTrace_1590114
  have hstable : (prefixWord ++ tailWord_1590114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590114).length < 2 ^ (prefixWord ++ tailWord_1590114).sum := by decide
  have hdescent : baseEnd_1590114 < baseStart_1590114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590134 : List Nat := [5, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_1590134 : Nat := 118140960795 + 1590134 * 2 ^ 59
def prefixEnd_1590134 : Nat := 4983230072969 + 3 ^ 40 * 1590134 * 2
def baseEnd_1590134 : Nat := 90722560784065203012457

theorem tailTrace_1590134 : CollatzResearch.WordTrace tailWord_1590134 prefixEnd_1590134 90722560784065203012457 := by
  unfold tailWord_1590134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3624809476326472881953591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38664634414149044074171637 3624809476326472881953591)
  ·
    refine ⟨5437214214489709322930387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3624809476326472881953591 5437214214489709322930387)
    ·
      refine ⟨8155821321734563984395581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5437214214489709322930387 8155821321734563984395581)
      ·
        refine ⟨3058432995650461494148343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8155821321734563984395581 3058432995650461494148343)
        ·
          refine ⟨4587649493475692241222515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058432995650461494148343 4587649493475692241222515)
          ·
            refine ⟨6881474240213538361833773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4587649493475692241222515 6881474240213538361833773)
            ·
              refine ⟨2580552840080076885687665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6881474240213538361833773 2580552840080076885687665)
              ·
                refine ⟨1935414630060057664265749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2580552840080076885687665 1935414630060057664265749)
                ·
                  refine ⟨90722560784065203012457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1935414630060057664265749 90722560784065203012457)
                  ·
                    rfl

theorem cell23_1590134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_1590134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590134 prefixEnd_1590134 := by exact prefixLift 1590134
  have htrace : WordTrace (prefixWord ++ tailWord_1590134) baseStart_1590134 baseEnd_1590134 := by
    simpa [prefixWord, tailWord_1590134, baseEnd_1590134] using wordTrace_append hprefix tailTrace_1590134
  have hstable : (prefixWord ++ tailWord_1590134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590134).length < 2 ^ (prefixWord ++ tailWord_1590134).sum := by decide
  have hdescent : baseEnd_1590134 < baseStart_1590134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590154 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 1, 5, 2]
def baseStart_1590154 : Nat := 118140960795 + 1590154 * 2 ^ 59
def prefixEnd_1590154 : Nat := 4983230072969 + 3 ^ 40 * 1590154 * 2
def baseEnd_1590154 : Nat := 816513316669676748862021

theorem tailTrace_1590154 : CollatzResearch.WordTrace tailWord_1590154 prefixEnd_1590154 816513316669676748862021 := by
  unfold tailWord_1590154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14499420270287777381746379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38665120720767406351323677 14499420270287777381746379)
  ·
    refine ⟨21749130405431666072619569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14499420270287777381746379 21749130405431666072619569)
    ·
      refine ⟨16311847804073749554464677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21749130405431666072619569 16311847804073749554464677)
      ·
        refine ⟨3058471463263828041462127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16311847804073749554464677 3058471463263828041462127)
        ·
          refine ⟨4587707194895742062193191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058471463263828041462127 4587707194895742062193191)
          ·
            refine ⟨6881560792343613093289787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4587707194895742062193191 6881560792343613093289787)
            ·
              refine ⟨10322341188515419639934681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6881560792343613093289787 10322341188515419639934681)
              ·
                refine ⟨7741755891386564729951011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10322341188515419639934681 7741755891386564729951011)
                ·
                  refine ⟨11612633837079847094926517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7741755891386564729951011 11612633837079847094926517)
                  ·
                    refine ⟨1088684422226235665149361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11612633837079847094926517 1088684422226235665149361)
                    ·
                      refine ⟨816513316669676748862021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1088684422226235665149361 816513316669676748862021)
                      ·
                        rfl

theorem cell23_1590154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_1590154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590154 prefixEnd_1590154 := by exact prefixLift 1590154
  have htrace : WordTrace (prefixWord ++ tailWord_1590154) baseStart_1590154 baseEnd_1590154 := by
    simpa [prefixWord, tailWord_1590154, baseEnd_1590154] using wordTrace_append hprefix tailTrace_1590154
  have hstable : (prefixWord ++ tailWord_1590154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590154).length < 2 ^ (prefixWord ++ tailWord_1590154).sum := by decide
  have hdescent : baseEnd_1590154 < baseStart_1590154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590164 : List Nat := [2, 4, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1590164 : Nat := 118140960795 + 1590164 * 2 ^ 59
def prefixEnd_1590164 : Nat := 4983230072969 + 3 ^ 40 * 1590164 * 2
def baseEnd_1590164 : Nat := 272172817158740569912325

theorem tailTrace_1590164 : CollatzResearch.WordTrace tailWord_1590164 prefixEnd_1590164 272172817158740569912325 := by
  unfold tailWord_1590164
  simp only [CollatzResearch.WordTrace]
  refine ⟨28999022905557440617424773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38665363874076587489899697 28999022905557440617424773)
  ·
    refine ⟨5437316794792020115767145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28999022905557440617424773 5437316794792020115767145)
    ·
      refine ⟨4077987596094015086825359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5437316794792020115767145 4077987596094015086825359)
      ·
        refine ⟨6116981394141022630238039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4077987596094015086825359 6116981394141022630238039)
        ·
          refine ⟨9175472091211533945357059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6116981394141022630238039 9175472091211533945357059)
          ·
            refine ⟨13763208136817300918035589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9175472091211533945357059 13763208136817300918035589)
            ·
              refine ⟨2580601525653243922131673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13763208136817300918035589 2580601525653243922131673)
              ·
                refine ⟨1935451144239932941598755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2580601525653243922131673 1935451144239932941598755)
                ·
                  refine ⟨2903176716359899412398133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935451144239932941598755 2903176716359899412398133)
                  ·
                    refine ⟨272172817158740569912325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2903176716359899412398133 272172817158740569912325)
                    ·
                      rfl

theorem cell23_1590164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1590164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590164 prefixEnd_1590164 := by exact prefixLift 1590164
  have htrace : WordTrace (prefixWord ++ tailWord_1590164) baseStart_1590164 baseEnd_1590164 := by
    simpa [prefixWord, tailWord_1590164, baseEnd_1590164] using wordTrace_append hprefix tailTrace_1590164
  have hstable : (prefixWord ++ tailWord_1590164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590164).length < 2 ^ (prefixWord ++ tailWord_1590164).sum := by decide
  have hdescent : baseEnd_1590164 < baseStart_1590164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590167 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 2, 6, 2]
def baseStart_1590167 : Nat := 118140960795 + 1590167 * 2 ^ 59
def prefixEnd_1590167 : Nat := 4983230072969 + 3 ^ 40 * 1590167 * 2
def baseEnd_1590167 : Nat := 816519991918185197999461

theorem tailTrace_1590167 : CollatzResearch.WordTrace tailWord_1590167 prefixEnd_1590167 816519991918185197999461 := by
  unfold tailWord_1590167
  simp only [CollatzResearch.WordTrace]
  refine ⟨57998155230104012747208755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38665436820069341831472503 57998155230104012747208755)
  ·
    refine ⟨86997232845156019120813133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57998155230104012747208755 86997232845156019120813133)
    ·
      refine ⟨32623962316933507170304925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86997232845156019120813133 32623962316933507170304925)
      ·
        refine ⟨12233985868850065188864347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32623962316933507170304925 12233985868850065188864347)
        ·
          refine ⟨18350978803275097783296521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12233985868850065188864347 18350978803275097783296521)
          ·
            refine ⟨13763234102456323337472391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18350978803275097783296521 13763234102456323337472391)
            ·
              refine ⟨20644851153684485006208587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13763234102456323337472391 20644851153684485006208587)
              ·
                refine ⟨30967276730526727509312881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20644851153684485006208587 30967276730526727509312881)
                ·
                  refine ⟨23225457547895045631984661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30967276730526727509312881 23225457547895045631984661)
                  ·
                    refine ⟨1088693322557580263999281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23225457547895045631984661 1088693322557580263999281)
                    ·
                      refine ⟨816519991918185197999461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1088693322557580263999281 816519991918185197999461)
                      ·
                        rfl

theorem cell23_1590167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_1590167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590167 prefixEnd_1590167 := by exact prefixLift 1590167
  have htrace : WordTrace (prefixWord ++ tailWord_1590167) baseStart_1590167 baseEnd_1590167 := by
    simpa [prefixWord, tailWord_1590167, baseEnd_1590167] using wordTrace_append hprefix tailTrace_1590167
  have hstable : (prefixWord ++ tailWord_1590167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590167).length < 2 ^ (prefixWord ++ tailWord_1590167).sum := by decide
  have hdescent : baseEnd_1590167 < baseStart_1590167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590178 : List Nat := [3, 3, 1, 2, 2, 1, 3, 3, 1, 1, 3]
def baseStart_1590178 : Nat := 118140960795 + 1590178 * 2 ^ 59
def prefixEnd_1590178 : Nat := 4983230072969 + 3 ^ 40 * 1590178 * 2
def baseEnd_1590178 : Nat := 816525640205384654961911

theorem tailTrace_1590178 : CollatzResearch.WordTrace tailWord_1590178 prefixEnd_1590178 816525640205384654961911 := by
  unfold tailWord_1590178
  simp only [CollatzResearch.WordTrace]
  refine ⟨14499639108266040406464797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38665704288709441083906125 14499639108266040406464797)
  ·
    refine ⟨5437364665599765152424299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14499639108266040406464797 5437364665599765152424299)
    ·
      refine ⟨8156046998399647728636449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5437364665599765152424299 8156046998399647728636449)
      ·
        refine ⟨6117035248799735796477337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8156046998399647728636449 6117035248799735796477337)
        ·
          refine ⟨4587776436599801847358003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6117035248799735796477337 4587776436599801847358003)
          ·
            refine ⟨6881664654899702771037005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4587776436599801847358003 6881664654899702771037005)
            ·
              refine ⟨2580624245587388539138877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6881664654899702771037005 2580624245587388539138877)
              ·
                refine ⟨967734092095270702177079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2580624245587388539138877 967734092095270702177079)
                ·
                  refine ⟨1451601138142906053265619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967734092095270702177079 1451601138142906053265619)
                  ·
                    refine ⟨2177401707214359079898429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1451601138142906053265619 2177401707214359079898429)
                    ·
                      refine ⟨816525640205384654961911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2177401707214359079898429 816525640205384654961911)
                      ·
                        rfl

theorem cell23_1590178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_1590178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590178 prefixEnd_1590178 := by exact prefixLift 1590178
  have htrace : WordTrace (prefixWord ++ tailWord_1590178) baseStart_1590178 baseEnd_1590178 := by
    simpa [prefixWord, tailWord_1590178, baseEnd_1590178] using wordTrace_append hprefix tailTrace_1590178
  have hstable : (prefixWord ++ tailWord_1590178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590178).length < 2 ^ (prefixWord ++ tailWord_1590178).sum := by decide
  have hdescent : baseEnd_1590178 < baseStart_1590178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590201 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 3, 2, 2]
def baseStart_1590201 : Nat := 118140960795 + 1590201 * 2 ^ 59
def prefixEnd_1590201 : Nat := 4983230072969 + 3 ^ 40 * 1590201 * 2
def baseEnd_1590201 : Nat := 816537450260438064974305

theorem tailTrace_1590201 : CollatzResearch.WordTrace tailWord_1590201 prefixEnd_1590201 816537450260438064974305 := by
  unfold tailWord_1590201
  simp only [CollatzResearch.WordTrace]
  refine ⟨57999395311980836553946457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38666263541320557702630971 57999395311980836553946457)
  ·
    refine ⟨43499546483985627415459843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57999395311980836553946457 43499546483985627415459843)
    ·
      refine ⟨65249319725978441123189765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43499546483985627415459843 65249319725978441123189765)
      ·
        refine ⟨12234247448620957710598081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65249319725978441123189765 12234247448620957710598081)
        ·
          refine ⟨9175685586465718282948561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12234247448620957710598081 9175685586465718282948561)
          ·
            refine ⟨6881764189849288712211421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9175685586465718282948561 6881764189849288712211421)
            ·
              refine ⟨2580661571193483267079283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6881764189849288712211421 2580661571193483267079283)
              ·
                refine ⟨3870992356790224900618925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2580661571193483267079283 3870992356790224900618925)
                ·
                  refine ⟨1451622133796334337732097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3870992356790224900618925 1451622133796334337732097)
                  ·
                    refine ⟨1088716600347250753299073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1451622133796334337732097 1088716600347250753299073)
                    ·
                      refine ⟨816537450260438064974305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1088716600347250753299073 816537450260438064974305)
                      ·
                        rfl

theorem cell23_1590201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_1590201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590201 prefixEnd_1590201 := by exact prefixLift 1590201
  have htrace : WordTrace (prefixWord ++ tailWord_1590201) baseStart_1590201 baseEnd_1590201 := by
    simpa [prefixWord, tailWord_1590201, baseEnd_1590201] using wordTrace_append hprefix tailTrace_1590201
  have hstable : (prefixWord ++ tailWord_1590201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590201).length < 2 ^ (prefixWord ++ tailWord_1590201).sum := by decide
  have hdescent : baseEnd_1590201 < baseStart_1590201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590234 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3]
def baseStart_1590234 : Nat := 118140960795 + 1590234 * 2 ^ 59
def prefixEnd_1590234 : Nat := 4983230072969 + 3 ^ 40 * 1590234 * 2
def baseEnd_1590234 : Nat := 816554395122036435861653

theorem tailTrace_1590234 : CollatzResearch.WordTrace tailWord_1590234 prefixEnd_1590234 816554395122036435861653 := by
  unfold tailWord_1590234
  simp only [CollatzResearch.WordTrace]
  refine ⟨14500149730215320797474439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38667065947240855459931837 14500149730215320797474439)
  ·
    refine ⟨21750224595322981196211659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14500149730215320797474439 21750224595322981196211659)
    ·
      refine ⟨32625336892984471794317489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21750224595322981196211659 32625336892984471794317489)
      ·
        refine ⟨24469002669738353845738117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32625336892984471794317489 24469002669738353845738117)
        ·
          refine ⟨4587938000575941346075897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24469002669738353845738117 4587938000575941346075897)
          ·
            refine ⟨3440953500431956009556923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4587938000575941346075897 3440953500431956009556923)
            ·
              refine ⟨5161430250647934014335385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3440953500431956009556923 5161430250647934014335385)
              ·
                refine ⟨3871072687985950510751539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5161430250647934014335385 3871072687985950510751539)
                ·
                  refine ⟨5806609031978925766127309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3871072687985950510751539 5806609031978925766127309)
                  ·
                    refine ⟨2177478386992097162297741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5806609031978925766127309 2177478386992097162297741)
                    ·
                      refine ⟨816554395122036435861653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2177478386992097162297741 816554395122036435861653)
                      ·
                        rfl

theorem cell23_1590234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_1590234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590234 prefixEnd_1590234 := by exact prefixLift 1590234
  have htrace : WordTrace (prefixWord ++ tailWord_1590234) baseStart_1590234 baseEnd_1590234 := by
    simpa [prefixWord, tailWord_1590234, baseEnd_1590234] using wordTrace_append hprefix tailTrace_1590234
  have hstable : (prefixWord ++ tailWord_1590234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590234).length < 2 ^ (prefixWord ++ tailWord_1590234).sum := by decide
  have hdescent : baseEnd_1590234 < baseStart_1590234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590257 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_1590257 : Nat := 118140960795 + 1590257 * 2 ^ 59
def prefixEnd_1590257 : Nat := 4983230072969 + 3 ^ 40 * 1590257 * 2
def baseEnd_1590257 : Nat := 816566205177089845874047

theorem tailTrace_1590257 : CollatzResearch.WordTrace tailWord_1590257 prefixEnd_1590257 816566205177089845874047 := by
  unfold tailWord_1590257
  simp only [CollatzResearch.WordTrace]
  refine ⟨58001437799777958117985025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38667625199851972078656683 58001437799777958117985025)
  ·
    refine ⟨43501078349833468588488769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58001437799777958117985025 43501078349833468588488769)
    ·
      refine ⟨32625808762375101441366577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43501078349833468588488769 32625808762375101441366577)
      ·
        refine ⟨24469356571781326081024933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32625808762375101441366577 24469356571781326081024933)
        ·
          refine ⟨4588004357208998640192175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24469356571781326081024933 4588004357208998640192175)
          ·
            refine ⟨6882006535813497960288263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588004357208998640192175 6882006535813497960288263)
            ·
              refine ⟨10323009803720246940432395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6882006535813497960288263 10323009803720246940432395)
              ·
                refine ⟨15484514705580370410648593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10323009803720246940432395 15484514705580370410648593)
                ·
                  refine ⟨11613386029185277807986445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15484514705580370410648593 11613386029185277807986445)
                  ·
                    refine ⟨4355019760944479177994917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11613386029185277807986445 4355019760944479177994917)
                    ·
                      refine ⟨816566205177089845874047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4355019760944479177994917 816566205177089845874047)
                      ·
                        rfl

theorem cell23_1590257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_1590257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590257 prefixEnd_1590257 := by exact prefixLift 1590257
  have htrace : WordTrace (prefixWord ++ tailWord_1590257) baseStart_1590257 baseEnd_1590257 := by
    simpa [prefixWord, tailWord_1590257, baseEnd_1590257] using wordTrace_append hprefix tailTrace_1590257
  have hstable : (prefixWord ++ tailWord_1590257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590257).length < 2 ^ (prefixWord ++ tailWord_1590257).sum := by decide
  have hdescent : baseEnd_1590257 < baseStart_1590257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590277 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 2, 4, 3]
def baseStart_1590277 : Nat := 118140960795 + 1590277 * 2 ^ 59
def prefixEnd_1590277 : Nat := 4983230072969 + 3 ^ 40 * 1590277 * 2
def baseEnd_1590277 : Nat := 816576474790179767623955

theorem tailTrace_1590277 : CollatzResearch.WordTrace tailWord_1590277 prefixEnd_1590277 816576474790179767623955 := by
  unfold tailWord_1590277
  simp only [CollatzResearch.WordTrace]
  refine ⟨58002167259705501533713085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38668111506470334355808723 58002167259705501533713085)
  ·
    refine ⟨21750812722389563075142407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58002167259705501533713085 21750812722389563075142407)
    ·
      refine ⟨32626219083584344612713611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21750812722389563075142407 32626219083584344612713611)
      ·
        refine ⟨48939328625376516919070417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32626219083584344612713611 48939328625376516919070417)
        ·
          refine ⟨36704496469032387689302813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48939328625376516919070417 36704496469032387689302813)
          ·
            refine ⟨13764186175887145383488555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36704496469032387689302813 13764186175887145383488555)
            ·
              refine ⟨20646279263830718075232833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13764186175887145383488555 20646279263830718075232833)
              ·
                refine ⟨15484709447873038556424625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20646279263830718075232833 15484709447873038556424625)
                ·
                  refine ⟨11613532085904778917318469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15484709447873038556424625 11613532085904778917318469)
                  ·
                    refine ⟨2177537266107146046997213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11613532085904778917318469 2177537266107146046997213)
                    ·
                      refine ⟨816576474790179767623955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2177537266107146046997213 816576474790179767623955)
                      ·
                        rfl

theorem cell23_1590277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_1590277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590277 prefixEnd_1590277 := by exact prefixLift 1590277
  have htrace : WordTrace (prefixWord ++ tailWord_1590277) baseStart_1590277 baseEnd_1590277 := by
    simpa [prefixWord, tailWord_1590277, baseEnd_1590277] using wordTrace_append hprefix tailTrace_1590277
  have hstable : (prefixWord ++ tailWord_1590277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590277).length < 2 ^ (prefixWord ++ tailWord_1590277).sum := by decide
  have hdescent : baseEnd_1590277 < baseStart_1590277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590295 : List Nat := [1, 1, 3, 5, 1, 3, 2, 1, 1, 3, 2]
def baseStart_1590295 : Nat := 118140960795 + 1590295 * 2 ^ 59
def prefixEnd_1590295 : Nat := 4983230072969 + 3 ^ 40 * 1590295 * 2
def baseEnd_1590295 : Nat := 816585717441960697198873

theorem tailTrace_1590295 : CollatzResearch.WordTrace tailWord_1590295 prefixEnd_1590295 816585717441960697198873 := by
  unfold tailWord_1590295
  simp only [CollatzResearch.WordTrace]
  refine ⟨58002823773640290607868339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38668549182426860405245559 58002823773640290607868339)
  ·
    refine ⟨87004235660460435911802509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58002823773640290607868339 87004235660460435911802509)
    ·
      refine ⟨32626588372672663466925941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87004235660460435911802509 32626588372672663466925941)
      ·
        refine ⟨3058742659938062200024307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32626588372672663466925941 3058742659938062200024307)
        ·
          refine ⟨4588113989907093300036461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058742659938062200024307 4588113989907093300036461)
          ·
            refine ⟨1720542746215159987513673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4588113989907093300036461 1720542746215159987513673)
            ·
              refine ⟨1290407059661369990635255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1720542746215159987513673 1290407059661369990635255)
              ·
                refine ⟨1935610589492054985952883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290407059661369990635255 1935610589492054985952883)
                ·
                  refine ⟨2903415884238082478929325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935610589492054985952883 2903415884238082478929325)
                  ·
                    refine ⟨1088780956589280929598497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2903415884238082478929325 1088780956589280929598497)
                    ·
                      refine ⟨816585717441960697198873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1088780956589280929598497 816585717441960697198873)
                      ·
                        rfl

theorem cell23_1590295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_1590295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590295 prefixEnd_1590295 := by exact prefixLift 1590295
  have htrace : WordTrace (prefixWord ++ tailWord_1590295) baseStart_1590295 baseEnd_1590295 := by
    simpa [prefixWord, tailWord_1590295, baseEnd_1590295] using wordTrace_append hprefix tailTrace_1590295
  have hstable : (prefixWord ++ tailWord_1590295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590295).length < 2 ^ (prefixWord ++ tailWord_1590295).sum := by decide
  have hdescent : baseEnd_1590295 < baseStart_1590295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590308 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 4, 2, 2]
def baseStart_1590308 : Nat := 118140960795 + 1590308 * 2 ^ 59
def prefixEnd_1590308 : Nat := 4983230072969 + 3 ^ 40 * 1590308 * 2
def baseEnd_1590308 : Nat := 816592392690469146336313

theorem tailTrace_1590308 : CollatzResearch.WordTrace tailWord_1590308 prefixEnd_1590308 816592392690469146336313 := by
  unfold tailWord_1590308
  simp only [CollatzResearch.WordTrace]
  refine ⟨29001648961296596914045789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38668865281728795885394385 29001648961296596914045789)
  ·
    refine ⟨10875618360486223842767171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29001648961296596914045789 10875618360486223842767171)
    ·
      refine ⟨16313427540729335764150757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10875618360486223842767171 16313427540729335764150757)
      ·
        refine ⟨3058767663886750455778267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16313427540729335764150757 3058767663886750455778267)
        ·
          refine ⟨4588151495830125683667401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058767663886750455778267 4588151495830125683667401)
          ·
            refine ⟨3441113621872594262750551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4588151495830125683667401 3441113621872594262750551)
            ·
              refine ⟨5161670432808891394125827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441113621872594262750551 5161670432808891394125827)
              ·
                refine ⟨7742505649213337091188741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5161670432808891394125827 7742505649213337091188741)
                ·
                  refine ⟨1451719809227500704597889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7742505649213337091188741 1451719809227500704597889)
                  ·
                    refine ⟨1088789856920625528448417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1451719809227500704597889 1088789856920625528448417)
                    ·
                      refine ⟨816592392690469146336313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1088789856920625528448417 816592392690469146336313)
                      ·
                        rfl

theorem cell23_1590308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_1590308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590308 prefixEnd_1590308 := by exact prefixLift 1590308
  have htrace : WordTrace (prefixWord ++ tailWord_1590308) baseStart_1590308 baseEnd_1590308 := by
    simpa [prefixWord, tailWord_1590308, baseEnd_1590308] using wordTrace_append hprefix tailTrace_1590308
  have hstable : (prefixWord ++ tailWord_1590308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590308).length < 2 ^ (prefixWord ++ tailWord_1590308).sum := by decide
  have hdescent : baseEnd_1590308 < baseStart_1590308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590365 : List Nat := [1, 4, 4, 1, 2, 1, 3, 2, 5]
def baseStart_1590365 : Nat := 118140960795 + 1590365 * 2 ^ 59
def prefixEnd_1590365 : Nat := 4983230072969 + 3 ^ 40 * 1590365 * 2
def baseEnd_1590365 : Nat := 90735740120863935924839

theorem tailTrace_1590365 : CollatzResearch.WordTrace tailWord_1590365 prefixEnd_1590365 90735740120863935924839 := by
  unfold tailWord_1590365
  simp only [CollatzResearch.WordTrace]
  refine ⟨58005376883386692562916549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38670251255591128375277699 58005376883386692562916549)
  ·
    refine ⟨10876008165635004855546853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58005376883386692562916549 10876008165635004855546853)
    ·
      refine ⟨2039251531056563410415035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10876008165635004855546853 2039251531056563410415035)
      ·
        refine ⟨3058877296584845115622553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2039251531056563410415035 3058877296584845115622553)
        ·
          refine ⟨2294157972438633836716915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3058877296584845115622553 2294157972438633836716915)
          ·
            refine ⟨3441236958657950755075373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294157972438633836716915 3441236958657950755075373)
            ·
              refine ⟨1290463859496731533153265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3441236958657950755075373 1290463859496731533153265)
              ·
                refine ⟨967847894622548649864949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290463859496731533153265 967847894622548649864949)
                ·
                  refine ⟨90735740120863935924839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 967847894622548649864949 90735740120863935924839)
                  ·
                    rfl

theorem cell23_1590365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_1590365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590365 prefixEnd_1590365 := by exact prefixLift 1590365
  have htrace : WordTrace (prefixWord ++ tailWord_1590365) baseStart_1590365 baseEnd_1590365 := by
    simpa [prefixWord, tailWord_1590365, baseEnd_1590365] using wordTrace_append hprefix tailTrace_1590365
  have hstable : (prefixWord ++ tailWord_1590365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590365).length < 2 ^ (prefixWord ++ tailWord_1590365).sum := by decide
  have hdescent : baseEnd_1590365 < baseStart_1590365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590384 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 3]
def baseStart_1590384 : Nat := 118140960795 + 1590384 * 2 ^ 59
def prefixEnd_1590384 : Nat := 4983230072969 + 3 ^ 40 * 1590384 * 2
def baseEnd_1590384 : Nat := 816631417220210848985963

theorem tailTrace_1590384 : CollatzResearch.WordTrace tailWord_1590384 prefixEnd_1590384 816631417220210848985963 := by
  unfold tailWord_1590384
  simp only [CollatzResearch.WordTrace]
  refine ⟨29003034935158929403929103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38670713246878572538572137 29003034935158929403929103)
  ·
    refine ⟨43504552402738394105893655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29003034935158929403929103 43504552402738394105893655)
    ·
      refine ⟨65256828604107591158840483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43504552402738394105893655 65256828604107591158840483)
      ·
        refine ⟨97885242906161386738260725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65256828604107591158840483 97885242906161386738260725)
        ·
          refine ⟨9176741522452630006711943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97885242906161386738260725 9176741522452630006711943)
          ·
            refine ⟨13765112283678945010067915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9176741522452630006711943 13765112283678945010067915)
            ·
              refine ⟨20647668425518417515101873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13765112283678945010067915 20647668425518417515101873)
              ·
                refine ⟨15485751319138813136326405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20647668425518417515101873 15485751319138813136326405)
                ·
                  refine ⟨2903578372338527463061201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15485751319138813136326405 2903578372338527463061201)
                  ·
                    refine ⟨2177683779253895597295901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2903578372338527463061201 2177683779253895597295901)
                    ·
                      refine ⟨816631417220210848985963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2177683779253895597295901 816631417220210848985963)
                      ·
                        rfl

theorem cell23_1590384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 3].length) (baseStart_1590384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590384 prefixEnd_1590384 := by exact prefixLift 1590384
  have htrace : WordTrace (prefixWord ++ tailWord_1590384) baseStart_1590384 baseEnd_1590384 := by
    simpa [prefixWord, tailWord_1590384, baseEnd_1590384] using wordTrace_append hprefix tailTrace_1590384
  have hstable : (prefixWord ++ tailWord_1590384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590384).length < 2 ^ (prefixWord ++ tailWord_1590384).sum := by decide
  have hdescent : baseEnd_1590384 < baseStart_1590384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590401 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_1590401 : Nat := 118140960795 + 1590401 * 2 ^ 59
def prefixEnd_1590401 : Nat := 4983230072969 + 3 ^ 40 * 1590401 * 2
def baseEnd_1590401 : Nat := 816640146391337282473385

theorem tailTrace_1590401 : CollatzResearch.WordTrace tailWord_1590401 prefixEnd_1590401 816640146391337282473385 := by
  unfold tailWord_1590401
  simp only [CollatzResearch.WordTrace]
  refine ⟨58006689911256270711227057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38671126607504180474151371 58006689911256270711227057)
  ·
    refine ⟨43505017433442203033420293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58006689911256270711227057 43505017433442203033420293)
    ·
      refine ⟨8157190768770413068766305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43505017433442203033420293 8157190768770413068766305)
      ·
        refine ⟨6117893076577809801574729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8157190768770413068766305 6117893076577809801574729)
        ·
          refine ⟨4588419807433357351181047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6117893076577809801574729 4588419807433357351181047)
          ·
            refine ⟨6882629711150036026771571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588419807433357351181047 6882629711150036026771571)
            ·
              refine ⟨10323944566725054040157357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6882629711150036026771571 10323944566725054040157357)
              ·
                refine ⟨3871479212521895265059009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10323944566725054040157357 3871479212521895265059009)
                ·
                  refine ⟨2903609409391421448794257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3871479212521895265059009 2903609409391421448794257)
                  ·
                    refine ⟨2177707057043566086595693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2903609409391421448794257 2177707057043566086595693)
                    ·
                      refine ⟨816640146391337282473385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2177707057043566086595693 816640146391337282473385)
                      ·
                        rfl

theorem cell23_1590401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_1590401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590401 prefixEnd_1590401 := by exact prefixLift 1590401
  have htrace : WordTrace (prefixWord ++ tailWord_1590401) baseStart_1590401 baseEnd_1590401 := by
    simpa [prefixWord, tailWord_1590401, baseEnd_1590401] using wordTrace_append hprefix tailTrace_1590401
  have hstable : (prefixWord ++ tailWord_1590401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590401).length < 2 ^ (prefixWord ++ tailWord_1590401).sum := by decide
  have hdescent : baseEnd_1590401 < baseStart_1590401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590407 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_1590407 : Nat := 118140960795 + 1590407 * 2 ^ 59
def prefixEnd_1590407 : Nat := 4983230072969 + 3 ^ 40 * 1590407 * 2
def baseEnd_1590407 : Nat := 816643227275264258998357

theorem tailTrace_1590407 : CollatzResearch.WordTrace tailWord_1590407 prefixEnd_1590407 816643227275264258998357 := by
  unfold tailWord_1590407
  simp only [CollatzResearch.WordTrace]
  refine ⟨58006908749234533735945475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38671272499489689157296983 58006908749234533735945475)
  ·
    refine ⟨87010363123851800603918213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58006908749234533735945475 87010363123851800603918213)
    ·
      refine ⟨16314443085722212613234665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87010363123851800603918213 16314443085722212613234665)
      ·
        refine ⟨12235832314291659459925999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16314443085722212613234665 12235832314291659459925999)
        ·
          refine ⟨18353748471437489189888999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12235832314291659459925999 18353748471437489189888999)
          ·
            refine ⟨27530622707156233784833499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18353748471437489189888999 27530622707156233784833499)
            ·
              refine ⟨41295934060734350677250249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27530622707156233784833499 41295934060734350677250249)
              ·
                refine ⟨30971950545550763007937687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41295934060734350677250249 30971950545550763007937687)
                ·
                  refine ⟨46457925818326144511906531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30971950545550763007937687 46457925818326144511906531)
                  ·
                    refine ⟨69686888727489216767859797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46457925818326144511906531 69686888727489216767859797)
                    ·
                      refine ⟨816643227275264258998357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 69686888727489216767859797 816643227275264258998357)
                      ·
                        rfl

theorem cell23_1590407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_1590407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590407 prefixEnd_1590407 := by exact prefixLift 1590407
  have htrace : WordTrace (prefixWord ++ tailWord_1590407) baseStart_1590407 baseEnd_1590407 := by
    simpa [prefixWord, tailWord_1590407, baseEnd_1590407] using wordTrace_append hprefix tailTrace_1590407
  have hstable : (prefixWord ++ tailWord_1590407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590407).length < 2 ^ (prefixWord ++ tailWord_1590407).sum := by decide
  have hdescent : baseEnd_1590407 < baseStart_1590407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590468 : List Nat := [2, 3, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_1590468 : Nat := 118140960795 + 1590468 * 2 ^ 59
def prefixEnd_1590468 : Nat := 4983230072969 + 3 ^ 40 * 1590468 * 2
def baseEnd_1590468 : Nat := 272224849865062840111859

theorem tailTrace_1590468 : CollatzResearch.WordTrace tailWord_1590468 prefixEnd_1590468 272224849865062840111859 := by
  unfold tailWord_1590468
  simp only [CollatzResearch.WordTrace]
  refine ⟨29004566801006770576958029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38672755734675694102610705 29004566801006770576958029)
  ·
    refine ⟨10876712550377538966359261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29004566801006770576958029 10876712550377538966359261)
    ·
      refine ⟨4078767206391577112384723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10876712550377538966359261 4078767206391577112384723)
      ·
        refine ⟨6118150809587365668577085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4078767206391577112384723 6118150809587365668577085)
        ·
          refine ⟨2294306553595262125716407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6118150809587365668577085 2294306553595262125716407)
          ·
            refine ⟨3441459830392893188574611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294306553595262125716407 3441459830392893188574611)
            ·
              refine ⟨5162189745589339782861917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441459830392893188574611 5162189745589339782861917)
              ·
                refine ⟨1935821154596002418573219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5162189745589339782861917 1935821154596002418573219)
                ·
                  refine ⟨2903731731894003627859829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935821154596002418573219 2903731731894003627859829)
                  ·
                    refine ⟨272224849865062840111859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2903731731894003627859829 272224849865062840111859)
                    ·
                      rfl

theorem cell23_1590468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_1590468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590468 prefixEnd_1590468 := by exact prefixLift 1590468
  have htrace : WordTrace (prefixWord ++ tailWord_1590468) baseStart_1590468 baseEnd_1590468 := by
    simpa [prefixWord, tailWord_1590468, baseEnd_1590468] using wordTrace_append hprefix tailTrace_1590468
  have hstable : (prefixWord ++ tailWord_1590468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590468).length < 2 ^ (prefixWord ++ tailWord_1590468).sum := by decide
  have hdescent : baseEnd_1590468 < baseStart_1590468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590501 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 6]
def baseStart_1590501 : Nat := 118140960795 + 1590501 * 2 ^ 59
def prefixEnd_1590501 : Nat := 4983230072969 + 3 ^ 40 * 1590501 * 2
def baseEnd_1590501 : Nat := 816691494456786891222925

theorem tailTrace_1590501 : CollatzResearch.WordTrace tailWord_1590501 prefixEnd_1590501 816691494456786891222925 := by
  unfold tailWord_1590501
  simp only [CollatzResearch.WordTrace]
  refine ⟨58010337210893987789867357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38673558140595991859911571 58010337210893987789867357)
  ·
    refine ⟨21753876454085245421200259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58010337210893987789867357 21753876454085245421200259)
    ·
      refine ⟨32630814681127868131800389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21753876454085245421200259 32630814681127868131800389)
      ·
        refine ⟨6118277752711475274712573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32630814681127868131800389 6118277752711475274712573)
        ·
          refine ⟨2294354157266803228017215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6118277752711475274712573 2294354157266803228017215)
          ·
            refine ⟨3441531235900204842025823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294354157266803228017215 3441531235900204842025823)
            ·
              refine ⟨5162296853850307263038735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441531235900204842025823 5162296853850307263038735)
              ·
                refine ⟨7743445280775460894558103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5162296853850307263038735 7743445280775460894558103)
                ·
                  refine ⟨11615167921163191341837155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7743445280775460894558103 11615167921163191341837155)
                  ·
                    refine ⟨17422751881744787012755733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11615167921163191341837155 17422751881744787012755733)
                    ·
                      refine ⟨816691494456786891222925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17422751881744787012755733 816691494456786891222925)
                      ·
                        rfl

theorem cell23_1590501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_1590501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590501 prefixEnd_1590501 := by exact prefixLift 1590501
  have htrace : WordTrace (prefixWord ++ tailWord_1590501) baseStart_1590501 baseEnd_1590501 := by
    simpa [prefixWord, tailWord_1590501, baseEnd_1590501] using wordTrace_append hprefix tailTrace_1590501
  have hstable : (prefixWord ++ tailWord_1590501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590501).length < 2 ^ (prefixWord ++ tailWord_1590501).sum := by decide
  have hdescent : baseEnd_1590501 < baseStart_1590501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590508 : List Nat := [2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 3]
def baseStart_1590508 : Nat := 118140960795 + 1590508 * 2 ^ 59
def prefixEnd_1590508 : Nat := 4983230072969 + 3 ^ 40 * 1590508 * 2
def baseEnd_1590508 : Nat := 816695088821368363835393

theorem tailTrace_1590508 : CollatzResearch.WordTrace tailWord_1590508 prefixEnd_1590508 816695088821368363835393 := by
  unfold tailWord_1590508
  simp only [CollatzResearch.WordTrace]
  refine ⟨29005296260934313992686089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38673728347912418656914785 29005296260934313992686089)
  ·
    refine ⟨21753972195700735494514567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29005296260934313992686089 21753972195700735494514567)
    ·
      refine ⟨32630958293551103241771851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21753972195700735494514567 32630958293551103241771851)
      ·
        refine ⟨48946437440326654862657777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32630958293551103241771851 48946437440326654862657777)
        ·
          refine ⟨36709828080244991146993333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48946437440326654862657777 36709828080244991146993333)
          ·
            refine ⟨3441546382522967920030625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36709828080244991146993333 3441546382522967920030625)
            ·
              refine ⟨2581159786892225940022969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3441546382522967920030625 2581159786892225940022969)
              ·
                refine ⟨1935869840169169455017227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2581159786892225940022969 1935869840169169455017227)
                ·
                  refine ⟨2903804760253754182525841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935869840169169455017227 2903804760253754182525841)
                  ·
                    refine ⟨2177853570190315636894381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2903804760253754182525841 2177853570190315636894381)
                    ·
                      refine ⟨816695088821368363835393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2177853570190315636894381 816695088821368363835393)
                      ·
                        rfl

theorem cell23_1590508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_1590508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590508 prefixEnd_1590508 := by exact prefixLift 1590508
  have htrace : WordTrace (prefixWord ++ tailWord_1590508) baseStart_1590508 baseEnd_1590508 := by
    simpa [prefixWord, tailWord_1590508, baseEnd_1590508] using wordTrace_append hprefix tailTrace_1590508
  have hstable : (prefixWord ++ tailWord_1590508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590508).length < 2 ^ (prefixWord ++ tailWord_1590508).sum := by decide
  have hdescent : baseEnd_1590508 < baseStart_1590508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590521 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 6, 1, 3]
def baseStart_1590521 : Nat := 118140960795 + 1590521 * 2 ^ 59
def prefixEnd_1590521 : Nat := 4983230072969 + 3 ^ 40 * 1590521 * 2
def baseEnd_1590521 : Nat := 816701764069876812972833

theorem tailTrace_1590521 : CollatzResearch.WordTrace tailWord_1590521 prefixEnd_1590521 816701764069876812972833 := by
  unfold tailWord_1590521
  simp only [CollatzResearch.WordTrace]
  refine ⟨58011066670821531205595417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38674044447214354137063611 58011066670821531205595417)
  ·
    refine ⟨43508300003116148404196563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58011066670821531205595417 43508300003116148404196563)
    ·
      refine ⟨65262450004674222606294845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43508300003116148404196563 65262450004674222606294845)
      ·
        refine ⟨24473418751752833477360567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65262450004674222606294845 24473418751752833477360567)
        ·
          refine ⟨36710128127629250216040851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24473418751752833477360567 36710128127629250216040851)
          ·
            refine ⟨55065192191443875324061277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36710128127629250216040851 55065192191443875324061277)
            ·
              refine ⟨20649447071791453246522979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55065192191443875324061277 20649447071791453246522979)
              ·
                refine ⟨30974170607687179869784469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20649447071791453246522979 30974170607687179869784469)
                ·
                  refine ⟨1451914247235336556396147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30974170607687179869784469 1451914247235336556396147)
                  ·
                    refine ⟨2177871370853004834594221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1451914247235336556396147 2177871370853004834594221)
                    ·
                      refine ⟨816701764069876812972833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2177871370853004834594221 816701764069876812972833)
                      ·
                        rfl

theorem cell23_1590521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_1590521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590521 prefixEnd_1590521 := by exact prefixLift 1590521
  have htrace : WordTrace (prefixWord ++ tailWord_1590521) baseStart_1590521 baseEnd_1590521 := by
    simpa [prefixWord, tailWord_1590521, baseEnd_1590521] using wordTrace_append hprefix tailTrace_1590521
  have hstable : (prefixWord ++ tailWord_1590521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590521).length < 2 ^ (prefixWord ++ tailWord_1590521).sum := by decide
  have hdescent : baseEnd_1590521 < baseStart_1590521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590538 : List Nat := [3, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3]
def baseStart_1590538 : Nat := 118140960795 + 1590538 * 2 ^ 59
def prefixEnd_1590538 : Nat := 4983230072969 + 3 ^ 40 * 1590538 * 2
def baseEnd_1590538 : Nat := 816710493241003246460255

theorem tailTrace_1590538 : CollatzResearch.WordTrace tailWord_1590538 prefixEnd_1590538 816710493241003246460255 := by
  unfold tailWord_1590538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14502921677939985777241067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38674457807839962072642845 14502921677939985777241067)
  ·
    refine ⟨21754382516909978665861601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14502921677939985777241067 21754382516909978665861601)
    ·
      refine ⟨16315786887682483999396201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21754382516909978665861601 16315786887682483999396201)
      ·
        refine ⟨12236840165761862999547151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16315786887682483999396201 12236840165761862999547151)
        ·
          refine ⟨18355260248642794499320727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12236840165761862999547151 18355260248642794499320727)
          ·
            refine ⟨27532890372964191748981091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18355260248642794499320727 27532890372964191748981091)
            ·
              refine ⟨41299335559446287623471637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27532890372964191748981091 41299335559446287623471637)
              ·
                refine ⟨1935906354349044732350233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41299335559446287623471637 1935906354349044732350233)
                ·
                  refine ⟨1451929765761783549262675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1935906354349044732350233 1451929765761783549262675)
                  ·
                    refine ⟨2177894648642675323894013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1451929765761783549262675 2177894648642675323894013)
                    ·
                      refine ⟨816710493241003246460255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2177894648642675323894013 816710493241003246460255)
                      ·
                        rfl

theorem cell23_1590538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_1590538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590538 prefixEnd_1590538 := by exact prefixLift 1590538
  have htrace : WordTrace (prefixWord ++ tailWord_1590538) baseStart_1590538 baseEnd_1590538 := by
    simpa [prefixWord, tailWord_1590538, baseEnd_1590538] using wordTrace_append hprefix tailTrace_1590538
  have hstable : (prefixWord ++ tailWord_1590538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590538).length < 2 ^ (prefixWord ++ tailWord_1590538).sum := by decide
  have hdescent : baseEnd_1590538 < baseStart_1590538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590565 : List Nat := [1, 3, 1, 2, 4, 1, 3, 2, 1, 3, 2]
def baseStart_1590565 : Nat := 118140960795 + 1590565 * 2 ^ 59
def prefixEnd_1590565 : Nat := 4983230072969 + 3 ^ 40 * 1590565 * 2
def baseEnd_1590565 : Nat := 816724357218674640822631

theorem tailTrace_1590565 : CollatzResearch.WordTrace tailWord_1590565 prefixEnd_1590565 816724357218674640822631 := by
  unfold tailWord_1590565
  simp only [CollatzResearch.WordTrace]
  refine ⟨58012671482662126720197149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38675114321774751146798099 58012671482662126720197149)
  ·
    refine ⟨21754751805998297520073931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58012671482662126720197149 21754751805998297520073931)
    ·
      refine ⟨32632127708997446280110897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21754751805998297520073931 32632127708997446280110897)
      ·
        refine ⟨24474095781748084710083173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32632127708997446280110897 24474095781748084710083173)
        ·
          refine ⟨4588892959077765883140595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24474095781748084710083173 4588892959077765883140595)
          ·
            refine ⟨6883339438616648824710893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588892959077765883140595 6883339438616648824710893)
            ·
              refine ⟨2581252289481243309266585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6883339438616648824710893 2581252289481243309266585)
              ·
                refine ⟨1935939217110932481949939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2581252289481243309266585 1935939217110932481949939)
                ·
                  refine ⟨2903908825666398722924909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935939217110932481949939 2903908825666398722924909)
                  ·
                    refine ⟨1088965809624899521096841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2903908825666398722924909 1088965809624899521096841)
                    ·
                      refine ⟨816724357218674640822631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1088965809624899521096841 816724357218674640822631)
                      ·
                        rfl

theorem cell23_1590565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_1590565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590565 prefixEnd_1590565 := by exact prefixLift 1590565
  have htrace : WordTrace (prefixWord ++ tailWord_1590565) baseStart_1590565 baseEnd_1590565 := by
    simpa [prefixWord, tailWord_1590565, baseEnd_1590565] using wordTrace_append hprefix tailTrace_1590565
  have hstable : (prefixWord ++ tailWord_1590565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590565).length < 2 ^ (prefixWord ++ tailWord_1590565).sum := by decide
  have hdescent : baseEnd_1590565 < baseStart_1590565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590578 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2]
def baseStart_1590578 : Nat := 118140960795 + 1590578 * 2 ^ 59
def prefixEnd_1590578 : Nat := 4983230072969 + 3 ^ 40 * 1590578 * 2
def baseEnd_1590578 : Nat := 816731032467183089960071

theorem tailTrace_1590578 : CollatzResearch.WordTrace tailWord_1590578 prefixEnd_1590578 816731032467183089960071 := by
  unfold tailWord_1590578
  simp only [CollatzResearch.WordTrace]
  refine ⟨14503286407903757485105097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38675430421076686626946925 14503286407903757485105097)
  ·
    refine ⟨10877464805927818113828823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14503286407903757485105097 10877464805927818113828823)
    ·
      refine ⟨16316197208891727170743235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10877464805927818113828823 16316197208891727170743235)
      ·
        refine ⟨24474295813337590756114853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16316197208891727170743235 24474295813337590756114853)
        ·
          refine ⟨4588930465000798266771535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24474295813337590756114853 4588930465000798266771535)
          ·
            refine ⟨6883395697501197400157303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588930465000798266771535 6883395697501197400157303)
            ·
              refine ⟨10325093546251796100235955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6883395697501197400157303 10325093546251796100235955)
              ·
                refine ⟨15487640319377694150353933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10325093546251796100235955 15487640319377694150353933)
                ·
                  refine ⟨5807865119766635306382725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15487640319377694150353933 5807865119766635306382725)
                  ·
                    refine ⟨1088974709956244119946761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5807865119766635306382725 1088974709956244119946761)
                    ·
                      refine ⟨816731032467183089960071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1088974709956244119946761 816731032467183089960071)
                      ·
                        rfl

theorem cell23_1590578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_1590578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590578 prefixEnd_1590578 := by exact prefixLift 1590578
  have htrace : WordTrace (prefixWord ++ tailWord_1590578) baseStart_1590578 baseEnd_1590578 := by
    simpa [prefixWord, tailWord_1590578, baseEnd_1590578] using wordTrace_append hprefix tailTrace_1590578
  have hstable : (prefixWord ++ tailWord_1590578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590578).length < 2 ^ (prefixWord ++ tailWord_1590578).sum := by decide
  have hdescent : baseEnd_1590578 < baseStart_1590578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590581 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1590581 : Nat := 118140960795 + 1590581 * 2 ^ 59
def prefixEnd_1590581 : Nat := 4983230072969 + 3 ^ 40 * 1590581 * 2
def baseEnd_1590581 : Nat := 816732572909146578222557

theorem tailTrace_1590581 : CollatzResearch.WordTrace tailWord_1590581 prefixEnd_1590581 816732572909146578222557 := by
  unfold tailWord_1590581
  simp only [CollatzResearch.WordTrace]
  refine ⟨58013255050604161452779597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38675503367069440968519731 58013255050604161452779597)
  ·
    refine ⟨21754970643976560544792349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58013255050604161452779597 21754970643976560544792349)
    ·
      refine ⟨8158113991491210204297131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21754970643976560544792349 8158113991491210204297131)
      ·
        refine ⟨12237170987236815306445697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8158113991491210204297131 12237170987236815306445697)
        ·
          refine ⟨9177878240427611479834273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12237170987236815306445697 9177878240427611479834273)
          ·
            refine ⟨6883408680320708609875705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9177878240427611479834273 6883408680320708609875705)
            ·
              refine ⟨5162556510240531457406779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6883408680320708609875705 5162556510240531457406779)
              ·
                refine ⟨7743834765360797186110169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5162556510240531457406779 7743834765360797186110169)
                ·
                  refine ⟨5807876074020597889582627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7743834765360797186110169 5807876074020597889582627)
                  ·
                    refine ⟨8711814111030896834373941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5807876074020597889582627 8711814111030896834373941)
                    ·
                      refine ⟨816732572909146578222557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8711814111030896834373941 816732572909146578222557)
                      ·
                        rfl

theorem cell23_1590581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1590581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590581 prefixEnd_1590581 := by exact prefixLift 1590581
  have htrace : WordTrace (prefixWord ++ tailWord_1590581) baseStart_1590581 baseEnd_1590581 := by
    simpa [prefixWord, tailWord_1590581, baseEnd_1590581] using wordTrace_append hprefix tailTrace_1590581
  have hstable : (prefixWord ++ tailWord_1590581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590581).length < 2 ^ (prefixWord ++ tailWord_1590581).sum := by decide
  have hdescent : baseEnd_1590581 < baseStart_1590581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590605 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1590605 : Nat := 118140960795 + 1590605 * 2 ^ 59
def prefixEnd_1590605 : Nat := 4983230072969 + 3 ^ 40 * 1590605 * 2
def baseEnd_1590605 : Nat := 272248298814951494774149

theorem tailTrace_1590605 : CollatzResearch.WordTrace tailWord_1590605 prefixEnd_1590605 272248298814951494774149 := by
  unfold tailWord_1590605
  simp only [CollatzResearch.WordTrace]
  refine ⟨58014130402517213551653269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38676086935011475701102179 58014130402517213551653269)
  ·
    refine ⟨2719412362617994385233747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58014130402517213551653269 2719412362617994385233747)
    ·
      refine ⟨4079118543926991577850621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2719412362617994385233747 4079118543926991577850621)
      ·
        refine ⟨1529669453972621841693983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4079118543926991577850621 1529669453972621841693983)
        ·
          refine ⟨2294504180958932762540975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529669453972621841693983 2294504180958932762540975)
          ·
            refine ⟨3441756271438399143811463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294504180958932762540975 3441756271438399143811463)
            ·
              refine ⟨5162634407157598715717195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3441756271438399143811463 5162634407157598715717195)
              ·
                refine ⟨7743951610736398073575793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5162634407157598715717195 7743951610736398073575793)
                ·
                  refine ⟨5807963708052298555181845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7743951610736398073575793 5807963708052298555181845)
                  ·
                    refine ⟨272248298814951494774149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5807963708052298555181845 272248298814951494774149)
                    ·
                      rfl

theorem cell23_1590605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1590605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590605 prefixEnd_1590605 := by exact prefixLift 1590605
  have htrace : WordTrace (prefixWord ++ tailWord_1590605) baseStart_1590605 baseEnd_1590605 := by
    simpa [prefixWord, tailWord_1590605, baseEnd_1590605] using wordTrace_append hprefix tailTrace_1590605
  have hstable : (prefixWord ++ tailWord_1590605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590605).length < 2 ^ (prefixWord ++ tailWord_1590605).sum := by decide
  have hdescent : baseEnd_1590605 < baseStart_1590605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590611 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 3]
def baseStart_1590611 : Nat := 118140960795 + 1590611 * 2 ^ 59
def prefixEnd_1590611 : Nat := 4983230072969 + 3 ^ 40 * 1590611 * 2
def baseEnd_1590611 : Nat := 816747977328781460847419

theorem tailTrace_1590611 : CollatzResearch.WordTrace tailWord_1590611 prefixEnd_1590611 816747977328781460847419 := by
  unfold tailWord_1590611
  simp only [CollatzResearch.WordTrace]
  refine ⟨58014349240495476576371687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38676232826996984384247791 58014349240495476576371687)
  ·
    refine ⟨87021523860743214864557531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58014349240495476576371687 87021523860743214864557531)
    ·
      refine ⟨130532285791114822296836297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87021523860743214864557531 130532285791114822296836297)
      ·
        refine ⟨97899214343336116722627223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130532285791114822296836297 97899214343336116722627223)
        ·
          refine ⟨146848821515004175083940835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97899214343336116722627223 146848821515004175083940835)
          ·
            refine ⟨220273232272506262625911253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146848821515004175083940835 220273232272506262625911253)
            ·
              refine ⟨5162653881386865530294795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 220273232272506262625911253 5162653881386865530294795)
              ·
                refine ⟨7743980822080298295442193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5162653881386865530294795 7743980822080298295442193)
                ·
                  refine ⟨5807985616560223721581645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7743980822080298295442193 5807985616560223721581645)
                  ·
                    refine ⟨2177994606210083895593117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5807985616560223721581645 2177994606210083895593117)
                    ·
                      refine ⟨816747977328781460847419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2177994606210083895593117 816747977328781460847419)
                      ·
                        rfl

theorem cell23_1590611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 3].length) (baseStart_1590611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590611 prefixEnd_1590611 := by exact prefixLift 1590611
  have htrace : WordTrace (prefixWord ++ tailWord_1590611) baseStart_1590611 baseEnd_1590611 := by
    simpa [prefixWord, tailWord_1590611, baseEnd_1590611] using wordTrace_append hprefix tailTrace_1590611
  have hstable : (prefixWord ++ tailWord_1590611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590611).length < 2 ^ (prefixWord ++ tailWord_1590611).sum := by decide
  have hdescent : baseEnd_1590611 < baseStart_1590611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590651 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 4]
def baseStart_1590651 : Nat := 118140960795 + 1590651 * 2 ^ 59
def prefixEnd_1590651 : Nat := 4983230072969 + 3 ^ 40 * 1590651 * 2
def baseEnd_1590651 : Nat := 816768516554961304347235

theorem tailTrace_1590651 : CollatzResearch.WordTrace tailWord_1590651 prefixEnd_1590651 816768516554961304347235 := by
  unfold tailWord_1590651
  simp only [CollatzResearch.WordTrace]
  refine ⟨58015808160350563407827807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38677205440233708938551871 58015808160350563407827807)
  ·
    refine ⟨87023712240525845111741711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58015808160350563407827807 87023712240525845111741711)
    ·
      refine ⟨130535568360788767667612567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87023712240525845111741711 130535568360788767667612567)
      ·
        refine ⟨195803352541183151501418851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130535568360788767667612567 195803352541183151501418851)
        ·
          refine ⟨293705028811774727252128277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195803352541183151501418851 293705028811774727252128277)
          ·
            refine ⟨13767423225551940339943513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 293705028811774727252128277 13767423225551940339943513)
            ·
              refine ⟨10325567419163955254957635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13767423225551940339943513 10325567419163955254957635)
              ·
                refine ⟨15488351128745932882436453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10325567419163955254957635 15488351128745932882436453)
                ·
                  refine ⟨2904065836639862415456835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15488351128745932882436453 2904065836639862415456835)
                  ·
                    refine ⟨4356098754959793623185253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2904065836639862415456835 4356098754959793623185253)
                    ·
                      refine ⟨816768516554961304347235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4356098754959793623185253 816768516554961304347235)
                      ·
                        rfl

theorem cell23_1590651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 4].length) (baseStart_1590651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590651 prefixEnd_1590651 := by exact prefixLift 1590651
  have htrace : WordTrace (prefixWord ++ tailWord_1590651) baseStart_1590651 baseEnd_1590651 := by
    simpa [prefixWord, tailWord_1590651, baseEnd_1590651] using wordTrace_append hprefix tailTrace_1590651
  have hstable : (prefixWord ++ tailWord_1590651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590651).length < 2 ^ (prefixWord ++ tailWord_1590651).sum := by decide
  have hdescent : baseEnd_1590651 < baseStart_1590651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590668 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 2, 4, 2]
def baseStart_1590668 : Nat := 118140960795 + 1590668 * 2 ^ 59
def prefixEnd_1590668 : Nat := 4983230072969 + 3 ^ 40 * 1590668 * 2
def baseEnd_1590668 : Nat := 816777245726087737834657

theorem tailTrace_1590668 : CollatzResearch.WordTrace tailWord_1590668 prefixEnd_1590668 816777245726087737834657 := by
  unfold tailWord_1590668
  simp only [CollatzResearch.WordTrace]
  refine ⟨29008214100644487655598329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38677618800859316874131105 29008214100644487655598329)
  ·
    refine ⟨21756160575483365741698747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29008214100644487655598329 21756160575483365741698747)
    ·
      refine ⟨32634240863225048612548121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21756160575483365741698747 32634240863225048612548121)
      ·
        refine ⟨24475680647418786459411091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32634240863225048612548121 24475680647418786459411091)
        ·
          refine ⟨36713520971128179689116637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24475680647418786459411091 36713520971128179689116637)
          ·
            refine ⟨13767570364173067383418739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36713520971128179689116637 13767570364173067383418739)
            ·
              refine ⟨20651355546259601075128109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13767570364173067383418739 20651355546259601075128109)
              ·
                refine ⟨7744258329847350403173041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20651355546259601075128109 7744258329847350403173041)
                ·
                  refine ⟨5808193747385512802379781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7744258329847350403173041 5808193747385512802379781)
                  ·
                    refine ⟨1089036327634783650446209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5808193747385512802379781 1089036327634783650446209)
                    ·
                      refine ⟨816777245726087737834657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1089036327634783650446209 816777245726087737834657)
                      ·
                        rfl

theorem cell23_1590668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_1590668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590668 prefixEnd_1590668 := by exact prefixLift 1590668
  have htrace : WordTrace (prefixWord ++ tailWord_1590668) baseStart_1590668 baseEnd_1590668 := by
    simpa [prefixWord, tailWord_1590668, baseEnd_1590668] using wordTrace_append hprefix tailTrace_1590668
  have hstable : (prefixWord ++ tailWord_1590668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590668).length < 2 ^ (prefixWord ++ tailWord_1590668).sum := by decide
  have hdescent : baseEnd_1590668 < baseStart_1590668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590688 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 3]
def baseStart_1590688 : Nat := 118140960795 + 1590688 * 2 ^ 59
def prefixEnd_1590688 : Nat := 4983230072969 + 3 ^ 40 * 1590688 * 2
def baseEnd_1590688 : Nat := 816787515339177659584565

theorem tailTrace_1590688 : CollatzResearch.WordTrace tailWord_1590688 prefixEnd_1590688 816787515339177659584565 := by
  unfold tailWord_1590688
  simp only [CollatzResearch.WordTrace]
  refine ⟨29008578830608259363462359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38678105107477679151283145 29008578830608259363462359)
  ·
    refine ⟨43512868245912389045193539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29008578830608259363462359 43512868245912389045193539)
    ·
      refine ⟨65269302368868583567790309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43512868245912389045193539 65269302368868583567790309)
      ·
        refine ⟨12237994194162859418960683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65269302368868583567790309 12237994194162859418960683)
        ·
          refine ⟨18356991291244289128441025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12237994194162859418960683 18356991291244289128441025)
          ·
            refine ⟨13767743468433216846330769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18356991291244289128441025 13767743468433216846330769)
            ·
              refine ⟨10325807601324912634748077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13767743468433216846330769 10325807601324912634748077)
              ·
                refine ⟨3872177850496842238030529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10325807601324912634748077 3872177850496842238030529)
                ·
                  refine ⟨2904133387872631678522897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3872177850496842238030529 2904133387872631678522897)
                  ·
                    refine ⟨2178100040904473758892173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2904133387872631678522897 2178100040904473758892173)
                    ·
                      refine ⟨816787515339177659584565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2178100040904473758892173 816787515339177659584565)
                      ·
                        rfl

theorem cell23_1590688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_1590688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590688 prefixEnd_1590688 := by exact prefixLift 1590688
  have htrace : WordTrace (prefixWord ++ tailWord_1590688) baseStart_1590688 baseEnd_1590688 := by
    simpa [prefixWord, tailWord_1590688, baseEnd_1590688] using wordTrace_append hprefix tailTrace_1590688
  have hstable : (prefixWord ++ tailWord_1590688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590688).length < 2 ^ (prefixWord ++ tailWord_1590688).sum := by decide
  have hdescent : baseEnd_1590688 < baseStart_1590688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590745 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 2, 3, 2]
def baseStart_1590745 : Nat := 118140960795 + 1590745 * 2 ^ 59
def prefixEnd_1590745 : Nat := 4983230072969 + 3 ^ 40 * 1590745 * 2
def baseEnd_1590745 : Nat := 816816783736483936571803

theorem tailTrace_1590745 : CollatzResearch.WordTrace tailWord_1590745 prefixEnd_1590745 816816783736483936571803 := by
  unfold tailWord_1590745
  simp only [CollatzResearch.WordTrace]
  refine ⟨58019236622010017461749689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38679491081340011641166459 58019236622010017461749689)
  ·
    refine ⟨43514427466507513096312267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58019236622010017461749689 43514427466507513096312267)
    ·
      refine ⟨65271641199761269644468401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43514427466507513096312267 65271641199761269644468401)
      ·
        refine ⟨48953730899820952233351301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65271641199761269644468401 48953730899820952233351301)
        ·
          refine ⟨9178824543716428543753369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48953730899820952233351301 9178824543716428543753369)
          ·
            refine ⟨6884118407787321407815027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9178824543716428543753369 6884118407787321407815027)
            ·
              refine ⟨10326177611680982111722541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6884118407787321407815027 10326177611680982111722541)
              ·
                refine ⟨3872316604380368291895953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10326177611680982111722541 3872316604380368291895953)
                ·
                  refine ⟨2904237453285276218921965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3872316604380368291895953 2904237453285276218921965)
                  ·
                    refine ⟨1089089044981978582095737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2904237453285276218921965 1089089044981978582095737)
                    ·
                      refine ⟨816816783736483936571803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1089089044981978582095737 816816783736483936571803)
                      ·
                        rfl

theorem cell23_1590745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 3, 2].length) (baseStart_1590745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590745 prefixEnd_1590745 := by exact prefixLift 1590745
  have htrace : WordTrace (prefixWord ++ tailWord_1590745) baseStart_1590745 baseEnd_1590745 := by
    simpa [prefixWord, tailWord_1590745, baseEnd_1590745] using wordTrace_append hprefix tailTrace_1590745
  have hstable : (prefixWord ++ tailWord_1590745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590745).length < 2 ^ (prefixWord ++ tailWord_1590745).sum := by decide
  have hdescent : baseEnd_1590745 < baseStart_1590745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590769 : List Nat := [1, 2, 2, 2, 3, 2, 4, 2, 1, 1, 3]
def baseStart_1590769 : Nat := 118140960795 + 1590769 * 2 ^ 59
def prefixEnd_1590769 : Nat := 4983230072969 + 3 ^ 40 * 1590769 * 2
def baseEnd_1590769 : Nat := 816829107272191842671693

theorem tailTrace_1590769 : CollatzResearch.WordTrace tailWord_1590769 prefixEnd_1590769 816829107272191842671693 := by
  unfold tailWord_1590769
  simp only [CollatzResearch.WordTrace]
  refine ⟨58020111973923069560623361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38680074649282046373748907 58020111973923069560623361)
  ·
    refine ⟨43515083980442302170467521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58020111973923069560623361 43515083980442302170467521)
    ·
      refine ⟨32636312985331726627850641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43515083980442302170467521 32636312985331726627850641)
      ·
        refine ⟨24477234738998794970887981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32636312985331726627850641 24477234738998794970887981)
        ·
          refine ⟨9178963027124548114082993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24477234738998794970887981 9178963027124548114082993)
          ·
            refine ⟨6884222270343411085562245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9178963027124548114082993 6884222270343411085562245)
            ·
              refine ⟨1290791675689389578542921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6884222270343411085562245 1290791675689389578542921)
              ·
                refine ⟨968093756767042183907191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290791675689389578542921 968093756767042183907191)
                ·
                  refine ⟨1452140635150563275860787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968093756767042183907191 1452140635150563275860787)
                  ·
                    refine ⟨2178210952725844913791181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1452140635150563275860787 2178210952725844913791181)
                    ·
                      refine ⟨816829107272191842671693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2178210952725844913791181 816829107272191842671693)
                      ·
                        rfl

theorem cell23_1590769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_1590769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590769 prefixEnd_1590769 := by exact prefixLift 1590769
  have htrace : WordTrace (prefixWord ++ tailWord_1590769) baseStart_1590769 baseEnd_1590769 := by
    simpa [prefixWord, tailWord_1590769, baseEnd_1590769] using wordTrace_append hprefix tailTrace_1590769
  have hstable : (prefixWord ++ tailWord_1590769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590769).length < 2 ^ (prefixWord ++ tailWord_1590769).sum := by decide
  have hdescent : baseEnd_1590769 < baseStart_1590769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590771 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 6]
def baseStart_1590771 : Nat := 118140960795 + 1590771 * 2 ^ 59
def prefixEnd_1590771 : Nat := 4983230072969 + 3 ^ 40 * 1590771 * 2
def baseEnd_1590771 : Nat := 816830134233500834846683

theorem tailTrace_1590771 : CollatzResearch.WordTrace tailWord_1590771 prefixEnd_1590771 816830134233500834846683 := by
  unfold tailWord_1590771
  simp only [CollatzResearch.WordTrace]
  refine ⟨58020184919915823902196167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38680123279943882601464111 58020184919915823902196167)
  ·
    refine ⟨87030277379873735853294251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58020184919915823902196167 87030277379873735853294251)
    ·
      refine ⟨130545416069810603779941377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87030277379873735853294251 130545416069810603779941377)
      ·
        refine ⟨97909062052357952834956033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130545416069810603779941377 97909062052357952834956033)
        ·
          refine ⟨73431796539268464626217025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97909062052357952834956033 73431796539268464626217025)
          ·
            refine ⟨55073847404451348469662769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73431796539268464626217025 55073847404451348469662769)
            ·
              refine ⟨41305385553338511352247077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55073847404451348469662769 41305385553338511352247077)
              ·
                refine ⟨7744759791250970878546327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41305385553338511352247077 7744759791250970878546327)
                ·
                  refine ⟨11617139686876456317819491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7744759791250970878546327 11617139686876456317819491)
                  ·
                    refine ⟨17425709530314684476729237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11617139686876456317819491 17425709530314684476729237)
                    ·
                      refine ⟨816830134233500834846683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17425709530314684476729237 816830134233500834846683)
                      ·
                        rfl

theorem cell23_1590771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_1590771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590771 prefixEnd_1590771 := by exact prefixLift 1590771
  have htrace : WordTrace (prefixWord ++ tailWord_1590771) baseStart_1590771 baseEnd_1590771 := by
    simpa [prefixWord, tailWord_1590771, baseEnd_1590771] using wordTrace_append hprefix tailTrace_1590771
  have hstable : (prefixWord ++ tailWord_1590771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590771).length < 2 ^ (prefixWord ++ tailWord_1590771).sum := by decide
  have hdescent : baseEnd_1590771 < baseStart_1590771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590778 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3]
def baseStart_1590778 : Nat := 118140960795 + 1590778 * 2 ^ 59
def prefixEnd_1590778 : Nat := 4983230072969 + 3 ^ 40 * 1590778 * 2
def baseEnd_1590778 : Nat := 816833728598082307459151

theorem tailTrace_1590778 : CollatzResearch.WordTrace tailWord_1590778 prefixEnd_1590778 816833728598082307459151 := by
  unfold tailWord_1590778
  simp only [CollatzResearch.WordTrace]
  refine ⟨14505110057722616024425247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38680293487260309398467325 14505110057722616024425247)
  ·
    refine ⟨21757665086583924036637871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14505110057722616024425247 21757665086583924036637871)
    ·
      refine ⟨32636497629875886054956807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21757665086583924036637871 32636497629875886054956807)
      ·
        refine ⟨48954746444813829082435211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32636497629875886054956807 48954746444813829082435211)
        ·
          refine ⟨73432119667220743623652817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48954746444813829082435211 73432119667220743623652817)
          ·
            refine ⟨55074089750415557717739613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73432119667220743623652817 55074089750415557717739613)
            ·
              refine ⟨20652783656405834144152355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55074089750415557717739613 20652783656405834144152355)
              ·
                refine ⟨30979175484608751216228533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20652783656405834144152355 30979175484608751216228533)
                ·
                  refine ⟨2904297701682070426521425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30979175484608751216228533 2904297701682070426521425)
                  ·
                    refine ⟨2178223276261552819891069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2904297701682070426521425 2178223276261552819891069)
                    ·
                      refine ⟨816833728598082307459151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2178223276261552819891069 816833728598082307459151)
                      ·
                        rfl

theorem cell23_1590778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_1590778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590778 prefixEnd_1590778 := by exact prefixLift 1590778
  have htrace : WordTrace (prefixWord ++ tailWord_1590778) baseStart_1590778 baseEnd_1590778 := by
    simpa [prefixWord, tailWord_1590778, baseEnd_1590778] using wordTrace_append hprefix tailTrace_1590778
  have hstable : (prefixWord ++ tailWord_1590778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590778).length < 2 ^ (prefixWord ++ tailWord_1590778).sum := by decide
  have hdescent : baseEnd_1590778 < baseStart_1590778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590785 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 1, 6]
def baseStart_1590785 : Nat := 118140960795 + 1590785 * 2 ^ 59
def prefixEnd_1590785 : Nat := 4983230072969 + 3 ^ 40 * 1590785 * 2
def baseEnd_1590785 : Nat := 272279107654221260023873

theorem tailTrace_1590785 : CollatzResearch.WordTrace tailWord_1590785 prefixEnd_1590785 272279107654221260023873 := by
  unfold tailWord_1590785
  simp only [CollatzResearch.WordTrace]
  refine ⟨58020695541865104293205809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38680463694576736195470539 58020695541865104293205809)
  ·
    refine ⟨43515521656398828219904357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58020695541865104293205809 43515521656398828219904357)
    ·
      refine ⟨8159160310574780291232067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43515521656398828219904357 8159160310574780291232067)
      ·
        refine ⟨12238740465862170436848101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8159160310574780291232067 12238740465862170436848101)
        ·
          refine ⟨2294763837349156956909019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12238740465862170436848101 2294763837349156956909019)
          ·
            refine ⟨3442145756023735435363529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294763837349156956909019 3442145756023735435363529)
            ·
              refine ⟨2581609317017801576522647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3442145756023735435363529 2581609317017801576522647)
              ·
                refine ⟨3872413975526702364783971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2581609317017801576522647 3872413975526702364783971)
                ·
                  refine ⟨5808620963290053547175957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3872413975526702364783971 5808620963290053547175957)
                  ·
                    refine ⟨272279107654221260023873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5808620963290053547175957 272279107654221260023873)
                    ·
                      rfl

theorem cell23_1590785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_1590785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590785 prefixEnd_1590785 := by exact prefixLift 1590785
  have htrace : WordTrace (prefixWord ++ tailWord_1590785) baseStart_1590785 baseEnd_1590785 := by
    simpa [prefixWord, tailWord_1590785, baseEnd_1590785] using wordTrace_append hprefix tailTrace_1590785
  have hstable : (prefixWord ++ tailWord_1590785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590785).length < 2 ^ (prefixWord ++ tailWord_1590785).sum := by decide
  have hdescent : baseEnd_1590785 < baseStart_1590785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590819 : List Nat := [1, 1, 1, 4, 6, 1, 1, 2, 2, 4]
def baseStart_1590819 : Nat := 118140960795 + 1590819 * 2 ^ 59
def prefixEnd_1590819 : Nat := 4983230072969 + 3 ^ 40 * 1590819 * 2
def baseEnd_1590819 : Nat := 272284927101638882348821

theorem tailTrace_1590819 : CollatzResearch.WordTrace tailWord_1590819 prefixEnd_1590819 272284927101638882348821 := by
  unfold tailWord_1590819
  simp only [CollatzResearch.WordTrace]
  refine ⟨58021935623741928099943511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38681290415827952066629007 58021935623741928099943511)
  ·
    refine ⟨87032903435612892149915267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58021935623741928099943511 87032903435612892149915267)
    ·
      refine ⟨130549355153419338224872901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87032903435612892149915267 130549355153419338224872901)
      ·
        refine ⟨24478004091266125917163669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130549355153419338224872901 24478004091266125917163669)
        ·
          refine ⟨1147406441778099652367047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24478004091266125917163669 1147406441778099652367047)
          ·
            refine ⟨1721109662667149478550571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147406441778099652367047 1721109662667149478550571)
            ·
              refine ⟨2581664494000724217825857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1721109662667149478550571 2581664494000724217825857)
              ·
                refine ⟨1936248370500543163369393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2581664494000724217825857 1936248370500543163369393)
                ·
                  refine ⟨1452186277875407372527045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1936248370500543163369393 1452186277875407372527045)
                  ·
                    refine ⟨272284927101638882348821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1452186277875407372527045 272284927101638882348821)
                    ·
                      rfl

theorem cell23_1590819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 2, 4].length) (baseStart_1590819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590819 prefixEnd_1590819 := by exact prefixLift 1590819
  have htrace : WordTrace (prefixWord ++ tailWord_1590819) baseStart_1590819 baseEnd_1590819 := by
    simpa [prefixWord, tailWord_1590819, baseEnd_1590819] using wordTrace_append hprefix tailTrace_1590819
  have hstable : (prefixWord ++ tailWord_1590819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590819).length < 2 ^ (prefixWord ++ tailWord_1590819).sum := by decide
  have hdescent : baseEnd_1590819 < baseStart_1590819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590865 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 3, 4, 2]
def baseStart_1590865 : Nat := 118140960795 + 1590865 * 2 ^ 59
def prefixEnd_1590865 : Nat := 4983230072969 + 3 ^ 40 * 1590865 * 2
def baseEnd_1590865 : Nat := 816878401415023467071251

theorem tailTrace_1590865 : CollatzResearch.WordTrace tailWord_1590865 prefixEnd_1590865 816878401415023467071251 := by
  unfold tailWord_1590865
  simp only [CollatzResearch.WordTrace]
  refine ⟨58023613381575277956118049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38682408921050185304078699 58023613381575277956118049)
  ·
    refine ⟨43517710036181458467088537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58023613381575277956118049 43517710036181458467088537)
    ·
      refine ⟨32638282527136093850316403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43517710036181458467088537 32638282527136093850316403)
      ·
        refine ⟨48957423790704140775474605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32638282527136093850316403 48957423790704140775474605)
        ·
          refine ⟨18359033921514052790802977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48957423790704140775474605 18359033921514052790802977)
          ·
            refine ⟨13769275441135539593102233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18359033921514052790802977 13769275441135539593102233)
            ·
              refine ⟨10326956580851654694826675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13769275441135539593102233 10326956580851654694826675)
              ·
                refine ⟨15490434871277482042240013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10326956580851654694826675 15490434871277482042240013)
                ·
                  refine ⟨5808913076729055765840005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15490434871277482042240013 5808913076729055765840005)
                  ·
                    refine ⟨1089171201886697956095001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5808913076729055765840005 1089171201886697956095001)
                    ·
                      refine ⟨816878401415023467071251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1089171201886697956095001 816878401415023467071251)
                      ·
                        rfl

theorem cell23_1590865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 4, 2].length) (baseStart_1590865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590865 prefixEnd_1590865 := by exact prefixLift 1590865
  have htrace : WordTrace (prefixWord ++ tailWord_1590865) baseStart_1590865 baseEnd_1590865 := by
    simpa [prefixWord, tailWord_1590865, baseEnd_1590865] using wordTrace_append hprefix tailTrace_1590865
  have hstable : (prefixWord ++ tailWord_1590865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590865).length < 2 ^ (prefixWord ++ tailWord_1590865).sum := by decide
  have hdescent : baseEnd_1590865 < baseStart_1590865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590893 : List Nat := [1, 5, 1, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_1590893 : Nat := 118140960795 + 1590893 * 2 ^ 59
def prefixEnd_1590893 : Nat := 4983230072969 + 3 ^ 40 * 1590893 * 2
def baseEnd_1590893 : Nat := 816892778873349357521123

theorem tailTrace_1590893 : CollatzResearch.WordTrace tailWord_1590893 prefixEnd_1590893 816892778873349357521123 := by
  unfold tailWord_1590893
  simp only [CollatzResearch.WordTrace]
  refine ⟨58024634625473838738137333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38683089750315892492091555 58024634625473838738137333)
  ·
    refine ⟨5439809496138172381700375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58024634625473838738137333 5439809496138172381700375)
    ·
      refine ⟨8159714244207258572550563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5439809496138172381700375 8159714244207258572550563)
      ·
        refine ⟨12239571366310887858825845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8159714244207258572550563 12239571366310887858825845)
        ·
          refine ⟨1147459815591645736764923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12239571366310887858825845 1147459815591645736764923)
          ·
            refine ⟨1721189723387468605147385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147459815591645736764923 1721189723387468605147385)
            ·
              refine ⟨1290892292540601453860539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1721189723387468605147385 1290892292540601453860539)
              ·
                refine ⟨1936338438810902180790809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290892292540601453860539 1936338438810902180790809)
                ·
                  refine ⟨1452253829108176635593107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1936338438810902180790809 1452253829108176635593107)
                  ·
                    refine ⟨2178380743662264953389661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1452253829108176635593107 2178380743662264953389661)
                    ·
                      refine ⟨816892778873349357521123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2178380743662264953389661 816892778873349357521123)
                      ·
                        rfl

theorem cell23_1590893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_1590893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590893 prefixEnd_1590893 := by exact prefixLift 1590893
  have htrace : WordTrace (prefixWord ++ tailWord_1590893) baseStart_1590893 baseEnd_1590893 := by
    simpa [prefixWord, tailWord_1590893, baseEnd_1590893] using wordTrace_append hprefix tailTrace_1590893
  have hstable : (prefixWord ++ tailWord_1590893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590893).length < 2 ^ (prefixWord ++ tailWord_1590893).sum := by decide
  have hdescent : baseEnd_1590893 < baseStart_1590893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590935 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 2, 5]
def baseStart_1590935 : Nat := 118140960795 + 1590935 * 2 ^ 59
def prefixEnd_1590935 : Nat := 4983230072969 + 3 ^ 40 * 1590935 * 2
def baseEnd_1590935 : Nat := 272304781686946064398643

theorem tailTrace_1590935 : CollatzResearch.WordTrace tailWord_1590935 prefixEnd_1590935 272304781686946064398643 := by
  unfold tailWord_1590935
  simp only [CollatzResearch.WordTrace]
  refine ⟨58026166491321679911166259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38684110994214453274110839 58026166491321679911166259)
  ·
    refine ⟨87039249736982519866749389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58026166491321679911166259 87039249736982519866749389)
    ·
      refine ⟨32639718651368444950031021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87039249736982519866749389 32639718651368444950031021)
      ·
        refine ⟨12239894494263166856261633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32639718651368444950031021 12239894494263166856261633)
        ·
          refine ⟨9179920870697375142196225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12239894494263166856261633 9179920870697375142196225)
          ·
            refine ⟨6884940653023031356647169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9179920870697375142196225 6884940653023031356647169)
            ·
              refine ⟨5163705489767273517485377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6884940653023031356647169 5163705489767273517485377)
              ·
                refine ⟨3872779117325455138114033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5163705489767273517485377 3872779117325455138114033)
                ·
                  refine ⟨2904584337994091353585525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3872779117325455138114033 2904584337994091353585525)
                  ·
                    refine ⟨272304781686946064398643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2904584337994091353585525 272304781686946064398643)
                    ·
                      rfl

theorem cell23_1590935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_1590935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590935 prefixEnd_1590935 := by exact prefixLift 1590935
  have htrace : WordTrace (prefixWord ++ tailWord_1590935) baseStart_1590935 baseEnd_1590935 := by
    simpa [prefixWord, tailWord_1590935, baseEnd_1590935] using wordTrace_append hprefix tailTrace_1590935
  have hstable : (prefixWord ++ tailWord_1590935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590935).length < 2 ^ (prefixWord ++ tailWord_1590935).sum := by decide
  have hdescent : baseEnd_1590935 < baseStart_1590935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590945 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1590945 : Nat := 118140960795 + 1590945 * 2 ^ 59
def prefixEnd_1590945 : Nat := 4983230072969 + 3 ^ 40 * 1590945 * 2
def baseEnd_1590945 : Nat := 816919479867383154070883

theorem tailTrace_1590945 : CollatzResearch.WordTrace tailWord_1590945 prefixEnd_1590945 816919479867383154070883 := by
  unfold tailWord_1590945
  simp only [CollatzResearch.WordTrace]
  refine ⟨58026531221285451619030289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38684354147523634412686859 58026531221285451619030289)
  ·
    refine ⟨43519898415964088714272717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58026531221285451619030289 43519898415964088714272717)
    ·
      refine ⟨16319961905986533267852269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43519898415964088714272717 16319961905986533267852269)
      ·
        refine ⟨6119985714744949975444601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16319961905986533267852269 6119985714744949975444601)
        ·
          refine ⟨4589989286058712481583451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6119985714744949975444601 4589989286058712481583451)
          ·
            refine ⟨6884983929088068722375177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4589989286058712481583451 6884983929088068722375177)
            ·
              refine ⟨5163737946816051541781383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6884983929088068722375177 5163737946816051541781383)
              ·
                refine ⟨7745606920224077312672075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5163737946816051541781383 7745606920224077312672075)
                ·
                  refine ⟨11618410380336115969008113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7745606920224077312672075 11618410380336115969008113)
                  ·
                    refine ⟨8713807785252086976756085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11618410380336115969008113 8713807785252086976756085)
                    ·
                      refine ⟨816919479867383154070883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8713807785252086976756085 816919479867383154070883)
                      ·
                        rfl

theorem cell23_1590945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1590945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590945 prefixEnd_1590945 := by exact prefixLift 1590945
  have htrace : WordTrace (prefixWord ++ tailWord_1590945) baseStart_1590945 baseEnd_1590945 := by
    simpa [prefixWord, tailWord_1590945, baseEnd_1590945] using wordTrace_append hprefix tailTrace_1590945
  have hstable : (prefixWord ++ tailWord_1590945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590945).length < 2 ^ (prefixWord ++ tailWord_1590945).sum := by decide
  have hdescent : baseEnd_1590945 < baseStart_1590945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590968 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_1590968 : Nat := 118140960795 + 1590968 * 2 ^ 59
def prefixEnd_1590968 : Nat := 4983230072969 + 3 ^ 40 * 1590968 * 2
def baseEnd_1590968 : Nat := 816931289922436564083277

theorem tailTrace_1590968 : CollatzResearch.WordTrace tailWord_1590968 prefixEnd_1590968 816931289922436564083277 := by
  unfold tailWord_1590968
  simp only [CollatzResearch.WordTrace]
  refine ⟨29013685050101063273558779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38684913400134751031411705 29013685050101063273558779)
  ·
    refine ⟨43520527575151594910338169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29013685050101063273558779 43520527575151594910338169)
    ·
      refine ⟨32640395681363696182753627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43520527575151594910338169 32640395681363696182753627)
      ·
        refine ⟨48960593522045544274130441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32640395681363696182753627 48960593522045544274130441)
        ·
          refine ⟨36720445141534158205597831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48960593522045544274130441 36720445141534158205597831)
          ·
            refine ⟨55080667712301237308396747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36720445141534158205597831 55080667712301237308396747)
            ·
              refine ⟨82621001568451855962595121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55080667712301237308396747 82621001568451855962595121)
              ·
                refine ⟨61965751176338891971946341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82621001568451855962595121 61965751176338891971946341)
                ·
                  refine ⟨11618578345563542244739939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61965751176338891971946341 11618578345563542244739939)
                  ·
                    refine ⟨17427867518345313367109909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11618578345563542244739939 17427867518345313367109909)
                    ·
                      refine ⟨816931289922436564083277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17427867518345313367109909 816931289922436564083277)
                      ·
                        rfl

theorem cell23_1590968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_1590968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590968 prefixEnd_1590968 := by exact prefixLift 1590968
  have htrace : WordTrace (prefixWord ++ tailWord_1590968) baseStart_1590968 baseEnd_1590968 := by
    simpa [prefixWord, tailWord_1590968, baseEnd_1590968] using wordTrace_append hprefix tailTrace_1590968
  have hstable : (prefixWord ++ tailWord_1590968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590968).length < 2 ^ (prefixWord ++ tailWord_1590968).sum := by decide
  have hdescent : baseEnd_1590968 < baseStart_1590968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590972 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_1590972 : Nat := 118140960795 + 1590972 * 2 ^ 59
def prefixEnd_1590972 : Nat := 4983230072969 + 3 ^ 40 * 1590972 * 2
def baseEnd_1590972 : Nat := 816933343845054548433259

theorem tailTrace_1590972 : CollatzResearch.WordTrace tailWord_1590972 prefixEnd_1590972 816933343845054548433259 := by
  unfold tailWord_1590972
  simp only [CollatzResearch.WordTrace]
  refine ⟨29013757996093817615131585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38685010661458423486842113 29013757996093817615131585)
  ·
    refine ⟨21760318497070363211348689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29013757996093817615131585 21760318497070363211348689)
    ·
      refine ⟨16320238872802772408511517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21760318497070363211348689 16320238872802772408511517)
      ·
        refine ⟨6120089577301039653191819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16320238872802772408511517 6120089577301039653191819)
        ·
          refine ⟨9180134365951559479787729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6120089577301039653191819 9180134365951559479787729)
          ·
            refine ⟨6885100774463669609840797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9180134365951559479787729 6885100774463669609840797)
            ·
              refine ⟨2581912790423876103690299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6885100774463669609840797 2581912790423876103690299)
              ·
                refine ⟨3872869185635814155535449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2581912790423876103690299 3872869185635814155535449)
                ·
                  refine ⟨2904651889226860616651587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3872869185635814155535449 2904651889226860616651587)
                  ·
                    refine ⟨4356977833840290924977381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2904651889226860616651587 4356977833840290924977381)
                    ·
                      refine ⟨816933343845054548433259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4356977833840290924977381 816933343845054548433259)
                      ·
                        rfl

theorem cell23_1590972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_1590972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590972 prefixEnd_1590972 := by exact prefixLift 1590972
  have htrace : WordTrace (prefixWord ++ tailWord_1590972) baseStart_1590972 baseEnd_1590972 := by
    simpa [prefixWord, tailWord_1590972, baseEnd_1590972] using wordTrace_append hprefix tailTrace_1590972
  have hstable : (prefixWord ++ tailWord_1590972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590972).length < 2 ^ (prefixWord ++ tailWord_1590972).sum := by decide
  have hdescent : baseEnd_1590972 < baseStart_1590972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1590975 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 3]
def baseStart_1590975 : Nat := 118140960795 + 1590975 * 2 ^ 59
def prefixEnd_1590975 : Nat := 4983230072969 + 3 ^ 40 * 1590975 * 2
def baseEnd_1590975 : Nat := 816934884287018036695745

theorem tailTrace_1590975 : CollatzResearch.WordTrace tailWord_1590975 prefixEnd_1590975 816934884287018036695745 := by
  unfold tailWord_1590975
  simp only [CollatzResearch.WordTrace]
  refine ⟨58027625411176766742622379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38685083607451177828414919 58027625411176766742622379)
  ·
    refine ⟨87041438116765150113933569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58027625411176766742622379 87041438116765150113933569)
    ·
      refine ⟨65281078587573862585450177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87041438116765150113933569 65281078587573862585450177)
      ·
        refine ⟨48960808940680396939087633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65281078587573862585450177 48960808940680396939087633)
        ·
          refine ⟨36720606705510297704315725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48960808940680396939087633 36720606705510297704315725)
          ·
            refine ⟨13770227514566361639118397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36720606705510297704315725 13770227514566361639118397)
            ·
              refine ⟨5163835317962385614669399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13770227514566361639118397 5163835317962385614669399)
              ·
                refine ⟨7745752976943578422004099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5163835317962385614669399 7745752976943578422004099)
                ·
                  refine ⟨11618629465415367633006149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7745752976943578422004099 11618629465415367633006149)
                  ·
                    refine ⟨2178493024765381431188653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11618629465415367633006149 2178493024765381431188653)
                    ·
                      refine ⟨816934884287018036695745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2178493024765381431188653 816934884287018036695745)
                      ·
                        rfl

theorem cell23_1590975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_1590975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1590975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1590975 prefixEnd_1590975 := by exact prefixLift 1590975
  have htrace : WordTrace (prefixWord ++ tailWord_1590975) baseStart_1590975 baseEnd_1590975 := by
    simpa [prefixWord, tailWord_1590975, baseEnd_1590975] using wordTrace_append hprefix tailTrace_1590975
  have hstable : (prefixWord ++ tailWord_1590975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1590975).length < 2 ^ (prefixWord ++ tailWord_1590975).sum := by decide
  have hdescent : baseEnd_1590975 < baseStart_1590975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1590975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591012 : List Nat := [2, 3, 1, 1, 1, 3, 5, 1, 6]
def baseStart_1591012 : Nat := 118140960795 + 1591012 * 2 ^ 59
def prefixEnd_1591012 : Nat := 4983230072969 + 3 ^ 40 * 1591012 * 2
def baseEnd_1591012 : Nat := 90772653674581599103675

theorem tailTrace_1591012 : CollatzResearch.WordTrace tailWord_1591012 prefixEnd_1591012 90772653674581599103675 := by
  unfold tailWord_1591012
  simp only [CollatzResearch.WordTrace]
  refine ⟨29014487456021361030859645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38685983274695148041146193 29014487456021361030859645)
  ·
    refine ⟨10880432796008010386572367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29014487456021361030859645 10880432796008010386572367)
    ·
      refine ⟨16320649194012015579858551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10880432796008010386572367 16320649194012015579858551)
      ·
        refine ⟨24480973791018023369787827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16320649194012015579858551 24480973791018023369787827)
        ·
          refine ⟨36721460686527035054681741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24480973791018023369787827 36721460686527035054681741)
          ·
            refine ⟨13770547757447638145505653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36721460686527035054681741 13770547757447638145505653)
            ·
              refine ⟨1290988852260716076141155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13770547757447638145505653 1290988852260716076141155)
              ·
                refine ⟨1936483278391074114211733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290988852260716076141155 1936483278391074114211733)
                ·
                  refine ⟨90772653674581599103675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1936483278391074114211733 90772653674581599103675)
                  ·
                    rfl

theorem cell23_1591012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_1591012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591012 prefixEnd_1591012 := by exact prefixLift 1591012
  have htrace : WordTrace (prefixWord ++ tailWord_1591012) baseStart_1591012 baseEnd_1591012 := by
    simpa [prefixWord, tailWord_1591012, baseEnd_1591012] using wordTrace_append hprefix tailTrace_1591012
  have hstable : (prefixWord ++ tailWord_1591012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591012).length < 2 ^ (prefixWord ++ tailWord_1591012).sum := by decide
  have hdescent : baseEnd_1591012 < baseStart_1591012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591045 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 7, 1, 4]
def baseStart_1591045 : Nat := 118140960795 + 1591045 * 2 ^ 59
def prefixEnd_1591045 : Nat := 4983230072969 + 3 ^ 40 * 1591045 * 2
def baseEnd_1591045 : Nat := 816970827932832762820423

theorem tailTrace_1591045 : CollatzResearch.WordTrace tailWord_1591045 prefixEnd_1591045 816970827932832762820423 := by
  unfold tailWord_1591045
  simp only [CollatzResearch.WordTrace]
  refine ⟨58030178520923168697670589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38686785680615445798447059 58030178520923168697670589)
  ·
    refine ⟨21761316945346188261626471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58030178520923168697670589 21761316945346188261626471)
    ·
      refine ⟨32641975418019282392439707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21761316945346188261626471 32641975418019282392439707)
      ·
        refine ⟨48962963127028923588659561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32641975418019282392439707 48962963127028923588659561)
        ·
          refine ⟨36722222345271692691494671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48962963127028923588659561 36722222345271692691494671)
          ·
            refine ⟨55083333517907539037242007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36722222345271692691494671 55083333517907539037242007)
            ·
              refine ⟨82625000276861308555863011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55083333517907539037242007 82625000276861308555863011)
              ·
                refine ⟨123937500415291962833794517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82625000276861308555863011 123937500415291962833794517)
                ·
                  refine ⟨2904785165983405378917059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 123937500415291962833794517 2904785165983405378917059)
                  ·
                    refine ⟨4357177748975108068375589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2904785165983405378917059 4357177748975108068375589)
                    ·
                      refine ⟨816970827932832762820423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4357177748975108068375589 816970827932832762820423)
                      ·
                        rfl

theorem cell23_1591045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_1591045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591045 prefixEnd_1591045 := by exact prefixLift 1591045
  have htrace : WordTrace (prefixWord ++ tailWord_1591045) baseStart_1591045 baseEnd_1591045 := by
    simpa [prefixWord, tailWord_1591045, baseEnd_1591045] using wordTrace_append hprefix tailTrace_1591045
  have hstable : (prefixWord ++ tailWord_1591045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591045).length < 2 ^ (prefixWord ++ tailWord_1591045).sum := by decide
  have hdescent : baseEnd_1591045 < baseStart_1591045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591075 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 6]
def baseStart_1591075 : Nat := 118140960795 + 1591075 * 2 ^ 59
def prefixEnd_1591075 : Nat := 4983230072969 + 3 ^ 40 * 1591075 * 2
def baseEnd_1591075 : Nat := 816986232352467645445285

theorem tailTrace_1591075 : CollatzResearch.WordTrace tailWord_1591075 prefixEnd_1591075 816986232352467645445285 := by
  unfold tailWord_1591075
  simp only [CollatzResearch.WordTrace]
  refine ⟨58031272710814483821262679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38687515140542989214175119 58031272710814483821262679)
  ·
    refine ⟨87046909066221725731894019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58031272710814483821262679 87046909066221725731894019)
    ·
      refine ⟨130570363599332588597841029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87046909066221725731894019 130570363599332588597841029)
      ·
        refine ⟨24481943174874860362095193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130570363599332588597841029 24481943174874860362095193)
        ·
          refine ⟨18361457381156145271571395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24481943174874860362095193 18361457381156145271571395)
          ·
            refine ⟨27542186071734217907357093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18361457381156145271571395 27542186071734217907357093)
            ·
              refine ⟨5164159888450165857629455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27542186071734217907357093 5164159888450165857629455)
              ·
                refine ⟨7746239832675248786444183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5164159888450165857629455 7746239832675248786444183)
                ·
                  refine ⟨11619359749012873179666275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7746239832675248786444183 11619359749012873179666275)
                  ·
                    refine ⟨17429039623519309769499413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11619359749012873179666275 17429039623519309769499413)
                    ·
                      refine ⟨816986232352467645445285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17429039623519309769499413 816986232352467645445285)
                      ·
                        rfl

theorem cell23_1591075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_1591075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591075 prefixEnd_1591075 := by exact prefixLift 1591075
  have htrace : WordTrace (prefixWord ++ tailWord_1591075) baseStart_1591075 baseEnd_1591075 := by
    simpa [prefixWord, tailWord_1591075, baseEnd_1591075] using wordTrace_append hprefix tailTrace_1591075
  have hstable : (prefixWord ++ tailWord_1591075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591075).length < 2 ^ (prefixWord ++ tailWord_1591075).sum := by decide
  have hdescent : baseEnd_1591075 < baseStart_1591075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591129 : List Nat := [1, 2, 1, 2, 2, 3, 1, 5, 2, 1, 3]
def baseStart_1591129 : Nat := 118140960795 + 1591129 * 2 ^ 59
def prefixEnd_1591129 : Nat := 4983230072969 + 3 ^ 40 * 1591129 * 2
def baseEnd_1591129 : Nat := 817013960307810434170037

theorem tailTrace_1591129 : CollatzResearch.WordTrace tailWord_1591129 prefixEnd_1591129 817013960307810434170037 := by
  unfold tailWord_1591129
  simp only [CollatzResearch.WordTrace]
  refine ⟨58033242252618851043728441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38688828168412567362485627 58033242252618851043728441)
  ·
    refine ⟨43524931689464138282796331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58033242252618851043728441 43524931689464138282796331)
    ·
      refine ⟨65287397534196207424194497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43524931689464138282796331 65287397534196207424194497)
      ·
        refine ⟨48965548150647155568145873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65287397534196207424194497 48965548150647155568145873)
        ·
          refine ⟨36724161112985366676109405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48965548150647155568145873 36724161112985366676109405)
          ·
            refine ⟨13771560417369512503541027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36724161112985366676109405 13771560417369512503541027)
            ·
              refine ⟨20657340626054268755311541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13771560417369512503541027 20657340626054268755311541)
              ·
                refine ⟨1936625683692587695810457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20657340626054268755311541 1936625683692587695810457)
                ·
                  refine ⟨1452469262769440771857843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1936625683692587695810457 1452469262769440771857843)
                  ·
                    refine ⟨2178703894154161157786765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1452469262769440771857843 2178703894154161157786765)
                    ·
                      refine ⟨817013960307810434170037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2178703894154161157786765 817013960307810434170037)
                      ·
                        rfl

theorem cell23_1591129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_1591129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591129 prefixEnd_1591129 := by exact prefixLift 1591129
  have htrace : WordTrace (prefixWord ++ tailWord_1591129) baseStart_1591129 baseEnd_1591129 := by
    simpa [prefixWord, tailWord_1591129, baseEnd_1591129] using wordTrace_append hprefix tailTrace_1591129
  have hstable : (prefixWord ++ tailWord_1591129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591129).length < 2 ^ (prefixWord ++ tailWord_1591129).sum := by decide
  have hdescent : baseEnd_1591129 < baseStart_1591129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591155 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 5]
def baseStart_1591155 : Nat := 118140960795 + 1591155 * 2 ^ 59
def prefixEnd_1591155 : Nat := 4983230072969 + 3 ^ 40 * 1591155 * 2
def baseEnd_1591155 : Nat := 817027310804827332444917

theorem tailTrace_1591155 : CollatzResearch.WordTrace tailWord_1591155 prefixEnd_1591155 817027310804827332444917 := by
  unfold tailWord_1591155
  simp only [CollatzResearch.WordTrace]
  refine ⟨58034190550524657484174919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38689460367016438322783279 58034190550524657484174919)
  ·
    refine ⟨87051285825786986226262379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58034190550524657484174919 87051285825786986226262379)
    ·
      refine ⟨130576928738680479339393569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87051285825786986226262379 130576928738680479339393569)
      ·
        refine ⟨97932696554010359504545177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130576928738680479339393569 97932696554010359504545177)
        ·
          refine ⟨73449522415507769628408883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97932696554010359504545177 73449522415507769628408883)
          ·
            refine ⟨110174283623261654442613325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73449522415507769628408883 110174283623261654442613325)
            ·
              refine ⟨41315356358723120415979997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110174283623261654442613325 41315356358723120415979997)
              ·
                refine ⟨15493258634521170155992499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41315356358723120415979997 15493258634521170155992499)
                ·
                  refine ⟨23239887951781755233988749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15493258634521170155992499 23239887951781755233988749)
                  ·
                    refine ⟨8714957981918158212745781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23239887951781755233988749 8714957981918158212745781)
                    ·
                      refine ⟨817027310804827332444917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8714957981918158212745781 817027310804827332444917)
                      ·
                        rfl

theorem cell23_1591155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_1591155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591155 prefixEnd_1591155 := by exact prefixLift 1591155
  have htrace : WordTrace (prefixWord ++ tailWord_1591155) baseStart_1591155 baseEnd_1591155 := by
    simpa [prefixWord, tailWord_1591155, baseEnd_1591155] using wordTrace_append hprefix tailTrace_1591155
  have hstable : (prefixWord ++ tailWord_1591155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591155).length < 2 ^ (prefixWord ++ tailWord_1591155).sum := by decide
  have hdescent : baseEnd_1591155 < baseStart_1591155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591172 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_1591172 : Nat := 118140960795 + 1591172 * 2 ^ 59
def prefixEnd_1591172 : Nat := 4983230072969 + 3 ^ 40 * 1591172 * 2
def baseEnd_1591172 : Nat := 817036039975953765932339

theorem tailTrace_1591172 : CollatzResearch.WordTrace tailWord_1591172 prefixEnd_1591172 817036039975953765932339 := by
  unfold tailWord_1591172
  simp only [CollatzResearch.WordTrace]
  refine ⟨29017405295731534693771885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38689873727642046258362513 29017405295731534693771885)
  ·
    refine ⟨10881526985899325510164457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29017405295731534693771885 10881526985899325510164457)
    ·
      refine ⟨8161145239424494132623343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10881526985899325510164457 8161145239424494132623343)
      ·
        refine ⟨12241717859136741198935015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8161145239424494132623343 12241717859136741198935015)
        ·
          refine ⟨18362576788705111798402523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12241717859136741198935015 18362576788705111798402523)
          ·
            refine ⟨27543865183057667697603785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18362576788705111798402523 27543865183057667697603785)
            ·
              refine ⟨20657898887293250773202839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27543865183057667697603785 20657898887293250773202839)
              ·
                refine ⟨30986848330939876159804259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20657898887293250773202839 30986848330939876159804259)
                ·
                  refine ⟨46480272496409814239706389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30986848330939876159804259 46480272496409814239706389)
                  ·
                    refine ⟨2178762773269210042486237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46480272496409814239706389 2178762773269210042486237)
                    ·
                      refine ⟨817036039975953765932339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2178762773269210042486237 817036039975953765932339)
                      ·
                        rfl

theorem cell23_1591172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_1591172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591172 prefixEnd_1591172 := by exact prefixLift 1591172
  have htrace : WordTrace (prefixWord ++ tailWord_1591172) baseStart_1591172 baseEnd_1591172 := by
    simpa [prefixWord, tailWord_1591172, baseEnd_1591172] using wordTrace_append hprefix tailTrace_1591172
  have hstable : (prefixWord ++ tailWord_1591172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591172).length < 2 ^ (prefixWord ++ tailWord_1591172).sum := by decide
  have hdescent : baseEnd_1591172 < baseStart_1591172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591232 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 5]
def baseStart_1591232 : Nat := 118140960795 + 1591232 * 2 ^ 59
def prefixEnd_1591232 : Nat := 4983230072969 + 3 ^ 40 * 1591232 * 2
def baseEnd_1591232 : Nat := 817066848815223531182063

theorem tailTrace_1591232 : CollatzResearch.WordTrace tailWord_1591232 prefixEnd_1591232 817066848815223531182063 := by
  unfold tailWord_1591232
  simp only [CollatzResearch.WordTrace]
  refine ⟨29018499485622849817363975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38691332647497133089818633 29018499485622849817363975)
  ·
    refine ⟨43527749228434274726045963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29018499485622849817363975 43527749228434274726045963)
    ·
      refine ⟨65291623842651412089068945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43527749228434274726045963 65291623842651412089068945)
      ·
        refine ⟨48968717881988559066801709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65291623842651412089068945 48968717881988559066801709)
        ·
          refine ⟨18363269205745709650050641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48968717881988559066801709 18363269205745709650050641)
          ·
            refine ⟨13772451904309282237537981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18363269205745709650050641 13772451904309282237537981)
            ·
              refine ⟨5164669464115980839076743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13772451904309282237537981 5164669464115980839076743)
              ·
                refine ⟨7747004196173971258615115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5164669464115980839076743 7747004196173971258615115)
                ·
                  refine ⟨11620506294260956887922673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7747004196173971258615115 11620506294260956887922673)
                  ·
                    refine ⟨8715379720695717665942005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11620506294260956887922673 8715379720695717665942005)
                    ·
                      refine ⟨817066848815223531182063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8715379720695717665942005 817066848815223531182063)
                      ·
                        rfl

theorem cell23_1591232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_1591232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591232 prefixEnd_1591232 := by exact prefixLift 1591232
  have htrace : WordTrace (prefixWord ++ tailWord_1591232) baseStart_1591232 baseEnd_1591232 := by
    simpa [prefixWord, tailWord_1591232, baseEnd_1591232] using wordTrace_append hprefix tailTrace_1591232
  have hstable : (prefixWord ++ tailWord_1591232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591232).length < 2 ^ (prefixWord ++ tailWord_1591232).sum := by decide
  have hdescent : baseEnd_1591232 < baseStart_1591232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591242 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_1591242 : Nat := 118140960795 + 1591242 * 2 ^ 59
def prefixEnd_1591242 : Nat := 4983230072969 + 3 ^ 40 * 1591242 * 2
def baseEnd_1591242 : Nat := 817071983621768492057017

theorem tailTrace_1591242 : CollatzResearch.WordTrace tailWord_1591242 prefixEnd_1591242 817071983621768492057017 := by
  unfold tailWord_1591242
  simp only [CollatzResearch.WordTrace]
  refine ⟨14509340925302367835647995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38691575800806314228394653 14509340925302367835647995)
  ·
    refine ⟨21764011387953551753471993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14509340925302367835647995 21764011387953551753471993)
    ·
      refine ⟨16323008540965163815103995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21764011387953551753471993 16323008540965163815103995)
      ·
        refine ⟨24484512811447745722655993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16323008540965163815103995 24484512811447745722655993)
        ·
          refine ⟨18363384608585809291991995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24484512811447745722655993 18363384608585809291991995)
          ·
            refine ⟨27545076912878713937987993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18363384608585809291991995 27545076912878713937987993)
            ·
              refine ⟨20658807684659035453490995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27545076912878713937987993 20658807684659035453490995)
              ·
                refine ⟨30988211526988553180236493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20658807684659035453490995 30988211526988553180236493)
                ·
                  refine ⟨11620579322620707442588685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30988211526988553180236493 11620579322620707442588685)
                  ·
                    refine ⟨4357717245982765290970757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11620579322620707442588685 4357717245982765290970757)
                    ·
                      refine ⟨817071983621768492057017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4357717245982765290970757 817071983621768492057017)
                      ·
                        rfl

theorem cell23_1591242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_1591242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591242 prefixEnd_1591242 := by exact prefixLift 1591242
  have htrace : WordTrace (prefixWord ++ tailWord_1591242) baseStart_1591242 baseEnd_1591242 := by
    simpa [prefixWord, tailWord_1591242, baseEnd_1591242] using wordTrace_append hprefix tailTrace_1591242
  have hstable : (prefixWord ++ tailWord_1591242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591242).length < 2 ^ (prefixWord ++ tailWord_1591242).sum := by decide
  have hdescent : baseEnd_1591242 < baseStart_1591242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591272 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_1591272 : Nat := 118140960795 + 1591272 * 2 ^ 59
def prefixEnd_1591272 : Nat := 4983230072969 + 3 ^ 40 * 1591272 * 2
def baseEnd_1591272 : Nat := 817087388041403374681879

theorem tailTrace_1591272 : CollatzResearch.WordTrace tailWord_1591272 prefixEnd_1591272 817087388041403374681879 := by
  unfold tailWord_1591272
  simp only [CollatzResearch.WordTrace]
  refine ⟨29019228945550393233092035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38692305260733857644122713 29019228945550393233092035)
  ·
    refine ⟨43528843418325589849638053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29019228945550393233092035 43528843418325589849638053)
    ·
      refine ⟨8161658140936048096807135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43528843418325589849638053 8161658140936048096807135)
      ·
        refine ⟨12242487211404072145210703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8161658140936048096807135 12242487211404072145210703)
        ·
          refine ⟨18363730817106108217816055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12242487211404072145210703 18363730817106108217816055)
          ·
            refine ⟨27545596225659162326724083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18363730817106108217816055 27545596225659162326724083)
            ·
              refine ⟨41318394338488743490086125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27545596225659162326724083 41318394338488743490086125)
              ·
                refine ⟨15494397876933278808782297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41318394338488743490086125 15494397876933278808782297)
                ·
                  refine ⟨11620798407699959106586723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15494397876933278808782297 11620798407699959106586723)
                  ·
                    refine ⟨17431197611549938659880085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11620798407699959106586723 17431197611549938659880085)
                    ·
                      refine ⟨817087388041403374681879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17431197611549938659880085 817087388041403374681879)
                      ·
                        rfl

theorem cell23_1591272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_1591272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591272 prefixEnd_1591272 := by exact prefixLift 1591272
  have htrace : WordTrace (prefixWord ++ tailWord_1591272) baseStart_1591272 baseEnd_1591272 := by
    simpa [prefixWord, tailWord_1591272, baseEnd_1591272] using wordTrace_append hprefix tailTrace_1591272
  have hstable : (prefixWord ++ tailWord_1591272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591272).length < 2 ^ (prefixWord ++ tailWord_1591272).sum := by decide
  have hdescent : baseEnd_1591272 < baseStart_1591272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591277 : List Nat := [1, 5, 1, 4, 2, 1, 2, 2, 5]
def baseStart_1591277 : Nat := 118140960795 + 1591277 * 2 ^ 59
def prefixEnd_1591277 : Nat := 4983230072969 + 3 ^ 40 * 1591277 * 2
def baseEnd_1591277 : Nat := 90787772827186206124373

theorem tailTrace_1591277 : CollatzResearch.WordTrace tailWord_1591277 prefixEnd_1591277 90787772827186206124373 := by
  unfold tailWord_1591277
  simp only [CollatzResearch.WordTrace]
  refine ⟨58038640256082672320116085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38692426837388448213410723 58038640256082672320116085)
  ·
    refine ⟨5441122524007750530010883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58038640256082672320116085 5441122524007750530010883)
    ·
      refine ⟨8161683786011625795016325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5441122524007750530010883 8161683786011625795016325)
      ·
        refine ⟨1530315709877179836565561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8161683786011625795016325 1530315709877179836565561)
        ·
          refine ⟨1147736782407884877424171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1530315709877179836565561 1147736782407884877424171)
          ·
            refine ⟨1721605173611827316136257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147736782407884877424171 1721605173611827316136257)
            ·
              refine ⟨1291203880208870487102193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1721605173611827316136257 1291203880208870487102193)
              ·
                refine ⟨968402910156652865326645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1291203880208870487102193 968402910156652865326645)
                ·
                  refine ⟨90787772827186206124373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 968402910156652865326645 90787772827186206124373)
                  ·
                    rfl

theorem cell23_1591277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_1591277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591277 prefixEnd_1591277 := by exact prefixLift 1591277
  have htrace : WordTrace (prefixWord ++ tailWord_1591277) baseStart_1591277 baseEnd_1591277 := by
    simpa [prefixWord, tailWord_1591277, baseEnd_1591277] using wordTrace_append hprefix tailTrace_1591277
  have hstable : (prefixWord ++ tailWord_1591277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591277).length < 2 ^ (prefixWord ++ tailWord_1591277).sum := by decide
  have hdescent : baseEnd_1591277 < baseStart_1591277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591279 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 3]
def baseStart_1591279 : Nat := 118140960795 + 1591279 * 2 ^ 59
def prefixEnd_1591279 : Nat := 4983230072969 + 3 ^ 40 * 1591279 * 2
def baseEnd_1591279 : Nat := 817090982405984847294347

theorem tailTrace_1591279 : CollatzResearch.WordTrace tailWord_1591279 prefixEnd_1591279 817090982405984847294347 := by
  unfold tailWord_1591279
  simp only [CollatzResearch.WordTrace]
  refine ⟨58038713202075426661688891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38692475468050284441125927 58038713202075426661688891)
  ·
    refine ⟨87058069803113139992533337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58038713202075426661688891 87058069803113139992533337)
    ·
      refine ⟨65293552352334854994400003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87058069803113139992533337 65293552352334854994400003)
      ·
        refine ⟨97940328528502282491600005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65293552352334854994400003 97940328528502282491600005)
        ·
          refine ⟨18363811599094177967175001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97940328528502282491600005 18363811599094177967175001)
          ·
            refine ⟨13772858699320633475381251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18363811599094177967175001 13772858699320633475381251)
            ·
              refine ⟨20659288048980950213071877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13772858699320633475381251 20659288048980950213071877)
              ·
                refine ⟨3873616509183928164950977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20659288048980950213071877 3873616509183928164950977)
                ·
                  refine ⟨2905212381887946123713233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3873616509183928164950977 2905212381887946123713233)
                  ·
                    refine ⟨2178909286415959592784925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2905212381887946123713233 2178909286415959592784925)
                    ·
                      refine ⟨817090982405984847294347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2178909286415959592784925 817090982405984847294347)
                      ·
                        rfl

theorem cell23_1591279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 3].length) (baseStart_1591279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591279 prefixEnd_1591279 := by exact prefixLift 1591279
  have htrace : WordTrace (prefixWord ++ tailWord_1591279) baseStart_1591279 baseEnd_1591279 := by
    simpa [prefixWord, tailWord_1591279, baseEnd_1591279] using wordTrace_append hprefix tailTrace_1591279
  have hstable : (prefixWord ++ tailWord_1591279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591279).length < 2 ^ (prefixWord ++ tailWord_1591279).sum := by decide
  have hdescent : baseEnd_1591279 < baseStart_1591279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591349 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_1591349 : Nat := 118140960795 + 1591349 * 2 ^ 59
def prefixEnd_1591349 : Nat := 4983230072969 + 3 ^ 40 * 1591349 * 2
def baseEnd_1591349 : Nat := 817126926051799573419025

theorem tailTrace_1591349 : CollatzResearch.WordTrace tailWord_1591349 prefixEnd_1591349 817126926051799573419025 := by
  unfold tailWord_1591349
  simp only [CollatzResearch.WordTrace]
  refine ⟨58041266311821828616737101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38694177541214552411158067 58041266311821828616737101)
  ·
    refine ⟨21765474866933185731276413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58041266311821828616737101 21765474866933185731276413)
    ·
      refine ⟨8162053075099944649228655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21765474866933185731276413 8162053075099944649228655)
      ·
        refine ⟨12243079612649916973842983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8162053075099944649228655 12243079612649916973842983)
        ·
          refine ⟨18364619418974875460764475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12243079612649916973842983 18364619418974875460764475)
          ·
            refine ⟨27546929128462313191146713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18364619418974875460764475 27546929128462313191146713)
            ·
              refine ⟨20660196846346734893360035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27546929128462313191146713 20660196846346734893360035)
              ·
                refine ⟨30990295269520102340040053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20660196846346734893360035 30990295269520102340040053)
                ·
                  refine ⟨2905340181517509594378755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30990295269520102340040053 2905340181517509594378755)
                  ·
                    refine ⟨4358010272276264391568133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2905340181517509594378755 4358010272276264391568133)
                    ·
                      refine ⟨817126926051799573419025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4358010272276264391568133 817126926051799573419025)
                      ·
                        rfl

theorem cell23_1591349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_1591349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591349 prefixEnd_1591349 := by exact prefixLift 1591349
  have htrace : WordTrace (prefixWord ++ tailWord_1591349) baseStart_1591349 baseEnd_1591349 := by
    simpa [prefixWord, tailWord_1591349, baseEnd_1591349] using wordTrace_append hprefix tailTrace_1591349
  have hstable : (prefixWord ++ tailWord_1591349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591349).length < 2 ^ (prefixWord ++ tailWord_1591349).sum := by decide
  have hdescent : baseEnd_1591349 < baseStart_1591349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1591359 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 1, 6]
def baseStart_1591359 : Nat := 118140960795 + 1591359 * 2 ^ 59
def prefixEnd_1591359 : Nat := 4983230072969 + 3 ^ 40 * 1591359 * 2
def baseEnd_1591359 : Nat := 272377353619448178097993

theorem tailTrace_1591359 : CollatzResearch.WordTrace tailWord_1591359 prefixEnd_1591359 272377353619448178097993 := by
  unfold tailWord_1591359
  simp only [CollatzResearch.WordTrace]
  refine ⟨58041631041785600324601131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38694420694523733549734087 58041631041785600324601131)
  ·
    refine ⟨87062446562678400486901697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58041631041785600324601131 87062446562678400486901697)
    ·
      refine ⟨65296834922008800365176273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87062446562678400486901697 65296834922008800365176273)
      ·
        refine ⟨48972626191506600273882205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65296834922008800365176273 48972626191506600273882205)
        ·
          refine ⟨18364734821814975102705827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48972626191506600273882205 18364734821814975102705827)
          ·
            refine ⟨27547102232722462654058741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18364734821814975102705827 27547102232722462654058741)
            ·
              refine ⟨2582540834317730873818007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27547102232722462654058741 2582540834317730873818007)
              ·
                refine ⟨3873811251476596310727011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582540834317730873818007 3873811251476596310727011)
                ·
                  refine ⟨5810716877214894466090517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873811251476596310727011 5810716877214894466090517)
                  ·
                    refine ⟨272377353619448178097993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5810716877214894466090517 272377353619448178097993)
                    ·
                      rfl

theorem cell23_1591359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 6].length) (baseStart_1591359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1591359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1591359 prefixEnd_1591359 := by exact prefixLift 1591359
  have htrace : WordTrace (prefixWord ++ tailWord_1591359) baseStart_1591359 baseEnd_1591359 := by
    simpa [prefixWord, tailWord_1591359, baseEnd_1591359] using wordTrace_append hprefix tailTrace_1591359
  have hstable : (prefixWord ++ tailWord_1591359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1591359).length < 2 ^ (prefixWord ++ tailWord_1591359).sum := by decide
  have hdescent : baseEnd_1591359 < baseStart_1591359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1591359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
