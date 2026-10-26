import V185TrunkScan23Chunk0103

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_615493 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_615493 : Nat := 118140960795 + 615493 * 2 ^ 59
def prefixEnd_615493 : Nat := 4983230072969 + 3 ^ 40 * 615493 * 2
def baseEnd_615493 : Nat := 316043748477865614506905

theorem tailTrace_615493 : CollatzResearch.WordTrace tailWord_615493 prefixEnd_615493 316043748477865614506905 := by
  unfold tailWord_615493
  simp only [CollatzResearch.WordTrace]
  refine ⟨22448873959181453680651133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14965915972787635787100755 22448873959181453680651133)
  ·
    refine ⟨8418327734693045130244175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22448873959181453680651133 8418327734693045130244175)
    ·
      refine ⟨12627491602039567695366263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8418327734693045130244175 12627491602039567695366263)
      ·
        refine ⟨18941237403059351543049395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12627491602039567695366263 18941237403059351543049395)
        ·
          refine ⟨28411856104589027314574093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18941237403059351543049395 28411856104589027314574093)
          ·
            refine ⟨10654446039220885242965285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28411856104589027314574093 10654446039220885242965285)
            ·
              refine ⟨1997708632353915983055991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10654446039220885242965285 1997708632353915983055991)
              ·
                refine ⟨2996562948530873974583987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1997708632353915983055991 2996562948530873974583987)
                ·
                  refine ⟨4494844422796310961875981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2996562948530873974583987 4494844422796310961875981)
                  ·
                    refine ⟨1685566658548616610703493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4494844422796310961875981 1685566658548616610703493)
                    ·
                      refine ⟨316043748477865614506905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1685566658548616610703493 316043748477865614506905)
                      ·
                        rfl

theorem cell23_615493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_615493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615493 prefixEnd_615493 := by exact prefixLift 615493
  have htrace : WordTrace (prefixWord ++ tailWord_615493) baseStart_615493 baseEnd_615493 := by
    simpa [prefixWord, tailWord_615493, baseEnd_615493] using wordTrace_append hprefix tailTrace_615493
  have hstable : (prefixWord ++ tailWord_615493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615493).length < 2 ^ (prefixWord ++ tailWord_615493).sum := by decide
  have hdescent : baseEnd_615493 < baseStart_615493 := by decide
  rcases family_descends (prefixWord ++ tailWord_615493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615494 : List Nat := [6, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_615494 : Nat := 118140960795 + 615494 * 2 ^ 59
def prefixEnd_615494 : Nat := 4983230072969 + 3 ^ 40 * 615494 * 2
def baseEnd_615494 : Nat := 35116029106502234510489

theorem tailTrace_615494 : CollatzResearch.WordTrace tailWord_615494 prefixEnd_615494 35116029106502234510489 := by
  unfold tailWord_615494
  simp only [CollatzResearch.WordTrace]
  refine ⟨701528451005557214107423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14965940288118553900958357 701528451005557214107423)
  ·
    refine ⟨1052292676508335821161135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 701528451005557214107423 1052292676508335821161135)
    ·
      refine ⟨1578439014762503731741703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1052292676508335821161135 1578439014762503731741703)
      ·
        refine ⟨2367658522143755597612555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1578439014762503731741703 2367658522143755597612555)
        ·
          refine ⟨3551487783215633396418833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367658522143755597612555 3551487783215633396418833)
          ·
            refine ⟨2663615837411725047314125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3551487783215633396418833 2663615837411725047314125)
            ·
              refine ⟨998855939029396892742797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2663615837411725047314125 998855939029396892742797)
              ·
                refine ⟨374570977136023834778549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 998855939029396892742797 374570977136023834778549)
                ·
                  refine ⟨35116029106502234510489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 374570977136023834778549 35116029106502234510489)
                  ·
                    rfl

theorem cell23_615494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_615494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615494 prefixEnd_615494 := by exact prefixLift 615494
  have htrace : WordTrace (prefixWord ++ tailWord_615494) baseStart_615494 baseEnd_615494 := by
    simpa [prefixWord, tailWord_615494, baseEnd_615494] using wordTrace_append hprefix tailTrace_615494
  have hstable : (prefixWord ++ tailWord_615494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615494).length < 2 ^ (prefixWord ++ tailWord_615494).sum := by decide
  have hdescent : baseEnd_615494 < baseStart_615494 := by decide
  rcases family_descends (prefixWord ++ tailWord_615494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615513 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 3, 4, 3]
def baseStart_615513 : Nat := 118140960795 + 615513 * 2 ^ 59
def prefixEnd_615513 : Nat := 4983230072969 + 3 ^ 40 * 615513 * 2
def baseEnd_615513 : Nat := 316054018090955536256813

theorem tailTrace_615513 : CollatzResearch.WordTrace tailWord_615513 prefixEnd_615513 316054018090955536256813 := by
  unfold tailWord_615513
  simp only [CollatzResearch.WordTrace]
  refine ⟨22449603419108997096379193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14966402279405998064252795 22449603419108997096379193)
  ·
    refine ⟨16837202564331747822284395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22449603419108997096379193 16837202564331747822284395)
    ·
      refine ⟨25255803846497621733426593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16837202564331747822284395 25255803846497621733426593)
      ·
        refine ⟨18941852884873216300069945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25255803846497621733426593 18941852884873216300069945)
        ·
          refine ⟨14206389663654912225052459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18941852884873216300069945 14206389663654912225052459)
          ·
            refine ⟨21309584495482368337578689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14206389663654912225052459 21309584495482368337578689)
            ·
              refine ⟨15982188371611776253184017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21309584495482368337578689 15982188371611776253184017)
              ·
                refine ⟨11986641278708832189888013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15982188371611776253184017 11986641278708832189888013)
                ·
                  refine ⟨4494990479515812071208005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11986641278708832189888013 4494990479515812071208005)
                  ·
                    refine ⟨842810714909214763351501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4494990479515812071208005 842810714909214763351501)
                    ·
                      refine ⟨316054018090955536256813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 842810714909214763351501 316054018090955536256813)
                      ·
                        rfl

theorem cell23_615513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_615513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615513 prefixEnd_615513 := by exact prefixLift 615513
  have htrace : WordTrace (prefixWord ++ tailWord_615513) baseStart_615513 baseEnd_615513 := by
    simpa [prefixWord, tailWord_615513, baseEnd_615513] using wordTrace_append hprefix tailTrace_615513
  have hstable : (prefixWord ++ tailWord_615513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615513).length < 2 ^ (prefixWord ++ tailWord_615513).sum := by decide
  have hdescent : baseEnd_615513 < baseStart_615513 := by decide
  rcases family_descends (prefixWord ++ tailWord_615513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615517 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_615517 : Nat := 118140960795 + 615517 * 2 ^ 59
def prefixEnd_615517 : Nat := 4983230072969 + 3 ^ 40 * 615517 * 2
def baseEnd_615517 : Nat := 316056072013573520606795

theorem tailTrace_615517 : CollatzResearch.WordTrace tailWord_615517 prefixEnd_615517 316056072013573520606795 := by
  unfold tailWord_615517
  simp only [CollatzResearch.WordTrace]
  refine ⟨22449749311094505779524805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14966499540729670519683203 22449749311094505779524805)
  ·
    refine ⟨4209327995830219833660901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22449749311094505779524805 4209327995830219833660901)
    ·
      refine ⟨789248999218166218811419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4209327995830219833660901 789248999218166218811419)
      ·
        refine ⟨1183873498827249328217129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789248999218166218811419 1183873498827249328217129)
        ·
          refine ⟨887905124120436996162847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1183873498827249328217129 887905124120436996162847)
          ·
            refine ⟨1331857686180655494244271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887905124120436996162847 1331857686180655494244271)
            ·
              refine ⟨1997786529270983241366407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331857686180655494244271 1997786529270983241366407)
              ·
                refine ⟨2996679793906474862049611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1997786529270983241366407 2996679793906474862049611)
                ·
                  refine ⟨4495019690859712293074417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2996679793906474862049611 4495019690859712293074417)
                  ·
                    refine ⟨3371264768144784219805813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4495019690859712293074417 3371264768144784219805813)
                    ·
                      refine ⟨316056072013573520606795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3371264768144784219805813 316056072013573520606795)
                      ·
                        rfl

theorem cell23_615517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_615517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615517 prefixEnd_615517 := by exact prefixLift 615517
  have htrace : WordTrace (prefixWord ++ tailWord_615517) baseStart_615517 baseEnd_615517 := by
    simpa [prefixWord, tailWord_615517, baseEnd_615517] using wordTrace_append hprefix tailTrace_615517
  have hstable : (prefixWord ++ tailWord_615517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615517).length < 2 ^ (prefixWord ++ tailWord_615517).sum := by decide
  have hdescent : baseEnd_615517 < baseStart_615517 := by decide
  rcases family_descends (prefixWord ++ tailWord_615517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615580 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 3, 5]
def baseStart_615580 : Nat := 118140960795 + 615580 * 2 ^ 59
def prefixEnd_615580 : Nat := 4983230072969 + 3 ^ 40 * 615580 * 2
def baseEnd_615580 : Nat := 105362807098268924706335

theorem tailTrace_615580 : CollatzResearch.WordTrace tailWord_615580 prefixEnd_615580 105362807098268924706335 := by
  unfold tailWord_615580
  simp only [CollatzResearch.WordTrace]
  refine ⟨11226023554933133769534097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14968031406577511692712129 11226023554933133769534097)
  ·
    refine ⟨8419517666199850327150573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11226023554933133769534097 8419517666199850327150573)
    ·
      refine ⟨3157319124824943872681465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8419517666199850327150573 3157319124824943872681465)
      ·
        refine ⟨2367989343618707904511099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3157319124824943872681465 2367989343618707904511099)
        ·
          refine ⟨3551984015428061856766649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367989343618707904511099 3551984015428061856766649)
          ·
            refine ⟨2663988011571046392574987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3551984015428061856766649 2663988011571046392574987)
            ·
              refine ⟨3995982017356569588862481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663988011571046392574987 3995982017356569588862481)
              ·
                refine ⟨2996986513017427191646861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3995982017356569588862481 2996986513017427191646861)
                ·
                  refine ⟨1123869942381535196867573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2996986513017427191646861 1123869942381535196867573)
                  ·
                    refine ⟨105362807098268924706335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1123869942381535196867573 105362807098268924706335)
                    ·
                      rfl

theorem cell23_615580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_615580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615580 prefixEnd_615580 := by exact prefixLift 615580
  have htrace : WordTrace (prefixWord ++ tailWord_615580) baseStart_615580 baseEnd_615580 := by
    simpa [prefixWord, tailWord_615580, baseEnd_615580] using wordTrace_append hprefix tailTrace_615580
  have hstable : (prefixWord ++ tailWord_615580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615580).length < 2 ^ (prefixWord ++ tailWord_615580).sum := by decide
  have hdescent : baseEnd_615580 < baseStart_615580 := by decide
  rcases family_descends (prefixWord ++ tailWord_615580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615594 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_615594 : Nat := 118140960795 + 615594 * 2 ^ 59
def prefixEnd_615594 : Nat := 4983230072969 + 3 ^ 40 * 615594 * 2
def baseEnd_615594 : Nat := 316095610023969719343941

theorem tailTrace_615594 : CollatzResearch.WordTrace tailWord_615594 prefixEnd_615594 316095610023969719343941 := by
  unfold tailWord_615594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613139432953886982519459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14968371821210365286718557 5613139432953886982519459)
  ·
    refine ⟨8419709149430830473779189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5613139432953886982519459 8419709149430830473779189)
    ·
      refine ⟨789347732759140356916799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8419709149430830473779189 789347732759140356916799)
      ·
        refine ⟨1184021599138710535375199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789347732759140356916799 1184021599138710535375199)
        ·
          refine ⟨1776032398708065803062799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184021599138710535375199 1776032398708065803062799)
          ·
            refine ⟨2664048598062098704594199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776032398708065803062799 2664048598062098704594199)
            ·
              refine ⟨3996072897093148056891299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664048598062098704594199 3996072897093148056891299)
              ·
                refine ⟨5994109345639722085336949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3996072897093148056891299 5994109345639722085336949)
                ·
                  refine ⟨561947751153723945500339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5994109345639722085336949 561947751153723945500339)
                  ·
                    refine ⟨842921626730585918250509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 561947751153723945500339 842921626730585918250509)
                    ·
                      refine ⟨316095610023969719343941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 842921626730585918250509 316095610023969719343941)
                      ·
                        rfl

theorem cell23_615594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_615594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615594 prefixEnd_615594 := by exact prefixLift 615594
  have htrace : WordTrace (prefixWord ++ tailWord_615594) baseStart_615594 baseEnd_615594 := by
    simpa [prefixWord, tailWord_615594, baseEnd_615594] using wordTrace_append hprefix tailTrace_615594
  have hstable : (prefixWord ++ tailWord_615594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615594).length < 2 ^ (prefixWord ++ tailWord_615594).sum := by decide
  have hdescent : baseEnd_615594 < baseStart_615594 := by decide
  rcases family_descends (prefixWord ++ tailWord_615594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615600 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 2, 6, 2]
def baseStart_615600 : Nat := 118140960795 + 615600 * 2 ^ 59
def prefixEnd_615600 : Nat := 4983230072969 + 3 ^ 40 * 615600 * 2
def baseEnd_615600 : Nat := 316098690907896695868913

theorem tailTrace_615600 : CollatzResearch.WordTrace tailWord_615600 prefixEnd_615600 316098690907896695868913 := by
  unfold tailWord_615600
  simp only [CollatzResearch.WordTrace]
  refine ⟨11226388284896905477398127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14968517713195873969864169 11226388284896905477398127)
  ·
    refine ⟨16839582427345358216097191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11226388284896905477398127 16839582427345358216097191)
    ·
      refine ⟨25259373641018037324145787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16839582427345358216097191 25259373641018037324145787)
      ·
        refine ⟨37889060461527055986218681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25259373641018037324145787 37889060461527055986218681)
        ·
          refine ⟨28416795346145291989664011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37889060461527055986218681 28416795346145291989664011)
          ·
            refine ⟨42625193019217937984496017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28416795346145291989664011 42625193019217937984496017)
            ·
              refine ⟨31968894764413453488372013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42625193019217937984496017 31968894764413453488372013)
              ·
                refine ⟨11988335536655045058139505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31968894764413453488372013 11988335536655045058139505)
                ·
                  refine ⟨8991251652491283793604629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11988335536655045058139505 8991251652491283793604629)
                  ·
                    refine ⟨421464921210528927825217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8991251652491283793604629 421464921210528927825217)
                    ·
                      refine ⟨316098690907896695868913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 421464921210528927825217 316098690907896695868913)
                      ·
                        rfl

theorem cell23_615600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 6, 2].length) (baseStart_615600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615600 prefixEnd_615600 := by exact prefixLift 615600
  have htrace : WordTrace (prefixWord ++ tailWord_615600) baseStart_615600 baseEnd_615600 := by
    simpa [prefixWord, tailWord_615600, baseEnd_615600] using wordTrace_append hprefix tailTrace_615600
  have hstable : (prefixWord ++ tailWord_615600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615600).length < 2 ^ (prefixWord ++ tailWord_615600).sum := by decide
  have hdescent : baseEnd_615600 < baseStart_615600 := by decide
  rcases family_descends (prefixWord ++ tailWord_615600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615610 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 4, 4]
def baseStart_615610 : Nat := 118140960795 + 615610 * 2 ^ 59
def prefixEnd_615610 : Nat := 4983230072969 + 3 ^ 40 * 615610 * 2
def baseEnd_615610 : Nat := 105367941904813885581289

theorem tailTrace_615610 : CollatzResearch.WordTrace tailWord_615610 prefixEnd_615610 105367941904813885581289 := by
  unfold tailWord_615610
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613285324939395665665071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14968760866505055108440189 5613285324939395665665071)
  ·
    refine ⟨8419927987409093498497607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5613285324939395665665071 8419927987409093498497607)
    ·
      refine ⟨12629891981113640247746411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8419927987409093498497607 12629891981113640247746411)
      ·
        refine ⟨18944837971670460371619617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12629891981113640247746411 18944837971670460371619617)
        ·
          refine ⟨14208628478752845278714713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18944837971670460371619617 14208628478752845278714713)
          ·
            refine ⟨10656471359064633959036035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14208628478752845278714713 10656471359064633959036035)
            ·
              refine ⟨15984707038596950938554053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10656471359064633959036035 15984707038596950938554053)
              ·
                refine ⟨2997132569736928300978885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15984707038596950938554053 2997132569736928300978885)
                ·
                  refine ⟨561962356825674056433541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2997132569736928300978885 561962356825674056433541)
                  ·
                    refine ⟨105367941904813885581289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 561962356825674056433541 105367941904813885581289)
                    ·
                      rfl

theorem cell23_615610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_615610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615610 prefixEnd_615610 := by exact prefixLift 615610
  have htrace : WordTrace (prefixWord ++ tailWord_615610) baseStart_615610 baseEnd_615610 := by
    simpa [prefixWord, tailWord_615610, baseEnd_615610] using wordTrace_append hprefix tailTrace_615610
  have hstable : (prefixWord ++ tailWord_615610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615610).length < 2 ^ (prefixWord ++ tailWord_615610).sum := by decide
  have hdescent : baseEnd_615610 < baseStart_615610 := by decide
  rcases family_descends (prefixWord ++ tailWord_615610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615614 : List Nat := [4, 2, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_615614 : Nat := 118140960795 + 615614 * 2 ^ 59
def prefixEnd_615614 : Nat := 4983230072969 + 3 ^ 40 * 615614 * 2
def baseEnd_615614 : Nat := 105368626545686547031283

theorem tailTrace_615614 : CollatzResearch.WordTrace tailWord_615614 prefixEnd_615614 105368626545686547031283 := by
  unfold tailWord_615614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2806660898967886418225737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14968858127828727563870597 2806660898967886418225737)
  ·
    refine ⟨2104995674225914813669303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2806660898967886418225737 2104995674225914813669303)
    ·
      refine ⟨3157493511338872220503955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2104995674225914813669303 3157493511338872220503955)
      ·
        refine ⟨4736240267008308330755933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3157493511338872220503955 4736240267008308330755933)
        ·
          refine ⟨1776090100128115624033475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4736240267008308330755933 1776090100128115624033475)
          ·
            refine ⟨2664135150192173436050213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776090100128115624033475 2664135150192173436050213)
            ·
              refine ⟨499525340661032519259415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2664135150192173436050213 499525340661032519259415)
              ·
                refine ⟨749288010991548778889123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499525340661032519259415 749288010991548778889123)
                ·
                  refine ⟨1123932016487323168333685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 749288010991548778889123 1123932016487323168333685)
                  ·
                    refine ⟨105368626545686547031283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1123932016487323168333685 105368626545686547031283)
                    ·
                      rfl

theorem cell23_615614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_615614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615614 prefixEnd_615614 := by exact prefixLift 615614
  have htrace : WordTrace (prefixWord ++ tailWord_615614) baseStart_615614 baseEnd_615614 := by
    simpa [prefixWord, tailWord_615614, baseEnd_615614] using wordTrace_append hprefix tailTrace_615614
  have hstable : (prefixWord ++ tailWord_615614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615614).length < 2 ^ (prefixWord ++ tailWord_615614).sum := by decide
  have hdescent : baseEnd_615614 < baseStart_615614 := by decide
  rcases family_descends (prefixWord ++ tailWord_615614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615618 : List Nat := [3, 5, 1, 1, 3, 1, 1, 2, 6]
def baseStart_615618 : Nat := 118140960795 + 615618 * 2 ^ 59
def prefixEnd_615618 : Nat := 4983230072969 + 3 ^ 40 * 615618 * 2
def baseEnd_615618 : Nat := 35123103728853069493759

theorem tailTrace_615618 : CollatzResearch.WordTrace tailWord_615618 prefixEnd_615618 35123103728853069493759 := by
  unfold tailWord_615618
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613358270932150007237877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14968955389152400019301005 5613358270932150007237877)
  ·
    refine ⟨526252337899889063178551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5613358270932150007237877 526252337899889063178551)
    ·
      refine ⟨789378506849833594767827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 526252337899889063178551 789378506849833594767827)
      ·
        refine ⟨1184067760274750392151741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789378506849833594767827 1184067760274750392151741)
        ·
          refine ⟨444025410103031397056903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1184067760274750392151741 444025410103031397056903)
          ·
            refine ⟨666038115154547095585355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444025410103031397056903 666038115154547095585355)
            ·
              refine ⟨999057172731820643378033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666038115154547095585355 999057172731820643378033)
              ·
                refine ⟨749292879548865482533525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 999057172731820643378033 749292879548865482533525)
                ·
                  refine ⟨35123103728853069493759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 749292879548865482533525 35123103728853069493759)
                  ·
                    rfl

theorem cell23_615618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_615618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615618 prefixEnd_615618 := by exact prefixLift 615618
  have htrace : WordTrace (prefixWord ++ tailWord_615618) baseStart_615618 baseEnd_615618 := by
    simpa [prefixWord, tailWord_615618, baseEnd_615618] using wordTrace_append hprefix tailTrace_615618
  have hstable : (prefixWord ++ tailWord_615618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615618).length < 2 ^ (prefixWord ++ tailWord_615618).sum := by decide
  have hdescent : baseEnd_615618 < baseStart_615618 := by decide
  rcases family_descends (prefixWord ++ tailWord_615618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615633 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_615633 : Nat := 118140960795 + 615633 * 2 ^ 59
def prefixEnd_615633 : Nat := 4983230072969 + 3 ^ 40 * 615633 * 2
def baseEnd_615633 : Nat := 316115635769495066756261

theorem tailTrace_615633 : CollatzResearch.WordTrace tailWord_615633 prefixEnd_615633 316115635769495066756261 := by
  unfold tailWord_615633
  simp only [CollatzResearch.WordTrace]
  refine ⟨22453980178674257590747553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14969320119116171727165035 22453980178674257590747553)
  ·
    refine ⟨16840485134005693193060665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22453980178674257590747553 16840485134005693193060665)
    ·
      refine ⟨12630363850504269894795499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16840485134005693193060665 12630363850504269894795499)
      ·
        refine ⟨18945545775756404842193249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12630363850504269894795499 18945545775756404842193249)
        ·
          refine ⟨14209159331817303631644937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18945545775756404842193249 14209159331817303631644937)
          ·
            refine ⟨10656869498862977723733703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14209159331817303631644937 10656869498862977723733703)
            ·
              refine ⟨15985304248294466585600555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10656869498862977723733703 15985304248294466585600555)
              ·
                refine ⟨23977956372441699878400833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15985304248294466585600555 23977956372441699878400833)
                ·
                  refine ⟨17983467279331274908800625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23977956372441699878400833 17983467279331274908800625)
                  ·
                    refine ⟨13487600459498456181600469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17983467279331274908800625 13487600459498456181600469)
                    ·
                      refine ⟨316115635769495066756261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13487600459498456181600469 316115635769495066756261)
                      ·
                        rfl

theorem cell23_615633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_615633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615633 prefixEnd_615633 := by exact prefixLift 615633
  have htrace : WordTrace (prefixWord ++ tailWord_615633) baseStart_615633 baseEnd_615633 := by
    simpa [prefixWord, tailWord_615633, baseEnd_615633] using wordTrace_append hprefix tailTrace_615633
  have hstable : (prefixWord ++ tailWord_615633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615633).length < 2 ^ (prefixWord ++ tailWord_615633).sum := by decide
  have hdescent : baseEnd_615633 < baseStart_615633 := by decide
  rcases family_descends (prefixWord ++ tailWord_615633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615637 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_615637 : Nat := 118140960795 + 615637 * 2 ^ 59
def prefixEnd_615637 : Nat := 4983230072969 + 3 ^ 40 * 615637 * 2
def baseEnd_615637 : Nat := 316117689692113051106243

theorem tailTrace_615637 : CollatzResearch.WordTrace tailWord_615637 prefixEnd_615637 316117689692113051106243 := by
  unfold tailWord_615637
  simp only [CollatzResearch.WordTrace]
  refine ⟨22454126070659766273893165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14969417380439844182595443 22454126070659766273893165)
  ·
    refine ⟨8420297276497412352709937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22454126070659766273893165 8420297276497412352709937)
    ·
      refine ⟨6315222957373059264532453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8420297276497412352709937 6315222957373059264532453)
      ·
        refine ⟨1184104304507448612099835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6315222957373059264532453 1184104304507448612099835)
        ·
          refine ⟨1776156456761172918149753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184104304507448612099835 1776156456761172918149753)
          ·
            refine ⟨1332117342570879688612315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1776156456761172918149753 1332117342570879688612315)
            ·
              refine ⟨1998176013856319532918473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332117342570879688612315 1998176013856319532918473)
              ·
                refine ⟨1498632010392239649688855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1998176013856319532918473 1498632010392239649688855)
                ·
                  refine ⟨2247948015588359474533283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498632010392239649688855 2247948015588359474533283)
                  ·
                    refine ⟨3371922023382539211799925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2247948015588359474533283 3371922023382539211799925)
                    ·
                      refine ⟨316117689692113051106243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3371922023382539211799925 316117689692113051106243)
                      ·
                        rfl

theorem cell23_615637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_615637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615637 prefixEnd_615637 := by exact prefixLift 615637
  have htrace : WordTrace (prefixWord ++ tailWord_615637) baseStart_615637 baseEnd_615637 := by
    simpa [prefixWord, tailWord_615637, baseEnd_615637] using wordTrace_append hprefix tailTrace_615637
  have hstable : (prefixWord ++ tailWord_615637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615637).length < 2 ^ (prefixWord ++ tailWord_615637).sum := by decide
  have hdescent : baseEnd_615637 < baseStart_615637 := by decide
  rcases family_descends (prefixWord ++ tailWord_615637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615667 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 4, 1, 3]
def baseStart_615667 : Nat := 118140960795 + 615667 * 2 ^ 59
def prefixEnd_615667 : Nat := 4983230072969 + 3 ^ 40 * 615667 * 2
def baseEnd_615667 : Nat := 316133094111747933731105

theorem tailTrace_615667 : CollatzResearch.WordTrace tailWord_615667 prefixEnd_615667 316133094111747933731105 := by
  unfold tailWord_615667
  simp only [CollatzResearch.WordTrace]
  refine ⟨22455220260551081397485255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14970146840367387598323503 22455220260551081397485255)
  ·
    refine ⟨33682830390826622096227883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22455220260551081397485255 33682830390826622096227883)
    ·
      refine ⟨50524245586239933144341825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33682830390826622096227883 50524245586239933144341825)
      ·
        refine ⟨37893184189679949858256369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50524245586239933144341825 37893184189679949858256369)
        ·
          refine ⟨28419888142259962393692277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37893184189679949858256369 28419888142259962393692277)
          ·
            refine ⟨2664364513336871474408651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28419888142259962393692277 2664364513336871474408651)
            ·
              refine ⟨3996546770005307211612977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2664364513336871474408651 3996546770005307211612977)
              ·
                refine ⟨2997410077503980408709733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3996546770005307211612977 2997410077503980408709733)
                ·
                  refine ⟨562014389531996326633075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2997410077503980408709733 562014389531996326633075)
                  ·
                    refine ⟨843021584297994489949613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 562014389531996326633075 843021584297994489949613)
                    ·
                      refine ⟨316133094111747933731105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 843021584297994489949613 316133094111747933731105)
                      ·
                        rfl

theorem cell23_615667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 1, 3].length) (baseStart_615667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615667 prefixEnd_615667 := by exact prefixLift 615667
  have htrace : WordTrace (prefixWord ++ tailWord_615667) baseStart_615667 baseEnd_615667 := by
    simpa [prefixWord, tailWord_615667, baseEnd_615667] using wordTrace_append hprefix tailTrace_615667
  have hstable : (prefixWord ++ tailWord_615667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615667).length < 2 ^ (prefixWord ++ tailWord_615667).sum := by decide
  have hdescent : baseEnd_615667 < baseStart_615667 := by decide
  rcases family_descends (prefixWord ++ tailWord_615667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615670 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_615670 : Nat := 118140960795 + 615670 * 2 ^ 59
def prefixEnd_615670 : Nat := 4983230072969 + 3 ^ 40 * 615670 * 2
def baseEnd_615670 : Nat := 105378211517903807331197

theorem tailTrace_615670 : CollatzResearch.WordTrace tailWord_615670 prefixEnd_615670 105378211517903807331197 := by
  unfold tailWord_615670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1403458104971263306865279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14970219786360141939896309 1403458104971263306865279)
  ·
    refine ⟨2105187157456894960297919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1403458104971263306865279 2105187157456894960297919)
    ·
      refine ⟨3157780736185342440446879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2105187157456894960297919 3157780736185342440446879)
      ·
        refine ⟨4736671104278013660670319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3157780736185342440446879 4736671104278013660670319)
        ·
          refine ⟨7105006656417020491005479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4736671104278013660670319 7105006656417020491005479)
          ·
            refine ⟨10657509984625530736508219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7105006656417020491005479 10657509984625530736508219)
            ·
              refine ⟨15986264976938296104762329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10657509984625530736508219 15986264976938296104762329)
              ·
                refine ⟨11989698732703722078571747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15986264976938296104762329 11989698732703722078571747)
                ·
                  refine ⟨17984548099055583117857621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11989698732703722078571747 17984548099055583117857621)
                  ·
                    refine ⟨105378211517903807331197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 17984548099055583117857621 105378211517903807331197)
                    ·
                      rfl

theorem cell23_615670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_615670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615670 prefixEnd_615670 := by exact prefixLift 615670
  have htrace : WordTrace (prefixWord ++ tailWord_615670) baseStart_615670 baseEnd_615670 := by
    simpa [prefixWord, tailWord_615670, baseEnd_615670] using wordTrace_append hprefix tailTrace_615670
  have hstable : (prefixWord ++ tailWord_615670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615670).length < 2 ^ (prefixWord ++ tailWord_615670).sum := by decide
  have hdescent : baseEnd_615670 < baseStart_615670 := by decide
  rcases family_descends (prefixWord ++ tailWord_615670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615677 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 7, 3, 2]
def baseStart_615677 : Nat := 118140960795 + 615677 * 2 ^ 59
def prefixEnd_615677 : Nat := 4983230072969 + 3 ^ 40 * 615677 * 2
def baseEnd_615677 : Nat := 316138228918292894606059

theorem tailTrace_615677 : CollatzResearch.WordTrace tailWord_615677 prefixEnd_615677 316138228918292894606059 := by
  unfold tailWord_615677
  simp only [CollatzResearch.WordTrace]
  refine ⟨22455584990514853105349285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14970389993676568736899523 22455584990514853105349285)
  ·
    refine ⟨4210422185721534957252991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22455584990514853105349285 4210422185721534957252991)
    ·
      refine ⟨6315633278582302435879487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4210422185721534957252991 6315633278582302435879487)
      ·
        refine ⟨9473449917873453653819231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6315633278582302435879487 9473449917873453653819231)
        ·
          refine ⟨14210174876810180480728847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9473449917873453653819231 14210174876810180480728847)
          ·
            refine ⟨21315262315215270721093271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14210174876810180480728847 21315262315215270721093271)
            ·
              refine ⟨31972893472822906081639907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21315262315215270721093271 31972893472822906081639907)
              ·
                refine ⟨47959340209234359122459861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31972893472822906081639907 47959340209234359122459861)
                ·
                  refine ⟨1124047036153930291932653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 47959340209234359122459861 1124047036153930291932653)
                  ·
                    refine ⟨421517638557723859474745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1124047036153930291932653 421517638557723859474745)
                    ·
                      refine ⟨316138228918292894606059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 421517638557723859474745 316138228918292894606059)
                      ·
                        rfl

theorem cell23_615677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_615677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615677 prefixEnd_615677 := by exact prefixLift 615677
  have htrace : WordTrace (prefixWord ++ tailWord_615677) baseStart_615677 baseEnd_615677 := by
    simpa [prefixWord, tailWord_615677, baseEnd_615677] using wordTrace_append hprefix tailTrace_615677
  have hstable : (prefixWord ++ tailWord_615677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615677).length < 2 ^ (prefixWord ++ tailWord_615677).sum := by decide
  have hdescent : baseEnd_615677 < baseStart_615677 := by decide
  rcases family_descends (prefixWord ++ tailWord_615677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615684 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_615684 : Nat := 118140960795 + 615684 * 2 ^ 59
def prefixEnd_615684 : Nat := 4983230072969 + 3 ^ 40 * 615684 * 2
def baseEnd_615684 : Nat := 316141823282874367218527

theorem tailTrace_615684 : CollatzResearch.WordTrace tailWord_615684 prefixEnd_615684 316141823282874367218527 := by
  unfold tailWord_615684
  simp only [CollatzResearch.WordTrace]
  refine ⟨11227920150744746650427053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14970560200992995533902737 11227920150744746650427053)
  ·
    refine ⟨4210470056529279993910145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11227920150744746650427053 4210470056529279993910145)
    ·
      refine ⟨3157852542396959995432609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4210470056529279993910145 3157852542396959995432609)
      ·
        refine ⟨2368389406797719996574457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3157852542396959995432609 2368389406797719996574457)
        ·
          refine ⟨1776292055098289997430843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2368389406797719996574457 1776292055098289997430843)
          ·
            refine ⟨2664438082647434996146265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776292055098289997430843 2664438082647434996146265)
            ·
              refine ⟨1998328561985576247109699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2664438082647434996146265 1998328561985576247109699)
              ·
                refine ⟨2997492842978364370664549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1998328561985576247109699 2997492842978364370664549)
                ·
                  refine ⟨562029908058443319499603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2997492842978364370664549 562029908058443319499603)
                  ·
                    refine ⟨843044862087664979249405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 562029908058443319499603 843044862087664979249405)
                    ·
                      refine ⟨316141823282874367218527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 843044862087664979249405 316141823282874367218527)
                      ·
                        rfl

theorem cell23_615684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_615684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615684 prefixEnd_615684 := by exact prefixLift 615684
  have htrace : WordTrace (prefixWord ++ tailWord_615684) baseStart_615684 baseEnd_615684 := by
    simpa [prefixWord, tailWord_615684, baseEnd_615684] using wordTrace_append hprefix tailTrace_615684
  have hstable : (prefixWord ++ tailWord_615684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615684).length < 2 ^ (prefixWord ++ tailWord_615684).sum := by decide
  have hdescent : baseEnd_615684 < baseStart_615684 := by decide
  rcases family_descends (prefixWord ++ tailWord_615684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615690 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4]
def baseStart_615690 : Nat := 118140960795 + 615690 * 2 ^ 59
def prefixEnd_615690 : Nat := 4983230072969 + 3 ^ 40 * 615690 * 2
def baseEnd_615690 : Nat := 316144904166801343743499

theorem tailTrace_615690 : CollatzResearch.WordTrace tailWord_615690 prefixEnd_615690 316144904166801343743499 := by
  unfold tailWord_615690
  simp only [CollatzResearch.WordTrace]
  refine ⟨5614014784866939081393131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14970706092978504217048349 5614014784866939081393131)
  ·
    refine ⟨8421022177300408622089697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5614014784866939081393131 8421022177300408622089697)
    ·
      refine ⟨6315766632975306466567273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8421022177300408622089697 6315766632975306466567273)
      ·
        refine ⟨4736824974731479849925455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6315766632975306466567273 4736824974731479849925455)
        ·
          refine ⟨7105237462097219774888183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4736824974731479849925455 7105237462097219774888183)
          ·
            refine ⟨10657856193145829662332275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7105237462097219774888183 10657856193145829662332275)
            ·
              refine ⟨15986784289718744493498413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10657856193145829662332275 15986784289718744493498413)
              ·
                refine ⟨5995044108644529185061905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15986784289718744493498413 5995044108644529185061905)
                ·
                  refine ⟨4496283081483396888796429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5995044108644529185061905 4496283081483396888796429)
                  ·
                    refine ⟨1686106155556273833298661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4496283081483396888796429 1686106155556273833298661)
                    ·
                      refine ⟨316144904166801343743499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1686106155556273833298661 316144904166801343743499)
                      ·
                        rfl

theorem cell23_615690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_615690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615690 prefixEnd_615690 := by exact prefixLift 615690
  have htrace : WordTrace (prefixWord ++ tailWord_615690) baseStart_615690 baseEnd_615690 := by
    simpa [prefixWord, tailWord_615690, baseEnd_615690] using wordTrace_append hprefix tailTrace_615690
  have hstable : (prefixWord ++ tailWord_615690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615690).length < 2 ^ (prefixWord ++ tailWord_615690).sum := by decide
  have hdescent : baseEnd_615690 < baseStart_615690 := by decide
  rcases family_descends (prefixWord ++ tailWord_615690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615707 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 1, 4, 2]
def baseStart_615707 : Nat := 118140960795 + 615707 * 2 ^ 59
def prefixEnd_615707 : Nat := 4983230072969 + 3 ^ 40 * 615707 * 2
def baseEnd_615707 : Nat := 316153633337927777230921

theorem tailTrace_615707 : CollatzResearch.WordTrace tailWord_615707 prefixEnd_615707 316153633337927777230921 := by
  unfold tailWord_615707
  simp only [CollatzResearch.WordTrace]
  refine ⟨22456679180406168228941375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14971119453604112152627583 22456679180406168228941375)
  ·
    refine ⟨33685018770609252343412063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22456679180406168228941375 33685018770609252343412063)
    ·
      refine ⟨50527528155913878515118095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33685018770609252343412063 50527528155913878515118095)
      ·
        refine ⟨75791292233870817772677143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50527528155913878515118095 75791292233870817772677143)
        ·
          refine ⟨113686938350806226659015715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75791292233870817772677143 113686938350806226659015715)
          ·
            refine ⟨170530407526209339988523573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113686938350806226659015715 170530407526209339988523573)
            ·
              refine ⟨15987225705582125623924085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 170530407526209339988523573 15987225705582125623924085)
              ·
                refine ⟨1498802409898324277242883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15987225705582125623924085 1498802409898324277242883)
                ·
                  refine ⟨2248203614847486415864325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1498802409898324277242883 2248203614847486415864325)
                  ·
                    refine ⟨421538177783903702974561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2248203614847486415864325 421538177783903702974561)
                    ·
                      refine ⟨316153633337927777230921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 421538177783903702974561 316153633337927777230921)
                      ·
                        rfl

theorem cell23_615707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 4, 2].length) (baseStart_615707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615707 prefixEnd_615707 := by exact prefixLift 615707
  have htrace : WordTrace (prefixWord ++ tailWord_615707) baseStart_615707 baseEnd_615707 := by
    simpa [prefixWord, tailWord_615707, baseEnd_615707] using wordTrace_append hprefix tailTrace_615707
  have hstable : (prefixWord ++ tailWord_615707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615707).length < 2 ^ (prefixWord ++ tailWord_615707).sum := by decide
  have hdescent : baseEnd_615707 < baseStart_615707 := by decide
  rcases family_descends (prefixWord ++ tailWord_615707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615760 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 1, 7]
def baseStart_615760 : Nat := 118140960795 + 615760 * 2 ^ 59
def prefixEnd_615760 : Nat := 4983230072969 + 3 ^ 40 * 615760 * 2
def baseEnd_615760 : Nat := 105393615937538689956059

theorem tailTrace_615760 : CollatzResearch.WordTrace tailWord_615760 prefixEnd_615760 105393615937538689956059 := by
  unfold tailWord_615760
  simp only [CollatzResearch.WordTrace]
  refine ⟨11229306124607079140310367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14972408166142772187080489 11229306124607079140310367)
  ·
    refine ⟨16843959186910618710465551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11229306124607079140310367 16843959186910618710465551)
    ·
      refine ⟨25265938780365928065698327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16843959186910618710465551 25265938780365928065698327)
      ·
        refine ⟨37898908170548892098547491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25265938780365928065698327 37898908170548892098547491)
        ·
          refine ⟨56848362255823338147821237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37898908170548892098547491 56848362255823338147821237)
          ·
            refine ⟨5329533961483437951358241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56848362255823338147821237 5329533961483437951358241)
            ·
              refine ⟨3997150471112578463518681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5329533961483437951358241 3997150471112578463518681)
              ·
                refine ⟨2997862853334433847639011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3997150471112578463518681 2997862853334433847639011)
                ·
                  refine ⟨4496794280001650771458517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2997862853334433847639011 4496794280001650771458517)
                  ·
                    refine ⟨105393615937538689956059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4496794280001650771458517 105393615937538689956059)
                    ·
                      rfl

theorem cell23_615760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 7].length) (baseStart_615760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615760 prefixEnd_615760 := by exact prefixLift 615760
  have htrace : WordTrace (prefixWord ++ tailWord_615760) baseStart_615760 baseEnd_615760 := by
    simpa [prefixWord, tailWord_615760, baseEnd_615760] using wordTrace_append hprefix tailTrace_615760
  have hstable : (prefixWord ++ tailWord_615760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615760).length < 2 ^ (prefixWord ++ tailWord_615760).sum := by decide
  have hdescent : baseEnd_615760 < baseStart_615760 := by decide
  rcases family_descends (prefixWord ++ tailWord_615760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615770 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7]
def baseStart_615770 : Nat := 118140960795 + 615770 * 2 ^ 59
def prefixEnd_615770 : Nat := 4983230072969 + 3 ^ 40 * 615770 * 2
def baseEnd_615770 : Nat := 316185982619161030743131

theorem tailTrace_615770 : CollatzResearch.WordTrace tailWord_615770 prefixEnd_615770 316185982619161030743131 := by
  unfold tailWord_615770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5614744244794482497121191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14972651319451953325656509 5614744244794482497121191)
  ·
    refine ⟨8422116367191723745681787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5614744244794482497121191 8422116367191723745681787)
    ·
      refine ⟨12633174550787585618522681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8422116367191723745681787 12633174550787585618522681)
      ·
        refine ⟨9474880913090689213892011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12633174550787585618522681 9474880913090689213892011)
        ·
          refine ⟨14212321369636033820838017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9474880913090689213892011 14212321369636033820838017)
          ·
            refine ⟨10659241027227025365628513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14212321369636033820838017 10659241027227025365628513)
            ·
              refine ⟨7994430770420269024221385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10659241027227025365628513 7994430770420269024221385)
              ·
                refine ⟨5995823077815201768166039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7994430770420269024221385 5995823077815201768166039)
                ·
                  refine ⟨8993734616722802652249059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5995823077815201768166039 8993734616722802652249059)
                  ·
                    refine ⟨13490601925084203978373589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8993734616722802652249059 13490601925084203978373589)
                    ·
                      refine ⟨316185982619161030743131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13490601925084203978373589 316185982619161030743131)
                      ·
                        rfl

theorem cell23_615770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_615770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615770 prefixEnd_615770 := by exact prefixLift 615770
  have htrace : WordTrace (prefixWord ++ tailWord_615770) baseStart_615770 baseEnd_615770 := by
    simpa [prefixWord, tailWord_615770, baseEnd_615770] using wordTrace_append hprefix tailTrace_615770
  have hstable : (prefixWord ++ tailWord_615770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615770).length < 2 ^ (prefixWord ++ tailWord_615770).sum := by decide
  have hdescent : baseEnd_615770 < baseStart_615770 := by decide
  rcases family_descends (prefixWord ++ tailWord_615770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615834 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3]
def baseStart_615834 : Nat := 118140960795 + 615834 * 2 ^ 59
def prefixEnd_615834 : Nat := 4983230072969 + 3 ^ 40 * 615834 * 2
def baseEnd_615834 : Nat := 316218845381048780342837

theorem tailTrace_615834 : CollatzResearch.WordTrace tailWord_615834 prefixEnd_615834 316218845381048780342837 := by
  unfold tailWord_615834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5615327812736517229703639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14974207500630712612543037 5615327812736517229703639)
  ·
    refine ⟨8422991719104775844555459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5615327812736517229703639 8422991719104775844555459)
    ·
      refine ⟨12634487578657163766833189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8422991719104775844555459 12634487578657163766833189)
      ·
        refine ⟨2368966420998218206281223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12634487578657163766833189 2368966420998218206281223)
        ·
          refine ⟨3553449631497327309421835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2368966420998218206281223 3553449631497327309421835)
          ·
            refine ⟨5330174447245990964132753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3553449631497327309421835 5330174447245990964132753)
            ·
              refine ⟨3997630835434493223099565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5330174447245990964132753 3997630835434493223099565)
              ·
                refine ⟨1499111563287934958662337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3997630835434493223099565 1499111563287934958662337)
                ·
                  refine ⟨1124333672465951218996753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1499111563287934958662337 1124333672465951218996753)
                  ·
                    refine ⟨843250254349463414247565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1124333672465951218996753 843250254349463414247565)
                    ·
                      refine ⟨316218845381048780342837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 843250254349463414247565 316218845381048780342837)
                      ·
                        rfl

theorem cell23_615834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_615834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615834 prefixEnd_615834 := by exact prefixLift 615834
  have htrace : WordTrace (prefixWord ++ tailWord_615834) baseStart_615834 baseEnd_615834 := by
    simpa [prefixWord, tailWord_615834, baseEnd_615834] using wordTrace_append hprefix tailTrace_615834
  have hstable : (prefixWord ++ tailWord_615834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615834).length < 2 ^ (prefixWord ++ tailWord_615834).sum := by decide
  have hdescent : baseEnd_615834 < baseStart_615834 := by decide
  rcases family_descends (prefixWord ++ tailWord_615834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615837 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 8]
def baseStart_615837 : Nat := 118140960795 + 615837 * 2 ^ 59
def prefixEnd_615837 : Nat := 4983230072969 + 3 ^ 40 * 615837 * 2
def baseEnd_615837 : Nat := 35135598424779140956147

theorem tailTrace_615837 : CollatzResearch.WordTrace tailWord_615837 prefixEnd_615837 35135598424779140956147 := by
  unfold tailWord_615837
  simp only [CollatzResearch.WordTrace]
  refine ⟨22461420669935200431173765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14974280446623466954115843 22461420669935200431173765)
  ·
    refine ⟨4211516375612850080845081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22461420669935200431173765 4211516375612850080845081)
    ·
      refine ⟨3158637281709637560633811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4211516375612850080845081 3158637281709637560633811)
      ·
        refine ⟨4737955922564456340950717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3158637281709637560633811 4737955922564456340950717)
        ·
          refine ⟨1776733470961671127856519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4737955922564456340950717 1776733470961671127856519)
          ·
            refine ⟨2665100206442506691784779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776733470961671127856519 2665100206442506691784779)
            ·
              refine ⟨3997650309663760037677169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2665100206442506691784779 3997650309663760037677169)
              ·
                refine ⟨2998237732247820028257877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3997650309663760037677169 2998237732247820028257877)
                ·
                  refine ⟨35135598424779140956147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2998237732247820028257877 35135598424779140956147)
                  ·
                    rfl

theorem cell23_615837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_615837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615837 prefixEnd_615837 := by exact prefixLift 615837
  have htrace : WordTrace (prefixWord ++ tailWord_615837) baseStart_615837 baseEnd_615837 := by
    simpa [prefixWord, tailWord_615837, baseEnd_615837] using wordTrace_append hprefix tailTrace_615837
  have hstable : (prefixWord ++ tailWord_615837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615837).length < 2 ^ (prefixWord ++ tailWord_615837).sum := by decide
  have hdescent : baseEnd_615837 < baseStart_615837 := by decide
  rcases family_descends (prefixWord ++ tailWord_615837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615884 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 3, 5]
def baseStart_615884 : Nat := 118140960795 + 615884 * 2 ^ 59
def prefixEnd_615884 : Nat := 4983230072969 + 3 ^ 40 * 615884 * 2
def baseEnd_615884 : Nat := 105414839804591194905869

theorem tailTrace_615884 : CollatzResearch.WordTrace tailWord_615884 prefixEnd_615884 105414839804591194905869 := by
  unfold tailWord_615884
  simp only [CollatzResearch.WordTrace]
  refine ⟨11231567450382463729067353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14975423267176618305423137 11231567450382463729067353)
  ·
    refine ⟨8423675587786847796800515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11231567450382463729067353 8423675587786847796800515)
    ·
      refine ⟨12635513381680271695200773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8423675587786847796800515 12635513381680271695200773)
      ·
        refine ⟨2369158759065050942850145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12635513381680271695200773 2369158759065050942850145)
        ·
          refine ⟨1776869069298788207137609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2369158759065050942850145 1776869069298788207137609)
          ·
            refine ⟨1332651801974091155353207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1776869069298788207137609 1332651801974091155353207)
            ·
              refine ⟨1998977702961136733029811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332651801974091155353207 1998977702961136733029811)
              ·
                refine ⟨2998466554441705099544717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1998977702961136733029811 2998466554441705099544717)
                ·
                  refine ⟨1124424957915639412329269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2998466554441705099544717 1124424957915639412329269)
                  ·
                    refine ⟨105414839804591194905869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1124424957915639412329269 105414839804591194905869)
                    ·
                      rfl

theorem cell23_615884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_615884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615884 prefixEnd_615884 := by exact prefixLift 615884
  have htrace : WordTrace (prefixWord ++ tailWord_615884) baseStart_615884 baseEnd_615884 := by
    simpa [prefixWord, tailWord_615884, baseEnd_615884] using wordTrace_append hprefix tailTrace_615884
  have hstable : (prefixWord ++ tailWord_615884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615884).length < 2 ^ (prefixWord ++ tailWord_615884).sum := by decide
  have hdescent : baseEnd_615884 < baseStart_615884 := by decide
  rcases family_descends (prefixWord ++ tailWord_615884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615897 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 3, 6]
def baseStart_615897 : Nat := 118140960795 + 615897 * 2 ^ 59
def prefixEnd_615897 : Nat := 4983230072969 + 3 ^ 40 * 615897 * 2
def baseEnd_615897 : Nat := 105417064887427344618349

theorem tailTrace_615897 : CollatzResearch.WordTrace tailWord_615897 prefixEnd_615897 105417064887427344618349 := by
  unfold tailWord_615897
  simp only [CollatzResearch.WordTrace]
  refine ⟨22463609049717830678357945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14975739366478553785571963 22463609049717830678357945)
  ·
    refine ⟨16847706787288373008768459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22463609049717830678357945 16847706787288373008768459)
    ·
      refine ⟨25271560180932559513152689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16847706787288373008768459 25271560180932559513152689)
      ·
        refine ⟨18953670135699419634864517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25271560180932559513152689 18953670135699419634864517)
        ·
          refine ⟨3553813150443641181537097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18953670135699419634864517 3553813150443641181537097)
          ·
            refine ⟨2665359862832730886152823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3553813150443641181537097 2665359862832730886152823)
            ·
              refine ⟨3998039794249096329229235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2665359862832730886152823 3998039794249096329229235)
              ·
                refine ⟨5997059691373644493843853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3998039794249096329229235 5997059691373644493843853)
                ·
                  refine ⟨2248897384265116685191445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5997059691373644493843853 2248897384265116685191445)
                  ·
                    refine ⟨105417064887427344618349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2248897384265116685191445 105417064887427344618349)
                    ·
                      rfl

theorem cell23_615897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 6].length) (baseStart_615897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615897 prefixEnd_615897 := by exact prefixLift 615897
  have htrace : WordTrace (prefixWord ++ tailWord_615897) baseStart_615897 baseEnd_615897 := by
    simpa [prefixWord, tailWord_615897, baseEnd_615897] using wordTrace_append hprefix tailTrace_615897
  have hstable : (prefixWord ++ tailWord_615897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615897).length < 2 ^ (prefixWord ++ tailWord_615897).sum := by decide
  have hdescent : baseEnd_615897 < baseStart_615897 := by decide
  rcases family_descends (prefixWord ++ tailWord_615897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615942 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_615942 : Nat := 118140960795 + 615942 * 2 ^ 59
def prefixEnd_615942 : Nat := 4983230072969 + 3 ^ 40 * 615942 * 2
def baseEnd_615942 : Nat := 316274301291734357792341

theorem tailTrace_615942 : CollatzResearch.WordTrace tailWord_615942 prefixEnd_615942 316274301291734357792341 := by
  unfold tailWord_615942
  simp only [CollatzResearch.WordTrace]
  refine ⟨702039072954837605117065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14976833556369868909164053 702039072954837605117065)
  ·
    refine ⟨526529304716128203837799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 702039072954837605117065 526529304716128203837799)
    ·
      refine ⟨789793957074192305756699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 526529304716128203837799 789793957074192305756699)
      ·
        refine ⟨1184690935611288458635049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789793957074192305756699 1184690935611288458635049)
        ·
          refine ⟨888518201708466343976287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1184690935611288458635049 888518201708466343976287)
          ·
            refine ⟨1332777302562699515964431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888518201708466343976287 1332777302562699515964431)
            ·
              refine ⟨1999165953844049273946647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332777302562699515964431 1999165953844049273946647)
              ·
                refine ⟨2998748930766073910919971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1999165953844049273946647 2998748930766073910919971)
                ·
                  refine ⟨4498123396149110866379957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2998748930766073910919971 4498123396149110866379957)
                  ·
                    refine ⟨421699068388979143723121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4498123396149110866379957 421699068388979143723121)
                    ·
                      refine ⟨316274301291734357792341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 421699068388979143723121 316274301291734357792341)
                      ·
                        rfl

theorem cell23_615942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_615942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615942 prefixEnd_615942 := by exact prefixLift 615942
  have htrace : WordTrace (prefixWord ++ tailWord_615942) baseStart_615942 baseEnd_615942 := by
    simpa [prefixWord, tailWord_615942, baseEnd_615942] using wordTrace_append hprefix tailTrace_615942
  have hstable : (prefixWord ++ tailWord_615942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615942).length < 2 ^ (prefixWord ++ tailWord_615942).sum := by decide
  have hdescent : baseEnd_615942 < baseStart_615942 := by decide
  rcases family_descends (prefixWord ++ tailWord_615942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615949 : List Nat := [1, 7, 1, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_615949 : Nat := 118140960795 + 615949 * 2 ^ 59
def prefixEnd_615949 : Nat := 4983230072969 + 3 ^ 40 * 615949 * 2
def baseEnd_615949 : Nat := 316277895656315830404809

theorem tailTrace_615949 : CollatzResearch.WordTrace tailWord_615949 prefixEnd_615949 316277895656315830404809 := by
  unfold tailWord_615949
  simp only [CollatzResearch.WordTrace]
  refine ⟨22465505645529443559250901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14977003763686295706167267 22465505645529443559250901)
  ·
    refine ⟨526535288567096333419943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 22465505645529443559250901 526535288567096333419943)
    ·
      refine ⟨789802932850644500129915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 526535288567096333419943 789802932850644500129915)
      ·
        refine ⟨1184704399275966750194873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789802932850644500129915 1184704399275966750194873)
        ·
          refine ⟨888528299456975062646155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1184704399275966750194873 888528299456975062646155)
          ·
            refine ⟨1332792449185462593969233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888528299456975062646155 1332792449185462593969233)
            ·
              refine ⟨999594336889096945476925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1332792449185462593969233 999594336889096945476925)
              ·
                refine ⟨374847876333411354553847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 999594336889096945476925 374847876333411354553847)
                ·
                  refine ⟨562271814500117031830771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374847876333411354553847 562271814500117031830771)
                  ·
                    refine ⟨843407721750175547746157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 562271814500117031830771 843407721750175547746157)
                    ·
                      refine ⟨316277895656315830404809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 843407721750175547746157 316277895656315830404809)
                      ·
                        rfl

theorem cell23_615949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_615949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615949 prefixEnd_615949 := by exact prefixLift 615949
  have htrace : WordTrace (prefixWord ++ tailWord_615949) baseStart_615949 baseEnd_615949 := by
    simpa [prefixWord, tailWord_615949, baseEnd_615949] using wordTrace_append hprefix tailTrace_615949
  have hstable : (prefixWord ++ tailWord_615949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615949).length < 2 ^ (prefixWord ++ tailWord_615949).sum := by decide
  have hdescent : baseEnd_615949 < baseStart_615949 := by decide
  rcases family_descends (prefixWord ++ tailWord_615949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615955 : List Nat := [1, 1, 1, 2, 1, 7, 2, 3, 1, 2, 2]
def baseStart_615955 : Nat := 118140960795 + 615955 * 2 ^ 59
def prefixEnd_615955 : Nat := 4983230072969 + 3 ^ 40 * 615955 * 2
def baseEnd_615955 : Nat := 316280976540242806929781

theorem tailTrace_615955 : CollatzResearch.WordTrace tailWord_615955 prefixEnd_615955 316280976540242806929781 := by
  unfold tailWord_615955
  simp only [CollatzResearch.WordTrace]
  refine ⟨22465724483507706583969319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14977149655671804389312879 22465724483507706583969319)
  ·
    refine ⟨33698586725261559875953979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22465724483507706583969319 33698586725261559875953979)
    ·
      refine ⟨50547880087892339813930969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33698586725261559875953979 50547880087892339813930969)
      ·
        refine ⟨37910910065919254860448227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50547880087892339813930969 37910910065919254860448227)
        ·
          refine ⟨56866365098878882290672341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37910910065919254860448227 56866365098878882290672341)
          ·
            refine ⟨1332805432004973803687633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 56866365098878882290672341 1332805432004973803687633)
            ·
              refine ⟨999604074003730352765725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1332805432004973803687633 999604074003730352765725)
              ·
                refine ⟨374851527751398882287147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 999604074003730352765725 374851527751398882287147)
                ·
                  refine ⟨562277291627098323430721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374851527751398882287147 562277291627098323430721)
                  ·
                    refine ⟨421707968720323742573041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 562277291627098323430721 421707968720323742573041)
                    ·
                      refine ⟨316280976540242806929781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 421707968720323742573041 316280976540242806929781)
                      ·
                        rfl

theorem cell23_615955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 1, 2, 2].length) (baseStart_615955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_615955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_615955 prefixEnd_615955 := by exact prefixLift 615955
  have htrace : WordTrace (prefixWord ++ tailWord_615955) baseStart_615955 baseEnd_615955 := by
    simpa [prefixWord, tailWord_615955, baseEnd_615955] using wordTrace_append hprefix tailTrace_615955
  have hstable : (prefixWord ++ tailWord_615955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615955).length < 2 ^ (prefixWord ++ tailWord_615955).sum := by decide
  have hdescent : baseEnd_615955 < baseStart_615955 := by decide
  rcases family_descends (prefixWord ++ tailWord_615955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616006 : List Nat := [6, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_616006 : Nat := 118140960795 + 616006 * 2 ^ 59
def prefixEnd_616006 : Nat := 4983230072969 + 3 ^ 40 * 616006 * 2
def baseEnd_616006 : Nat := 316307164053622107392047

theorem tailTrace_616006 : CollatzResearch.WordTrace tailWord_616006 prefixEnd_616006 316307164053622107392047 := by
  unfold tailWord_616006
  simp only [CollatzResearch.WordTrace]
  refine ⟨702112018947591946689871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14978389737548628196050581 702112018947591946689871)
  ·
    refine ⟨1053168028421387920034807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 702112018947591946689871 1053168028421387920034807)
    ·
      refine ⟨1579752042632081880052211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1053168028421387920034807 1579752042632081880052211)
      ·
        refine ⟨2369628063948122820078317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1579752042632081880052211 2369628063948122820078317)
        ·
          refine ⟨888610523980546057529369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2369628063948122820078317 888610523980546057529369)
          ·
            refine ⟨666457892985409543147027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 888610523980546057529369 666457892985409543147027)
            ·
              refine ⟨999686839478114314720541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666457892985409543147027 999686839478114314720541)
              ·
                refine ⟨374882564804292868020203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 999686839478114314720541 374882564804292868020203)
                ·
                  refine ⟨562323847206439302030305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374882564804292868020203 562323847206439302030305)
                  ·
                    refine ⟨421742885404829476522729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 562323847206439302030305 421742885404829476522729)
                    ·
                      refine ⟨316307164053622107392047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 421742885404829476522729 316307164053622107392047)
                      ·
                        rfl

theorem cell23_616006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_616006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616006 prefixEnd_616006 := by exact prefixLift 616006
  have htrace : WordTrace (prefixWord ++ tailWord_616006) baseStart_616006 baseEnd_616006 := by
    simpa [prefixWord, tailWord_616006, baseEnd_616006] using wordTrace_append hprefix tailTrace_616006
  have hstable : (prefixWord ++ tailWord_616006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616006).length < 2 ^ (prefixWord ++ tailWord_616006).sum := by decide
  have hdescent : baseEnd_616006 < baseStart_616006 := by decide
  rcases family_descends (prefixWord ++ tailWord_616006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616014 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_616014 : Nat := 118140960795 + 616014 * 2 ^ 59
def prefixEnd_616014 : Nat := 4983230072969 + 3 ^ 40 * 616014 * 2
def baseEnd_616014 : Nat := 316311271898858076092009

theorem tailTrace_616014 : CollatzResearch.WordTrace tailWord_616014 prefixEnd_616014 316311271898858076092009 := by
  unfold tailWord_616014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2808484548786744957545887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14978584260195973106911397 2808484548786744957545887)
  ·
    refine ⟨4212726823180117436318831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2808484548786744957545887 4212726823180117436318831)
    ·
      refine ⟨6319090234770176154478247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4212726823180117436318831 6319090234770176154478247)
      ·
        refine ⟨9478635352155264231717371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6319090234770176154478247 9478635352155264231717371)
        ·
          refine ⟨14217953028232896347576057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9478635352155264231717371 14217953028232896347576057)
          ·
            refine ⟨10663464771174672260682043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14217953028232896347576057 10663464771174672260682043)
            ·
              refine ⟨15995197156762008391023065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10663464771174672260682043 15995197156762008391023065)
              ·
                refine ⟨11996397867571506293267299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15995197156762008391023065 11996397867571506293267299)
                ·
                  refine ⟨17994596801357259439900949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11996397867571506293267299 17994596801357259439900949)
                  ·
                    refine ⟨843496725063621536245357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17994596801357259439900949 843496725063621536245357)
                    ·
                      refine ⟨316311271898858076092009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 843496725063621536245357 316311271898858076092009)
                      ·
                        rfl

theorem cell23_616014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_616014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616014 prefixEnd_616014 := by exact prefixLift 616014
  have htrace : WordTrace (prefixWord ++ tailWord_616014) baseStart_616014 baseEnd_616014 := by
    simpa [prefixWord, tailWord_616014, baseEnd_616014] using wordTrace_append hprefix tailTrace_616014
  have hstable : (prefixWord ++ tailWord_616014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616014).length < 2 ^ (prefixWord ++ tailWord_616014).sum := by decide
  have hdescent : baseEnd_616014 < baseStart_616014 := by decide
  rcases family_descends (prefixWord ++ tailWord_616014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616044 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 3]
def baseStart_616044 : Nat := 118140960795 + 616044 * 2 ^ 59
def prefixEnd_616044 : Nat := 4983230072969 + 3 ^ 40 * 616044 * 2
def baseEnd_616044 : Nat := 316326676318492958716871

theorem tailTrace_616044 : CollatzResearch.WordTrace tailWord_616044 prefixEnd_616044 316326676318492958716871 := by
  unfold tailWord_616044
  simp only [CollatzResearch.WordTrace]
  refine ⟨11234485290092637391979593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14979313720123516522639457 11234485290092637391979593)
  ·
    refine ⟨8425863967569478043984695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11234485290092637391979593 8425863967569478043984695)
    ·
      refine ⟨12638795951354217065977043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8425863967569478043984695 12638795951354217065977043)
      ·
        refine ⟨18958193927031325598965565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12638795951354217065977043 18958193927031325598965565)
        ·
          refine ⟨7109322722636747099612087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18958193927031325598965565 7109322722636747099612087)
          ·
            refine ⟨10663984083955120649418131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7109322722636747099612087 10663984083955120649418131)
            ·
              refine ⟨15995976125932680974127197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10663984083955120649418131 15995976125932680974127197)
              ·
                refine ⟨5998491047224755365297699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15995976125932680974127197 5998491047224755365297699)
                ·
                  refine ⟨8997736570837133047946549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5998491047224755365297699 8997736570837133047946549)
                  ·
                    refine ⟨843537803515981223244989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8997736570837133047946549 843537803515981223244989)
                    ·
                      refine ⟨316326676318492958716871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 843537803515981223244989 316326676318492958716871)
                      ·
                        rfl

theorem cell23_616044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_616044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616044 prefixEnd_616044 := by exact prefixLift 616044
  have htrace : WordTrace (prefixWord ++ tailWord_616044) baseStart_616044 baseEnd_616044 := by
    simpa [prefixWord, tailWord_616044, baseEnd_616044] using wordTrace_append hprefix tailTrace_616044
  have hstable : (prefixWord ++ tailWord_616044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616044).length < 2 ^ (prefixWord ++ tailWord_616044).sum := by decide
  have hdescent : baseEnd_616044 < baseStart_616044 := by decide
  rcases family_descends (prefixWord ++ tailWord_616044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616101 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 1, 6, 2]
def baseStart_616101 : Nat := 118140960795 + 616101 * 2 ^ 59
def prefixEnd_616101 : Nat := 4983230072969 + 3 ^ 40 * 616101 * 2
def baseEnd_616101 : Nat := 316355944715799235704109

theorem tailTrace_616101 : CollatzResearch.WordTrace tailWord_616101 prefixEnd_616101 316355944715799235704109 := by
  unfold tailWord_616101
  simp only [CollatzResearch.WordTrace]
  refine ⟨22471049540978773518784157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14980699693985849012522771 22471049540978773518784157)
  ·
    refine ⟨8426643577867040069544059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22471049540978773518784157 8426643577867040069544059)
    ·
      refine ⟨12639965366800560104316089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8426643577867040069544059 12639965366800560104316089)
      ·
        refine ⟨9479974025100420078237067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12639965366800560104316089 9479974025100420078237067)
        ·
          refine ⟨14219961037650630117355601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9479974025100420078237067 14219961037650630117355601)
          ·
            refine ⟨10664970778237972588016701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14219961037650630117355601 10664970778237972588016701)
            ·
              refine ⟨3999364041839239720506263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10664970778237972588016701 3999364041839239720506263)
              ·
                refine ⟨5999046062758859580759395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3999364041839239720506263 5999046062758859580759395)
                ·
                  refine ⟨8998569094138289371139093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5999046062758859580759395 8998569094138289371139093)
                  ·
                    refine ⟨421807926287732314272145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8998569094138289371139093 421807926287732314272145)
                    ·
                      refine ⟨316355944715799235704109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 421807926287732314272145 316355944715799235704109)
                      ·
                        rfl

theorem cell23_616101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_616101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616101 prefixEnd_616101 := by exact prefixLift 616101
  have htrace : WordTrace (prefixWord ++ tailWord_616101) baseStart_616101 baseEnd_616101 := by
    simpa [prefixWord, tailWord_616101, baseEnd_616101] using wordTrace_append hprefix tailTrace_616101
  have hstable : (prefixWord ++ tailWord_616101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616101).length < 2 ^ (prefixWord ++ tailWord_616101).sum := by decide
  have hdescent : baseEnd_616101 < baseStart_616101 := by decide
  rcases family_descends (prefixWord ++ tailWord_616101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616111 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 3, 4]
def baseStart_616111 : Nat := 118140960795 + 616111 * 2 ^ 59
def prefixEnd_616111 : Nat := 4983230072969 + 3 ^ 40 * 616111 * 2
def baseEnd_616111 : Nat := 105453693174114732193021

theorem tailTrace_616111 : CollatzResearch.WordTrace tailWord_616111 prefixEnd_616111 105453693174114732193021 := by
  unfold tailWord_616111
  simp only [CollatzResearch.WordTrace]
  refine ⟨22471414270942545226648187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14980942847295030151098791 22471414270942545226648187)
  ·
    refine ⟨33707121406413817839972281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22471414270942545226648187 33707121406413817839972281)
    ·
      refine ⟨25280341054810363379979211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33707121406413817839972281 25280341054810363379979211)
      ·
        refine ⟨37920511582215545069968817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25280341054810363379979211 37920511582215545069968817)
        ·
          refine ⟨28440383686661658802476613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37920511582215545069968817 28440383686661658802476613)
          ·
            refine ⟨5332571941249061025464365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28440383686661658802476613 5332571941249061025464365)
            ·
              refine ⟨1999714477968397884549137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5332571941249061025464365 1999714477968397884549137)
              ·
                refine ⟨1499785858476298413411853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999714477968397884549137 1499785858476298413411853)
                ·
                  refine ⟨562419696928611905029445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1499785858476298413411853 562419696928611905029445)
                  ·
                    refine ⟨105453693174114732193021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 562419696928611905029445 105453693174114732193021)
                    ·
                      rfl

theorem cell23_616111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 4].length) (baseStart_616111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616111 prefixEnd_616111 := by exact prefixLift 616111
  have htrace : WordTrace (prefixWord ++ tailWord_616111) baseStart_616111 baseEnd_616111 := by
    simpa [prefixWord, tailWord_616111, baseEnd_616111] using wordTrace_append hprefix tailTrace_616111
  have hstable : (prefixWord ++ tailWord_616111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616111).length < 2 ^ (prefixWord ++ tailWord_616111).sum := by decide
  have hdescent : baseEnd_616111 < baseStart_616111 := by decide
  rcases family_descends (prefixWord ++ tailWord_616111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616171 : List Nat := [1, 1, 1, 1, 2, 4, 3, 4, 1, 5]
def baseStart_616171 : Nat := 118140960795 + 616171 * 2 ^ 59
def prefixEnd_616171 : Nat := 4983230072969 + 3 ^ 40 * 616171 * 2
def baseEnd_616171 : Nat := 105463962787204653942929

theorem tailTrace_616171 : CollatzResearch.WordTrace tailWord_616171 prefixEnd_616171 105463962787204653942929 := by
  unfold tailWord_616171
  simp only [CollatzResearch.WordTrace]
  refine ⟨22473602650725175473832367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14982401767150116982554911 22473602650725175473832367)
  ·
    refine ⟨33710403976087763210748551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22473602650725175473832367 33710403976087763210748551)
    ·
      refine ⟨50565605964131644816122827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33710403976087763210748551 50565605964131644816122827)
      ·
        refine ⟨75848408946197467224184241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50565605964131644816122827 75848408946197467224184241)
        ·
          refine ⟨56886306709648100418138181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75848408946197467224184241 56886306709648100418138181)
          ·
            refine ⟨10666182508059018828400909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56886306709648100418138181 10666182508059018828400909)
            ·
              refine ⟨3999818440522132060650341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10666182508059018828400909 3999818440522132060650341)
              ·
                refine ⟨749965957597899761371939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3999818440522132060650341 749965957597899761371939)
                ·
                  refine ⟨1124948936396849642057909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 749965957597899761371939 1124948936396849642057909)
                  ·
                    refine ⟨105463962787204653942929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1124948936396849642057909 105463962787204653942929)
                    ·
                      rfl

theorem cell23_616171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 5].length) (baseStart_616171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616171 prefixEnd_616171 := by exact prefixLift 616171
  have htrace : WordTrace (prefixWord ++ tailWord_616171) baseStart_616171 baseEnd_616171 := by
    simpa [prefixWord, tailWord_616171, baseEnd_616171] using wordTrace_append hprefix tailTrace_616171
  have hstable : (prefixWord ++ tailWord_616171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616171).length < 2 ^ (prefixWord ++ tailWord_616171).sum := by decide
  have hdescent : baseEnd_616171 < baseStart_616171 := by decide
  rcases family_descends (prefixWord ++ tailWord_616171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616178 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 1, 5, 2]
def baseStart_616178 : Nat := 118140960795 + 616178 * 2 ^ 59
def prefixEnd_616178 : Nat := 4983230072969 + 3 ^ 40 * 616178 * 2
def baseEnd_616178 : Nat := 316395482726195434441255

theorem tailTrace_616178 : CollatzResearch.WordTrace tailWord_616178 prefixEnd_616178 316395482726195434441255 := by
  unfold tailWord_616178
  simp only [CollatzResearch.WordTrace]
  refine ⟨5618464490424953917334297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14982571974466543779558125 5618464490424953917334297)
  ·
    refine ⟨4213848367818715438000723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5618464490424953917334297 4213848367818715438000723)
    ·
      refine ⟨6320772551728073157001085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4213848367818715438000723 6320772551728073157001085)
      ·
        refine ⟨2370289706898027433875407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6320772551728073157001085 2370289706898027433875407)
        ·
          refine ⟨3555434560347041150813111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2370289706898027433875407 3555434560347041150813111)
          ·
            refine ⟨5333151840520561726219667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3555434560347041150813111 5333151840520561726219667)
            ·
              refine ⟨7999727760780842589329501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5333151840520561726219667 7999727760780842589329501)
              ·
                refine ⟨2999897910292815970998563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7999727760780842589329501 2999897910292815970998563)
                ·
                  refine ⟨4499846865439223956497845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2999897910292815970998563 4499846865439223956497845)
                  ·
                    refine ⟨421860643634927245921673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4499846865439223956497845 421860643634927245921673)
                    ·
                      refine ⟨316395482726195434441255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 421860643634927245921673 316395482726195434441255)
                      ·
                        rfl

theorem cell23_616178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_616178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616178 prefixEnd_616178 := by exact prefixLift 616178
  have htrace : WordTrace (prefixWord ++ tailWord_616178) baseStart_616178 baseEnd_616178 := by
    simpa [prefixWord, tailWord_616178, baseEnd_616178] using wordTrace_append hprefix tailTrace_616178
  have hstable : (prefixWord ++ tailWord_616178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616178).length < 2 ^ (prefixWord ++ tailWord_616178).sum := by decide
  have hdescent : baseEnd_616178 < baseStart_616178 := by decide
  rcases family_descends (prefixWord ++ tailWord_616178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616222 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_616222 : Nat := 118140960795 + 616222 * 2 ^ 59
def prefixEnd_616222 : Nat := 4983230072969 + 3 ^ 40 * 616222 * 2
def baseEnd_616222 : Nat := 105472691958331087430351

theorem tailTrace_616222 : CollatzResearch.WordTrace tailWord_616222 prefixEnd_616222 105472691958331087430351 := by
  unfold tailWord_616222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2809432846692551397992365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14983641849026940789292613 2809432846692551397992365)
  ·
    refine ⟨1053537317509706774247137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2809432846692551397992365 1053537317509706774247137)
    ·
      refine ⟨790152988132280080685353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1053537317509706774247137 790152988132280080685353)
      ·
        refine ⟨592614741099210060514015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 790152988132280080685353 592614741099210060514015)
        ·
          refine ⟨888922111648815090771023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592614741099210060514015 888922111648815090771023)
          ·
            refine ⟨1333383167473222636156535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888922111648815090771023 1333383167473222636156535)
            ·
              refine ⟨2000074751209833954234803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333383167473222636156535 2000074751209833954234803)
              ·
                refine ⟨3000112126814750931352205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2000074751209833954234803 3000112126814750931352205)
                ·
                  refine ⟨1125042047555531599257077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3000112126814750931352205 1125042047555531599257077)
                  ·
                    refine ⟨105472691958331087430351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1125042047555531599257077 105472691958331087430351)
                    ·
                      rfl

theorem cell23_616222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_616222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616222 prefixEnd_616222 := by exact prefixLift 616222
  have htrace : WordTrace (prefixWord ++ tailWord_616222) baseStart_616222 baseEnd_616222 := by
    simpa [prefixWord, tailWord_616222, baseEnd_616222] using wordTrace_append hprefix tailTrace_616222
  have hstable : (prefixWord ++ tailWord_616222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616222).length < 2 ^ (prefixWord ++ tailWord_616222).sum := by decide
  have hdescent : baseEnd_616222 < baseStart_616222 := by decide
  rcases family_descends (prefixWord ++ tailWord_616222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616225 : List Nat := [1, 2, 3, 2, 1, 5, 1, 2, 1, 1, 4]
def baseStart_616225 : Nat := 118140960795 + 616225 * 2 ^ 59
def prefixEnd_616225 : Nat := 4983230072969 + 3 ^ 40 * 616225 * 2
def baseEnd_616225 : Nat := 316419616316956750553539

theorem tailTrace_616225 : CollatzResearch.WordTrace tailWord_616225 prefixEnd_616225 316419616316956750553539 := by
  unfold tailWord_616225
  simp only [CollatzResearch.WordTrace]
  refine ⟨22475572192529542696298129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14983714795019695130865419 22475572192529542696298129)
  ·
    refine ⟨16856679144397157022223597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22475572192529542696298129 16856679144397157022223597)
    ·
      refine ⟨6321254679148933883333849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16856679144397157022223597 6321254679148933883333849)
      ·
        refine ⟨4740941009361700412500387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6321254679148933883333849 4740941009361700412500387)
        ·
          refine ⟨7111411514042550618750581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4740941009361700412500387 7111411514042550618750581)
          ·
            refine ⟨666694829441489120507867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7111411514042550618750581 666694829441489120507867)
            ·
              refine ⟨1000042244162233680761801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666694829441489120507867 1000042244162233680761801)
              ·
                refine ⟨750031683121675260571351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1000042244162233680761801 750031683121675260571351)
                ·
                  refine ⟨1125047524682512890857027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750031683121675260571351 1125047524682512890857027)
                  ·
                    refine ⟨1687571287023769336285541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1125047524682512890857027 1687571287023769336285541)
                    ·
                      refine ⟨316419616316956750553539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1687571287023769336285541 316419616316956750553539)
                      ·
                        rfl

theorem cell23_616225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_616225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616225 prefixEnd_616225 := by exact prefixLift 616225
  have htrace : WordTrace (prefixWord ++ tailWord_616225) baseStart_616225 baseEnd_616225 := by
    simpa [prefixWord, tailWord_616225, baseEnd_616225] using wordTrace_append hprefix tailTrace_616225
  have hstable : (prefixWord ++ tailWord_616225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616225).length < 2 ^ (prefixWord ++ tailWord_616225).sum := by decide
  have hdescent : baseEnd_616225 < baseStart_616225 := by decide
  rcases family_descends (prefixWord ++ tailWord_616225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616245 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_616245 : Nat := 118140960795 + 616245 * 2 ^ 59
def prefixEnd_616245 : Nat := 4983230072969 + 3 ^ 40 * 616245 * 2
def baseEnd_616245 : Nat := 316429885930046672303447

theorem tailTrace_616245 : CollatzResearch.WordTrace tailWord_616245 prefixEnd_616245 316429885930046672303447 := by
  unfold tailWord_616245
  simp only [CollatzResearch.WordTrace]
  refine ⟨22476301652457086112026189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14984201101638057408017459 22476301652457086112026189)
  ·
    refine ⟨8428613119671407292009821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22476301652457086112026189 8428613119671407292009821)
    ·
      refine ⟨3160729919876777734503683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8428613119671407292009821 3160729919876777734503683)
      ·
        refine ⟨4741094879815166601755525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3160729919876777734503683 4741094879815166601755525)
        ·
          refine ⟨888955289965343737829161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4741094879815166601755525 888955289965343737829161)
          ·
            refine ⟨666716467474007803371871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 888955289965343737829161 666716467474007803371871)
            ·
              refine ⟨1000074701211011705057807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666716467474007803371871 1000074701211011705057807)
              ·
                refine ⟨1500112051816517557586711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000074701211011705057807 1500112051816517557586711)
                ·
                  refine ⟨2250168077724776336380067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500112051816517557586711 2250168077724776336380067)
                  ·
                    refine ⟨3375252116587164504570101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2250168077724776336380067 3375252116587164504570101)
                    ·
                      refine ⟨316429885930046672303447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3375252116587164504570101 316429885930046672303447)
                      ·
                        rfl

theorem cell23_616245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_616245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616245 prefixEnd_616245 := by exact prefixLift 616245
  have htrace : WordTrace (prefixWord ++ tailWord_616245) baseStart_616245 baseEnd_616245 := by
    simpa [prefixWord, tailWord_616245, baseEnd_616245] using wordTrace_append hprefix tailTrace_616245
  have hstable : (prefixWord ++ tailWord_616245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616245).length < 2 ^ (prefixWord ++ tailWord_616245).sum := by decide
  have hdescent : baseEnd_616245 < baseStart_616245 := by decide
  rcases family_descends (prefixWord ++ tailWord_616245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616259 : List Nat := [1, 1, 1, 3, 1, 5, 4, 2, 1, 2, 2]
def baseStart_616259 : Nat := 118140960795 + 616259 * 2 ^ 59
def prefixEnd_616259 : Nat := 4983230072969 + 3 ^ 40 * 616259 * 2
def baseEnd_616259 : Nat := 316437074659209617528383

theorem tailTrace_616259 : CollatzResearch.WordTrace tailWord_616259 prefixEnd_616259 316437074659209617528383 := by
  unfold tailWord_616259
  simp only [CollatzResearch.WordTrace]
  refine ⟨22476812274406366503035831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14984541516270911002023887 22476812274406366503035831)
  ·
    refine ⟨33715218411609549754553747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22476812274406366503035831 33715218411609549754553747)
    ·
      refine ⟨50572827617414324631830621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33715218411609549754553747 50572827617414324631830621)
      ·
        refine ⟨18964810356530371736936483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50572827617414324631830621 18964810356530371736936483)
        ·
          refine ⟨28447215534795557605404725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18964810356530371736936483 28447215534795557605404725)
          ·
            refine ⟨2666926456387083525506693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28447215534795557605404725 2666926456387083525506693)
            ·
              refine ⟨500048710572578161032505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2666926456387083525506693 500048710572578161032505)
              ·
                refine ⟨375036532929433620774379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500048710572578161032505 375036532929433620774379)
                ·
                  refine ⟨562554799394150431161569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375036532929433620774379 562554799394150431161569)
                  ·
                    refine ⟨421916099545612823371177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 562554799394150431161569 421916099545612823371177)
                    ·
                      refine ⟨316437074659209617528383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 421916099545612823371177 316437074659209617528383)
                      ·
                        rfl

theorem cell23_616259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 1, 2, 2].length) (baseStart_616259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616259 prefixEnd_616259 := by exact prefixLift 616259
  have htrace : WordTrace (prefixWord ++ tailWord_616259) baseStart_616259 baseEnd_616259 := by
    simpa [prefixWord, tailWord_616259, baseEnd_616259] using wordTrace_append hprefix tailTrace_616259
  have hstable : (prefixWord ++ tailWord_616259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616259).length < 2 ^ (prefixWord ++ tailWord_616259).sum := by decide
  have hdescent : baseEnd_616259 < baseStart_616259 := by decide
  rcases family_descends (prefixWord ++ tailWord_616259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616262 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_616262 : Nat := 118140960795 + 616262 * 2 ^ 59
def prefixEnd_616262 : Nat := 4983230072969 + 3 ^ 40 * 616262 * 2
def baseEnd_616262 : Nat := 316438615101173105790869

theorem tailTrace_616262 : CollatzResearch.WordTrace tailWord_616262 prefixEnd_616262 316438615101173105790869 := by
  unfold tailWord_616262
  simp only [CollatzResearch.WordTrace]
  refine ⟨702403802918609312981095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14984614462263665343596693 702403802918609312981095)
  ·
    refine ⟨1053605704377913969471643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 702403802918609312981095 1053605704377913969471643)
    ·
      refine ⟨1580408556566870954207465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1053605704377913969471643 1580408556566870954207465)
      ·
        refine ⟨1185306417425153215655599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1580408556566870954207465 1185306417425153215655599)
        ·
          refine ⟨1777959626137729823483399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1185306417425153215655599 1777959626137729823483399)
          ·
            refine ⟨2666939439206594735225099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1777959626137729823483399 2666939439206594735225099)
            ·
              refine ⟨4000409158809892102837649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2666939439206594735225099 4000409158809892102837649)
              ·
                refine ⟨3000306869107419077128237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4000409158809892102837649 3000306869107419077128237)
                ·
                  refine ⟨1125115075915282153923089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3000306869107419077128237 1125115075915282153923089)
                  ·
                    refine ⟨843836306936461615442317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1125115075915282153923089 843836306936461615442317)
                    ·
                      refine ⟨316438615101173105790869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 843836306936461615442317 316438615101173105790869)
                      ·
                        rfl

theorem cell23_616262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_616262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616262 prefixEnd_616262 := by exact prefixLift 616262
  have htrace : WordTrace (prefixWord ++ tailWord_616262) baseStart_616262 baseEnd_616262 := by
    simpa [prefixWord, tailWord_616262, baseEnd_616262] using wordTrace_append hprefix tailTrace_616262
  have hstable : (prefixWord ++ tailWord_616262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616262).length < 2 ^ (prefixWord ++ tailWord_616262).sum := by decide
  have hdescent : baseEnd_616262 < baseStart_616262 := by decide
  rcases family_descends (prefixWord ++ tailWord_616262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616281 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 4]
def baseStart_616281 : Nat := 118140960795 + 616281 * 2 ^ 59
def prefixEnd_616281 : Nat := 4983230072969 + 3 ^ 40 * 616281 * 2
def baseEnd_616281 : Nat := 316448371233608531453281

theorem tailTrace_616281 : CollatzResearch.WordTrace tailWord_616281 prefixEnd_616281 316448371233608531453281 := by
  unfold tailWord_616281
  simp only [CollatzResearch.WordTrace]
  refine ⟨22477614680326664260336697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14985076453551109506891131 22477614680326664260336697)
  ·
    refine ⟨16858211010244998195252523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22477614680326664260336697 16858211010244998195252523)
    ·
      refine ⟨25287316515367497292878785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16858211010244998195252523 25287316515367497292878785)
      ·
        refine ⟨18965487386525622969659089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25287316515367497292878785 18965487386525622969659089)
        ·
          refine ⟨14224115539894217227244317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18965487386525622969659089 14224115539894217227244317)
          ·
            refine ⟨5334043327460331460216619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14224115539894217227244317 5334043327460331460216619)
            ·
              refine ⟨8001064991190497190324929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5334043327460331460216619 8001064991190497190324929)
              ·
                refine ⟨6000798743392872892743697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8001064991190497190324929 6000798743392872892743697)
                ·
                  refine ⟨4500599057544654669557773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6000798743392872892743697 4500599057544654669557773)
                  ·
                    refine ⟨1687724646579245501084165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4500599057544654669557773 1687724646579245501084165)
                    ·
                      refine ⟨316448371233608531453281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1687724646579245501084165 316448371233608531453281)
                      ·
                        rfl

theorem cell23_616281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_616281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616281 prefixEnd_616281 := by exact prefixLift 616281
  have htrace : WordTrace (prefixWord ++ tailWord_616281) baseStart_616281 baseEnd_616281 := by
    simpa [prefixWord, tailWord_616281, baseEnd_616281] using wordTrace_append hprefix tailTrace_616281
  have hstable : (prefixWord ++ tailWord_616281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616281).length < 2 ^ (prefixWord ++ tailWord_616281).sum := by decide
  have hdescent : baseEnd_616281 < baseStart_616281 := by decide
  rcases family_descends (prefixWord ++ tailWord_616281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616402 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_616402 : Nat := 118140960795 + 616402 * 2 ^ 59
def prefixEnd_616402 : Nat := 4983230072969 + 3 ^ 40 * 616402 * 2
def baseEnd_616402 : Nat := 105503500797600852680075

theorem tailTrace_616402 : CollatzResearch.WordTrace tailWord_616402 prefixEnd_616402 105503500797600852680075 := by
  unfold tailWord_616402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5620506978222075481372865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14988018608592201283660973 5620506978222075481372865)
  ·
    refine ⟨4215380233666556611029649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5620506978222075481372865 4215380233666556611029649)
    ·
      refine ⟨3161535175249917458272237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4215380233666556611029649 3161535175249917458272237)
      ·
        refine ⟨1185575690718719046852089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3161535175249917458272237 1185575690718719046852089)
        ·
          refine ⟨889181768039039285139067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1185575690718719046852089 889181768039039285139067)
          ·
            refine ⟨1333772652058558927708601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889181768039039285139067 1333772652058558927708601)
            ·
              refine ⟨1000329489043919195781451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1333772652058558927708601 1000329489043919195781451)
              ·
                refine ⟨1500494233565878793672177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000329489043919195781451 1500494233565878793672177)
                ·
                  refine ⟨1125370675174409095254133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1500494233565878793672177 1125370675174409095254133)
                  ·
                    refine ⟨105503500797600852680075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1125370675174409095254133 105503500797600852680075)
                    ·
                      rfl

theorem cell23_616402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_616402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616402 prefixEnd_616402 := by exact prefixLift 616402
  have htrace : WordTrace (prefixWord ++ tailWord_616402) baseStart_616402 baseEnd_616402 := by
    simpa [prefixWord, tailWord_616402, baseEnd_616402] using wordTrace_append hprefix tailTrace_616402
  have hstable : (prefixWord ++ tailWord_616402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616402).length < 2 ^ (prefixWord ++ tailWord_616402).sum := by decide
  have hdescent : baseEnd_616402 < baseStart_616402 := by decide
  rcases family_descends (prefixWord ++ tailWord_616402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616405 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_616405 : Nat := 118140960795 + 616405 * 2 ^ 59
def prefixEnd_616405 : Nat := 4983230072969 + 3 ^ 40 * 616405 * 2
def baseEnd_616405 : Nat := 316512042834766046302711

theorem tailTrace_616405 : CollatzResearch.WordTrace tailWord_616405 prefixEnd_616405 316512042834766046302711 := by
  unfold tailWord_616405
  simp only [CollatzResearch.WordTrace]
  refine ⟨22482137331877433437850669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14988091554584955625233779 22482137331877433437850669)
  ·
    refine ⟨8430801499454037539194001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22482137331877433437850669 8430801499454037539194001)
    ·
      refine ⟨6323101124590528154395501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8430801499454037539194001 6323101124590528154395501)
      ·
        refine ⟨2371162921721448057898313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6323101124590528154395501 2371162921721448057898313)
        ·
          refine ⟨1778372191291086043423735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2371162921721448057898313 1778372191291086043423735)
          ·
            refine ⟨2667558286936629065135603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1778372191291086043423735 2667558286936629065135603)
            ·
              refine ⟨4001337430404943597703405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2667558286936629065135603 4001337430404943597703405)
              ·
                refine ⟨1500501536401853849138777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4001337430404943597703405 1500501536401853849138777)
                ·
                  refine ⟨1125376152301390386854083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1500501536401853849138777 1125376152301390386854083)
                  ·
                    refine ⟨1688064228452085580281125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1125376152301390386854083 1688064228452085580281125)
                    ·
                      refine ⟨316512042834766046302711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1688064228452085580281125 316512042834766046302711)
                      ·
                        rfl

theorem cell23_616405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_616405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616405 prefixEnd_616405 := by exact prefixLift 616405
  have htrace : WordTrace (prefixWord ++ tailWord_616405) baseStart_616405 baseEnd_616405 := by
    simpa [prefixWord, tailWord_616405, baseEnd_616405] using wordTrace_append hprefix tailTrace_616405
  have hstable : (prefixWord ++ tailWord_616405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616405).length < 2 ^ (prefixWord ++ tailWord_616405).sum := by decide
  have hdescent : baseEnd_616405 < baseStart_616405 := by decide
  rcases family_descends (prefixWord ++ tailWord_616405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616482 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_616482 : Nat := 118140960795 + 616482 * 2 ^ 59
def prefixEnd_616482 : Nat := 4983230072969 + 3 ^ 40 * 616482 * 2
def baseEnd_616482 : Nat := 316551580845162245039857

theorem tailTrace_616482 : CollatzResearch.WordTrace tailWord_616482 prefixEnd_616482 316551580845162245039857 := by
  unfold tailWord_616482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5621236438149618897100925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14989963835065650392269133 5621236438149618897100925)
  ·
    refine ⟨2107963664306107086412847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5621236438149618897100925 2107963664306107086412847)
    ·
      refine ⟨3161945496459160629619271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2107963664306107086412847 3161945496459160629619271)
      ·
        refine ⟨4742918244688740944428907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3161945496459160629619271 4742918244688740944428907)
        ·
          refine ⟨7114377367033111416643361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4742918244688740944428907 7114377367033111416643361)
          ·
            refine ⟨5335783025274833562482521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7114377367033111416643361 5335783025274833562482521)
            ·
              refine ⟨4001837268956125171861891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5335783025274833562482521 4001837268956125171861891)
              ·
                refine ⟨6002755903434187757792837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4001837268956125171861891 6002755903434187757792837)
                ·
                  refine ⟨1125516731893910204586157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6002755903434187757792837 1125516731893910204586157)
                  ·
                    refine ⟨422068774460216326719809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1125516731893910204586157 422068774460216326719809)
                    ·
                      refine ⟨316551580845162245039857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422068774460216326719809 316551580845162245039857)
                      ·
                        rfl

theorem cell23_616482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_616482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616482 prefixEnd_616482 := by exact prefixLift 616482
  have htrace : WordTrace (prefixWord ++ tailWord_616482) baseStart_616482 baseEnd_616482 := by
    simpa [prefixWord, tailWord_616482, baseEnd_616482] using wordTrace_append hprefix tailTrace_616482
  have hstable : (prefixWord ++ tailWord_616482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616482).length < 2 ^ (prefixWord ++ tailWord_616482).sum := by decide
  have hdescent : baseEnd_616482 < baseStart_616482 := by decide
  rcases family_descends (prefixWord ++ tailWord_616482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616512 : List Nat := [2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 4]
def baseStart_616512 : Nat := 118140960795 + 616512 * 2 ^ 59
def prefixEnd_616512 : Nat := 4983230072969 + 3 ^ 40 * 616512 * 2
def baseEnd_616512 : Nat := 316566985264797127664719

theorem tailTrace_616512 : CollatzResearch.WordTrace tailWord_616512 prefixEnd_616512 316566985264797127664719 := by
  unfold tailWord_616512
  simp only [CollatzResearch.WordTrace]
  refine ⟨11243019971244895355997895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14990693294993193807997193 11243019971244895355997895)
  ·
    refine ⟨16864529956867343033996843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11243019971244895355997895 16864529956867343033996843)
    ·
      refine ⟨25296794935301014550995265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16864529956867343033996843 25296794935301014550995265)
      ·
        refine ⟨18972596201475760913246449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25296794935301014550995265 18972596201475760913246449)
        ·
          refine ⟨14229447151106820684934837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18972596201475760913246449 14229447151106820684934837)
          ·
            refine ⟨1334010670416264439212641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14229447151106820684934837 1334010670416264439212641)
            ·
              refine ⟨1000508002812198329409481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1334010670416264439212641 1000508002812198329409481)
              ·
                refine ⟨750381002109148747057111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1000508002812198329409481 750381002109148747057111)
                ·
                  refine ⟨1125571503163723120585667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750381002109148747057111 1125571503163723120585667)
                  ·
                    refine ⟨1688357254745584680878501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1125571503163723120585667 1688357254745584680878501)
                    ·
                      refine ⟨316566985264797127664719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1688357254745584680878501 316566985264797127664719)
                      ·
                        rfl

theorem cell23_616512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_616512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616512 prefixEnd_616512 := by exact prefixLift 616512
  have htrace : WordTrace (prefixWord ++ tailWord_616512) baseStart_616512 baseEnd_616512 := by
    simpa [prefixWord, tailWord_616512, baseEnd_616512] using wordTrace_append hprefix tailTrace_616512
  have hstable : (prefixWord ++ tailWord_616512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616512).length < 2 ^ (prefixWord ++ tailWord_616512).sum := by decide
  have hdescent : baseEnd_616512 < baseStart_616512 := by decide
  rcases family_descends (prefixWord ++ tailWord_616512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616566 : List Nat := [5, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_616566 : Nat := 118140960795 + 616566 * 2 ^ 59
def prefixEnd_616566 : Nat := 4983230072969 + 3 ^ 40 * 616566 * 2
def baseEnd_616566 : Nat := 316594713220139916389471

theorem tailTrace_616566 : CollatzResearch.WordTrace tailWord_616566 prefixEnd_616566 316594713220139916389471 := by
  unfold tailWord_616566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1405500592768384870903847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14992006322862771956307701 1405500592768384870903847)
  ·
    refine ⟨2108250889152577306355771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1405500592768384870903847 2108250889152577306355771)
    ·
      refine ⟨3162376333728865959533657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2108250889152577306355771 3162376333728865959533657)
      ·
        refine ⟨2371782250296649469650243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3162376333728865959533657 2371782250296649469650243)
        ·
          refine ⟨3557673375444974204475365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2371782250296649469650243 3557673375444974204475365)
          ·
            refine ⟨667063757895932663339131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3557673375444974204475365 667063757895932663339131)
            ·
              refine ⟨1000595636843898995008697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667063757895932663339131 1000595636843898995008697)
              ·
                refine ⟨750446727632924246256523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1000595636843898995008697 750446727632924246256523)
                ·
                  refine ⟨1125670091449386369384785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750446727632924246256523 1125670091449386369384785)
                  ·
                    refine ⟨844252568587039777038589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1125670091449386369384785 844252568587039777038589)
                    ·
                      refine ⟨316594713220139916389471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 844252568587039777038589 316594713220139916389471)
                      ·
                        rfl

theorem cell23_616566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_616566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616566 prefixEnd_616566 := by exact prefixLift 616566
  have htrace : WordTrace (prefixWord ++ tailWord_616566) baseStart_616566 baseEnd_616566 := by
    simpa [prefixWord, tailWord_616566, baseEnd_616566] using wordTrace_append hprefix tailTrace_616566
  have hstable : (prefixWord ++ tailWord_616566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616566).length < 2 ^ (prefixWord ++ tailWord_616566).sum := by decide
  have hdescent : baseEnd_616566 < baseStart_616566 := by decide
  rcases family_descends (prefixWord ++ tailWord_616566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616568 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_616568 : Nat := 118140960795 + 616568 * 2 ^ 59
def prefixEnd_616568 : Nat := 4983230072969 + 3 ^ 40 * 616568 * 2
def baseEnd_616568 : Nat := 316595740181448908564461

theorem tailTrace_616568 : CollatzResearch.WordTrace tailWord_616568 prefixEnd_616568 316595740181448908564461 := by
  unfold tailWord_616568
  simp only [CollatzResearch.WordTrace]
  refine ⟨11244041215143456138017179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14992054953524608184022905 11244041215143456138017179)
  ·
    refine ⟨16866061822715184207025769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11244041215143456138017179 16866061822715184207025769)
    ·
      refine ⟨12649546367036388155269327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16866061822715184207025769 12649546367036388155269327)
      ·
        refine ⟨18974319550554582232903991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12649546367036388155269327 18974319550554582232903991)
        ·
          refine ⟨28461479325831873349355987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18974319550554582232903991 28461479325831873349355987)
          ·
            refine ⟨42692218988747810024033981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28461479325831873349355987 42692218988747810024033981)
            ·
              refine ⟨16009582120780428759012743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42692218988747810024033981 16009582120780428759012743)
              ·
                refine ⟨24014373181170643138519115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16009582120780428759012743 24014373181170643138519115)
                ·
                  refine ⟨36021559771755964707778673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24014373181170643138519115 36021559771755964707778673)
                  ·
                    refine ⟨27016169828816973530834005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36021559771755964707778673 27016169828816973530834005)
                    ·
                      refine ⟨316595740181448908564461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 27016169828816973530834005 316595740181448908564461)
                      ·
                        rfl

theorem cell23_616568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_616568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616568 prefixEnd_616568 := by exact prefixLift 616568
  have htrace : WordTrace (prefixWord ++ tailWord_616568) baseStart_616568 baseEnd_616568 := by
    simpa [prefixWord, tailWord_616568, baseEnd_616568] using wordTrace_append hprefix tailTrace_616568
  have hstable : (prefixWord ++ tailWord_616568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616568).length < 2 ^ (prefixWord ++ tailWord_616568).sum := by decide
  have hdescent : baseEnd_616568 < baseStart_616568 := by decide
  rcases family_descends (prefixWord ++ tailWord_616568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616612 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_616612 : Nat := 118140960795 + 616612 * 2 ^ 59
def prefixEnd_616612 : Nat := 4983230072969 + 3 ^ 40 * 616612 * 2
def baseEnd_616612 : Nat := 105539444443415578804753

theorem tailTrace_616612 : CollatzResearch.WordTrace tailWord_616612 prefixEnd_616612 105539444443415578804753 := by
  unfold tailWord_616612
  simp only [CollatzResearch.WordTrace]
  refine ⟨11244843621063753895318045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14993124828085005193757393 11244843621063753895318045)
  ·
    refine ⟨4216816357898907710744267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11244843621063753895318045 4216816357898907710744267)
    ·
      refine ⟨6325224536848361566116401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4216816357898907710744267 6325224536848361566116401)
      ·
        refine ⟨4743918402636271174587301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6325224536848361566116401 4743918402636271174587301)
        ·
          refine ⟨889484700494300845235119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4743918402636271174587301 889484700494300845235119)
          ·
            refine ⟨1334227050741451267852679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889484700494300845235119 1334227050741451267852679)
            ·
              refine ⟨2001340576112176901779019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334227050741451267852679 2001340576112176901779019)
              ·
                refine ⟨3002010864168265352668529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2001340576112176901779019 3002010864168265352668529)
                ·
                  refine ⟨2251508148126199014501397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3002010864168265352668529 2251508148126199014501397)
                  ·
                    refine ⟨105539444443415578804753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2251508148126199014501397 105539444443415578804753)
                    ·
                      rfl

theorem cell23_616612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_616612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616612 prefixEnd_616612 := by exact prefixLift 616612
  have htrace : WordTrace (prefixWord ++ tailWord_616612) baseStart_616612 baseEnd_616612 := by
    simpa [prefixWord, tailWord_616612, baseEnd_616612] using wordTrace_append hprefix tailTrace_616612
  have hstable : (prefixWord ++ tailWord_616612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616612).length < 2 ^ (prefixWord ++ tailWord_616612).sum := by decide
  have hdescent : baseEnd_616612 < baseStart_616612 := by decide
  rcases family_descends (prefixWord ++ tailWord_616612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616635 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 3]
def baseStart_616635 : Nat := 118140960795 + 616635 * 2 ^ 59
def prefixEnd_616635 : Nat := 4983230072969 + 3 ^ 40 * 616635 * 2
def baseEnd_616635 : Nat := 316630143385300146426653

theorem tailTrace_616635 : CollatzResearch.WordTrace tailWord_616635 prefixEnd_616635 316630143385300146426653 := by
  unfold tailWord_616635
  simp only [CollatzResearch.WordTrace]
  refine ⟨22490526121044182718723359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14993684080696121812482239 22490526121044182718723359)
  ·
    refine ⟨33735789181566274078085039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22490526121044182718723359 33735789181566274078085039)
    ·
      refine ⟨50603683772349411117127559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33735789181566274078085039 50603683772349411117127559)
      ·
        refine ⟨75905525658524116675691339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50603683772349411117127559 75905525658524116675691339)
        ·
          refine ⟨113858288487786175013537009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75905525658524116675691339 113858288487786175013537009)
          ·
            refine ⟨85393716365839631260152757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113858288487786175013537009 85393716365839631260152757)
            ·
              refine ⟨8005660909297465430639321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85393716365839631260152757 8005660909297465430639321)
              ·
                refine ⟨6004245681973099072979491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8005660909297465430639321 6004245681973099072979491)
                ·
                  refine ⟨9006368522959648609469237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6004245681973099072979491 9006368522959648609469237)
                  ·
                    refine ⟨844347049027467057137741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9006368522959648609469237 844347049027467057137741)
                    ·
                      refine ⟨316630143385300146426653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 844347049027467057137741 316630143385300146426653)
                      ·
                        rfl

theorem cell23_616635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 3].length) (baseStart_616635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616635 prefixEnd_616635 := by exact prefixLift 616635
  have htrace : WordTrace (prefixWord ++ tailWord_616635) baseStart_616635 baseEnd_616635 := by
    simpa [prefixWord, tailWord_616635, baseEnd_616635] using wordTrace_append hprefix tailTrace_616635
  have hstable : (prefixWord ++ tailWord_616635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616635).length < 2 ^ (prefixWord ++ tailWord_616635).sum := by decide
  have hdescent : baseEnd_616635 < baseStart_616635 := by decide
  rcases family_descends (prefixWord ++ tailWord_616635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616655 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 4, 5]
def baseStart_616655 : Nat := 118140960795 + 616655 * 2 ^ 59
def prefixEnd_616655 : Nat := 4983230072969 + 3 ^ 40 * 616655 * 2
def baseEnd_616655 : Nat := 105546804332796689392187

theorem tailTrace_616655 : CollatzResearch.WordTrace tailWord_616655 prefixEnd_616655 105546804332796689392187 := by
  unfold tailWord_616655
  simp only [CollatzResearch.WordTrace]
  refine ⟨22491255580971726134451419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14994170387314484089634279 22491255580971726134451419)
  ·
    refine ⟨33736883371457589201677129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22491255580971726134451419 33736883371457589201677129)
    ·
      refine ⟨25302662528593191901257847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33736883371457589201677129 25302662528593191901257847)
      ·
        refine ⟨37953993792889787851886771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25302662528593191901257847 37953993792889787851886771)
        ·
          refine ⟨56930990689334681777830157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37953993792889787851886771 56930990689334681777830157)
          ·
            refine ⟨21349121508500505666686309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56930990689334681777830157 21349121508500505666686309)
            ·
              refine ⟨4002960282843844812503683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21349121508500505666686309 4002960282843844812503683)
              ·
                refine ⟨6004440424265767218755525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4002960282843844812503683 6004440424265767218755525)
                ·
                  refine ⟨1125832579549831353516661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6004440424265767218755525 1125832579549831353516661)
                  ·
                    refine ⟨105546804332796689392187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1125832579549831353516661 105546804332796689392187)
                    ·
                      rfl

theorem cell23_616655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 5].length) (baseStart_616655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616655 prefixEnd_616655 := by exact prefixLift 616655
  have htrace : WordTrace (prefixWord ++ tailWord_616655) baseStart_616655 baseEnd_616655 := by
    simpa [prefixWord, tailWord_616655, baseEnd_616655] using wordTrace_append hprefix tailTrace_616655
  have hstable : (prefixWord ++ tailWord_616655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616655).length < 2 ^ (prefixWord ++ tailWord_616655).sum := by decide
  have hdescent : baseEnd_616655 < baseStart_616655 := by decide
  rcases family_descends (prefixWord ++ tailWord_616655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616665 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 1, 2, 5]
def baseStart_616665 : Nat := 118140960795 + 616665 * 2 ^ 59
def prefixEnd_616665 : Nat := 4983230072969 + 3 ^ 40 * 616665 * 2
def baseEnd_616665 : Nat := 316645547804935029051515

theorem tailTrace_616665 : CollatzResearch.WordTrace tailWord_616665 prefixEnd_616665 316645547804935029051515 := by
  unfold tailWord_616665
  simp only [CollatzResearch.WordTrace]
  refine ⟨22491620310935497842315449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14994413540623665228210299 22491620310935497842315449)
  ·
    refine ⟨16868715233201623381736587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22491620310935497842315449 16868715233201623381736587)
    ·
      refine ⟨25303072849802435072604881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16868715233201623381736587 25303072849802435072604881)
      ·
        refine ⟨18977304637351826304453661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25303072849802435072604881 18977304637351826304453661)
        ·
          refine ⟨7116489239006934864170123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18977304637351826304453661 7116489239006934864170123)
          ·
            refine ⟨10674733858510402296255185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7116489239006934864170123 10674733858510402296255185)
            ·
              refine ⟨8006050393882801722191389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10674733858510402296255185 8006050393882801722191389)
              ·
                refine ⟨3002268897706050645821771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8006050393882801722191389 3002268897706050645821771)
                ·
                  refine ⟨4503403346559075968732657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3002268897706050645821771 4503403346559075968732657)
                  ·
                    refine ⟨3377552509919306976549493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4503403346559075968732657 3377552509919306976549493)
                    ·
                      refine ⟨316645547804935029051515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3377552509919306976549493 316645547804935029051515)
                      ·
                        rfl

theorem cell23_616665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_616665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616665 prefixEnd_616665 := by exact prefixLift 616665
  have htrace : WordTrace (prefixWord ++ tailWord_616665) baseStart_616665 baseEnd_616665 := by
    simpa [prefixWord, tailWord_616665, baseEnd_616665] using wordTrace_append hprefix tailTrace_616665
  have hstable : (prefixWord ++ tailWord_616665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616665).length < 2 ^ (prefixWord ++ tailWord_616665).sum := by decide
  have hdescent : baseEnd_616665 < baseStart_616665 := by decide
  rcases family_descends (prefixWord ++ tailWord_616665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616669 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_616669 : Nat := 118140960795 + 616669 * 2 ^ 59
def prefixEnd_616669 : Nat := 4983230072969 + 3 ^ 40 * 616669 * 2
def baseEnd_616669 : Nat := 316647601727553013401497

theorem tailTrace_616669 : CollatzResearch.WordTrace tailWord_616669 prefixEnd_616669 316647601727553013401497 := by
  unfold tailWord_616669
  simp only [CollatzResearch.WordTrace]
  refine ⟨22491766202921006525461061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14994510801947337683640707 22491766202921006525461061)
  ·
    refine ⟨4217206163047688723523949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22491766202921006525461061 4217206163047688723523949)
    ·
      refine ⟨1581452311142883271321481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4217206163047688723523949 1581452311142883271321481)
      ·
        refine ⟨1186089233357162453491111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1581452311142883271321481 1186089233357162453491111)
        ·
          refine ⟨1779133850035743680236667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186089233357162453491111 1779133850035743680236667)
          ·
            refine ⟨2668700775053615520355001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779133850035743680236667 2668700775053615520355001)
            ·
              refine ⟨2001525581290211640266251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2668700775053615520355001 2001525581290211640266251)
              ·
                refine ⟨3002288371935317460399377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2001525581290211640266251 3002288371935317460399377)
                ·
                  refine ⟨2251716278951488095299533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3002288371935317460399377 2251716278951488095299533)
                  ·
                    refine ⟨844393604606808035737325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2251716278951488095299533 844393604606808035737325)
                    ·
                      refine ⟨316647601727553013401497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 844393604606808035737325 316647601727553013401497)
                      ·
                        rfl

theorem cell23_616669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_616669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616669 prefixEnd_616669 := by exact prefixLift 616669
  have htrace : WordTrace (prefixWord ++ tailWord_616669) baseStart_616669 baseEnd_616669 := by
    simpa [prefixWord, tailWord_616669, baseEnd_616669] using wordTrace_append hprefix tailTrace_616669
  have hstable : (prefixWord ++ tailWord_616669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616669).length < 2 ^ (prefixWord ++ tailWord_616669).sum := by decide
  have hdescent : baseEnd_616669 < baseStart_616669 := by decide
  rcases family_descends (prefixWord ++ tailWord_616669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616715 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 8]
def baseStart_616715 : Nat := 118140960795 + 616715 * 2 ^ 59
def prefixEnd_616715 : Nat := 4983230072969 + 3 ^ 40 * 616715 * 2
def baseEnd_616715 : Nat := 35185691315295537047365

theorem tailTrace_616715 : CollatzResearch.WordTrace tailWord_616715 prefixEnd_616715 35185691315295537047365 := by
  unfold tailWord_616715
  simp only [CollatzResearch.WordTrace]
  refine ⟨22493443960754356381635599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14995629307169570921090399 22493443960754356381635599)
  ·
    refine ⟨33740165941131534572453399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22493443960754356381635599 33740165941131534572453399)
    ·
      refine ⟨50610248911697301858680099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33740165941131534572453399 50610248911697301858680099)
      ·
        refine ⟨75915373367545952788020149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50610248911697301858680099 75915373367545952788020149)
        ·
          refine ⟨7117066253207433073876889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75915373367545952788020149 7117066253207433073876889)
          ·
            refine ⟨5337799689905574805407667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7117066253207433073876889 5337799689905574805407667)
            ·
              refine ⟨8006699534858362208111501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5337799689905574805407667 8006699534858362208111501)
              ·
                refine ⟨3002512325571885828041813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8006699534858362208111501 3002512325571885828041813)
                ·
                  refine ⟨35185691315295537047365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3002512325571885828041813 35185691315295537047365)
                  ·
                    rfl

theorem cell23_616715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 8].length) (baseStart_616715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616715 prefixEnd_616715 := by exact prefixLift 616715
  have htrace : WordTrace (prefixWord ++ tailWord_616715) baseStart_616715 baseEnd_616715 := by
    simpa [prefixWord, tailWord_616715, baseEnd_616715] using wordTrace_append hprefix tailTrace_616715
  have hstable : (prefixWord ++ tailWord_616715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616715).length < 2 ^ (prefixWord ++ tailWord_616715).sum := by decide
  have hdescent : baseEnd_616715 < baseStart_616715 := by decide
  rcases family_descends (prefixWord ++ tailWord_616715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616719 : List Nat := [1, 1, 2, 1, 1, 1, 3, 8, 1, 4]
def baseStart_616719 : Nat := 118140960795 + 616719 * 2 ^ 59
def prefixEnd_616719 : Nat := 4983230072969 + 3 ^ 40 * 616719 * 2
def baseEnd_616719 : Nat := 105557758586759272592089

theorem tailTrace_616719 : CollatzResearch.WordTrace tailWord_616719 prefixEnd_616719 105557758586759272592089 := by
  unfold tailWord_616719
  simp only [CollatzResearch.WordTrace]
  refine ⟨22493589852739865064781211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14995726568493243376520807 22493589852739865064781211)
  ·
    refine ⟨33740384779109797597171817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22493589852739865064781211 33740384779109797597171817)
    ·
      refine ⟨25305288584332348197878863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33740384779109797597171817 25305288584332348197878863)
      ·
        refine ⟨37957932876498522296818295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25305288584332348197878863 37957932876498522296818295)
        ·
          refine ⟨56936899314747783445227443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37957932876498522296818295 56936899314747783445227443)
          ·
            refine ⟨85405348972121675167841165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56936899314747783445227443 85405348972121675167841165)
            ·
              refine ⟨32027005864545628187940437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85405348972121675167841165 32027005864545628187940437)
              ·
                refine ⟨375316474975144080327427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 32027005864545628187940437 375316474975144080327427)
                ·
                  refine ⟨562974712462716120491141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375316474975144080327427 562974712462716120491141)
                  ·
                    refine ⟨105557758586759272592089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 562974712462716120491141 105557758586759272592089)
                    ·
                      rfl

theorem cell23_616719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 1, 4].length) (baseStart_616719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616719 prefixEnd_616719 := by exact prefixLift 616719
  have htrace : WordTrace (prefixWord ++ tailWord_616719) baseStart_616719 baseEnd_616719 := by
    simpa [prefixWord, tailWord_616719, baseEnd_616719] using wordTrace_append hprefix tailTrace_616719
  have hstable : (prefixWord ++ tailWord_616719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616719).length < 2 ^ (prefixWord ++ tailWord_616719).sum := by decide
  have hdescent : baseEnd_616719 < baseStart_616719 := by decide
  rcases family_descends (prefixWord ++ tailWord_616719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616810 : List Nat := [3, 1, 3, 3, 1, 2, 2, 3, 1, 1, 3]
def baseStart_616810 : Nat := 118140960795 + 616810 * 2 ^ 59
def prefixEnd_616810 : Nat := 4983230072969 + 3 ^ 40 * 616810 * 2
def baseEnd_616810 : Nat := 316720002499836961738349

theorem tailTrace_616810 : CollatzResearch.WordTrace tailWord_616810 prefixEnd_616810 316720002499836961738349 := by
  unfold tailWord_616810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5624227223852546901585971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14997939263606791737562589 5624227223852546901585971)
  ·
    refine ⟨8436340835778820352378957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5624227223852546901585971 8436340835778820352378957)
    ·
      refine ⟨3163627813417057632142109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8436340835778820352378957 3163627813417057632142109)
      ·
        refine ⟨1186360430031396612053291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3163627813417057632142109 1186360430031396612053291)
        ·
          refine ⟨1779540645047094918079937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186360430031396612053291 1779540645047094918079937)
          ·
            refine ⟨1334655483785321188559953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1779540645047094918079937 1334655483785321188559953)
            ·
              refine ⟨1000991612838990891419965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1334655483785321188559953 1000991612838990891419965)
              ·
                refine ⟨375371854814621584282487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1000991612838990891419965 375371854814621584282487)
                ·
                  refine ⟨563057782221932376423731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375371854814621584282487 563057782221932376423731)
                  ·
                    refine ⟨844586673332898564635597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 563057782221932376423731 844586673332898564635597)
                    ·
                      refine ⟨316720002499836961738349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 844586673332898564635597 316720002499836961738349)
                      ·
                        rfl

theorem cell23_616810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_616810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616810 prefixEnd_616810 := by exact prefixLift 616810
  have htrace : WordTrace (prefixWord ++ tailWord_616810) baseStart_616810 baseEnd_616810 := by
    simpa [prefixWord, tailWord_616810, baseEnd_616810] using wordTrace_append hprefix tailTrace_616810
  have hstable : (prefixWord ++ tailWord_616810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616810).length < 2 ^ (prefixWord ++ tailWord_616810).sum := by decide
  have hdescent : baseEnd_616810 < baseStart_616810 := by decide
  rcases family_descends (prefixWord ++ tailWord_616810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616816 : List Nat := [2, 1, 1, 1, 4, 3, 4, 1, 1, 1, 4]
def baseStart_616816 : Nat := 118140960795 + 616816 * 2 ^ 59
def prefixEnd_616816 : Nat := 4983230072969 + 3 ^ 40 * 616816 * 2
def baseEnd_616816 : Nat := 316723083383763938263321

theorem tailTrace_616816 : CollatzResearch.WordTrace tailWord_616816 prefixEnd_616816 316723083383763938263321 := by
  unfold tailWord_616816
  simp only [CollatzResearch.WordTrace]
  refine ⟨11248563866694225315531151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14998085155592300420708201 11248563866694225315531151)
  ·
    refine ⟨16872845800041337973296727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11248563866694225315531151 16872845800041337973296727)
    ·
      refine ⟨25309268700062006959945091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16872845800041337973296727 25309268700062006959945091)
      ·
        refine ⟨37963903050093010439917637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25309268700062006959945091 37963903050093010439917637)
        ·
          refine ⟨7118231821892439457484557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37963903050093010439917637 7118231821892439457484557)
          ·
            refine ⟨2669336933209664796556709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7118231821892439457484557 2669336933209664796556709)
            ·
              refine ⟨500500674976812149354383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2669336933209664796556709 500500674976812149354383)
              ·
                refine ⟨750751012465218224031575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500500674976812149354383 750751012465218224031575)
                ·
                  refine ⟨1126126518697827336047363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750751012465218224031575 1126126518697827336047363)
                  ·
                    refine ⟨1689189778046741004071045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1126126518697827336047363 1689189778046741004071045)
                    ·
                      refine ⟨316723083383763938263321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1689189778046741004071045 316723083383763938263321)
                      ·
                        rfl

theorem cell23_616816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 1, 1, 4].length) (baseStart_616816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616816 prefixEnd_616816 := by exact prefixLift 616816
  have htrace : WordTrace (prefixWord ++ tailWord_616816) baseStart_616816 baseEnd_616816 := by
    simpa [prefixWord, tailWord_616816, baseEnd_616816] using wordTrace_append hprefix tailTrace_616816
  have hstable : (prefixWord ++ tailWord_616816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616816).length < 2 ^ (prefixWord ++ tailWord_616816).sum := by decide
  have hdescent : baseEnd_616816 < baseStart_616816 := by decide
  rcases family_descends (prefixWord ++ tailWord_616816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616819 : List Nat := [1, 1, 1, 2, 2, 1, 2, 7, 1, 2, 3]
def baseStart_616819 : Nat := 118140960795 + 616819 * 2 ^ 59
def prefixEnd_616819 : Nat := 4983230072969 + 3 ^ 40 * 616819 * 2
def baseEnd_616819 : Nat := 316724623825727426525807

theorem tailTrace_616819 : CollatzResearch.WordTrace tailWord_616819 prefixEnd_616819 316724623825727426525807 := by
  unfold tailWord_616819
  simp only [CollatzResearch.WordTrace]
  refine ⟨22497237152377582143421511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14998158101585054762281007 22497237152377582143421511)
  ·
    refine ⟨33745855728566373215132267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22497237152377582143421511 33745855728566373215132267)
    ·
      refine ⟨50618783592849559822698401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33745855728566373215132267 50618783592849559822698401)
      ·
        refine ⟨37964087694637169867023801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50618783592849559822698401 37964087694637169867023801)
        ·
          refine ⟨28473065770977877400267851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37964087694637169867023801 28473065770977877400267851)
          ·
            refine ⟨42709598656466816100401777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28473065770977877400267851 42709598656466816100401777)
            ·
              refine ⟨32032198992350112075301333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42709598656466816100401777 32032198992350112075301333)
              ·
                refine ⟨750754663883205751764875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32032198992350112075301333 750754663883205751764875)
                ·
                  refine ⟨1126131995824808627647313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750754663883205751764875 1126131995824808627647313)
                  ·
                    refine ⟨844598996868606470735485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1126131995824808627647313 844598996868606470735485)
                    ·
                      refine ⟨316724623825727426525807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 844598996868606470735485 316724623825727426525807)
                      ·
                        rfl

theorem cell23_616819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 2, 3].length) (baseStart_616819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616819 prefixEnd_616819 := by exact prefixLift 616819
  have htrace : WordTrace (prefixWord ++ tailWord_616819) baseStart_616819 baseEnd_616819 := by
    simpa [prefixWord, tailWord_616819, baseEnd_616819] using wordTrace_append hprefix tailTrace_616819
  have hstable : (prefixWord ++ tailWord_616819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616819).length < 2 ^ (prefixWord ++ tailWord_616819).sum := by decide
  have hdescent : baseEnd_616819 < baseStart_616819 := by decide
  rcases family_descends (prefixWord ++ tailWord_616819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616832 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 3]
def baseStart_616832 : Nat := 118140960795 + 616832 * 2 ^ 59
def prefixEnd_616832 : Nat := 4983230072969 + 3 ^ 40 * 616832 * 2
def baseEnd_616832 : Nat := 316731299074235875663247

theorem tailTrace_616832 : CollatzResearch.WordTrace tailWord_616832 prefixEnd_616832 316731299074235875663247 := by
  unfold tailWord_616832
  simp only [CollatzResearch.WordTrace]
  refine ⟨11248855650665242681822375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14998474200886990242429833 11248855650665242681822375)
  ·
    refine ⟨16873283475997864022733563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11248855650665242681822375 16873283475997864022733563)
    ·
      refine ⟨25309925213996796034100345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16873283475997864022733563 25309925213996796034100345)
      ·
        refine ⟨18982443910497597025575259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25309925213996796034100345 18982443910497597025575259)
        ·
          refine ⟨28473665865746395538362889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18982443910497597025575259 28473665865746395538362889)
          ·
            refine ⟨21355249399309796653772167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28473665865746395538362889 21355249399309796653772167)
            ·
              refine ⟨32032874098964694980658251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21355249399309796653772167 32032874098964694980658251)
              ·
                refine ⟨48049311148447042470987377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32032874098964694980658251 48049311148447042470987377)
                ·
                  refine ⟨36036983361335281853240533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48049311148447042470987377 36036983361335281853240533)
                  ·
                    refine ⟨844616797531295668435325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36036983361335281853240533 844616797531295668435325)
                    ·
                      refine ⟨316731299074235875663247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 844616797531295668435325 316731299074235875663247)
                      ·
                        rfl

theorem cell23_616832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_616832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616832 prefixEnd_616832 := by exact prefixLift 616832
  have htrace : WordTrace (prefixWord ++ tailWord_616832) baseStart_616832 baseEnd_616832 := by
    simpa [prefixWord, tailWord_616832, baseEnd_616832] using wordTrace_append hprefix tailTrace_616832
  have hstable : (prefixWord ++ tailWord_616832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616832).length < 2 ^ (prefixWord ++ tailWord_616832).sum := by decide
  have hdescent : baseEnd_616832 < baseStart_616832 := by decide
  rcases family_descends (prefixWord ++ tailWord_616832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616833 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_616833 : Nat := 118140960795 + 616833 * 2 ^ 59
def prefixEnd_616833 : Nat := 4983230072969 + 3 ^ 40 * 616833 * 2
def baseEnd_616833 : Nat := 316731812554890371750743

theorem tailTrace_616833 : CollatzResearch.WordTrace tailWord_616833 prefixEnd_616833 316731812554890371750743 := by
  unfold tailWord_616833
  simp only [CollatzResearch.WordTrace]
  refine ⟨22497747774326862534431153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14998498516217908356287435 22497747774326862534431153)
  ·
    refine ⟨16873310830745146900823365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22497747774326862534431153 16873310830745146900823365)
    ·
      refine ⟨3163745780764715043904381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16873310830745146900823365 3163745780764715043904381)
      ·
        refine ⟨1186404667786768141464143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3163745780764715043904381 1186404667786768141464143)
        ·
          refine ⟨1779607001680152212196215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186404667786768141464143 1779607001680152212196215)
          ·
            refine ⟨2669410502520228318294323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779607001680152212196215 2669410502520228318294323)
            ·
              refine ⟨4004115753780342477441485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2669410502520228318294323 4004115753780342477441485)
              ·
                refine ⟨1501543407667628429040557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4004115753780342477441485 1501543407667628429040557)
                ·
                  refine ⟨563078777875360660890209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1501543407667628429040557 563078777875360660890209)
                  ·
                    refine ⟨422309083406520495667657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 563078777875360660890209 422309083406520495667657)
                    ·
                      refine ⟨316731812554890371750743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422309083406520495667657 316731812554890371750743)
                      ·
                        rfl

theorem cell23_616833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_616833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616833 prefixEnd_616833 := by exact prefixLift 616833
  have htrace : WordTrace (prefixWord ++ tailWord_616833) baseStart_616833 baseEnd_616833 := by
    simpa [prefixWord, tailWord_616833, baseEnd_616833] using wordTrace_append hprefix tailTrace_616833
  have hstable : (prefixWord ++ tailWord_616833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616833).length < 2 ^ (prefixWord ++ tailWord_616833).sum := by decide
  have hdescent : baseEnd_616833 < baseStart_616833 := by decide
  rcases family_descends (prefixWord ++ tailWord_616833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616846 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_616846 : Nat := 118140960795 + 616846 * 2 ^ 59
def prefixEnd_616846 : Nat := 4983230072969 + 3 ^ 40 * 616846 * 2
def baseEnd_616846 : Nat := 316738487803398820888183

theorem tailTrace_616846 : CollatzResearch.WordTrace tailWord_616846 prefixEnd_616846 316738487803398820888183 := by
  unfold tailWord_616846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2812277740409970719331799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14998814615519843836436261 2812277740409970719331799)
  ·
    refine ⟨4218416610614956078997699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2812277740409970719331799 4218416610614956078997699)
    ·
      refine ⟨6327624915922434118496549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4218416610614956078997699 6327624915922434118496549)
      ·
        refine ⟨1186429671735456397218103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6327624915922434118496549 1186429671735456397218103)
        ·
          refine ⟨1779644507603184595827155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186429671735456397218103 1779644507603184595827155)
          ·
            refine ⟨2669466761404776893740733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779644507603184595827155 2669466761404776893740733)
            ·
              refine ⟨1001050035526791335152775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2669466761404776893740733 1001050035526791335152775)
              ·
                refine ⟨1501575053290187002729163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001050035526791335152775 1501575053290187002729163)
                ·
                  refine ⟨2252362579935280504093745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501575053290187002729163 2252362579935280504093745)
                  ·
                    refine ⟨1689271934951460378070309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2252362579935280504093745 1689271934951460378070309)
                    ·
                      refine ⟨316738487803398820888183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1689271934951460378070309 316738487803398820888183)
                      ·
                        rfl

theorem cell23_616846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_616846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616846 prefixEnd_616846 := by exact prefixLift 616846
  have htrace : WordTrace (prefixWord ++ tailWord_616846) baseStart_616846 baseEnd_616846 := by
    simpa [prefixWord, tailWord_616846, baseEnd_616846] using wordTrace_append hprefix tailTrace_616846
  have hstable : (prefixWord ++ tailWord_616846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616846).length < 2 ^ (prefixWord ++ tailWord_616846).sum := by decide
  have hdescent : baseEnd_616846 < baseStart_616846 := by decide
  rcases family_descends (prefixWord ++ tailWord_616846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616849 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 8, 1, 3]
def baseStart_616849 : Nat := 118140960795 + 616849 * 2 ^ 59
def prefixEnd_616849 : Nat := 4983230072969 + 3 ^ 40 * 616849 * 2
def baseEnd_616849 : Nat := 316740028245362309150669

theorem tailTrace_616849 : CollatzResearch.WordTrace tailWord_616849 prefixEnd_616849 316740028245362309150669 := by
  unfold tailWord_616849
  simp only [CollatzResearch.WordTrace]
  refine ⟨22498331342268897267013601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14998887561512598178009067 22498331342268897267013601)
  ·
    refine ⟨16873748506701672950260201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22498331342268897267013601 16873748506701672950260201)
    ·
      refine ⟨12655311380026254712695151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16873748506701672950260201 12655311380026254712695151)
      ·
        refine ⟨18982967070039382069042727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12655311380026254712695151 18982967070039382069042727)
        ·
          refine ⟨28474450605059073103564091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18982967070039382069042727 28474450605059073103564091)
          ·
            refine ⟨42711675907588609655346137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28474450605059073103564091 42711675907588609655346137)
            ·
              refine ⟨32033756930691457241509603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42711675907588609655346137 32033756930691457241509603)
              ·
                refine ⟨48050635396037185862264405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32033756930691457241509603 48050635396037185862264405)
                ·
                  refine ⟨563093383547310771823411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 48050635396037185862264405 563093383547310771823411)
                  ·
                    refine ⟨844640075320966157735117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 563093383547310771823411 844640075320966157735117)
                    ·
                      refine ⟨316740028245362309150669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 844640075320966157735117 316740028245362309150669)
                      ·
                        rfl

theorem cell23_616849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_616849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616849 prefixEnd_616849 := by exact prefixLift 616849
  have htrace : WordTrace (prefixWord ++ tailWord_616849) baseStart_616849 baseEnd_616849 := by
    simpa [prefixWord, tailWord_616849, baseEnd_616849] using wordTrace_append hprefix tailTrace_616849
  have hstable : (prefixWord ++ tailWord_616849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616849).length < 2 ^ (prefixWord ++ tailWord_616849).sum := by decide
  have hdescent : baseEnd_616849 < baseStart_616849 := by decide
  rcases family_descends (prefixWord ++ tailWord_616849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616856 : List Nat := [2, 1, 2, 5, 1, 3, 2, 7]
def baseStart_616856 : Nat := 118140960795 + 616856 * 2 ^ 59
def prefixEnd_616856 : Nat := 4983230072969 + 3 ^ 40 * 616856 * 2
def baseEnd_616856 : Nat := 11731245281849769694931

theorem tailTrace_616856 : CollatzResearch.WordTrace tailWord_616856 prefixEnd_616856 11731245281849769694931 := by
  unfold tailWord_616856
  simp only [CollatzResearch.WordTrace]
  refine ⟨11249293326621768731259211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14999057768829024975012281 11249293326621768731259211)
  ·
    refine ⟨16873939989932653096888817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11249293326621768731259211 16873939989932653096888817)
    ·
      refine ⟨12655454992449489822666613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16873939989932653096888817 12655454992449489822666613)
      ·
        refine ⟨1186448905542139670874995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12655454992449489822666613 1186448905542139670874995)
        ·
          refine ⟨1779673358313209506312493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186448905542139670874995 1779673358313209506312493)
          ·
            refine ⟨667377509367453564867185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1779673358313209506312493 667377509367453564867185)
            ·
              refine ⟨500533132025590173650389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667377509367453564867185 500533132025590173650389)
              ·
                refine ⟨11731245281849769694931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 500533132025590173650389 11731245281849769694931)
                ·
                  rfl

theorem cell23_616856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 7].length) (baseStart_616856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616856 prefixEnd_616856 := by exact prefixLift 616856
  have htrace : WordTrace (prefixWord ++ tailWord_616856) baseStart_616856 baseEnd_616856 := by
    simpa [prefixWord, tailWord_616856, baseEnd_616856] using wordTrace_append hprefix tailTrace_616856
  have hstable : (prefixWord ++ tailWord_616856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616856).length < 2 ^ (prefixWord ++ tailWord_616856).sum := by decide
  have hdescent : baseEnd_616856 < baseStart_616856 := by decide
  rcases family_descends (prefixWord ++ tailWord_616856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616866 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_616866 : Nat := 118140960795 + 616866 * 2 ^ 59
def prefixEnd_616866 : Nat := 4983230072969 + 3 ^ 40 * 616866 * 2
def baseEnd_616866 : Nat := 316748757416488742638091

theorem tailTrace_616866 : CollatzResearch.WordTrace tailWord_616866 prefixEnd_616866 316748757416488742638091 := by
  unfold tailWord_616866
  simp only [CollatzResearch.WordTrace]
  refine ⟨5624737845801827292595613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14999300922138206113588301 5624737845801827292595613)
  ·
    refine ⟨2109276692175685234723355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5624737845801827292595613 2109276692175685234723355)
    ·
      refine ⟨3163915038263527852085033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2109276692175685234723355 3163915038263527852085033)
      ·
        refine ⟨2372936278697645889063775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3163915038263527852085033 2372936278697645889063775)
        ·
          refine ⟨3559404418046468833595663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2372936278697645889063775 3559404418046468833595663)
          ·
            refine ⟨5339106627069703250393495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3559404418046468833595663 5339106627069703250393495)
            ·
              refine ⟨8008659940604554875590243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5339106627069703250393495 8008659940604554875590243)
              ·
                refine ⟨12012989910906832313385365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8008659940604554875590243 12012989910906832313385365)
                ·
                  refine ⟨563108902073757764689939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12012989910906832313385365 563108902073757764689939)
                  ·
                    refine ⟨844663353110636647034909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 563108902073757764689939 844663353110636647034909)
                    ·
                      refine ⟨316748757416488742638091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 844663353110636647034909 316748757416488742638091)
                      ·
                        rfl

theorem cell23_616866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_616866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616866 prefixEnd_616866 := by exact prefixLift 616866
  have htrace : WordTrace (prefixWord ++ tailWord_616866) baseStart_616866 baseEnd_616866 := by
    simpa [prefixWord, tailWord_616866, baseEnd_616866] using wordTrace_append hprefix tailTrace_616866
  have hstable : (prefixWord ++ tailWord_616866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616866).length < 2 ^ (prefixWord ++ tailWord_616866).sum := by decide
  have hdescent : baseEnd_616866 < baseStart_616866 := by decide
  rcases family_descends (prefixWord ++ tailWord_616866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616884 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_616884 : Nat := 118140960795 + 616884 * 2 ^ 59
def prefixEnd_616884 : Nat := 4983230072969 + 3 ^ 40 * 616884 * 2
def baseEnd_616884 : Nat := 316758000068269672213009

theorem tailTrace_616884 : CollatzResearch.WordTrace tailWord_616884 prefixEnd_616884 316758000068269672213009 := by
  unfold tailWord_616884
  simp only [CollatzResearch.WordTrace]
  refine ⟨11249803948571049122268853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14999738598094732163025137 11249803948571049122268853)
  ·
    refine ⟨1054669120178535855212705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11249803948571049122268853 1054669120178535855212705)
    ·
      refine ⟨791001840133901891409529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1054669120178535855212705 791001840133901891409529)
      ·
        refine ⟨593251380100426418557147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 791001840133901891409529 593251380100426418557147)
        ·
          refine ⟨889877070150639627835721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593251380100426418557147 889877070150639627835721)
          ·
            refine ⟨667407802612979720876791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 889877070150639627835721 667407802612979720876791)
            ·
              refine ⟨1001111703919469581315187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667407802612979720876791 1001111703919469581315187)
              ·
                refine ⟨1501667555879204371972781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001111703919469581315187 1501667555879204371972781)
                ·
                  refine ⟨563125333454701639489793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1501667555879204371972781 563125333454701639489793)
                  ·
                    refine ⟨422344000091026229617345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 563125333454701639489793 422344000091026229617345)
                    ·
                      refine ⟨316758000068269672213009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422344000091026229617345 316758000068269672213009)
                      ·
                        rfl

theorem cell23_616884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_616884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616884 prefixEnd_616884 := by exact prefixLift 616884
  have htrace : WordTrace (prefixWord ++ tailWord_616884) baseStart_616884 baseEnd_616884 := by
    simpa [prefixWord, tailWord_616884, baseEnd_616884] using wordTrace_append hprefix tailTrace_616884
  have hstable : (prefixWord ++ tailWord_616884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616884).length < 2 ^ (prefixWord ++ tailWord_616884).sum := by decide
  have hdescent : baseEnd_616884 < baseStart_616884 := by decide
  rcases family_descends (prefixWord ++ tailWord_616884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616900 : List Nat := [2, 3, 3, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_616900 : Nat := 118140960795 + 616900 * 2 ^ 59
def prefixEnd_616900 : Nat := 4983230072969 + 3 ^ 40 * 616900 * 2
def baseEnd_616900 : Nat := 316766215758741609612935

theorem tailTrace_616900 : CollatzResearch.WordTrace tailWord_616900 prefixEnd_616900 316766215758741609612935 := by
  unfold tailWord_616900
  simp only [CollatzResearch.WordTrace]
  refine ⟨11250095732542066488560077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15000127643389421984746769 11250095732542066488560077)
  ·
    refine ⟨4218785899703274933210029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11250095732542066488560077 4218785899703274933210029)
    ·
      refine ⟨1582044712388728099953761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4218785899703274933210029 1582044712388728099953761)
      ·
        refine ⟨1186533534291546074965321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1582044712388728099953761 1186533534291546074965321)
        ·
          refine ⟨889900150718659556223991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1186533534291546074965321 889900150718659556223991)
          ·
            refine ⟨1334850226077989334335987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889900150718659556223991 1334850226077989334335987)
            ·
              refine ⟨2002275339116984001503981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334850226077989334335987 2002275339116984001503981)
              ·
                refine ⟨750853252168869000563993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2002275339116984001503981 750853252168869000563993)
                ·
                  refine ⟨563139939126651750422995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 750853252168869000563993 563139939126651750422995)
                  ·
                    refine ⟨844709908689977625634493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 563139939126651750422995 844709908689977625634493)
                    ·
                      refine ⟨316766215758741609612935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 844709908689977625634493 316766215758741609612935)
                      ·
                        rfl

theorem cell23_616900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_616900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616900 prefixEnd_616900 := by exact prefixLift 616900
  have htrace : WordTrace (prefixWord ++ tailWord_616900) baseStart_616900 baseEnd_616900 := by
    simpa [prefixWord, tailWord_616900, baseEnd_616900] using wordTrace_append hprefix tailTrace_616900
  have hstable : (prefixWord ++ tailWord_616900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616900).length < 2 ^ (prefixWord ++ tailWord_616900).sum := by decide
  have hdescent : baseEnd_616900 < baseStart_616900 := by decide
  rcases family_descends (prefixWord ++ tailWord_616900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616906 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 1, 4, 2]
def baseStart_616906 : Nat := 118140960795 + 616906 * 2 ^ 59
def prefixEnd_616906 : Nat := 4983230072969 + 3 ^ 40 * 616906 * 2
def baseEnd_616906 : Nat := 316769296642668586137907

theorem tailTrace_616906 : CollatzResearch.WordTrace tailWord_616906 prefixEnd_616906 316769296642668586137907 := by
  unfold tailWord_616906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5625102575765599000459643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15000273535374930667892381 5625102575765599000459643)
  ·
    refine ⟨8437653863648398500689465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5625102575765599000459643 8437653863648398500689465)
    ·
      refine ⟨6328240397736298875517099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8437653863648398500689465 6328240397736298875517099)
      ·
        refine ⟨9492360596604448313275649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6328240397736298875517099 9492360596604448313275649)
        ·
          refine ⟨7119270447453336234956737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9492360596604448313275649 7119270447453336234956737)
          ·
            refine ⟨5339452835590002176217553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7119270447453336234956737 5339452835590002176217553)
            ·
              refine ⟨4004589626692501632163165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5339452835590002176217553 4004589626692501632163165)
              ·
                refine ⟨1501721110009688112061187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4004589626692501632163165 1501721110009688112061187)
                ·
                  refine ⟨2252581665014532168091781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501721110009688112061187 2252581665014532168091781)
                  ·
                    refine ⟨422359062190224781517209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2252581665014532168091781 422359062190224781517209)
                    ·
                      refine ⟨316769296642668586137907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422359062190224781517209 316769296642668586137907)
                      ·
                        rfl

theorem cell23_616906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_616906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616906 prefixEnd_616906 := by exact prefixLift 616906
  have htrace : WordTrace (prefixWord ++ tailWord_616906) baseStart_616906 baseEnd_616906 := by
    simpa [prefixWord, tailWord_616906, baseEnd_616906] using wordTrace_append hprefix tailTrace_616906
  have hstable : (prefixWord ++ tailWord_616906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616906).length < 2 ^ (prefixWord ++ tailWord_616906).sum := by decide
  have hdescent : baseEnd_616906 < baseStart_616906 := by decide
  rcases family_descends (prefixWord ++ tailWord_616906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616939 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 3]
def baseStart_616939 : Nat := 118140960795 + 616939 * 2 ^ 59
def prefixEnd_616939 : Nat := 4983230072969 + 3 ^ 40 * 616939 * 2
def baseEnd_616939 : Nat := 316786241504266957025255

theorem tailTrace_616939 : CollatzResearch.WordTrace tailWord_616939 prefixEnd_616939 316786241504266957025255 := by
  unfold tailWord_616939
  simp only [CollatzResearch.WordTrace]
  refine ⟨22501613911942842637789871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15001075941295228425193247 22501613911942842637789871)
  ·
    refine ⟨33752420867914263956684807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22501613911942842637789871 33752420867914263956684807)
    ·
      refine ⟨50628631301871395935027211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33752420867914263956684807 50628631301871395935027211)
      ·
        refine ⟨75942946952807093902540817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50628631301871395935027211 75942946952807093902540817)
        ·
          refine ⟨56957210214605320426905613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75942946952807093902540817 56957210214605320426905613)
          ·
            refine ⟨21358953830476995160089605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56957210214605320426905613 21358953830476995160089605)
            ·
              refine ⟨4004803843214436592516801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21358953830476995160089605 4004803843214436592516801)
              ·
                refine ⟨3003602882410827444387601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4004803843214436592516801 3003602882410827444387601)
                ·
                  refine ⟨2252702161808120583290701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3003602882410827444387601 2252702161808120583290701)
                  ·
                    refine ⟨844763310678045218734013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2252702161808120583290701 844763310678045218734013)
                    ·
                      refine ⟨316786241504266957025255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 844763310678045218734013 316786241504266957025255)
                      ·
                        rfl

theorem cell23_616939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 3].length) (baseStart_616939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616939 prefixEnd_616939 := by exact prefixLift 616939
  have htrace : WordTrace (prefixWord ++ tailWord_616939) baseStart_616939 baseEnd_616939 := by
    simpa [prefixWord, tailWord_616939, baseEnd_616939] using wordTrace_append hprefix tailTrace_616939
  have hstable : (prefixWord ++ tailWord_616939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616939).length < 2 ^ (prefixWord ++ tailWord_616939).sum := by decide
  have hdescent : baseEnd_616939 < baseStart_616939 := by decide
  rcases family_descends (prefixWord ++ tailWord_616939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616979 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 4]
def baseStart_616979 : Nat := 118140960795 + 616979 * 2 ^ 59
def prefixEnd_616979 : Nat := 4983230072969 + 3 ^ 40 * 616979 * 2
def baseEnd_616979 : Nat := 316806780730446800525071

theorem tailTrace_616979 : CollatzResearch.WordTrace tailWord_616979 prefixEnd_616979 316806780730446800525071 := by
  unfold tailWord_616979
  simp only [CollatzResearch.WordTrace]
  refine ⟨22503072831797929469245991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15002048554531952979497327 22503072831797929469245991)
  ·
    refine ⟨33754609247696894203868987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22503072831797929469245991 33754609247696894203868987)
    ·
      refine ⟨50631913871545341305803481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33754609247696894203868987 50631913871545341305803481)
      ·
        refine ⟨37973935403659005979352611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50631913871545341305803481 37973935403659005979352611)
        ·
          refine ⟨56960903105488508969028917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37973935403659005979352611 56960903105488508969028917)
          ·
            refine ⟨5340084666139547715846461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56960903105488508969028917 5340084666139547715846461)
            ·
              refine ⟨2002531749802330393442423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5340084666139547715846461 2002531749802330393442423)
              ·
                refine ⟨3003797624703495590163635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002531749802330393442423 3003797624703495590163635)
                ·
                  refine ⟨4505696437055243385245453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3003797624703495590163635 4505696437055243385245453)
                  ·
                    refine ⟨1689636163895716269467045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4505696437055243385245453 1689636163895716269467045)
                    ·
                      refine ⟨316806780730446800525071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1689636163895716269467045 316806780730446800525071)
                      ·
                        rfl

theorem cell23_616979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_616979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616979 prefixEnd_616979 := by exact prefixLift 616979
  have htrace : WordTrace (prefixWord ++ tailWord_616979) baseStart_616979 baseEnd_616979 := by
    simpa [prefixWord, tailWord_616979, baseEnd_616979] using wordTrace_append hprefix tailTrace_616979
  have hstable : (prefixWord ++ tailWord_616979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616979).length < 2 ^ (prefixWord ++ tailWord_616979).sum := by decide
  have hdescent : baseEnd_616979 < baseStart_616979 := by decide
  rcases family_descends (prefixWord ++ tailWord_616979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616980 : List Nat := [2, 4, 3, 1, 1, 2, 2, 3, 5]
def baseStart_616980 : Nat := 118140960795 + 616980 * 2 ^ 59
def prefixEnd_616980 : Nat := 4983230072969 + 3 ^ 40 * 616980 * 2
def baseEnd_616980 : Nat := 35200810467900144068063

theorem tailTrace_616980 : CollatzResearch.WordTrace tailWord_616980 prefixEnd_616980 35200810467900144068063 := by
  unfold tailWord_616980
  simp only [CollatzResearch.WordTrace]
  refine ⟨11251554652397153320016197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15002072869862871093354929 11251554652397153320016197)
  ·
    refine ⟨2109666497324466247503037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11251554652397153320016197 2109666497324466247503037)
    ·
      refine ⟨791124936496674842813639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2109666497324466247503037 791124936496674842813639)
      ·
        refine ⟨1186687404745012264220459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791124936496674842813639 1186687404745012264220459)
        ·
          refine ⟨1780031107117518396330689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186687404745012264220459 1780031107117518396330689)
          ·
            refine ⟨1335023330338138797248017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1780031107117518396330689 1335023330338138797248017)
            ·
              refine ⟨1001267497753604097936013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1335023330338138797248017 1001267497753604097936013)
              ·
                refine ⟨375475311657601536726005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1001267497753604097936013 375475311657601536726005)
                ·
                  refine ⟨35200810467900144068063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 375475311657601536726005 35200810467900144068063)
                  ·
                    rfl

theorem cell23_616980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_616980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_616980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_616980 prefixEnd_616980 := by exact prefixLift 616980
  have htrace : WordTrace (prefixWord ++ tailWord_616980) baseStart_616980 baseEnd_616980 := by
    simpa [prefixWord, tailWord_616980, baseEnd_616980] using wordTrace_append hprefix tailTrace_616980
  have hstable : (prefixWord ++ tailWord_616980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616980).length < 2 ^ (prefixWord ++ tailWord_616980).sum := by decide
  have hdescent : baseEnd_616980 < baseStart_616980 := by decide
  rcases family_descends (prefixWord ++ tailWord_616980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617049 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 7, 5]
def baseStart_617049 : Nat := 118140960795 + 617049 * 2 ^ 59
def prefixEnd_617049 : Nat := 4983230072969 + 3 ^ 40 * 617049 * 2
def baseEnd_617049 : Nat := 105614241458753842216583

theorem tailTrace_617049 : CollatzResearch.WordTrace tailWord_617049 prefixEnd_617049 105614241458753842216583 := by
  unfold tailWord_617049
  simp only [CollatzResearch.WordTrace]
  refine ⟨22505625941544331424294201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15003750627696220949529467 22505625941544331424294201)
  ·
    refine ⟨16879219456158248568220651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22505625941544331424294201 16879219456158248568220651)
    ·
      refine ⟨25318829184237372852330977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16879219456158248568220651 25318829184237372852330977)
      ·
        refine ⟨18989121888178029639248233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25318829184237372852330977 18989121888178029639248233)
        ·
          refine ⟨14241841416133522229436175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18989121888178029639248233 14241841416133522229436175)
          ·
            refine ⟨21362762124200283344154263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14241841416133522229436175 21362762124200283344154263)
            ·
              refine ⟨32044143186300425016231395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21362762124200283344154263 32044143186300425016231395)
              ·
                refine ⟨48066214779450637524347093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32044143186300425016231395 48066214779450637524347093)
                ·
                  refine ⟨1126551908893374316976885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 48066214779450637524347093 1126551908893374316976885)
                  ·
                    refine ⟨105614241458753842216583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1126551908893374316976885 105614241458753842216583)
                    ·
                      rfl

theorem cell23_617049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 5].length) (baseStart_617049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617049 prefixEnd_617049 := by exact prefixLift 617049
  have htrace : WordTrace (prefixWord ++ tailWord_617049) baseStart_617049 baseEnd_617049 := by
    simpa [prefixWord, tailWord_617049, baseEnd_617049] using wordTrace_append hprefix tailTrace_617049
  have hstable : (prefixWord ++ tailWord_617049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617049).length < 2 ^ (prefixWord ++ tailWord_617049).sum := by decide
  have hdescent : baseEnd_617049 < baseStart_617049 := by decide
  rcases family_descends (prefixWord ++ tailWord_617049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617066 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 3, 5]
def baseStart_617066 : Nat := 118140960795 + 617066 * 2 ^ 59
def prefixEnd_617066 : Nat := 4983230072969 + 3 ^ 40 * 617066 * 2
def baseEnd_617066 : Nat := 105617151182462653379057

theorem tailTrace_617066 : CollatzResearch.WordTrace tailWord_617066 prefixEnd_617066 105617151182462653379057 := by
  unfold tailWord_617066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5626561495620685831915763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15004163988321828885108701 5626561495620685831915763)
  ·
    refine ⟨8439842243431028747873645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5626561495620685831915763 8439842243431028747873645)
    ·
      refine ⟨3164940841286635780452617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8439842243431028747873645 3164940841286635780452617)
      ·
        refine ⟨2373705630964976835339463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3164940841286635780452617 2373705630964976835339463)
        ·
          refine ⟨3560558446447465253009195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373705630964976835339463 3560558446447465253009195)
          ·
            refine ⟨5340837669671197879513793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560558446447465253009195 5340837669671197879513793)
            ·
              refine ⟨4005628252253398409635345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5340837669671197879513793 4005628252253398409635345)
              ·
                refine ⟨3004221189190048807226509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4005628252253398409635345 3004221189190048807226509)
                ·
                  refine ⟨1126582945946268302709941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3004221189190048807226509 1126582945946268302709941)
                  ·
                    refine ⟨105617151182462653379057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1126582945946268302709941 105617151182462653379057)
                    ·
                      rfl

theorem cell23_617066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_617066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617066 prefixEnd_617066 := by exact prefixLift 617066
  have htrace : WordTrace (prefixWord ++ tailWord_617066) baseStart_617066 baseEnd_617066 := by
    simpa [prefixWord, tailWord_617066, baseEnd_617066] using wordTrace_append hprefix tailTrace_617066
  have hstable : (prefixWord ++ tailWord_617066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617066).length < 2 ^ (prefixWord ++ tailWord_617066).sum := by decide
  have hdescent : baseEnd_617066 < baseStart_617066 := by decide
  rcases family_descends (prefixWord ++ tailWord_617066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617070 : List Nat := [4, 1, 2, 2, 2, 3, 2, 1, 6]
def baseStart_617070 : Nat := 118140960795 + 617070 * 2 ^ 59
def prefixEnd_617070 : Nat := 4983230072969 + 3 ^ 40 * 617070 * 2
def baseEnd_617070 : Nat := 35205945274445104943017

theorem tailTrace_617070 : CollatzResearch.WordTrace tailWord_617070 prefixEnd_617070 35205945274445104943017 := by
  unfold tailWord_617070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2813298984308531501351083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15004261249645501340539109 2813298984308531501351083)
  ·
    refine ⟨4219948476462797252026625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2813298984308531501351083 4219948476462797252026625)
    ·
      refine ⟨3164961357347097939019969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4219948476462797252026625 3164961357347097939019969)
      ·
        refine ⟨2373721018010323454264977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3164961357347097939019969 2373721018010323454264977)
        ·
          refine ⟨1780290763507742590698733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2373721018010323454264977 1780290763507742590698733)
          ·
            refine ⟨667609036315403471512025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1780290763507742590698733 667609036315403471512025)
            ·
              refine ⟨500706777236552603634019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667609036315403471512025 500706777236552603634019)
              ·
                refine ⟨751060165854828905451029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500706777236552603634019 751060165854828905451029)
                ·
                  refine ⟨35205945274445104943017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 751060165854828905451029 35205945274445104943017)
                  ·
                    rfl

theorem cell23_617070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_617070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617070 prefixEnd_617070 := by exact prefixLift 617070
  have htrace : WordTrace (prefixWord ++ tailWord_617070) baseStart_617070 baseEnd_617070 := by
    simpa [prefixWord, tailWord_617070, baseEnd_617070] using wordTrace_append hprefix tailTrace_617070
  have hstable : (prefixWord ++ tailWord_617070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617070).length < 2 ^ (prefixWord ++ tailWord_617070).sum := by decide
  have hdescent : baseEnd_617070 < baseStart_617070 := by decide
  rcases family_descends (prefixWord ++ tailWord_617070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617099 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 6]
def baseStart_617099 : Nat := 118140960795 + 617099 * 2 ^ 59
def prefixEnd_617099 : Nat := 4983230072969 + 3 ^ 40 * 617099 * 2
def baseEnd_617099 : Nat := 316868398408986331024519

theorem tailTrace_617099 : CollatzResearch.WordTrace tailWord_617099 prefixEnd_617099 316868398408986331024519 := by
  unfold tailWord_617099
  simp only [CollatzResearch.WordTrace]
  refine ⟨22507449591363189963614351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15004966394242126642409567 22507449591363189963614351)
  ·
    refine ⟨33761174387044784945421527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22507449591363189963614351 33761174387044784945421527)
    ·
      refine ⟨50641761580567177418132291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33761174387044784945421527 50641761580567177418132291)
      ·
        refine ⟨75962642370850766127198437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50641761580567177418132291 75962642370850766127198437)
        ·
          refine ⟨14242995444534518648849707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75962642370850766127198437 14242995444534518648849707)
          ·
            refine ⟨21364493166801777973274561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14242995444534518648849707 21364493166801777973274561)
            ·
              refine ⟨16023369875101333479955921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21364493166801777973274561 16023369875101333479955921)
              ·
                refine ⟨12017527406326000109966941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16023369875101333479955921 12017527406326000109966941)
                ·
                  refine ⟨4506572777372250041237603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12017527406326000109966941 4506572777372250041237603)
                  ·
                    refine ⟨6759859166058375061856405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4506572777372250041237603 6759859166058375061856405)
                    ·
                      refine ⟨316868398408986331024519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6759859166058375061856405 316868398408986331024519)
                      ·
                        rfl

theorem cell23_617099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 6].length) (baseStart_617099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617099 prefixEnd_617099 := by exact prefixLift 617099
  have htrace : WordTrace (prefixWord ++ tailWord_617099) baseStart_617099 baseEnd_617099 := by
    simpa [prefixWord, tailWord_617099, baseEnd_617099] using wordTrace_append hprefix tailTrace_617099
  have hstable : (prefixWord ++ tailWord_617099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617099).length < 2 ^ (prefixWord ++ tailWord_617099).sum := by decide
  have hdescent : baseEnd_617099 < baseStart_617099 := by decide
  rcases family_descends (prefixWord ++ tailWord_617099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617103 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 5, 2, 2]
def baseStart_617103 : Nat := 118140960795 + 617103 * 2 ^ 59
def prefixEnd_617103 : Nat := 4983230072969 + 3 ^ 40 * 617103 * 2
def baseEnd_617103 : Nat := 316870452331604315374501

theorem tailTrace_617103 : CollatzResearch.WordTrace tailWord_617103 prefixEnd_617103 316870452331604315374501 := by
  unfold tailWord_617103
  simp only [CollatzResearch.WordTrace]
  refine ⟨22507595483348698646759963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15005063655565799097839975 22507595483348698646759963)
  ·
    refine ⟨33761393225023047970139945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22507595483348698646759963 33761393225023047970139945)
    ·
      refine ⟨25321044918767285977604959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33761393225023047970139945 25321044918767285977604959)
      ·
        refine ⟨37981567378150928966407439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25321044918767285977604959 37981567378150928966407439)
        ·
          refine ⟨56972351067226393449611159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37981567378150928966407439 56972351067226393449611159)
          ·
            refine ⟨85458526600839590174416739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56972351067226393449611159 85458526600839590174416739)
            ·
              refine ⟨128187789901259385261625109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85458526600839590174416739 128187789901259385261625109)
              ·
                refine ⟨6008802651621533684138677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 128187789901259385261625109 6008802651621533684138677)
                ·
                  refine ⟨563325248589518782888001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6008802651621533684138677 563325248589518782888001)
                  ·
                    refine ⟨422493936442139087166001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 563325248589518782888001 422493936442139087166001)
                    ·
                      refine ⟨316870452331604315374501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422493936442139087166001 316870452331604315374501)
                      ·
                        rfl

theorem cell23_617103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 2, 2].length) (baseStart_617103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617103 prefixEnd_617103 := by exact prefixLift 617103
  have htrace : WordTrace (prefixWord ++ tailWord_617103) baseStart_617103 baseEnd_617103 := by
    simpa [prefixWord, tailWord_617103, baseEnd_617103] using wordTrace_append hprefix tailTrace_617103
  have hstable : (prefixWord ++ tailWord_617103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617103).length < 2 ^ (prefixWord ++ tailWord_617103).sum := by decide
  have hdescent : baseEnd_617103 < baseStart_617103 := by decide
  rcases family_descends (prefixWord ++ tailWord_617103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617113 : List Nat := [1, 2, 1, 2, 1, 2, 6, 2, 2, 4]
def baseStart_617113 : Nat := 118140960795 + 617113 * 2 ^ 59
def prefixEnd_617113 : Nat := 4983230072969 + 3 ^ 40 * 617113 * 2
def baseEnd_617113 : Nat := 105625195712716425416485

theorem tailTrace_617113 : CollatzResearch.WordTrace tailWord_617113 prefixEnd_617113 105625195712716425416485 := by
  unfold tailWord_617113
  simp only [CollatzResearch.WordTrace]
  refine ⟨22507960213312470354623993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15005306808874980236415995 22507960213312470354623993)
  ·
    refine ⟨16880970159984352765967995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22507960213312470354623993 16880970159984352765967995)
    ·
      refine ⟨25321455239976529148951993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16880970159984352765967995 25321455239976529148951993)
      ·
        refine ⟨18991091429982396861713995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25321455239976529148951993 18991091429982396861713995)
        ·
          refine ⟨28486637144973595292570993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18991091429982396861713995 28486637144973595292570993)
          ·
            refine ⟨21364977858730196469428245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28486637144973595292570993 21364977858730196469428245)
            ·
              refine ⟨1001483337127977959504449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21364977858730196469428245 1001483337127977959504449)
              ·
                refine ⟨751112502845983469628337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1001483337127977959504449 751112502845983469628337)
                ·
                  refine ⟨563334377134487602221253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 751112502845983469628337 563334377134487602221253)
                  ·
                    refine ⟨105625195712716425416485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 563334377134487602221253 105625195712716425416485)
                    ·
                      rfl

theorem cell23_617113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 4].length) (baseStart_617113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617113 prefixEnd_617113 := by exact prefixLift 617113
  have htrace : WordTrace (prefixWord ++ tailWord_617113) baseStart_617113 baseEnd_617113 := by
    simpa [prefixWord, tailWord_617113, baseEnd_617113] using wordTrace_append hprefix tailTrace_617113
  have hstable : (prefixWord ++ tailWord_617113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617113).length < 2 ^ (prefixWord ++ tailWord_617113).sum := by decide
  have hdescent : baseEnd_617113 < baseStart_617113 := by decide
  rcases family_descends (prefixWord ++ tailWord_617113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617114 : List Nat := [3, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3]
def baseStart_617114 : Nat := 118140960795 + 617114 * 2 ^ 59
def prefixEnd_617114 : Nat := 4983230072969 + 3 ^ 40 * 617114 * 2
def baseEnd_617114 : Nat := 316876100618803772336951

theorem tailTrace_617114 : CollatzResearch.WordTrace tailWord_617114 prefixEnd_617114 316876100618803772336951 := by
  unfold tailWord_617114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5626999171577211881352599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15005331124205898350273597 5626999171577211881352599)
  ·
    refine ⟨8440498757365817822028899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5626999171577211881352599 8440498757365817822028899)
    ·
      refine ⟨12660748136048726733043349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8440498757365817822028899 12660748136048726733043349)
      ·
        refine ⟨593472568877284065611407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12660748136048726733043349 593472568877284065611407)
        ·
          refine ⟨890208853315926098417111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593472568877284065611407 890208853315926098417111)
          ·
            refine ⟨1335313279973889147625667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890208853315926098417111 1335313279973889147625667)
            ·
              refine ⟨2002969919960833721438501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335313279973889147625667 2002969919960833721438501)
              ·
                refine ⟨375556859992656322769719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2002969919960833721438501 375556859992656322769719)
                ·
                  refine ⟨563335289988984484154579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375556859992656322769719 563335289988984484154579)
                  ·
                    refine ⟨845002934983476726231869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 563335289988984484154579 845002934983476726231869)
                    ·
                      refine ⟨316876100618803772336951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 845002934983476726231869 316876100618803772336951)
                      ·
                        rfl

theorem cell23_617114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_617114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617114 prefixEnd_617114 := by exact prefixLift 617114
  have htrace : WordTrace (prefixWord ++ tailWord_617114) baseStart_617114 baseEnd_617114 := by
    simpa [prefixWord, tailWord_617114, baseEnd_617114] using wordTrace_append hprefix tailTrace_617114
  have hstable : (prefixWord ++ tailWord_617114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617114).length < 2 ^ (prefixWord ++ tailWord_617114).sum := by decide
  have hdescent : baseEnd_617114 < baseStart_617114 := by decide
  rcases family_descends (prefixWord ++ tailWord_617114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617129 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 6]
def baseStart_617129 : Nat := 118140960795 + 617129 * 2 ^ 59
def prefixEnd_617129 : Nat := 4983230072969 + 3 ^ 40 * 617129 * 2
def baseEnd_617129 : Nat := 316883802828621213649381

theorem tailTrace_617129 : CollatzResearch.WordTrace tailWord_617129 prefixEnd_617129 316883802828621213649381 := by
  unfold tailWord_617129
  simp only [CollatzResearch.WordTrace]
  refine ⟨22508543781254505087206441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15005695854169670058137627 22508543781254505087206441)
  ·
    refine ⟨16881407835940878815404831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22508543781254505087206441 16881407835940878815404831)
    ·
      refine ⟨25322111753911318223107247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16881407835940878815404831 25322111753911318223107247)
      ·
        refine ⟨37983167630866977334660871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25322111753911318223107247 37983167630866977334660871)
        ·
          refine ⟨56974751446300466001991307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37983167630866977334660871 56974751446300466001991307)
          ·
            refine ⟨85462127169450699002986961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56974751446300466001991307 85462127169450699002986961)
            ·
              refine ⟨64096595377088024252240221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85462127169450699002986961 64096595377088024252240221)
              ·
                refine ⟨24036223266408009094590083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64096595377088024252240221 24036223266408009094590083)
                ·
                  refine ⟨36054334899612013641885125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24036223266408009094590083 36054334899612013641885125)
                  ·
                    refine ⟨6760187793677252557853461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36054334899612013641885125 6760187793677252557853461)
                    ·
                      refine ⟨316883802828621213649381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6760187793677252557853461 316883802828621213649381)
                      ·
                        rfl

theorem cell23_617129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_617129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617129 prefixEnd_617129 := by exact prefixLift 617129
  have htrace : WordTrace (prefixWord ++ tailWord_617129) baseStart_617129 baseEnd_617129 := by
    simpa [prefixWord, tailWord_617129, baseEnd_617129] using wordTrace_append hprefix tailTrace_617129
  have hstable : (prefixWord ++ tailWord_617129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617129).length < 2 ^ (prefixWord ++ tailWord_617129).sum := by decide
  have hdescent : baseEnd_617129 < baseStart_617129 := by decide
  rcases family_descends (prefixWord ++ tailWord_617129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617133 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_617133 : Nat := 118140960795 + 617133 * 2 ^ 59
def prefixEnd_617133 : Nat := 4983230072969 + 3 ^ 40 * 617133 * 2
def baseEnd_617133 : Nat := 316885856751239197999363

theorem tailTrace_617133 : CollatzResearch.WordTrace tailWord_617133 prefixEnd_617133 316885856751239197999363 := by
  unfold tailWord_617133
  simp only [CollatzResearch.WordTrace]
  refine ⟨22508689673240013770352053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15005793115493342513568035 22508689673240013770352053)
  ·
    refine ⟨2110189656866251290970505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22508689673240013770352053 2110189656866251290970505)
    ·
      refine ⟨1582642242649688468227879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2110189656866251290970505 1582642242649688468227879)
      ·
        refine ⟨2373963363974532702341819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582642242649688468227879 2373963363974532702341819)
        ·
          refine ⟨3560945045961799053512729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373963363974532702341819 3560945045961799053512729)
          ·
            refine ⟨2670708784471349290134547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3560945045961799053512729 2670708784471349290134547)
            ·
              refine ⟨4006063176707023935201821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670708784471349290134547 4006063176707023935201821)
              ·
                refine ⟨1502273691265133975700683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4006063176707023935201821 1502273691265133975700683)
                ·
                  refine ⟨2253410536897700963551025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502273691265133975700683 2253410536897700963551025)
                  ·
                    refine ⟨1690057902673275722663269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2253410536897700963551025 1690057902673275722663269)
                    ·
                      refine ⟨316885856751239197999363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1690057902673275722663269 316885856751239197999363)
                      ·
                        rfl

theorem cell23_617133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_617133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617133 prefixEnd_617133 := by exact prefixLift 617133
  have htrace : WordTrace (prefixWord ++ tailWord_617133) baseStart_617133 baseEnd_617133 := by
    simpa [prefixWord, tailWord_617133, baseEnd_617133] using wordTrace_append hprefix tailTrace_617133
  have hstable : (prefixWord ++ tailWord_617133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617133).length < 2 ^ (prefixWord ++ tailWord_617133).sum := by decide
  have hdescent : baseEnd_617133 < baseStart_617133 := by decide
  rcases family_descends (prefixWord ++ tailWord_617133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617143 : List Nat := [1, 1, 3, 1, 6, 1, 3, 7]
def baseStart_617143 : Nat := 118140960795 + 617143 * 2 ^ 59
def prefixEnd_617143 : Nat := 4983230072969 + 3 ^ 40 * 617143 * 2
def baseEnd_617143 : Nat := 11736703391029042921271

theorem tailTrace_617143 : CollatzResearch.WordTrace tailWord_617143 prefixEnd_617143 11736703391029042921271 := by
  unfold tailWord_617143
  simp only [CollatzResearch.WordTrace]
  refine ⟨22509054403203785478216083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15006036268802523652144055 22509054403203785478216083)
  ·
    refine ⟨33763581604805678217324125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22509054403203785478216083 33763581604805678217324125)
    ·
      refine ⟨12661343101802129331496547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33763581604805678217324125 12661343101802129331496547)
      ·
        refine ⟨18992014652703193997244821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12661343101802129331496547 18992014652703193997244821)
        ·
          refine ⟨890250686845462218620851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18992014652703193997244821 890250686845462218620851)
          ·
            refine ⟨1335376030268193327931277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890250686845462218620851 1335376030268193327931277)
            ·
              refine ⟨500766011350572497974229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1335376030268193327931277 500766011350572497974229)
              ·
                refine ⟨11736703391029042921271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 500766011350572497974229 11736703391029042921271)
                ·
                  rfl

theorem cell23_617143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 7].length) (baseStart_617143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617143 prefixEnd_617143 := by exact prefixLift 617143
  have htrace : WordTrace (prefixWord ++ tailWord_617143) baseStart_617143 baseEnd_617143 := by
    simpa [prefixWord, tailWord_617143, baseEnd_617143] using wordTrace_append hprefix tailTrace_617143
  have hstable : (prefixWord ++ tailWord_617143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617143).length < 2 ^ (prefixWord ++ tailWord_617143).sum := by decide
  have hdescent : baseEnd_617143 < baseStart_617143 := by decide
  rcases family_descends (prefixWord ++ tailWord_617143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617196 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_617196 : Nat := 118140960795 + 617196 * 2 ^ 59
def prefixEnd_617196 : Nat := 4983230072969 + 3 ^ 40 * 617196 * 2
def baseEnd_617196 : Nat := 316918206032472451511573

theorem tailTrace_617196 : CollatzResearch.WordTrace tailWord_617196 prefixEnd_617196 316918206032472451511573 := by
  unfold tailWord_617196
  simp only [CollatzResearch.WordTrace]
  refine ⟨11255493736005887764947721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15007324981341183686596961 11255493736005887764947721)
  ·
    refine ⟨8441620302004415823710791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11255493736005887764947721 8441620302004415823710791)
    ·
      refine ⟨12662430453006623735566187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8441620302004415823710791 12662430453006623735566187)
      ·
        refine ⟨18993645679509935603349281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12662430453006623735566187 18993645679509935603349281)
        ·
          refine ⟨14245234259632451702511961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18993645679509935603349281 14245234259632451702511961)
          ·
            refine ⟨10683925694724338776883971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14245234259632451702511961 10683925694724338776883971)
            ·
              refine ⟨16025888542086508165325957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10683925694724338776883971 16025888542086508165325957)
              ·
                refine ⟨3004854101641220280998617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16025888542086508165325957 3004854101641220280998617)
                ·
                  refine ⟨2253640576230915210748963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3004854101641220280998617 2253640576230915210748963)
                  ·
                    refine ⟨3380460864346372816123445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2253640576230915210748963 3380460864346372816123445)
                    ·
                      refine ⟨316918206032472451511573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3380460864346372816123445 316918206032472451511573)
                      ·
                        rfl

theorem cell23_617196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_617196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617196 prefixEnd_617196 := by exact prefixLift 617196
  have htrace : WordTrace (prefixWord ++ tailWord_617196) baseStart_617196 baseEnd_617196 := by
    simpa [prefixWord, tailWord_617196, baseEnd_617196] using wordTrace_append hprefix tailTrace_617196
  have hstable : (prefixWord ++ tailWord_617196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617196).length < 2 ^ (prefixWord ++ tailWord_617196).sum := by decide
  have hdescent : baseEnd_617196 < baseStart_617196 := by decide
  rcases family_descends (prefixWord ++ tailWord_617196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617197 : List Nat := [1, 5, 1, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_617197 : Nat := 118140960795 + 617197 * 2 ^ 59
def prefixEnd_617197 : Nat := 4983230072969 + 3 ^ 40 * 617197 * 2
def baseEnd_617197 : Nat := 316918719513126947599069

theorem tailTrace_617197 : CollatzResearch.WordTrace tailWord_617197 prefixEnd_617197 316918719513126947599069 := by
  unfold tailWord_617197
  simp only [CollatzResearch.WordTrace]
  refine ⟨22511023945008152700681845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15007349296672101800454563 22511023945008152700681845)
  ·
    refine ⟨2110408494844514315688923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22511023945008152700681845 2110408494844514315688923)
    ·
      refine ⟨3165612742266771473533385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2110408494844514315688923 3165612742266771473533385)
      ·
        refine ⟨2374209556700078605150039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3165612742266771473533385 2374209556700078605150039)
        ·
          refine ⟨3561314335050117907725059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374209556700078605150039 3561314335050117907725059)
          ·
            refine ⟨5341971502575176861587589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3561314335050117907725059 5341971502575176861587589)
            ·
              refine ⟨1001619656732845661547673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5341971502575176861587589 1001619656732845661547673)
              ·
                refine ⟨751214742549634246160755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1001619656732845661547673 751214742549634246160755)
                ·
                  refine ⟨1126822113824451369241133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751214742549634246160755 1126822113824451369241133)
                  ·
                    refine ⟨422558292684169263465425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1126822113824451369241133 422558292684169263465425)
                    ·
                      refine ⟨316918719513126947599069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422558292684169263465425 316918719513126947599069)
                      ·
                        rfl

theorem cell23_617197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_617197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617197 prefixEnd_617197 := by exact prefixLift 617197
  have htrace : WordTrace (prefixWord ++ tailWord_617197) baseStart_617197 baseEnd_617197 := by
    simpa [prefixWord, tailWord_617197, baseEnd_617197] using wordTrace_append hprefix tailTrace_617197
  have hstable : (prefixWord ++ tailWord_617197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617197).length < 2 ^ (prefixWord ++ tailWord_617197).sum := by decide
  have hdescent : baseEnd_617197 < baseStart_617197 := by decide
  rcases family_descends (prefixWord ++ tailWord_617197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617205 : List Nat := [1, 3, 6, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_617205 : Nat := 118140960795 + 617205 * 2 ^ 59
def prefixEnd_617205 : Nat := 4983230072969 + 3 ^ 40 * 617205 * 2
def baseEnd_617205 : Nat := 316922827358362916299033

theorem tailTrace_617205 : CollatzResearch.WordTrace tailWord_617205 prefixEnd_617205 316922827358362916299033 := by
  unfold tailWord_617205
  simp only [CollatzResearch.WordTrace]
  refine ⟨22511315728979170066973069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15007543819319446711315379 22511315728979170066973069)
  ·
    refine ⟨8441743398367188775114901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22511315728979170066973069 8441743398367188775114901)
    ·
      refine ⟨395706721798461973833511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8441743398367188775114901 395706721798461973833511)
      ·
        refine ⟨593560082697692960750267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395706721798461973833511 593560082697692960750267)
        ·
          refine ⟨890340124046539441125401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593560082697692960750267 890340124046539441125401)
          ·
            refine ⟨667755093034904580844051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 890340124046539441125401 667755093034904580844051)
            ·
              refine ⟨1001632639552356871266077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667755093034904580844051 1001632639552356871266077)
              ·
                refine ⟨375612239832133826724779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1001632639552356871266077 375612239832133826724779)
                ·
                  refine ⟨563418359748200740087169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375612239832133826724779 563418359748200740087169)
                  ·
                    refine ⟨422563769811150555065377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 563418359748200740087169 422563769811150555065377)
                    ·
                      refine ⟨316922827358362916299033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422563769811150555065377 316922827358362916299033)
                      ·
                        rfl

theorem cell23_617205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_617205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617205 prefixEnd_617205 := by exact prefixLift 617205
  have htrace : WordTrace (prefixWord ++ tailWord_617205) baseStart_617205 baseEnd_617205 := by
    simpa [prefixWord, tailWord_617205, baseEnd_617205] using wordTrace_append hprefix tailTrace_617205
  have hstable : (prefixWord ++ tailWord_617205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617205).length < 2 ^ (prefixWord ++ tailWord_617205).sum := by decide
  have hdescent : baseEnd_617205 < baseStart_617205 := by decide
  rcases family_descends (prefixWord ++ tailWord_617205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617210 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2]
def baseStart_617210 : Nat := 118140960795 + 617210 * 2 ^ 59
def prefixEnd_617210 : Nat := 4983230072969 + 3 ^ 40 * 617210 * 2
def baseEnd_617210 : Nat := 316925394761635396736509

theorem tailTrace_617210 : CollatzResearch.WordTrace tailWord_617210 prefixEnd_617210 316925394761635396736509 := by
  unfold tailWord_617210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5627874523490263980226271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15007665395974037280603389 5627874523490263980226271)
  ·
    refine ⟨8441811785235395970339407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5627874523490263980226271 8441811785235395970339407)
    ·
      refine ⟨12662717677853093955509111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8441811785235395970339407 12662717677853093955509111)
      ·
        refine ⟨18994076516779640933263667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12662717677853093955509111 18994076516779640933263667)
        ·
          refine ⟨28491114775169461399895501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18994076516779640933263667 28491114775169461399895501)
          ·
            refine ⟨10684168040688548024960813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28491114775169461399895501 10684168040688548024960813)
            ·
              refine ⟨4006563015258205509360305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10684168040688548024960813 4006563015258205509360305)
              ·
                refine ⟨3004922261443654132020229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4006563015258205509360305 3004922261443654132020229)
                ·
                  refine ⟨563422924020685149753793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3004922261443654132020229 563422924020685149753793)
                  ·
                    refine ⟨422567193015513862315345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 563422924020685149753793 422567193015513862315345)
                    ·
                      refine ⟨316925394761635396736509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422567193015513862315345 316925394761635396736509)
                      ·
                        rfl

theorem cell23_617210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2].length) (baseStart_617210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617210 prefixEnd_617210 := by exact prefixLift 617210
  have htrace : WordTrace (prefixWord ++ tailWord_617210) baseStart_617210 baseEnd_617210 := by
    simpa [prefixWord, tailWord_617210, baseEnd_617210] using wordTrace_append hprefix tailTrace_617210
  have hstable : (prefixWord ++ tailWord_617210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617210).length < 2 ^ (prefixWord ++ tailWord_617210).sum := by decide
  have hdescent : baseEnd_617210 < baseStart_617210 := by decide
  rcases family_descends (prefixWord ++ tailWord_617210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617226 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_617226 : Nat := 118140960795 + 617226 * 2 ^ 59
def prefixEnd_617226 : Nat := 4983230072969 + 3 ^ 40 * 617226 * 2
def baseEnd_617226 : Nat := 316933610452107334136435

theorem tailTrace_617226 : CollatzResearch.WordTrace tailWord_617226 prefixEnd_617226 316933610452107334136435 := by
  unfold tailWord_617226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5628020415475772663371883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15008054441268727102325021 5628020415475772663371883)
  ·
    refine ⟨8442030623213658995057825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5628020415475772663371883 8442030623213658995057825)
    ·
      refine ⟨6331522967410244246293369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8442030623213658995057825 6331522967410244246293369)
      ·
        refine ⟨4748642225557683184720027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6331522967410244246293369 4748642225557683184720027)
        ·
          refine ⟨7122963338336524777080041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4748642225557683184720027 7122963338336524777080041)
          ·
            refine ⟨5342222503752393582810031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7122963338336524777080041 5342222503752393582810031)
            ·
              refine ⟨8013333755628590374215047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5342222503752393582810031 8013333755628590374215047)
              ·
                refine ⟨12020000633442885561322571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8013333755628590374215047 12020000633442885561322571)
                ·
                  refine ⟨18030000950164328341983857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12020000633442885561322571 18030000950164328341983857)
                  ·
                    refine ⟨13522500712623246256487893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18030000950164328341983857 13522500712623246256487893)
                    ·
                      refine ⟨316933610452107334136435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13522500712623246256487893 316933610452107334136435)
                      ·
                        rfl

theorem cell23_617226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_617226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617226 prefixEnd_617226 := by exact prefixLift 617226
  have htrace : WordTrace (prefixWord ++ tailWord_617226) baseStart_617226 baseEnd_617226 := by
    simpa [prefixWord, tailWord_617226, baseEnd_617226] using wordTrace_append hprefix tailTrace_617226
  have hstable : (prefixWord ++ tailWord_617226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617226).length < 2 ^ (prefixWord ++ tailWord_617226).sum := by decide
  have hdescent : baseEnd_617226 < baseStart_617226 := by decide
  rcases family_descends (prefixWord ++ tailWord_617226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617233 : List Nat := [1, 2, 2, 1, 1, 3, 2, 6, 5]
def baseStart_617233 : Nat := 118140960795 + 617233 * 2 ^ 59
def prefixEnd_617233 : Nat := 4983230072969 + 3 ^ 40 * 617233 * 2
def baseEnd_617233 : Nat := 35215244979632089638767

theorem tailTrace_617233 : CollatzResearch.WordTrace tailWord_617233 prefixEnd_617233 35215244979632089638767 := by
  unfold tailWord_617233
  simp only [CollatzResearch.WordTrace]
  refine ⟨22512336972877730848992353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15008224648585153899328235 22512336972877730848992353)
  ·
    refine ⟨16884252729658298136744265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22512336972877730848992353 16884252729658298136744265)
    ·
      refine ⟨12663189547243723602558199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16884252729658298136744265 12663189547243723602558199)
      ·
        refine ⟨18994784320865585403837299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12663189547243723602558199 18994784320865585403837299)
        ·
          refine ⟨28492176481298378105755949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18994784320865585403837299 28492176481298378105755949)
          ·
            refine ⟨10684566180486891789658481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28492176481298378105755949 10684566180486891789658481)
            ·
              refine ⟨8013424635365168842243861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10684566180486891789658481 8013424635365168842243861)
              ·
                refine ⟨375629279782742289480181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8013424635365168842243861 375629279782742289480181)
                ·
                  refine ⟨35215244979632089638767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 375629279782742289480181 35215244979632089638767)
                  ·
                    rfl

theorem cell23_617233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 5].length) (baseStart_617233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617233 prefixEnd_617233 := by exact prefixLift 617233
  have htrace : WordTrace (prefixWord ++ tailWord_617233) baseStart_617233 baseEnd_617233 := by
    simpa [prefixWord, tailWord_617233, baseEnd_617233] using wordTrace_append hprefix tailTrace_617233
  have hstable : (prefixWord ++ tailWord_617233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617233).length < 2 ^ (prefixWord ++ tailWord_617233).sum := by decide
  have hdescent : baseEnd_617233 < baseStart_617233 := by decide
  rcases family_descends (prefixWord ++ tailWord_617233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617244 : List Nat := [2, 2, 3, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_617244 : Nat := 118140960795 + 617244 * 2 ^ 59
def prefixEnd_617244 : Nat := 4983230072969 + 3 ^ 40 * 617244 * 2
def baseEnd_617244 : Nat := 316942853103888263711353

theorem tailTrace_617244 : CollatzResearch.WordTrace tailWord_617244 prefixEnd_617244 316942853103888263711353 := by
  unfold tailWord_617244
  simp only [CollatzResearch.WordTrace]
  refine ⟨11256369087918939863821393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15008492117225253151761857 11256369087918939863821393)
  ·
    refine ⟨8442276815939204897866045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11256369087918939863821393 8442276815939204897866045)
    ·
      refine ⟨3165853805977201836699767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8442276815939204897866045 3165853805977201836699767)
      ·
        refine ⟨4748780708965802755049651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3165853805977201836699767 4748780708965802755049651)
        ·
          refine ⟨7123171063448704132574477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4748780708965802755049651 7123171063448704132574477)
          ·
            refine ⟨2671189148793264049715429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7123171063448704132574477 2671189148793264049715429)
            ·
              refine ⟨500847965398737009321643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2671189148793264049715429 500847965398737009321643)
              ·
                refine ⟨751271948098105513982465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500847965398737009321643 751271948098105513982465)
                ·
                  refine ⟨563453961073579135486849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 751271948098105513982465 563453961073579135486849)
                  ·
                    refine ⟨422590470805184351615137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 563453961073579135486849 422590470805184351615137)
                    ·
                      refine ⟨316942853103888263711353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422590470805184351615137 316942853103888263711353)
                      ·
                        rfl

theorem cell23_617244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_617244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617244 prefixEnd_617244 := by exact prefixLift 617244
  have htrace : WordTrace (prefixWord ++ tailWord_617244) baseStart_617244 baseEnd_617244 := by
    simpa [prefixWord, tailWord_617244, baseEnd_617244] using wordTrace_append hprefix tailTrace_617244
  have hstable : (prefixWord ++ tailWord_617244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617244).length < 2 ^ (prefixWord ++ tailWord_617244).sum := by decide
  have hdescent : baseEnd_617244 < baseStart_617244 := by decide
  rcases family_descends (prefixWord ++ tailWord_617244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617283 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 4]
def baseStart_617283 : Nat := 118140960795 + 617283 * 2 ^ 59
def prefixEnd_617283 : Nat := 4983230072969 + 3 ^ 40 * 617283 * 2
def baseEnd_617283 : Nat := 316962878849413611123673

theorem tailTrace_617283 : CollatzResearch.WordTrace tailWord_617283 prefixEnd_617283 316962878849413611123673 := by
  unfold tailWord_617283
  simp only [CollatzResearch.WordTrace]
  refine ⟨22514160622696589388312503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15009440415131059592208335 22514160622696589388312503)
  ·
    refine ⟨33771240934044884082468755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22514160622696589388312503 33771240934044884082468755)
    ·
      refine ⟨50656861401067326123703133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33771240934044884082468755 50656861401067326123703133)
      ·
        refine ⟨18996323025400247296388675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50656861401067326123703133 18996323025400247296388675)
        ·
          refine ⟨28494484538100370944583013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18996323025400247296388675 28494484538100370944583013)
          ·
            refine ⟨5342715850893819552109315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28494484538100370944583013 5342715850893819552109315)
            ·
              refine ⟨8014073776340729328163973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5342715850893819552109315 8014073776340729328163973)
              ·
                refine ⟨1502638833063886749030745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8014073776340729328163973 1502638833063886749030745)
                ·
                  refine ⟨1126979124797915061773059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1502638833063886749030745 1126979124797915061773059)
                  ·
                    refine ⟨1690468687196872592659589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1126979124797915061773059 1690468687196872592659589)
                    ·
                      refine ⟨316962878849413611123673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1690468687196872592659589 316962878849413611123673)
                      ·
                        rfl

theorem cell23_617283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_617283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617283 prefixEnd_617283 := by exact prefixLift 617283
  have htrace : WordTrace (prefixWord ++ tailWord_617283) baseStart_617283 baseEnd_617283 := by
    simpa [prefixWord, tailWord_617283, baseEnd_617283] using wordTrace_append hprefix tailTrace_617283
  have hstable : (prefixWord ++ tailWord_617283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617283).length < 2 ^ (prefixWord ++ tailWord_617283).sum := by decide
  have hdescent : baseEnd_617283 < baseStart_617283 := by decide
  rcases family_descends (prefixWord ++ tailWord_617283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617284 : List Nat := [2, 3, 4, 2, 1, 1, 1, 4, 5]
def baseStart_617284 : Nat := 118140960795 + 617284 * 2 ^ 59
def prefixEnd_617284 : Nat := 4983230072969 + 3 ^ 40 * 617284 * 2
def baseEnd_617284 : Nat := 35218154703340900801241

theorem tailTrace_617284 : CollatzResearch.WordTrace tailWord_617284 prefixEnd_617284 35218154703340900801241 := by
  unfold tailWord_617284
  simp only [CollatzResearch.WordTrace]
  refine ⟨11257098547846483279549453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15009464730461977706065937 11257098547846483279549453)
  ·
    refine ⟨4221411955442431229831045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11257098547846483279549453 4221411955442431229831045)
    ·
      refine ⟨791514741645455855593321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4221411955442431229831045 791514741645455855593321)
      ·
        refine ⟨593636056234091891694991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 791514741645455855593321 593636056234091891694991)
        ·
          refine ⟨890454084351137837542487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593636056234091891694991 890454084351137837542487)
          ·
            refine ⟨1335681126526706756313731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890454084351137837542487 1335681126526706756313731)
            ·
              refine ⟨2003521689790060134470597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335681126526706756313731 2003521689790060134470597)
              ·
                refine ⟨375660316835636275213237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2003521689790060134470597 375660316835636275213237)
                ·
                  refine ⟨35218154703340900801241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 375660316835636275213237 35218154703340900801241)
                  ·
                    rfl

theorem cell23_617284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_617284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617284 prefixEnd_617284 := by exact prefixLift 617284
  have htrace : WordTrace (prefixWord ++ tailWord_617284) baseStart_617284 baseEnd_617284 := by
    simpa [prefixWord, tailWord_617284, baseEnd_617284] using wordTrace_append hprefix tailTrace_617284
  have hstable : (prefixWord ++ tailWord_617284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617284).length < 2 ^ (prefixWord ++ tailWord_617284).sum := by decide
  have hdescent : baseEnd_617284 < baseStart_617284 := by decide
  rcases family_descends (prefixWord ++ tailWord_617284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617314 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_617314 : Nat := 118140960795 + 617314 * 2 ^ 59
def prefixEnd_617314 : Nat := 4983230072969 + 3 ^ 40 * 617314 * 2
def baseEnd_617314 : Nat := 105659598916567663278677

theorem tailTrace_617314 : CollatzResearch.WordTrace tailWord_617314 prefixEnd_617314 105659598916567663278677 := by
  unfold tailWord_617314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5628822821396070420672749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15010194190389521121793997 5628822821396070420672749)
  ·
    refine ⟨2110808558023526407752281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5628822821396070420672749 2110808558023526407752281)
    ·
      refine ⟨1583106418517644805814211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2110808558023526407752281 1583106418517644805814211)
      ·
        refine ⟨2374659627776467208721317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1583106418517644805814211 2374659627776467208721317)
        ·
          refine ⟨445248680208087601635247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2374659627776467208721317 445248680208087601635247)
          ·
            refine ⟨667873020312131402452871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445248680208087601635247 667873020312131402452871)
            ·
              refine ⟨1001809530468197103679307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667873020312131402452871 1001809530468197103679307)
              ·
                refine ⟨1502714295702295655518961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001809530468197103679307 1502714295702295655518961)
                ·
                  refine ⟨1127035721776721741639221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1502714295702295655518961 1127035721776721741639221)
                  ·
                    refine ⟨105659598916567663278677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1127035721776721741639221 105659598916567663278677)
                    ·
                      rfl

theorem cell23_617314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_617314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617314 prefixEnd_617314 := by exact prefixLift 617314
  have htrace : WordTrace (prefixWord ++ tailWord_617314) baseStart_617314 baseEnd_617314 := by
    simpa [prefixWord, tailWord_617314, baseEnd_617314] using wordTrace_append hprefix tailTrace_617314
  have hstable : (prefixWord ++ tailWord_617314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617314).length < 2 ^ (prefixWord ++ tailWord_617314).sum := by decide
  have hdescent : baseEnd_617314 < baseStart_617314 := by decide
  rcases family_descends (prefixWord ++ tailWord_617314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617320 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_617320 : Nat := 118140960795 + 617320 * 2 ^ 59
def prefixEnd_617320 : Nat := 4983230072969 + 3 ^ 40 * 617320 * 2
def baseEnd_617320 : Nat := 316981877633629966361003

theorem tailTrace_617320 : CollatzResearch.WordTrace tailWord_617320 prefixEnd_617320 316981877633629966361003 := by
  unfold tailWord_617320
  simp only [CollatzResearch.WordTrace]
  refine ⟨11257755061781272353704707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15010340082375029804939609 11257755061781272353704707)
  ·
    refine ⟨16886632592671908530557061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11257755061781272353704707 16886632592671908530557061)
    ·
      refine ⟨3166243611125982849479449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16886632592671908530557061 3166243611125982849479449)
      ·
        refine ⟨2374682708344487137109587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3166243611125982849479449 2374682708344487137109587)
        ·
          refine ⟨3562024062516730705664381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374682708344487137109587 3562024062516730705664381)
          ·
            refine ⟨1335759023443774014624143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3562024062516730705664381 1335759023443774014624143)
            ·
              refine ⟨2003638535165661021936215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335759023443774014624143 2003638535165661021936215)
              ·
                refine ⟨3005457802748491532904323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003638535165661021936215 3005457802748491532904323)
                ·
                  refine ⟨4508186704122737299356485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3005457802748491532904323 4508186704122737299356485)
                  ·
                    refine ⟨845285007023013243629341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4508186704122737299356485 845285007023013243629341)
                    ·
                      refine ⟨316981877633629966361003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 845285007023013243629341 316981877633629966361003)
                      ·
                        rfl

theorem cell23_617320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_617320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617320 prefixEnd_617320 := by exact prefixLift 617320
  have htrace : WordTrace (prefixWord ++ tailWord_617320) baseStart_617320 baseEnd_617320 := by
    simpa [prefixWord, tailWord_617320, baseEnd_617320] using wordTrace_append hprefix tailTrace_617320
  have hstable : (prefixWord ++ tailWord_617320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617320).length < 2 ^ (prefixWord ++ tailWord_617320).sum := by decide
  have hdescent : baseEnd_617320 < baseStart_617320 := by decide
  rcases family_descends (prefixWord ++ tailWord_617320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617377 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 1, 5, 2]
def baseStart_617377 : Nat := 118140960795 + 617377 * 2 ^ 59
def prefixEnd_617377 : Nat := 4983230072969 + 3 ^ 40 * 617377 * 2
def baseEnd_617377 : Nat := 317011146030936243348241

theorem tailTrace_617377 : CollatzResearch.WordTrace tailWord_617377 prefixEnd_617377 317011146030936243348241 := by
  unfold tailWord_617377
  simp only [CollatzResearch.WordTrace]
  refine ⟨22517589084356043442234385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15011726056237362294822923 22517589084356043442234385)
  ·
    refine ⟨16888191813267032581675789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22517589084356043442234385 16888191813267032581675789)
    ·
      refine ⟨6333071929975137218128421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16888191813267032581675789 6333071929975137218128421)
      ·
        refine ⟨1187450986870338228399079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6333071929975137218128421 1187450986870338228399079)
        ·
          refine ⟨1781176480305507342598619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187450986870338228399079 1781176480305507342598619)
          ·
            refine ⟨2671764720458261013897929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781176480305507342598619 2671764720458261013897929)
            ·
              refine ⟨2003823540343695760423447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2671764720458261013897929 2003823540343695760423447)
              ·
                refine ⟨3005735310515543640635171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003823540343695760423447 3005735310515543640635171)
                ·
                  refine ⟨4508602965773315460952757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3005735310515543640635171 4508602965773315460952757)
                  ·
                    refine ⟨422681528041248324464321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4508602965773315460952757 422681528041248324464321)
                    ·
                      refine ⟨317011146030936243348241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422681528041248324464321 317011146030936243348241)
                      ·
                        rfl

theorem cell23_617377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_617377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617377 prefixEnd_617377 := by exact prefixLift 617377
  have htrace : WordTrace (prefixWord ++ tailWord_617377) baseStart_617377 baseEnd_617377 := by
    simpa [prefixWord, tailWord_617377, baseEnd_617377] using wordTrace_append hprefix tailTrace_617377
  have hstable : (prefixWord ++ tailWord_617377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617377).length < 2 ^ (prefixWord ++ tailWord_617377).sum := by decide
  have hdescent : baseEnd_617377 < baseStart_617377 := by decide
  rcases family_descends (prefixWord ++ tailWord_617377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617400 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 4, 4]
def baseStart_617400 : Nat := 118140960795 + 617400 * 2 ^ 59
def prefixEnd_617400 : Nat := 4983230072969 + 3 ^ 40 * 617400 * 2
def baseEnd_617400 : Nat := 105674318695329884453545

theorem tailTrace_617400 : CollatzResearch.WordTrace tailWord_617400 prefixEnd_617400 105674318695329884453545 := by
  unfold tailWord_617400
  simp only [CollatzResearch.WordTrace]
  refine ⟨11259213981636359185160827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15012285308848478913547769 11259213981636359185160827)
  ·
    refine ⟨16888820972454538777741241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11259213981636359185160827 16888820972454538777741241)
    ·
      refine ⟨12666615729340904083305931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16888820972454538777741241 12666615729340904083305931)
      ·
        refine ⟨18999923594011356124958897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12666615729340904083305931 18999923594011356124958897)
        ·
          refine ⟨14249942695508517093719173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18999923594011356124958897 14249942695508517093719173)
          ·
            refine ⟨2671864255407846955072345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14249942695508517093719173 2671864255407846955072345)
            ·
              refine ⟨2003898191555885216304259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2671864255407846955072345 2003898191555885216304259)
              ·
                refine ⟨3005847287333827824456389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003898191555885216304259 3005847287333827824456389)
                ·
                  refine ⟨563596366375092717085573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3005847287333827824456389 563596366375092717085573)
                  ·
                    refine ⟨105674318695329884453545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 563596366375092717085573 105674318695329884453545)
                    ·
                      rfl

theorem cell23_617400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_617400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617400 prefixEnd_617400 := by exact prefixLift 617400
  have htrace : WordTrace (prefixWord ++ tailWord_617400) baseStart_617400 baseEnd_617400 := by
    simpa [prefixWord, tailWord_617400, baseEnd_617400] using wordTrace_append hprefix tailTrace_617400
  have hstable : (prefixWord ++ tailWord_617400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617400).length < 2 ^ (prefixWord ++ tailWord_617400).sum := by decide
  have hdescent : baseEnd_617400 < baseStart_617400 := by decide
  rcases family_descends (prefixWord ++ tailWord_617400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617401 : List Nat := [1, 2, 1, 4, 2, 3, 3, 2, 1, 1, 3]
def baseStart_617401 : Nat := 118140960795 + 617401 * 2 ^ 59
def prefixEnd_617401 : Nat := 4983230072969 + 3 ^ 40 * 617401 * 2
def baseEnd_617401 : Nat := 317023469566644149448131

theorem tailTrace_617401 : CollatzResearch.WordTrace tailWord_617401 prefixEnd_617401 317023469566644149448131 := by
  unfold tailWord_617401
  simp only [CollatzResearch.WordTrace]
  refine ⟨22518464436269095541108057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15012309624179397027405371 22518464436269095541108057)
  ·
    refine ⟨16888848327201821655831043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22518464436269095541108057 16888848327201821655831043)
    ·
      refine ⟨25333272490802732483746565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16888848327201821655831043 25333272490802732483746565)
      ·
        refine ⟨4749988592025512340702481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25333272490802732483746565 4749988592025512340702481)
        ·
          refine ⟨3562491444019134255526861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4749988592025512340702481 3562491444019134255526861)
          ·
            refine ⟨1335934291507175345822573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3562491444019134255526861 1335934291507175345822573)
            ·
              refine ⟨500975359315190754683465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1335934291507175345822573 500975359315190754683465)
              ·
                refine ⟨375731519486393066012599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500975359315190754683465 375731519486393066012599)
                ·
                  refine ⟨563597279229589599018899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375731519486393066012599 563597279229589599018899)
                  ·
                    refine ⟨845395918844384398528349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 563597279229589599018899 845395918844384398528349)
                    ·
                      refine ⟨317023469566644149448131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 845395918844384398528349 317023469566644149448131)
                      ·
                        rfl

theorem cell23_617401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_617401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617401 prefixEnd_617401 := by exact prefixLift 617401
  have htrace : WordTrace (prefixWord ++ tailWord_617401) baseStart_617401 baseEnd_617401 := by
    simpa [prefixWord, tailWord_617401, baseEnd_617401] using wordTrace_append hprefix tailTrace_617401
  have hstable : (prefixWord ++ tailWord_617401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617401).length < 2 ^ (prefixWord ++ tailWord_617401).sum := by decide
  have hdescent : baseEnd_617401 < baseStart_617401 := by decide
  rcases family_descends (prefixWord ++ tailWord_617401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617407 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 3, 2, 2]
def baseStart_617407 : Nat := 118140960795 + 617407 * 2 ^ 59
def prefixEnd_617407 : Nat := 4983230072969 + 3 ^ 40 * 617407 * 2
def baseEnd_617407 : Nat := 317026550450571125973103

theorem tailTrace_617407 : CollatzResearch.WordTrace tailWord_617407 prefixEnd_617407 317026550450571125973103 := by
  unfold tailWord_617407
  simp only [CollatzResearch.WordTrace]
  refine ⟨22518683274247358565826475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15012455516164905710550983 22518683274247358565826475)
  ·
    refine ⟨33778024911371037848739713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22518683274247358565826475 33778024911371037848739713)
    ·
      refine ⟨25333518683528278386554785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33778024911371037848739713 25333518683528278386554785)
      ·
        refine ⟨19000139012646208789916089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25333518683528278386554785 19000139012646208789916089)
        ·
          refine ⟨14250104259484656592437067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19000139012646208789916089 14250104259484656592437067)
          ·
            refine ⟨21375156389226984888655601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14250104259484656592437067 21375156389226984888655601)
            ·
              refine ⟨16031367291920238666491701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21375156389226984888655601 16031367291920238666491701)
              ·
                refine ⟨1502940683617522374983597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16031367291920238666491701 1502940683617522374983597)
                ·
                  refine ⟨563602756356570890618849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1502940683617522374983597 563602756356570890618849)
                  ·
                    refine ⟨422702067267428167964137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 563602756356570890618849 422702067267428167964137)
                    ·
                      refine ⟨317026550450571125973103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422702067267428167964137 317026550450571125973103)
                      ·
                        rfl

theorem cell23_617407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 2, 2].length) (baseStart_617407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617407 prefixEnd_617407 := by exact prefixLift 617407
  have htrace : WordTrace (prefixWord ++ tailWord_617407) baseStart_617407 baseEnd_617407 := by
    simpa [prefixWord, tailWord_617407, baseEnd_617407] using wordTrace_append hprefix tailTrace_617407
  have hstable : (prefixWord ++ tailWord_617407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617407).length < 2 ^ (prefixWord ++ tailWord_617407).sum := by decide
  have hdescent : baseEnd_617407 < baseStart_617407 := by decide
  rcases family_descends (prefixWord ++ tailWord_617407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617420 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 1, 2, 4]
def baseStart_617420 : Nat := 118140960795 + 617420 * 2 ^ 59
def prefixEnd_617420 : Nat := 4983230072969 + 3 ^ 40 * 617420 * 2
def baseEnd_617420 : Nat := 317033225699079575110543

theorem tailTrace_617420 : CollatzResearch.WordTrace tailWord_617420 prefixEnd_617420 317033225699079575110543 := by
  unfold tailWord_617420
  simp only [CollatzResearch.WordTrace]
  refine ⟨11259578711600130893024857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15012771615466841190699809 11259578711600130893024857)
  ·
    refine ⟨8444684033700098169768643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11259578711600130893024857 8444684033700098169768643)
    ·
      refine ⟨12667026050550147254652965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8444684033700098169768643 12667026050550147254652965)
      ·
        refine ⟨2375067384478152610247431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12667026050550147254652965 2375067384478152610247431)
        ·
          refine ⟨3562601076717228915371147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2375067384478152610247431 3562601076717228915371147)
          ·
            refine ⟨5343901615075843373056721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562601076717228915371147 5343901615075843373056721)
            ·
              refine ⟨4007926211306882529792541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5343901615075843373056721 4007926211306882529792541)
              ·
                refine ⟨1502972329240080948672203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4007926211306882529792541 1502972329240080948672203)
                ·
                  refine ⟨2254458493860121423008305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502972329240080948672203 2254458493860121423008305)
                  ·
                    refine ⟨1690843870395091067256229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2254458493860121423008305 1690843870395091067256229)
                    ·
                      refine ⟨317033225699079575110543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1690843870395091067256229 317033225699079575110543)
                      ·
                        rfl

theorem cell23_617420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_617420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617420 prefixEnd_617420 := by exact prefixLift 617420
  have htrace : WordTrace (prefixWord ++ tailWord_617420) baseStart_617420 baseEnd_617420 := by
    simpa [prefixWord, tailWord_617420, baseEnd_617420] using wordTrace_append hprefix tailTrace_617420
  have hstable : (prefixWord ++ tailWord_617420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617420).length < 2 ^ (prefixWord ++ tailWord_617420).sum := by decide
  have hdescent : baseEnd_617420 < baseStart_617420 := by decide
  rcases family_descends (prefixWord ++ tailWord_617420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617421 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_617421 : Nat := 118140960795 + 617421 * 2 ^ 59
def prefixEnd_617421 : Nat := 4983230072969 + 3 ^ 40 * 617421 * 2
def baseEnd_617421 : Nat := 105677913059911357066013

theorem tailTrace_617421 : CollatzResearch.WordTrace tailWord_617421 prefixEnd_617421 105677913059911357066013 := by
  unfold tailWord_617421
  simp only [CollatzResearch.WordTrace]
  refine ⟨22519193896196638956836117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15012795930797759304557411 22519193896196638956836117)
  ·
    refine ⟨1055587213884217451101693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22519193896196638956836117 1055587213884217451101693)
    ·
      refine ⟨395845205206581544163135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1055587213884217451101693 395845205206581544163135)
      ·
        refine ⟨593767807809872316244703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395845205206581544163135 593767807809872316244703)
        ·
          refine ⟨890651711714808474367055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593767807809872316244703 890651711714808474367055)
          ·
            refine ⟨1335977567572212711550583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890651711714808474367055 1335977567572212711550583)
            ·
              refine ⟨2003966351358319067325875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335977567572212711550583 2003966351358319067325875)
              ·
                refine ⟨3005949527037478600988813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003966351358319067325875 3005949527037478600988813)
                ·
                  refine ⟨1127231072639054475370805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3005949527037478600988813 1127231072639054475370805)
                  ·
                    refine ⟨105677913059911357066013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1127231072639054475370805 105677913059911357066013)
                    ·
                      rfl

theorem cell23_617421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_617421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617421 prefixEnd_617421 := by exact prefixLift 617421
  have htrace : WordTrace (prefixWord ++ tailWord_617421) baseStart_617421 baseEnd_617421 := by
    simpa [prefixWord, tailWord_617421, baseEnd_617421] using wordTrace_append hprefix tailTrace_617421
  have hstable : (prefixWord ++ tailWord_617421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617421).length < 2 ^ (prefixWord ++ tailWord_617421).sum := by decide
  have hdescent : baseEnd_617421 < baseStart_617421 := by decide
  rcases family_descends (prefixWord ++ tailWord_617421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617437 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_617437 : Nat := 118140960795 + 617437 * 2 ^ 59
def prefixEnd_617437 : Nat := 4983230072969 + 3 ^ 40 * 617437 * 2
def baseEnd_617437 : Nat := 317041954870206008597965

theorem tailTrace_617437 : CollatzResearch.WordTrace tailWord_617437 prefixEnd_617437 317041954870206008597965 := by
  unfold tailWord_617437
  simp only [CollatzResearch.WordTrace]
  refine ⟨22519777464138673689418565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15013184976092449126279043 22519777464138673689418565)
  ·
    refine ⟨4222458274526001316765981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22519777464138673689418565 4222458274526001316765981)
    ·
      refine ⟨1583421852947250493787243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4222458274526001316765981 1583421852947250493787243)
      ·
        refine ⟨2375132779420875740680865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1583421852947250493787243 2375132779420875740680865)
        ·
          refine ⟨1781349584565656805510649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2375132779420875740680865 1781349584565656805510649)
          ·
            refine ⟨1336012188424242604132987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1781349584565656805510649 1336012188424242604132987)
            ·
              refine ⟨2004018282636363906199481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1336012188424242604132987 2004018282636363906199481)
              ·
                refine ⟨1503013711977272929649611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2004018282636363906199481 1503013711977272929649611)
                ·
                  refine ⟨2254520567965909394474417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1503013711977272929649611 2254520567965909394474417)
                  ·
                    refine ⟨1690890425974432045855813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2254520567965909394474417 1690890425974432045855813)
                    ·
                      refine ⟨317041954870206008597965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1690890425974432045855813 317041954870206008597965)
                      ·
                        rfl

theorem cell23_617437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_617437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617437 prefixEnd_617437 := by exact prefixLift 617437
  have htrace : WordTrace (prefixWord ++ tailWord_617437) baseStart_617437 baseEnd_617437 := by
    simpa [prefixWord, tailWord_617437, baseEnd_617437] using wordTrace_append hprefix tailTrace_617437
  have hstable : (prefixWord ++ tailWord_617437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617437).length < 2 ^ (prefixWord ++ tailWord_617437).sum := by decide
  have hdescent : baseEnd_617437 < baseStart_617437 := by decide
  rcases family_descends (prefixWord ++ tailWord_617437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617497 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 1, 4, 2]
def baseStart_617497 : Nat := 118140960795 + 617497 * 2 ^ 59
def prefixEnd_617497 : Nat := 4983230072969 + 3 ^ 40 * 617497 * 2
def baseEnd_617497 : Nat := 317072763709475773847689

theorem tailTrace_617497 : CollatzResearch.WordTrace tailWord_617497 prefixEnd_617497 317072763709475773847689 := by
  unfold tailWord_617497
  simp only [CollatzResearch.WordTrace]
  refine ⟨22521965843921303936602745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15014643895947535957735163 22521965843921303936602745)
  ·
    refine ⟨16891474382940977952452059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22521965843921303936602745 16891474382940977952452059)
    ·
      refine ⟨25337211574411466928678089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16891474382940977952452059 25337211574411466928678089)
      ·
        refine ⟨19002908680808600196508567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25337211574411466928678089 19002908680808600196508567)
        ·
          refine ⟨28504363021212900294762851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19002908680808600196508567 28504363021212900294762851)
          ·
            refine ⟨42756544531819350442144277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28504363021212900294762851 42756544531819350442144277)
            ·
              refine ⟨2004213024929032051975513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42756544531819350442144277 2004213024929032051975513)
              ·
                refine ⟨1503159768696774038981635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2004213024929032051975513 1503159768696774038981635)
                ·
                  refine ⟨2254739653045161058472453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1503159768696774038981635 2254739653045161058472453)
                  ·
                    refine ⟨422763684945967698463585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2254739653045161058472453 422763684945967698463585)
                    ·
                      refine ⟨317072763709475773847689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422763684945967698463585 317072763709475773847689)
                      ·
                        rfl

theorem cell23_617497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 4, 2].length) (baseStart_617497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617497 prefixEnd_617497 := by exact prefixLift 617497
  have htrace : WordTrace (prefixWord ++ tailWord_617497) baseStart_617497 baseEnd_617497 := by
    simpa [prefixWord, tailWord_617497, baseEnd_617497] using wordTrace_append hprefix tailTrace_617497
  have hstable : (prefixWord ++ tailWord_617497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617497).length < 2 ^ (prefixWord ++ tailWord_617497).sum := by decide
  have hdescent : baseEnd_617497 < baseStart_617497 := by decide
  rcases family_descends (prefixWord ++ tailWord_617497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617501 : List Nat := [1, 4, 2, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_617501 : Nat := 118140960795 + 617501 * 2 ^ 59
def prefixEnd_617501 : Nat := 4983230072969 + 3 ^ 40 * 617501 * 2
def baseEnd_617501 : Nat := 317074817632093758197671

theorem tailTrace_617501 : CollatzResearch.WordTrace tailWord_617501 prefixEnd_617501 317074817632093758197671 := by
  unfold tailWord_617501
  simp only [CollatzResearch.WordTrace]
  refine ⟨22522111735906812619748357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15014741157271208413165571 22522111735906812619748357)
  ·
    refine ⟨4222895950482527366202817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22522111735906812619748357 4222895950482527366202817)
    ·
      refine ⟨3167171962861895524652113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4222895950482527366202817 3167171962861895524652113)
      ·
        refine ⟨2375378972146421643489085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3167171962861895524652113 2375378972146421643489085)
        ·
          refine ⟨890767114554908116308407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2375378972146421643489085 890767114554908116308407)
          ·
            refine ⟨1336150671832362174462611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890767114554908116308407 1336150671832362174462611)
            ·
              refine ⟨2004226007748543261693917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1336150671832362174462611 2004226007748543261693917)
              ·
                refine ⟨751584752905703723135219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2004226007748543261693917 751584752905703723135219)
                ·
                  refine ⟨1127377129358555584702829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751584752905703723135219 1127377129358555584702829)
                  ·
                    refine ⟨422766423509458344263561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1127377129358555584702829 422766423509458344263561)
                    ·
                      refine ⟨317074817632093758197671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422766423509458344263561 317074817632093758197671)
                      ·
                        rfl

theorem cell23_617501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_617501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617501 prefixEnd_617501 := by exact prefixLift 617501
  have htrace : WordTrace (prefixWord ++ tailWord_617501) baseStart_617501 baseEnd_617501 := by
    simpa [prefixWord, tailWord_617501, baseEnd_617501] using wordTrace_append hprefix tailTrace_617501
  have hstable : (prefixWord ++ tailWord_617501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617501).length < 2 ^ (prefixWord ++ tailWord_617501).sum := by decide
  have hdescent : baseEnd_617501 < baseStart_617501 := by decide
  rcases family_descends (prefixWord ++ tailWord_617501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617520 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 7]
def baseStart_617520 : Nat := 118140960795 + 617520 * 2 ^ 59
def prefixEnd_617520 : Nat := 4983230072969 + 3 ^ 40 * 617520 * 2
def baseEnd_617520 : Nat := 35231619307169909317787

theorem tailTrace_617520 : CollatzResearch.WordTrace tailWord_617520 prefixEnd_617520 35231619307169909317787 := by
  unfold tailWord_617520
  simp only [CollatzResearch.WordTrace]
  refine ⟨11261402361418989432345007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15015203148558652576460009 11261402361418989432345007)
  ·
    refine ⟨16892103542128484148517511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11261402361418989432345007 16892103542128484148517511)
    ·
      refine ⟨25338155313192726222776267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16892103542128484148517511 25338155313192726222776267)
      ·
        refine ⟨38007232969789089334164401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25338155313192726222776267 38007232969789089334164401)
        ·
          refine ⟨28505424727341817000623301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38007232969789089334164401 28505424727341817000623301)
          ·
            refine ⟨5344767136376590687616869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28505424727341817000623301 5344767136376590687616869)
            ·
              refine ⟨1002143838070610753928163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5344767136376590687616869 1002143838070610753928163)
              ·
                refine ⟨1503215757105916130892245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002143838070610753928163 1503215757105916130892245)
                ·
                  refine ⟨35231619307169909317787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1503215757105916130892245 35231619307169909317787)
                  ·
                    rfl

theorem cell23_617520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 7].length) (baseStart_617520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617520 prefixEnd_617520 := by exact prefixLift 617520
  have htrace : WordTrace (prefixWord ++ tailWord_617520) baseStart_617520 baseEnd_617520 := by
    simpa [prefixWord, tailWord_617520, baseEnd_617520] using wordTrace_append hprefix tailTrace_617520
  have hstable : (prefixWord ++ tailWord_617520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617520).length < 2 ^ (prefixWord ++ tailWord_617520).sum := by decide
  have hdescent : baseEnd_617520 < baseStart_617520 := by decide
  rcases family_descends (prefixWord ++ tailWord_617520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617550 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_617550 : Nat := 118140960795 + 617550 * 2 ^ 59
def prefixEnd_617550 : Nat := 4983230072969 + 3 ^ 40 * 617550 * 2
def baseEnd_617550 : Nat := 105699992728054688828315

theorem tailTrace_617550 : CollatzResearch.WordTrace tailWord_617550 prefixEnd_617550 105699992728054688828315 := by
  unfold tailWord_617550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2815487364091161748535263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15015932608486195992188069 2815487364091161748535263)
  ·
    refine ⟨4223231046136742622802895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2815487364091161748535263 4223231046136742622802895)
    ·
      refine ⟨6334846569205113934204343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4223231046136742622802895 6334846569205113934204343)
      ·
        refine ⟨9502269853807670901306515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6334846569205113934204343 9502269853807670901306515)
        ·
          refine ⟨14253404780711506351959773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9502269853807670901306515 14253404780711506351959773)
          ·
            refine ⟨5345026792766814881984915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14253404780711506351959773 5345026792766814881984915)
            ·
              refine ⟨8017540189150222322977373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5345026792766814881984915 8017540189150222322977373)
              ·
                refine ⟨3006577570931333371116515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8017540189150222322977373 3006577570931333371116515)
                ·
                  refine ⟨4509866356397000056674773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3006577570931333371116515 4509866356397000056674773)
                  ·
                    refine ⟨105699992728054688828315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4509866356397000056674773 105699992728054688828315)
                    ·
                      rfl

theorem cell23_617550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_617550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617550 prefixEnd_617550 := by exact prefixLift 617550
  have htrace : WordTrace (prefixWord ++ tailWord_617550) baseStart_617550 baseEnd_617550 := by
    simpa [prefixWord, tailWord_617550, baseEnd_617550] using wordTrace_append hprefix tailTrace_617550
  have hstable : (prefixWord ++ tailWord_617550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617550).length < 2 ^ (prefixWord ++ tailWord_617550).sum := by decide
  have hdescent : baseEnd_617550 < baseStart_617550 := by decide
  rcases family_descends (prefixWord ++ tailWord_617550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617554 : List Nat := [3, 2, 2, 1, 3, 1, 3, 3, 5]
def baseStart_617554 : Nat := 118140960795 + 617554 * 2 ^ 59
def prefixEnd_617554 : Nat := 4983230072969 + 3 ^ 40 * 617554 * 2
def baseEnd_617554 : Nat := 35233559122975783426103

theorem tailTrace_617554 : CollatzResearch.WordTrace tailWord_617554 prefixEnd_617554 35233559122975783426103 := by
  unfold tailWord_617554
  simp only [CollatzResearch.WordTrace]
  refine ⟨5631011201178700667856929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15016029869809868447618477 5631011201178700667856929)
  ·
    refine ⟨4223258400884025500892697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5631011201178700667856929 4223258400884025500892697)
    ·
      refine ⟨3167443800663019125669523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4223258400884025500892697 3167443800663019125669523)
      ·
        refine ⟨4751165700994528688504285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3167443800663019125669523 4751165700994528688504285)
        ·
          refine ⟨1781687137872948258189107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4751165700994528688504285 1781687137872948258189107)
          ·
            refine ⟨2672530706809422387283661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781687137872948258189107 2672530706809422387283661)
            ·
              refine ⟨1002199015053533395231373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2672530706809422387283661 1002199015053533395231373)
              ·
                refine ⟨375824630645075023211765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1002199015053533395231373 375824630645075023211765)
                ·
                  refine ⟨35233559122975783426103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 375824630645075023211765 35233559122975783426103)
                  ·
                    rfl

theorem cell23_617554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_617554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617554 prefixEnd_617554 := by exact prefixLift 617554
  have htrace : WordTrace (prefixWord ++ tailWord_617554) baseStart_617554 baseEnd_617554 := by
    simpa [prefixWord, tailWord_617554, baseEnd_617554] using wordTrace_append hprefix tailTrace_617554
  have hstable : (prefixWord ++ tailWord_617554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617554).length < 2 ^ (prefixWord ++ tailWord_617554).sum := by decide
  have hdescent : baseEnd_617554 < baseStart_617554 := by decide
  rcases family_descends (prefixWord ++ tailWord_617554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617560 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_617560 : Nat := 118140960795 + 617560 * 2 ^ 59
def prefixEnd_617560 : Nat := 4983230072969 + 3 ^ 40 * 617560 * 2
def baseEnd_617560 : Nat := 317105112990709027359899

theorem tailTrace_617560 : CollatzResearch.WordTrace tailWord_617560 prefixEnd_617560 317105112990709027359899 := by
  unfold tailWord_617560
  simp only [CollatzResearch.WordTrace]
  refine ⟨11262131821346532848073067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15016175761795377130764089 11262131821346532848073067)
  ·
    refine ⟨16893197732019799272109601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11262131821346532848073067 16893197732019799272109601)
    ·
      refine ⟨12669898299014849454082201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16893197732019799272109601 12669898299014849454082201)
      ·
        refine ⟨9502423724261137090561651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12669898299014849454082201 9502423724261137090561651)
        ·
          refine ⟨14253635586391705635842477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9502423724261137090561651 14253635586391705635842477)
          ·
            refine ⟨5345113344896889613440929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14253635586391705635842477 5345113344896889613440929)
            ·
              refine ⟨4008835008672667210080697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5345113344896889613440929 4008835008672667210080697)
              ·
                refine ⟨3006626256504500407560523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4008835008672667210080697 3006626256504500407560523)
                ·
                  refine ⟨4509939384756750611340785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3006626256504500407560523 4509939384756750611340785)
                  ·
                    refine ⟨3382454538567562958505589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4509939384756750611340785 3382454538567562958505589)
                    ·
                      refine ⟨317105112990709027359899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3382454538567562958505589 317105112990709027359899)
                      ·
                        rfl

theorem cell23_617560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_617560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617560 prefixEnd_617560 := by exact prefixLift 617560
  have htrace : WordTrace (prefixWord ++ tailWord_617560) baseStart_617560 baseEnd_617560 := by
    simpa [prefixWord, tailWord_617560, baseEnd_617560] using wordTrace_append hprefix tailTrace_617560
  have hstable : (prefixWord ++ tailWord_617560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617560).length < 2 ^ (prefixWord ++ tailWord_617560).sum := by decide
  have hdescent : baseEnd_617560 < baseStart_617560 := by decide
  rcases family_descends (prefixWord ++ tailWord_617560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617597 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_617597 : Nat := 118140960795 + 617597 * 2 ^ 59
def prefixEnd_617597 : Nat := 4983230072969 + 3 ^ 40 * 617597 * 2
def baseEnd_617597 : Nat := 105708037258308460865743

theorem tailTrace_617597 : CollatzResearch.WordTrace tailWord_617597 prefixEnd_617597 105708037258308460865743 := by
  unfold tailWord_617597
  simp only [CollatzResearch.WordTrace]
  refine ⟨22525613143559021015243045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15017075429039347343495363 22525613143559021015243045)
  ·
    refine ⟨4223552464417316440358071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22525613143559021015243045 4223552464417316440358071)
    ·
      refine ⟨6335328696625974660537107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4223552464417316440358071 6335328696625974660537107)
      ·
        refine ⟨9502993044938961990805661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6335328696625974660537107 9502993044938961990805661)
        ·
          refine ⟨3563622391852110746552123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9502993044938961990805661 3563622391852110746552123)
          ·
            refine ⟨5345433587778166119828185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3563622391852110746552123 5345433587778166119828185)
            ·
              refine ⟨4009075190833624589871139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5345433587778166119828185 4009075190833624589871139)
              ·
                refine ⟨6013612786250436884806709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4009075190833624589871139 6013612786250436884806709)
                ·
                  refine ⟨563776198710978457950629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6013612786250436884806709 563776198710978457950629)
                  ·
                    refine ⟨105708037258308460865743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 563776198710978457950629 105708037258308460865743)
                    ·
                      rfl

theorem cell23_617597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_617597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617597 prefixEnd_617597 := by exact prefixLift 617597
  have htrace : WordTrace (prefixWord ++ tailWord_617597) baseStart_617597 baseEnd_617597 := by
    simpa [prefixWord, tailWord_617597, baseEnd_617597] using wordTrace_append hprefix tailTrace_617597
  have hstable : (prefixWord ++ tailWord_617597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617597).length < 2 ^ (prefixWord ++ tailWord_617597).sum := by decide
  have hdescent : baseEnd_617597 < baseStart_617597 := by decide
  rcases family_descends (prefixWord ++ tailWord_617597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617600 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 4]
def baseStart_617600 : Nat := 118140960795 + 617600 * 2 ^ 59
def prefixEnd_617600 : Nat := 4983230072969 + 3 ^ 40 * 617600 * 2
def baseEnd_617600 : Nat := 317125652216888870859715

theorem tailTrace_617600 : CollatzResearch.WordTrace tailWord_617600 prefixEnd_617600 317125652216888870859715 := by
  unfold tailWord_617600
  simp only [CollatzResearch.WordTrace]
  refine ⟨11262861281274076263801127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15017148375032101685068169 11262861281274076263801127)
  ·
    refine ⟨16894291921911114395701691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11262861281274076263801127 16894291921911114395701691)
    ·
      refine ⟨25341437882866671593552537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16894291921911114395701691 25341437882866671593552537)
      ·
        refine ⟨19006078412150003695164403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25341437882866671593552537 19006078412150003695164403)
        ·
          refine ⟨28509117618225005542746605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19006078412150003695164403 28509117618225005542746605)
          ·
            refine ⟨10690919106834377078529977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28509117618225005542746605 10690919106834377078529977)
            ·
              refine ⟨8018189330125782808897483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10690919106834377078529977 8018189330125782808897483)
              ·
                refine ⟨12027283995188674213346225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8018189330125782808897483 12027283995188674213346225)
                ·
                  refine ⟨9020462996391505660009669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12027283995188674213346225 9020462996391505660009669)
                  ·
                    refine ⟨1691336811823407311251813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9020462996391505660009669 1691336811823407311251813)
                    ·
                      refine ⟨317125652216888870859715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1691336811823407311251813 317125652216888870859715)
                      ·
                        rfl

theorem cell23_617600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_617600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617600 prefixEnd_617600 := by exact prefixLift 617600
  have htrace : WordTrace (prefixWord ++ tailWord_617600) baseStart_617600 baseEnd_617600 := by
    simpa [prefixWord, tailWord_617600, baseEnd_617600] using wordTrace_append hprefix tailTrace_617600
  have hstable : (prefixWord ++ tailWord_617600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617600).length < 2 ^ (prefixWord ++ tailWord_617600).sum := by decide
  have hdescent : baseEnd_617600 < baseStart_617600 := by decide
  rcases family_descends (prefixWord ++ tailWord_617600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617604 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_617604 : Nat := 118140960795 + 617604 * 2 ^ 59
def prefixEnd_617604 : Nat := 4983230072969 + 3 ^ 40 * 617604 * 2
def baseEnd_617604 : Nat := 317127706139506855209697

theorem tailTrace_617604 : CollatzResearch.WordTrace tailWord_617604 prefixEnd_617604 317127706139506855209697 := by
  unfold tailWord_617604
  simp only [CollatzResearch.WordTrace]
  refine ⟨11262934227266830605373933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15017245636355774140498577 11262934227266830605373933)
  ·
    refine ⟨4223600335225061477015225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11262934227266830605373933 4223600335225061477015225)
    ·
      refine ⟨3167700251418796107761419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4223600335225061477015225 3167700251418796107761419)
      ·
        refine ⟨4751550377128194161642129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3167700251418796107761419 4751550377128194161642129)
        ·
          refine ⟨3563662782846145621231597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4751550377128194161642129 3563662782846145621231597)
          ·
            refine ⟨1336373543567304607961849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3563662782846145621231597 1336373543567304607961849)
            ·
              refine ⟨1002280157675478455971387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1336373543567304607961849 1002280157675478455971387)
              ·
                refine ⟨1503420236513217683957081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002280157675478455971387 1503420236513217683957081)
                ·
                  refine ⟨1127565177384913262967811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1503420236513217683957081 1127565177384913262967811)
                  ·
                    refine ⟨1691347766077369894451717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1127565177384913262967811 1691347766077369894451717)
                    ·
                      refine ⟨317127706139506855209697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1691347766077369894451717 317127706139506855209697)
                      ·
                        rfl

theorem cell23_617604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_617604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617604 prefixEnd_617604 := by exact prefixLift 617604
  have htrace : WordTrace (prefixWord ++ tailWord_617604) baseStart_617604 baseEnd_617604 := by
    simpa [prefixWord, tailWord_617604, baseEnd_617604] using wordTrace_append hprefix tailTrace_617604
  have hstable : (prefixWord ++ tailWord_617604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617604).length < 2 ^ (prefixWord ++ tailWord_617604).sum := by decide
  have hdescent : baseEnd_617604 < baseStart_617604 := by decide
  rcases family_descends (prefixWord ++ tailWord_617604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617624 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 2, 2, 3]
def baseStart_617624 : Nat := 118140960795 + 617624 * 2 ^ 59
def prefixEnd_617624 : Nat := 4983230072969 + 3 ^ 40 * 617624 * 2
def baseEnd_617624 : Nat := 317137975752596776959605

theorem tailTrace_617624 : CollatzResearch.WordTrace tailWord_617624 prefixEnd_617624 317137975752596776959605 := by
  unfold tailWord_617624
  simp only [CollatzResearch.WordTrace]
  refine ⟨11263298957230602313237963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15017731942974136417650617 11263298957230602313237963)
  ·
    refine ⟨16894948435845903469856945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11263298957230602313237963 16894948435845903469856945)
    ·
      refine ⟨12671211326884427602392709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16894948435845903469856945 12671211326884427602392709)
      ·
        refine ⟨2375852123790830175448633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12671211326884427602392709 2375852123790830175448633)
        ·
          refine ⟨1781889092843122631586475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2375852123790830175448633 1781889092843122631586475)
          ·
            refine ⟨2672833639264683947379713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781889092843122631586475 2672833639264683947379713)
            ·
              refine ⟨2004625229448512960534785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672833639264683947379713 2004625229448512960534785)
              ·
                refine ⟨1503468922086384720401089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2004625229448512960534785 1503468922086384720401089)
                ·
                  refine ⟨1127601691564788540300817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1503468922086384720401089 1127601691564788540300817)
                  ·
                    refine ⟨845701268673591405225613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1127601691564788540300817 845701268673591405225613)
                    ·
                      refine ⟨317137975752596776959605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 845701268673591405225613 317137975752596776959605)
                      ·
                        rfl

theorem cell23_617624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_617624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617624 prefixEnd_617624 := by exact prefixLift 617624
  have htrace : WordTrace (prefixWord ++ tailWord_617624) baseStart_617624 baseEnd_617624 := by
    simpa [prefixWord, tailWord_617624, baseEnd_617624] using wordTrace_append hprefix tailTrace_617624
  have hstable : (prefixWord ++ tailWord_617624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617624).length < 2 ^ (prefixWord ++ tailWord_617624).sum := by decide
  have hdescent : baseEnd_617624 < baseStart_617624 := by decide
  rcases family_descends (prefixWord ++ tailWord_617624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617657 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 3, 5]
def baseStart_617657 : Nat := 118140960795 + 617657 * 2 ^ 59
def prefixEnd_617657 : Nat := 4983230072969 + 3 ^ 40 * 617657 * 2
def baseEnd_617657 : Nat := 105718306871398382615651

theorem tailTrace_617657 : CollatzResearch.WordTrace tailWord_617657 prefixEnd_617657 105718306871398382615651 := by
  unfold tailWord_617657
  simp only [CollatzResearch.WordTrace]
  refine ⟨22527801523341651262427225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15018534348894434174951483 22527801523341651262427225)
  ·
    refine ⟨16895851142506238446820419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22527801523341651262427225 16895851142506238446820419)
    ·
      refine ⟨25343776713759357670230629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16895851142506238446820419 25343776713759357670230629)
      ·
        refine ⟨4751958133829879563168243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25343776713759357670230629 4751958133829879563168243)
        ·
          refine ⟨7127937200744819344752365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4751958133829879563168243 7127937200744819344752365)
          ·
            refine ⟨2672976450279307254282137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7127937200744819344752365 2672976450279307254282137)
            ·
              refine ⟨2004732337709480440711603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672976450279307254282137 2004732337709480440711603)
              ·
                refine ⟨3007098506564220661067405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004732337709480440711603 3007098506564220661067405)
                ·
                  refine ⟨1127661939961582747900277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3007098506564220661067405 1127661939961582747900277)
                  ·
                    refine ⟨105718306871398382615651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1127661939961582747900277 105718306871398382615651)
                    ·
                      rfl

theorem cell23_617657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 5].length) (baseStart_617657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617657 prefixEnd_617657 := by exact prefixLift 617657
  have htrace : WordTrace (prefixWord ++ tailWord_617657) baseStart_617657 baseEnd_617657 := by
    simpa [prefixWord, tailWord_617657, baseEnd_617657] using wordTrace_append hprefix tailTrace_617657
  have hstable : (prefixWord ++ tailWord_617657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617657).length < 2 ^ (prefixWord ++ tailWord_617657).sum := by decide
  have hdescent : baseEnd_617657 < baseStart_617657 := by decide
  rcases family_descends (prefixWord ++ tailWord_617657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617674 : List Nat := [3, 1, 2, 1, 3, 3, 1, 3, 1, 5]
def baseStart_617674 : Nat := 118140960795 + 617674 * 2 ^ 59
def prefixEnd_617674 : Nat := 4983230072969 + 3 ^ 40 * 617674 * 2
def baseEnd_617674 : Nat := 105721216595107193778125

theorem tailTrace_617674 : CollatzResearch.WordTrace tailWord_617674 prefixEnd_617674 105721216595107193778125 := by
  unfold tailWord_617674
  simp only [CollatzResearch.WordTrace]
  refine ⟨5632105391070015791449019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15018947709520042110530717 5632105391070015791449019)
  ·
    refine ⟨8448158086605023687173529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5632105391070015791449019 8448158086605023687173529)
    ·
      refine ⟨6336118564953767765380147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8448158086605023687173529 6336118564953767765380147)
      ·
        refine ⟨9504177847430651648070221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6336118564953767765380147 9504177847430651648070221)
        ·
          refine ⟨3564066692786494368026333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9504177847430651648070221 3564066692786494368026333)
          ·
            refine ⟨1336525009794935388009875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3564066692786494368026333 1336525009794935388009875)
            ·
              refine ⟨2004787514692403082014813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1336525009794935388009875 2004787514692403082014813)
              ·
                refine ⟨751795318009651155755555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2004787514692403082014813 751795318009651155755555)
                ·
                  refine ⟨1127692977014476733633333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751795318009651155755555 1127692977014476733633333)
                  ·
                    refine ⟨105721216595107193778125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1127692977014476733633333 105721216595107193778125)
                    ·
                      rfl

theorem cell23_617674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_617674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617674 prefixEnd_617674 := by exact prefixLift 617674
  have htrace : WordTrace (prefixWord ++ tailWord_617674) baseStart_617674 baseEnd_617674 := by
    simpa [prefixWord, tailWord_617674, baseEnd_617674] using wordTrace_append hprefix tailTrace_617674
  have hstable : (prefixWord ++ tailWord_617674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617674).length < 2 ^ (prefixWord ++ tailWord_617674).sum := by decide
  have hdescent : baseEnd_617674 < baseStart_617674 := by decide
  rcases family_descends (prefixWord ++ tailWord_617674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617697 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_617697 : Nat := 118140960795 + 617697 * 2 ^ 59
def prefixEnd_617697 : Nat := 4983230072969 + 3 ^ 40 * 617697 * 2
def baseEnd_617697 : Nat := 317175459840374991346769

theorem tailTrace_617697 : CollatzResearch.WordTrace tailWord_617697 prefixEnd_617697 317175459840374991346769 := by
  unfold tailWord_617697
  simp only [CollatzResearch.WordTrace]
  refine ⟨22529260443196738093883345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15019506962131158729255563 22529260443196738093883345)
  ·
    refine ⟨16896945332397553570412509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22529260443196738093883345 16896945332397553570412509)
    ·
      refine ⟨6336354499649082588904691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16896945332397553570412509 6336354499649082588904691)
      ·
        refine ⟨9504531749473623883357037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6336354499649082588904691 9504531749473623883357037)
        ·
          refine ⟨3564199406052608956258889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9504531749473623883357037 3564199406052608956258889)
          ·
            refine ⟨2673149554539456717194167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3564199406052608956258889 2673149554539456717194167)
            ·
              refine ⟨4009724331809185075791251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673149554539456717194167 4009724331809185075791251)
              ·
                refine ⟨6014586497713777613686877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4009724331809185075791251 6014586497713777613686877)
                ·
                  refine ⟨2255469936642666605132579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6014586497713777613686877 2255469936642666605132579)
                  ·
                    refine ⟨3383204904963999907698869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2255469936642666605132579 3383204904963999907698869)
                    ·
                      refine ⟨317175459840374991346769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3383204904963999907698869 317175459840374991346769)
                      ·
                        rfl

theorem cell23_617697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_617697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617697 prefixEnd_617697 := by exact prefixLift 617697
  have htrace : WordTrace (prefixWord ++ tailWord_617697) baseStart_617697 baseEnd_617697 := by
    simpa [prefixWord, tailWord_617697, baseEnd_617697] using wordTrace_append hprefix tailTrace_617697
  have hstable : (prefixWord ++ tailWord_617697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617697).length < 2 ^ (prefixWord ++ tailWord_617697).sum := by decide
  have hdescent : baseEnd_617697 < baseStart_617697 := by decide
  rcases family_descends (prefixWord ++ tailWord_617697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617707 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 6]
def baseStart_617707 : Nat := 118140960795 + 617707 * 2 ^ 59
def prefixEnd_617707 : Nat := 4983230072969 + 3 ^ 40 * 617707 * 2
def baseEnd_617707 : Nat := 317180594646919952221723

theorem tailTrace_617707 : CollatzResearch.WordTrace tailWord_617707 prefixEnd_617707 317180594646919952221723 := by
  unfold tailWord_617707
  simp only [CollatzResearch.WordTrace]
  refine ⟨22529625173160509801747375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15019750115440339867831583 22529625173160509801747375)
  ·
    refine ⟨33794437759740764702621063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22529625173160509801747375 33794437759740764702621063)
    ·
      refine ⟨50691656639611147053931595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33794437759740764702621063 50691656639611147053931595)
      ·
        refine ⟨76037484959416720580897393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50691656639611147053931595 76037484959416720580897393)
        ·
          refine ⟨57028113719562540435673045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76037484959416720580897393 57028113719562540435673045)
          ·
            refine ⟨1336596415302247041461087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 57028113719562540435673045 1336596415302247041461087)
            ·
              refine ⟨2004894622953370562191631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1336596415302247041461087 2004894622953370562191631)
              ·
                refine ⟨3007341934430055843287447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004894622953370562191631 3007341934430055843287447)
                ·
                  refine ⟨4511012901645083764931171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3007341934430055843287447 4511012901645083764931171)
                  ·
                    refine ⟨6766519352467625647396757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4511012901645083764931171 6766519352467625647396757)
                    ·
                      refine ⟨317180594646919952221723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6766519352467625647396757 317180594646919952221723)
                      ·
                        rfl

theorem cell23_617707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 6].length) (baseStart_617707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617707 prefixEnd_617707 := by exact prefixLift 617707
  have htrace : WordTrace (prefixWord ++ tailWord_617707) baseStart_617707 baseEnd_617707 := by
    simpa [prefixWord, tailWord_617707, baseEnd_617707] using wordTrace_append hprefix tailTrace_617707
  have hstable : (prefixWord ++ tailWord_617707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617707).length < 2 ^ (prefixWord ++ tailWord_617707).sum := by decide
  have hdescent : baseEnd_617707 < baseStart_617707 := by decide
  rcases family_descends (prefixWord ++ tailWord_617707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617711 : List Nat := [1, 1, 2, 1, 7, 1, 2, 2, 1, 1, 4]
def baseStart_617711 : Nat := 118140960795 + 617711 * 2 ^ 59
def prefixEnd_617711 : Nat := 4983230072969 + 3 ^ 40 * 617711 * 2
def baseEnd_617711 : Nat := 317182648569537936571705

theorem tailTrace_617711 : CollatzResearch.WordTrace tailWord_617711 prefixEnd_617711 317182648569537936571705 := by
  unfold tailWord_617711
  simp only [CollatzResearch.WordTrace]
  refine ⟨22529771065146018484892987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15019847376764012323261991 22529771065146018484892987)
  ·
    refine ⟨33794656597719027727339481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22529771065146018484892987 33794656597719027727339481)
    ·
      refine ⟨25345992448289270795504611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33794656597719027727339481 25345992448289270795504611)
      ·
        refine ⟨38018988672433906193256917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25345992448289270795504611 38018988672433906193256917)
        ·
          refine ⟨891070047010169676404459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 38018988672433906193256917 891070047010169676404459)
          ·
            refine ⟨1336605070515254514606689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 891070047010169676404459 1336605070515254514606689)
            ·
              refine ⟨1002453802886440885955017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1336605070515254514606689 1002453802886440885955017)
              ·
                refine ⟨751840352164830664466263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1002453802886440885955017 751840352164830664466263)
                ·
                  refine ⟨1127760528247245996699395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751840352164830664466263 1127760528247245996699395)
                  ·
                    refine ⟨1691640792370868995049093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1127760528247245996699395 1691640792370868995049093)
                    ·
                      refine ⟨317182648569537936571705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1691640792370868995049093 317182648569537936571705)
                      ·
                        rfl

theorem cell23_617711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 1, 4].length) (baseStart_617711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617711 prefixEnd_617711 := by exact prefixLift 617711
  have htrace : WordTrace (prefixWord ++ tailWord_617711) baseStart_617711 baseEnd_617711 := by
    simpa [prefixWord, tailWord_617711, baseEnd_617711] using wordTrace_append hprefix tailTrace_617711
  have hstable : (prefixWord ++ tailWord_617711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617711).length < 2 ^ (prefixWord ++ tailWord_617711).sum := by decide
  have hdescent : baseEnd_617711 < baseStart_617711 := by decide
  rcases family_descends (prefixWord ++ tailWord_617711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617745 : List Nat := [1, 2, 2, 1, 1, 4, 5, 2, 1, 2, 2]
def baseStart_617745 : Nat := 118140960795 + 617745 * 2 ^ 59
def prefixEnd_617745 : Nat := 4983230072969 + 3 ^ 40 * 617745 * 2
def baseEnd_617745 : Nat := 317200106911790803546549

theorem tailTrace_617745 : CollatzResearch.WordTrace tailWord_617745 prefixEnd_617745 317200106911790803546549 := by
  unfold tailWord_617745
  simp only [CollatzResearch.WordTrace]
  refine ⟨22531011147022842291630689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15020674098015228194420459 22531011147022842291630689)
  ·
    refine ⟨16898258360267131718723017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22531011147022842291630689 16898258360267131718723017)
    ·
      refine ⟨12673693770200348789042263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16898258360267131718723017 12673693770200348789042263)
      ·
        refine ⟨19010540655300523183563395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12673693770200348789042263 19010540655300523183563395)
        ·
          refine ⟨28515810982950784775345093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19010540655300523183563395 28515810982950784775345093)
          ·
            refine ⟨5346714559303272145377205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28515810982950784775345093 5346714559303272145377205)
            ·
              refine ⟨501254489934681763629113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5346714559303272145377205 501254489934681763629113)
              ·
                refine ⟨375940867451011322721835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501254489934681763629113 375940867451011322721835)
                ·
                  refine ⟨563911301176516984082753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375940867451011322721835 563911301176516984082753)
                  ·
                    refine ⟨422933475882387738062065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 563911301176516984082753 422933475882387738062065)
                    ·
                      refine ⟨317200106911790803546549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422933475882387738062065 317200106911790803546549)
                      ·
                        rfl

theorem cell23_617745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 1, 2, 2].length) (baseStart_617745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617745 prefixEnd_617745 := by exact prefixLift 617745
  have htrace : WordTrace (prefixWord ++ tailWord_617745) baseStart_617745 baseEnd_617745 := by
    simpa [prefixWord, tailWord_617745, baseEnd_617745] using wordTrace_append hprefix tailTrace_617745
  have hstable : (prefixWord ++ tailWord_617745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617745).length < 2 ^ (prefixWord ++ tailWord_617745).sum := by decide
  have hdescent : baseEnd_617745 < baseStart_617745 := by decide
  rcases family_descends (prefixWord ++ tailWord_617745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617782 : List Nat := [5, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_617782 : Nat := 118140960795 + 617782 * 2 ^ 59
def prefixEnd_617782 : Nat := 4983230072969 + 3 ^ 40 * 617782 * 2
def baseEnd_617782 : Nat := 317219105696007158783879

theorem tailTrace_617782 : CollatzResearch.WordTrace tailWord_617782 prefixEnd_617782 317219105696007158783879 := by
  unfold tailWord_617782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1408272540493049850670475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15021573765259198407151733 1408272540493049850670475)
  ·
    refine ⟨2112408810739574776005713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1408272540493049850670475 2112408810739574776005713)
    ·
      refine ⟨1584306608054681082004285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2112408810739574776005713 1584306608054681082004285)
      ·
        refine ⟨594114978020505405751607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1584306608054681082004285 594114978020505405751607)
        ·
          refine ⟨891172467030758108627411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594114978020505405751607 891172467030758108627411)
          ·
            refine ⟨1336758700546137162941117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 891172467030758108627411 1336758700546137162941117)
            ·
              refine ⟨501284512704801436102919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1336758700546137162941117 501284512704801436102919)
              ·
                refine ⟨751926769057202154154379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501284512704801436102919 751926769057202154154379)
                ·
                  refine ⟨1127890153585803231231569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751926769057202154154379 1127890153585803231231569)
                  ·
                    refine ⟨845917615189352423423677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1127890153585803231231569 845917615189352423423677)
                    ·
                      refine ⟨317219105696007158783879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 845917615189352423423677 317219105696007158783879)
                      ·
                        rfl

theorem cell23_617782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_617782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617782 prefixEnd_617782 := by exact prefixLift 617782
  have htrace : WordTrace (prefixWord ++ tailWord_617782) baseStart_617782 baseEnd_617782 := by
    simpa [prefixWord, tailWord_617782, baseEnd_617782] using wordTrace_append hprefix tailTrace_617782
  have hstable : (prefixWord ++ tailWord_617782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617782).length < 2 ^ (prefixWord ++ tailWord_617782).sum := by decide
  have hdescent : baseEnd_617782 < baseStart_617782 := by decide
  rcases family_descends (prefixWord ++ tailWord_617782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617797 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_617797 : Nat := 118140960795 + 617797 * 2 ^ 59
def prefixEnd_617797 : Nat := 4983230072969 + 3 ^ 40 * 617797 * 2
def baseEnd_617797 : Nat := 317226807905824600096309

theorem tailTrace_617797 : CollatzResearch.WordTrace tailWord_617797 prefixEnd_617797 317226807905824600096309 := by
  unfold tailWord_617797
  simp only [CollatzResearch.WordTrace]
  refine ⟨22532907742834455172523645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15021938495222970115015763 22532907742834455172523645)
  ·
    refine ⟨8449840403562920689696367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22532907742834455172523645 8449840403562920689696367)
    ·
      refine ⟨12674760605344381034544551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8449840403562920689696367 12674760605344381034544551)
      ·
        refine ⟨19012140908016571551816827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12674760605344381034544551 19012140908016571551816827)
        ·
          refine ⟨28518211362024857327725241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19012140908016571551816827 28518211362024857327725241)
          ·
            refine ⟨21388658521518642995793931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28518211362024857327725241 21388658521518642995793931)
            ·
              refine ⟨32082987782277964493690897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21388658521518642995793931 32082987782277964493690897)
              ·
                refine ⟨24062240836708473370268173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32082987782277964493690897 24062240836708473370268173)
                ·
                  refine ⟨9023340313765677513850565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24062240836708473370268173 9023340313765677513850565)
                  ·
                    refine ⟨1691876308831064533846981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9023340313765677513850565 1691876308831064533846981)
                    ·
                      refine ⟨317226807905824600096309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1691876308831064533846981 317226807905824600096309)
                      ·
                        rfl

theorem cell23_617797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_617797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617797 prefixEnd_617797 := by exact prefixLift 617797
  have htrace : WordTrace (prefixWord ++ tailWord_617797) baseStart_617797 baseEnd_617797 := by
    simpa [prefixWord, tailWord_617797, baseEnd_617797] using wordTrace_append hprefix tailTrace_617797
  have hstable : (prefixWord ++ tailWord_617797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617797).length < 2 ^ (prefixWord ++ tailWord_617797).sum := by decide
  have hdescent : baseEnd_617797 < baseStart_617797 := by decide
  rcases family_descends (prefixWord ++ tailWord_617797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617801 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 4, 2, 2]
def baseStart_617801 : Nat := 118140960795 + 617801 * 2 ^ 59
def prefixEnd_617801 : Nat := 4983230072969 + 3 ^ 40 * 617801 * 2
def baseEnd_617801 : Nat := 317228861828442584446291

theorem tailTrace_617801 : CollatzResearch.WordTrace tailWord_617801 prefixEnd_617801 317228861828442584446291 := by
  unfold tailWord_617801
  simp only [CollatzResearch.WordTrace]
  refine ⟨22533053634819963855669257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15022035756546642570446171 22533053634819963855669257)
  ·
    refine ⟨16899790226114972891751943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22533053634819963855669257 16899790226114972891751943)
    ·
      refine ⟨25349685339172459337627915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16899790226114972891751943 25349685339172459337627915)
      ·
        refine ⟨38024528008758689006441873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25349685339172459337627915 38024528008758689006441873)
        ·
          refine ⟨28518396006569016754831405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38024528008758689006441873 28518396006569016754831405)
          ·
            refine ⟨10694398502463381283061777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28518396006569016754831405 10694398502463381283061777)
            ·
              refine ⟨8020798876847535962296333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10694398502463381283061777 8020798876847535962296333)
              ·
                refine ⟨3007799578817825985861125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8020798876847535962296333 3007799578817825985861125)
                ·
                  refine ⟨563962421028342372348961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3007799578817825985861125 563962421028342372348961)
                  ·
                    refine ⟨422971815771256779261721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 563962421028342372348961 422971815771256779261721)
                    ·
                      refine ⟨317228861828442584446291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422971815771256779261721 317228861828442584446291)
                      ·
                        rfl

theorem cell23_617801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 2, 2].length) (baseStart_617801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617801 prefixEnd_617801 := by exact prefixLift 617801
  have htrace : WordTrace (prefixWord ++ tailWord_617801) baseStart_617801 baseEnd_617801 := by
    simpa [prefixWord, tailWord_617801, baseEnd_617801] using wordTrace_append hprefix tailTrace_617801
  have hstable : (prefixWord ++ tailWord_617801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617801).length < 2 ^ (prefixWord ++ tailWord_617801).sum := by decide
  have hdescent : baseEnd_617801 < baseStart_617801 := by decide
  rcases family_descends (prefixWord ++ tailWord_617801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617804 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 2, 4, 3]
def baseStart_617804 : Nat := 118140960795 + 617804 * 2 ^ 59
def prefixEnd_617804 : Nat := 4983230072969 + 3 ^ 40 * 617804 * 2
def baseEnd_617804 : Nat := 317230402270406072708777

theorem tailTrace_617804 : CollatzResearch.WordTrace tailWord_617804 prefixEnd_617804 317230402270406072708777 := by
  unfold tailWord_617804
  simp only [CollatzResearch.WordTrace]
  refine ⟨11266581526904547684014233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15022108702539396912018977 11266581526904547684014233)
  ·
    refine ⟨8449936145178410763010675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11266581526904547684014233 8449936145178410763010675)
    ·
      refine ⟨12674904217767616144516013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8449936145178410763010675 12674904217767616144516013)
      ·
        refine ⟨4753089081662856054193505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12674904217767616144516013 4753089081662856054193505)
        ·
          refine ⟨3564816811247142040645129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4753089081662856054193505 3564816811247142040645129)
          ·
            refine ⟨2673612608435356530483847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3564816811247142040645129 2673612608435356530483847)
            ·
              refine ⟨4010418912653034795725771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673612608435356530483847 4010418912653034795725771)
              ·
                refine ⟨6015628368979552193588657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010418912653034795725771 6015628368979552193588657)
                ·
                  refine ⟨4511721276734664145191493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6015628368979552193588657 4511721276734664145191493)
                  ·
                    refine ⟨845947739387749527223405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4511721276734664145191493 845947739387749527223405)
                    ·
                      refine ⟨317230402270406072708777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 845947739387749527223405 317230402270406072708777)
                      ·
                        rfl

theorem cell23_617804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_617804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617804 prefixEnd_617804 := by exact prefixLift 617804
  have htrace : WordTrace (prefixWord ++ tailWord_617804) baseStart_617804 baseEnd_617804 := by
    simpa [prefixWord, tailWord_617804, baseEnd_617804] using wordTrace_append hprefix tailTrace_617804
  have hstable : (prefixWord ++ tailWord_617804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617804).length < 2 ^ (prefixWord ++ tailWord_617804).sum := by decide
  have hdescent : baseEnd_617804 < baseStart_617804 := by decide
  rcases family_descends (prefixWord ++ tailWord_617804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617818 : List Nat := [3, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2]
def baseStart_617818 : Nat := 118140960795 + 617818 * 2 ^ 59
def prefixEnd_617818 : Nat := 4983230072969 + 3 ^ 40 * 617818 * 2
def baseEnd_617818 : Nat := 317237590999569017933713

theorem tailTrace_617818 : CollatzResearch.WordTrace tailWord_617818 prefixEnd_617818 317237590999569017933713 := by
  unfold tailWord_617818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5633418418939593939759527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15022449117172250506025405 5633418418939593939759527)
  ·
    refine ⟨8450127628409390909639291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5633418418939593939759527 8450127628409390909639291)
    ·
      refine ⟨12675191442614086364458937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8450127628409390909639291 12675191442614086364458937)
      ·
        refine ⟨9506393581960564773344203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12675191442614086364458937 9506393581960564773344203)
        ·
          refine ⟨14259590372940847160016305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9506393581960564773344203 14259590372940847160016305)
          ·
            refine ⟨10694692779705635370012229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14259590372940847160016305 10694692779705635370012229)
            ·
              refine ⟨2005254896194806631877293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10694692779705635370012229 2005254896194806631877293)
              ·
                refine ⟨751970586073052486953985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2005254896194806631877293 751970586073052486953985)
                ·
                  refine ⟨563977939554789365215489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 751970586073052486953985 563977939554789365215489)
                  ·
                    refine ⟨422983454666092023911617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 563977939554789365215489 422983454666092023911617)
                    ·
                      refine ⟨317237590999569017933713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 422983454666092023911617 317237590999569017933713)
                      ·
                        rfl

theorem cell23_617818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_617818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617818 prefixEnd_617818 := by exact prefixLift 617818
  have htrace : WordTrace (prefixWord ++ tailWord_617818) baseStart_617818 baseEnd_617818 := by
    simpa [prefixWord, tailWord_617818, baseEnd_617818] using wordTrace_append hprefix tailTrace_617818
  have hstable : (prefixWord ++ tailWord_617818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617818).length < 2 ^ (prefixWord ++ tailWord_617818).sum := by decide
  have hdescent : baseEnd_617818 < baseStart_617818 := by decide
  rcases family_descends (prefixWord ++ tailWord_617818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617824 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 7]
def baseStart_617824 : Nat := 118140960795 + 617824 * 2 ^ 59
def prefixEnd_617824 : Nat := 4983230072969 + 3 ^ 40 * 617824 * 2
def baseEnd_617824 : Nat := 35248963542610666050965

theorem tailTrace_617824 : CollatzResearch.WordTrace tailWord_617824 prefixEnd_617824 35248963542610666050965 := by
  unfold tailWord_617824
  simp only [CollatzResearch.WordTrace]
  refine ⟨11266946256868319391878263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15022595009157759189171017 11266946256868319391878263)
  ·
    refine ⟨16900419385302479087817395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11266946256868319391878263 16900419385302479087817395)
    ·
      refine ⟨25350629077953718631726093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16900419385302479087817395 25350629077953718631726093)
      ·
        refine ⟨9506485904232644486897285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25350629077953718631726093 9506485904232644486897285)
        ·
          refine ⟨1782466107043620841293241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9506485904232644486897285 1782466107043620841293241)
          ·
            refine ⟨1336849580282715630969931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1782466107043620841293241 1336849580282715630969931)
            ·
              refine ⟨2005274370424073446454897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1336849580282715630969931 2005274370424073446454897)
              ·
                refine ⟨1503955777818055084841173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2005274370424073446454897 1503955777818055084841173)
                ·
                  refine ⟨35248963542610666050965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1503955777818055084841173 35248963542610666050965)
                  ·
                    rfl

theorem cell23_617824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 7].length) (baseStart_617824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617824 prefixEnd_617824 := by exact prefixLift 617824
  have htrace : WordTrace (prefixWord ++ tailWord_617824) baseStart_617824 baseEnd_617824 := by
    simpa [prefixWord, tailWord_617824, baseEnd_617824] using wordTrace_append hprefix tailTrace_617824
  have hstable : (prefixWord ++ tailWord_617824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617824).length < 2 ^ (prefixWord ++ tailWord_617824).sum := by decide
  have hdescent : baseEnd_617824 < baseStart_617824 := by decide
  rcases family_descends (prefixWord ++ tailWord_617824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617858 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 7]
def baseStart_617858 : Nat := 118140960795 + 617858 * 2 ^ 59
def prefixEnd_617858 : Nat := 4983230072969 + 3 ^ 40 * 617858 * 2
def baseEnd_617858 : Nat := 35250903358416540159281

theorem tailTrace_617858 : CollatzResearch.WordTrace tailWord_617858 prefixEnd_617858 35250903358416540159281 := by
  unfold tailWord_617858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5633783148903365647623557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15023421730408975060329485 5633783148903365647623557)
  ·
    refine ⟨1056334340419381058929417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5633783148903365647623557 1056334340419381058929417)
    ·
      refine ⟨792250755314535794197063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1056334340419381058929417 792250755314535794197063)
      ·
        refine ⟨1188376132971803691295595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792250755314535794197063 1188376132971803691295595)
        ·
          refine ⟨1782564199457705536943393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188376132971803691295595 1782564199457705536943393)
          ·
            refine ⟨1336923149593279152707545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1782564199457705536943393 1336923149593279152707545)
            ·
              refine ⟨1002692362194959364530659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1336923149593279152707545 1002692362194959364530659)
              ·
                refine ⟨1504038543292439046795989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002692362194959364530659 1504038543292439046795989)
                ·
                  refine ⟨35250903358416540159281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1504038543292439046795989 35250903358416540159281)
                  ·
                    rfl

theorem cell23_617858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_617858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617858 prefixEnd_617858 := by exact prefixLift 617858
  have htrace : WordTrace (prefixWord ++ tailWord_617858) baseStart_617858 baseEnd_617858 := by
    simpa [prefixWord, tailWord_617858, baseEnd_617858] using wordTrace_append hprefix tailTrace_617858
  have hstable : (prefixWord ++ tailWord_617858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617858).length < 2 ^ (prefixWord ++ tailWord_617858).sum := by decide
  have hdescent : baseEnd_617858 < baseStart_617858 := by decide
  rcases family_descends (prefixWord ++ tailWord_617858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617911 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 3]
def baseStart_617911 : Nat := 118140960795 + 617911 * 2 ^ 59
def prefixEnd_617911 : Nat := 4983230072969 + 3 ^ 40 * 617911 * 2
def baseEnd_617911 : Nat := 317285344700437154070785

theorem tailTrace_617911 : CollatzResearch.WordTrace tailWord_617911 prefixEnd_617911 317285344700437154070785 := by
  unfold tailWord_617911
  simp only [CollatzResearch.WordTrace]
  refine ⟨22537065664421452642173587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15024710442947635094782391 22537065664421452642173587)
  ·
    refine ⟨33805598496632178963260381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22537065664421452642173587 33805598496632178963260381)
    ·
      refine ⟨12677099436237067111222643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33805598496632178963260381 12677099436237067111222643)
      ·
        refine ⟨19015649154355600666833965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12677099436237067111222643 19015649154355600666833965)
        ·
          refine ⟨7130868432883350250062737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19015649154355600666833965 7130868432883350250062737)
          ·
            refine ⟨5348151324662512687547053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7130868432883350250062737 5348151324662512687547053)
            ·
              refine ⟨2005556746748442257830145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5348151324662512687547053 2005556746748442257830145)
              ·
                refine ⟨1504167560061331693372609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2005556746748442257830145 1504167560061331693372609)
                ·
                  refine ⟨1128125670045998770029457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1504167560061331693372609 1128125670045998770029457)
                  ·
                    refine ⟨846094252534499077522093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1128125670045998770029457 846094252534499077522093)
                    ·
                      refine ⟨317285344700437154070785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 846094252534499077522093 317285344700437154070785)
                      ·
                        rfl

theorem cell23_617911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_617911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617911 prefixEnd_617911 := by exact prefixLift 617911
  have htrace : WordTrace (prefixWord ++ tailWord_617911) baseStart_617911 baseEnd_617911 := by
    simpa [prefixWord, tailWord_617911, baseEnd_617911] using wordTrace_append hprefix tailTrace_617911
  have hstable : (prefixWord ++ tailWord_617911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617911).length < 2 ^ (prefixWord ++ tailWord_617911).sum := by decide
  have hdescent : baseEnd_617911 < baseStart_617911 := by decide
  rcases family_descends (prefixWord ++ tailWord_617911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617931 : List Nat := [1, 1, 1, 1, 3, 3, 6, 1, 6]
def baseStart_617931 : Nat := 118140960795 + 617931 * 2 ^ 59
def prefixEnd_617931 : Nat := 4983230072969 + 3 ^ 40 * 617931 * 2
def baseEnd_617931 : Nat := 35255068257058563980077

theorem tailTrace_617931 : CollatzResearch.WordTrace tailWord_617931 prefixEnd_617931 35255068257058563980077 := by
  unfold tailWord_617931
  simp only [CollatzResearch.WordTrace]
  refine ⟨22537795124348996057901647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15025196749565997371934431 22537795124348996057901647)
  ·
    refine ⟨33806692686523494086852471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22537795124348996057901647 33806692686523494086852471)
    ·
      refine ⟨50710039029785241130278707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33806692686523494086852471 50710039029785241130278707)
      ·
        refine ⟨76065058544677861695418061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50710039029785241130278707 76065058544677861695418061)
        ·
          refine ⟨28524396954254198135781773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76065058544677861695418061 28524396954254198135781773)
          ·
            refine ⟨10696648857845324300918165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28524396954254198135781773 10696648857845324300918165)
            ·
              refine ⟨501405415211499576605539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10696648857845324300918165 501405415211499576605539)
              ·
                refine ⟨752108122817249364908309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501405415211499576605539 752108122817249364908309)
                ·
                  refine ⟨35255068257058563980077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 752108122817249364908309 35255068257058563980077)
                  ·
                    rfl

theorem cell23_617931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 6].length) (baseStart_617931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617931 prefixEnd_617931 := by exact prefixLift 617931
  have htrace : WordTrace (prefixWord ++ tailWord_617931) baseStart_617931 baseEnd_617931 := by
    simpa [prefixWord, tailWord_617931, baseEnd_617931] using wordTrace_append hprefix tailTrace_617931
  have hstable : (prefixWord ++ tailWord_617931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617931).length < 2 ^ (prefixWord ++ tailWord_617931).sum := by decide
  have hdescent : baseEnd_617931 < baseStart_617931 := by decide
  rcases family_descends (prefixWord ++ tailWord_617931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617934 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_617934 : Nat := 118140960795 + 617934 * 2 ^ 59
def prefixEnd_617934 : Nat := 4983230072969 + 3 ^ 40 * 617934 * 2
def baseEnd_617934 : Nat := 317297154755490564083179

theorem tailTrace_617934 : CollatzResearch.WordTrace tailWord_617934 prefixEnd_617934 317297154755490564083179 := by
  unfold tailWord_617934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2817238067917265946282607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15025269695558751713507237 2817238067917265946282607)
  ·
    refine ⟨4225857101875898919423911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2817238067917265946282607 4225857101875898919423911)
    ·
      refine ⟨6338785652813848379135867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4225857101875898919423911 6338785652813848379135867)
      ·
        refine ⟨9508178479220772568703801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6338785652813848379135867 9508178479220772568703801)
        ·
          refine ⟨7131133859415579426527851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9508178479220772568703801 7131133859415579426527851)
          ·
            refine ⟨10696700789123369139791777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7131133859415579426527851 10696700789123369139791777)
            ·
              refine ⟨8022525591842526854843833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10696700789123369139791777 8022525591842526854843833)
              ·
                refine ⟨6016894193881895141132875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8022525591842526854843833 6016894193881895141132875)
                ·
                  refine ⟨9025341290822842711699313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6016894193881895141132875 9025341290822842711699313)
                  ·
                    refine ⟨6769005968117132033774485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9025341290822842711699313 6769005968117132033774485)
                    ·
                      refine ⟨317297154755490564083179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6769005968117132033774485 317297154755490564083179)
                      ·
                        rfl

theorem cell23_617934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_617934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617934 prefixEnd_617934 := by exact prefixLift 617934
  have htrace : WordTrace (prefixWord ++ tailWord_617934) baseStart_617934 baseEnd_617934 := by
    simpa [prefixWord, tailWord_617934, baseEnd_617934] using wordTrace_append hprefix tailTrace_617934
  have hstable : (prefixWord ++ tailWord_617934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617934).length < 2 ^ (prefixWord ++ tailWord_617934).sum := by decide
  have hdescent : baseEnd_617934 < baseStart_617934 := by decide
  rcases family_descends (prefixWord ++ tailWord_617934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617968 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 2, 3, 2]
def baseStart_617968 : Nat := 118140960795 + 617968 * 2 ^ 59
def prefixEnd_617968 : Nat := 4983230072969 + 3 ^ 40 * 617968 * 2
def baseEnd_617968 : Nat := 317314613097743431058023

theorem tailTrace_617968 : CollatzResearch.WordTrace tailWord_617968 prefixEnd_617968 317314613097743431058023 := by
  unfold tailWord_617968
  simp only [CollatzResearch.WordTrace]
  refine ⟨11269572312607475688499279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15026096416809967584665705 11269572312607475688499279)
  ·
    refine ⟨16904358468911213532748919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11269572312607475688499279 16904358468911213532748919)
    ·
      refine ⟨25356537703366820299123379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16904358468911213532748919 25356537703366820299123379)
      ·
        refine ⟨38034806555050230448685069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25356537703366820299123379 38034806555050230448685069)
        ·
          refine ⟨14263052458143836418256901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38034806555050230448685069 14263052458143836418256901)
          ·
            refine ⟨2674322335901969328423169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14263052458143836418256901 2674322335901969328423169)
            ·
              refine ⟨2005741751926476996317377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2674322335901969328423169 2005741751926476996317377)
              ·
                refine ⟨1504306313944857747238033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2005741751926476996317377 1504306313944857747238033)
                ·
                  refine ⟨1128229735458643310428525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1504306313944857747238033 1128229735458643310428525)
                  ·
                    refine ⟨423086150796991241410697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1128229735458643310428525 423086150796991241410697)
                    ·
                      refine ⟨317314613097743431058023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 423086150796991241410697 317314613097743431058023)
                      ·
                        rfl

theorem cell23_617968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 2, 3, 2].length) (baseStart_617968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617968 prefixEnd_617968 := by exact prefixLift 617968
  have htrace : WordTrace (prefixWord ++ tailWord_617968) baseStart_617968 baseEnd_617968 := by
    simpa [prefixWord, tailWord_617968, baseEnd_617968] using wordTrace_append hprefix tailTrace_617968
  have hstable : (prefixWord ++ tailWord_617968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617968).length < 2 ^ (prefixWord ++ tailWord_617968).sum := by decide
  have hdescent : baseEnd_617968 < baseStart_617968 := by decide
  rcases family_descends (prefixWord ++ tailWord_617968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617981 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_617981 : Nat := 118140960795 + 617981 * 2 ^ 59
def prefixEnd_617981 : Nat := 4983230072969 + 3 ^ 40 * 617981 * 2
def baseEnd_617981 : Nat := 317321288346251880195463

theorem tailTrace_617981 : CollatzResearch.WordTrace tailWord_617981 prefixEnd_617981 317321288346251880195463 := by
  unfold tailWord_617981
  simp only [CollatzResearch.WordTrace]
  refine ⟨22539618774167854597221797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15026412516111903064814531 22539618774167854597221797)
  ·
    refine ⟨4226178520156472736979087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22539618774167854597221797 4226178520156472736979087)
    ·
      refine ⟨6339267780234709105468631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4226178520156472736979087 6339267780234709105468631)
      ·
        refine ⟨9508901670352063658202947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6339267780234709105468631 9508901670352063658202947)
        ·
          refine ⟨14263352505528095487304421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9508901670352063658202947 14263352505528095487304421)
          ·
            refine ⟨2674378594786517903869579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14263352505528095487304421 2674378594786517903869579)
            ·
              refine ⟨4011567892179776855804369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2674378594786517903869579 4011567892179776855804369)
              ·
                refine ⟨3008675919134832641853277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4011567892179776855804369 3008675919134832641853277)
                ·
                  refine ⟨1128253469675562240694979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3008675919134832641853277 1128253469675562240694979)
                  ·
                    refine ⟨1692380204513343361042469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1128253469675562240694979 1692380204513343361042469)
                    ·
                      refine ⟨317321288346251880195463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1692380204513343361042469 317321288346251880195463)
                      ·
                        rfl

theorem cell23_617981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_617981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617981 prefixEnd_617981 := by exact prefixLift 617981
  have htrace : WordTrace (prefixWord ++ tailWord_617981) baseStart_617981 baseEnd_617981 := by
    simpa [prefixWord, tailWord_617981, baseEnd_617981] using wordTrace_append hprefix tailTrace_617981
  have hstable : (prefixWord ++ tailWord_617981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617981).length < 2 ^ (prefixWord ++ tailWord_617981).sum := by decide
  have hdescent : baseEnd_617981 < baseStart_617981 := by decide
  rcases family_descends (prefixWord ++ tailWord_617981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617991 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 1, 6]
def baseStart_617991 : Nat := 118140960795 + 617991 * 2 ^ 59
def prefixEnd_617991 : Nat := 4983230072969 + 3 ^ 40 * 617991 * 2
def baseEnd_617991 : Nat := 105775474384265613690139

theorem tailTrace_617991 : CollatzResearch.WordTrace tailWord_617991 prefixEnd_617991 105775474384265613690139 := by
  unfold tailWord_617991
  simp only [CollatzResearch.WordTrace]
  refine ⟨22539983504131626305085827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15026655669421084203390551 22539983504131626305085827)
  ·
    refine ⟨33809975256197439457628741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22539983504131626305085827 33809975256197439457628741)
    ·
      refine ⟨6339370360537019898305389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33809975256197439457628741 6339370360537019898305389)
      ·
        refine ⟨2377263885201382461864521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6339370360537019898305389 2377263885201382461864521)
        ·
          refine ⟨1782947913901036846398391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2377263885201382461864521 1782947913901036846398391)
          ·
            refine ⟨2674421870851555269597587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782947913901036846398391 2674421870851555269597587)
            ·
              refine ⟨4011632806277332904396381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2674421870851555269597587 4011632806277332904396381)
              ·
                refine ⟨1504362302353999839148643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4011632806277332904396381 1504362302353999839148643)
                ·
                  refine ⟨2256543453530999758722965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504362302353999839148643 2256543453530999758722965)
                  ·
                    refine ⟨105775474384265613690139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2256543453530999758722965 105775474384265613690139)
                    ·
                      rfl

theorem cell23_617991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_617991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_617991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_617991 prefixEnd_617991 := by exact prefixLift 617991
  have htrace : WordTrace (prefixWord ++ tailWord_617991) baseStart_617991 baseEnd_617991 := by
    simpa [prefixWord, tailWord_617991, baseEnd_617991] using wordTrace_append hprefix tailTrace_617991
  have hstable : (prefixWord ++ tailWord_617991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617991).length < 2 ^ (prefixWord ++ tailWord_617991).sum := by decide
  have hdescent : baseEnd_617991 < baseStart_617991 := by decide
  rcases family_descends (prefixWord ++ tailWord_617991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618001 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 3]
def baseStart_618001 : Nat := 118140960795 + 618001 * 2 ^ 59
def prefixEnd_618001 : Nat := 4983230072969 + 3 ^ 40 * 618001 * 2
def baseEnd_618001 : Nat := 317331557959341801945371

theorem tailTrace_618001 : CollatzResearch.WordTrace tailWord_618001 prefixEnd_618001 317331557959341801945371 := by
  unfold tailWord_618001
  simp only [CollatzResearch.WordTrace]
  refine ⟨22540348234095398012949857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15026898822730265341966571 22540348234095398012949857)
  ·
    refine ⟨16905261175571548509712393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22540348234095398012949857 16905261175571548509712393)
    ·
      refine ⟨12678945881678661382284295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16905261175571548509712393 12678945881678661382284295)
      ·
        refine ⟨19018418822517992073426443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12678945881678661382284295 19018418822517992073426443)
        ·
          refine ⟨28527628233776988110139665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19018418822517992073426443 28527628233776988110139665)
          ·
            refine ⟨21395721175332741082604749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28527628233776988110139665 21395721175332741082604749)
            ·
              refine ⟨8023395440749777905976781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21395721175332741082604749 8023395440749777905976781)
              ·
                refine ⟨3008773290281166714741293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8023395440749777905976781 3008773290281166714741293)
                ·
                  refine ⟨1128289983855437518027985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3008773290281166714741293 1128289983855437518027985)
                  ·
                    refine ⟨846217487891578138520989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1128289983855437518027985 846217487891578138520989)
                    ·
                      refine ⟨317331557959341801945371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 846217487891578138520989 317331557959341801945371)
                      ·
                        rfl

theorem cell23_618001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_618001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618001 prefixEnd_618001 := by exact prefixLift 618001
  have htrace : WordTrace (prefixWord ++ tailWord_618001) baseStart_618001 baseEnd_618001 := by
    simpa [prefixWord, tailWord_618001, baseEnd_618001] using wordTrace_append hprefix tailTrace_618001
  have hstable : (prefixWord ++ tailWord_618001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618001).length < 2 ^ (prefixWord ++ tailWord_618001).sum := by decide
  have hdescent : baseEnd_618001 < baseStart_618001 := by decide
  rcases family_descends (prefixWord ++ tailWord_618001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618045 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 1, 2, 4]
def baseStart_618045 : Nat := 118140960795 + 618045 * 2 ^ 59
def prefixEnd_618045 : Nat := 4983230072969 + 3 ^ 40 * 618045 * 2
def baseEnd_618045 : Nat := 317354151108139629795169

theorem tailTrace_618045 : CollatzResearch.WordTrace tailWord_618045 prefixEnd_618045 317354151108139629795169 := by
  unfold tailWord_618045
  simp only [CollatzResearch.WordTrace]
  refine ⟨22541953045935993527551589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15027968697290662351701059 22541953045935993527551589)
  ·
    refine ⟨4226616196112998786415923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22541953045935993527551589 4226616196112998786415923)
    ·
      refine ⟨6339924294169498179623885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4226616196112998786415923 6339924294169498179623885)
      ·
        refine ⟨2377471610313561817358957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6339924294169498179623885 2377471610313561817358957)
        ·
          refine ⟨891551853867585681509609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2377471610313561817358957 891551853867585681509609)
          ·
            refine ⟨668663890400689261132207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 891551853867585681509609 668663890400689261132207)
            ·
              refine ⟨1002995835601033891698311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668663890400689261132207 1002995835601033891698311)
              ·
                refine ⟨1504493753401550837547467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002995835601033891698311 1504493753401550837547467)
                ·
                  refine ⟨2256740630102326256321201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504493753401550837547467 2256740630102326256321201)
                  ·
                    refine ⟨1692555472576744692240901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2256740630102326256321201 1692555472576744692240901)
                    ·
                      refine ⟨317354151108139629795169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1692555472576744692240901 317354151108139629795169)
                      ·
                        rfl

theorem cell23_618045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_618045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618045 prefixEnd_618045 := by exact prefixLift 618045
  have htrace : WordTrace (prefixWord ++ tailWord_618045) baseStart_618045 baseEnd_618045 := by
    simpa [prefixWord, tailWord_618045, baseEnd_618045] using wordTrace_append hprefix tailTrace_618045
  have hstable : (prefixWord ++ tailWord_618045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618045).length < 2 ^ (prefixWord ++ tailWord_618045).sum := by decide
  have hdescent : baseEnd_618045 < baseStart_618045 := by decide
  rcases family_descends (prefixWord ++ tailWord_618045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618055 : List Nat := [1, 1, 4, 1, 6, 1, 2, 7]
def baseStart_618055 : Nat := 118140960795 + 618055 * 2 ^ 59
def prefixEnd_618055 : Nat := 4983230072969 + 3 ^ 40 * 618055 * 2
def baseEnd_618055 : Nat := 11754047626469799654449

theorem tailTrace_618055 : CollatzResearch.WordTrace tailWord_618055 prefixEnd_618055 11754047626469799654449 := by
  unfold tailWord_618055
  simp only [CollatzResearch.WordTrace]
  refine ⟨22542317775899765235415619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15028211850599843490277079 22542317775899765235415619)
  ·
    refine ⟨33813476663849647853123429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22542317775899765235415619 33813476663849647853123429)
    ·
      refine ⟨6340026874471808972460643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33813476663849647853123429 6340026874471808972460643)
      ·
        refine ⟨9510040311707713458690965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6340026874471808972460643 9510040311707713458690965)
        ·
          refine ⟨445783139611299068376139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9510040311707713458690965 445783139611299068376139)
          ·
            refine ⟨668674709416948602564209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445783139611299068376139 668674709416948602564209)
            ·
              refine ⟨501506032062711451923157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668674709416948602564209 501506032062711451923157)
              ·
                refine ⟨11754047626469799654449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 501506032062711451923157 11754047626469799654449)
                ·
                  rfl

theorem cell23_618055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 7].length) (baseStart_618055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618055 prefixEnd_618055 := by exact prefixLift 618055
  have htrace : WordTrace (prefixWord ++ tailWord_618055) baseStart_618055 baseEnd_618055 := by
    simpa [prefixWord, tailWord_618055, baseEnd_618055] using wordTrace_append hprefix tailTrace_618055
  have hstable : (prefixWord ++ tailWord_618055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618055).length < 2 ^ (prefixWord ++ tailWord_618055).sum := by decide
  have hdescent : baseEnd_618055 < baseStart_618055 := by decide
  rcases family_descends (prefixWord ++ tailWord_618055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618141 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_618141 : Nat := 118140960795 + 618141 * 2 ^ 59
def prefixEnd_618141 : Nat := 4983230072969 + 3 ^ 40 * 618141 * 2
def baseEnd_618141 : Nat := 105801148416990418064909

theorem tailTrace_618141 : CollatzResearch.WordTrace tailWord_618141 prefixEnd_618141 105801148416990418064909 := by
  unfold tailWord_618141
  simp only [CollatzResearch.WordTrace]
  refine ⟨22545454453588201923046277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15030302969058801282030851 22545454453588201923046277)
  ·
    refine ⟨4227272710047787860571177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22545454453588201923046277 4227272710047787860571177)
    ·
      refine ⟨3170454532535840895428383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4227272710047787860571177 3170454532535840895428383)
      ·
        refine ⟨4755681798803761343142575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3170454532535840895428383 4755681798803761343142575)
        ·
          refine ⟨7133522698205642014713863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4755681798803761343142575 7133522698205642014713863)
          ·
            refine ⟨10700284047308463022070795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7133522698205642014713863 10700284047308463022070795)
            ·
              refine ⟨16050426070962694533106193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10700284047308463022070795 16050426070962694533106193)
              ·
                refine ⟨12037819553222020899829645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16050426070962694533106193 12037819553222020899829645)
                ·
                  refine ⟨4514182332458257837436117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12037819553222020899829645 4514182332458257837436117)
                  ·
                    refine ⟨105801148416990418064909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4514182332458257837436117 105801148416990418064909)
                    ·
                      rfl

theorem cell23_618141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_618141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618141 prefixEnd_618141 := by exact prefixLift 618141
  have htrace : WordTrace (prefixWord ++ tailWord_618141) baseStart_618141 baseEnd_618141 := by
    simpa [prefixWord, tailWord_618141, baseEnd_618141] using wordTrace_append hprefix tailTrace_618141
  have hstable : (prefixWord ++ tailWord_618141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618141).length < 2 ^ (prefixWord ++ tailWord_618141).sum := by decide
  have hdescent : baseEnd_618141 < baseStart_618141 := by decide
  rcases family_descends (prefixWord ++ tailWord_618141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618145 : List Nat := [1, 2, 3, 3, 2, 2, 1, 4, 5]
def baseStart_618145 : Nat := 118140960795 + 618145 * 2 ^ 59
def prefixEnd_618145 : Nat := 4983230072969 + 3 ^ 40 * 618145 * 2
def baseEnd_618145 : Nat := 35267277685954359838301

theorem tailTrace_618145 : CollatzResearch.WordTrace tailWord_618145 prefixEnd_618145 35267277685954359838301 := by
  unfold tailWord_618145
  simp only [CollatzResearch.WordTrace]
  refine ⟨22545600345573710606191889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15030400230382473737461259 22545600345573710606191889)
  ·
    refine ⟨16909200259180282954643917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22545600345573710606191889 16909200259180282954643917)
    ·
      refine ⟨6340950097192606107991469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16909200259180282954643917 6340950097192606107991469)
      ·
        refine ⟨2377856286447227290496801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6340950097192606107991469 2377856286447227290496801)
        ·
          refine ⟨1783392214835420467872601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2377856286447227290496801 1783392214835420467872601)
          ·
            refine ⟨1337544161126565350904451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1783392214835420467872601 1337544161126565350904451)
            ·
              refine ⟨2006316241689848026356677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1337544161126565350904451 2006316241689848026356677)
              ·
                refine ⟨376184295316846504941877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2006316241689848026356677 376184295316846504941877)
                ·
                  refine ⟨35267277685954359838301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 376184295316846504941877 35267277685954359838301)
                  ·
                    rfl

theorem cell23_618145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 5].length) (baseStart_618145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618145 prefixEnd_618145 := by exact prefixLift 618145
  have htrace : WordTrace (prefixWord ++ tailWord_618145) baseStart_618145 baseEnd_618145 := by
    simpa [prefixWord, tailWord_618145, baseEnd_618145] using wordTrace_append hprefix tailTrace_618145
  have hstable : (prefixWord ++ tailWord_618145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618145).length < 2 ^ (prefixWord ++ tailWord_618145).sum := by decide
  have hdescent : baseEnd_618145 < baseStart_618145 := by decide
  rcases family_descends (prefixWord ++ tailWord_618145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618191 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 4]
def baseStart_618191 : Nat := 118140960795 + 618191 * 2 ^ 59
def prefixEnd_618191 : Nat := 4983230072969 + 3 ^ 40 * 618191 * 2
def baseEnd_618191 : Nat := 317429119283696058569497

theorem tailTrace_618191 : CollatzResearch.WordTrace tailWord_618191 prefixEnd_618191 317429119283696058569497 := by
  unfold tailWord_618191
  simp only [CollatzResearch.WordTrace]
  refine ⟨22547278103407060462366427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15031518735604706974910951 22547278103407060462366427)
  ·
    refine ⟨33820917155110590693549641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22547278103407060462366427 33820917155110590693549641)
    ·
      refine ⟨25365687866332943020162231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33820917155110590693549641 25365687866332943020162231)
      ·
        refine ⟨38048531799499414530243347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25365687866332943020162231 38048531799499414530243347)
        ·
          refine ⟨57072797699249121795365021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38048531799499414530243347 57072797699249121795365021)
          ·
            refine ⟨21402299137218420673261883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57072797699249121795365021 21402299137218420673261883)
            ·
              refine ⟨32103448705827631009892825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21402299137218420673261883 32103448705827631009892825)
              ·
                refine ⟨24077586529370723257419619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32103448705827631009892825 24077586529370723257419619)
                ·
                  refine ⟨36116379794056084886129429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24077586529370723257419619 36116379794056084886129429)
                  ·
                    refine ⟨1692955302846378979037317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36116379794056084886129429 1692955302846378979037317)
                    ·
                      refine ⟨317429119283696058569497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1692955302846378979037317 317429119283696058569497)
                      ·
                        rfl

theorem cell23_618191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_618191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618191 prefixEnd_618191 := by exact prefixLift 618191
  have htrace : WordTrace (prefixWord ++ tailWord_618191) baseStart_618191 baseEnd_618191 := by
    simpa [prefixWord, tailWord_618191, baseEnd_618191] using wordTrace_append hprefix tailTrace_618191
  have hstable : (prefixWord ++ tailWord_618191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618191).length < 2 ^ (prefixWord ++ tailWord_618191).sum := by decide
  have hdescent : baseEnd_618191 < baseStart_618191 := by decide
  rcases family_descends (prefixWord ++ tailWord_618191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618218 : List Nat := [3, 1, 3, 1, 1, 1, 2, 5, 6]
def baseStart_618218 : Nat := 118140960795 + 618218 * 2 ^ 59
def prefixEnd_618218 : Nat := 4983230072969 + 3 ^ 40 * 618218 * 2
def baseEnd_618218 : Nat := 35271442584596383659097

theorem tailTrace_618218 : CollatzResearch.WordTrace tailWord_618218 prefixEnd_618218 35271442584596383659097 := by
  unfold tailWord_618218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5637065718577311018399827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15032175249539496049066205 5637065718577311018399827)
  ·
    refine ⟨8455598577865966527599741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5637065718577311018399827 8455598577865966527599741)
    ·
      refine ⟨3170849466699737447849903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8455598577865966527599741 3170849466699737447849903)
      ·
        refine ⟨4756274200049606171774855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3170849466699737447849903 4756274200049606171774855)
        ·
          refine ⟨7134411300074409257662283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4756274200049606171774855 7134411300074409257662283)
          ·
            refine ⟨10701616950111613886493425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7134411300074409257662283 10701616950111613886493425)
            ·
              refine ⟨8026212712583710414870069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10701616950111613886493425 8026212712583710414870069)
              ·
                refine ⟨752457441804722851394069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8026212712583710414870069 752457441804722851394069)
                ·
                  refine ⟨35271442584596383659097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 752457441804722851394069 35271442584596383659097)
                  ·
                    rfl

theorem cell23_618218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 6].length) (baseStart_618218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618218 prefixEnd_618218 := by exact prefixLift 618218
  have htrace : WordTrace (prefixWord ++ tailWord_618218) baseStart_618218 baseEnd_618218 := by
    simpa [prefixWord, tailWord_618218, baseEnd_618218] using wordTrace_append hprefix tailTrace_618218
  have hstable : (prefixWord ++ tailWord_618218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618218).length < 2 ^ (prefixWord ++ tailWord_618218).sum := by decide
  have hdescent : baseEnd_618218 < baseStart_618218 := by decide
  rcases family_descends (prefixWord ++ tailWord_618218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618308 : List Nat := [2, 3, 4, 14]
def baseStart_618308 : Nat := 118140960795 + 618308 * 2 ^ 59
def prefixEnd_618308 : Nat := 4983230072969 + 3 ^ 40 * 618308 * 2
def baseEnd_618308 : Nat := 145171100375067261457

theorem tailTrace_618308 : CollatzResearch.WordTrace tailWord_618308 prefixEnd_618308 145171100375067261457 := by
  unfold tailWord_618308
  simp only [CollatzResearch.WordTrace]
  refine ⟨11275772721991594722187789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15034363629322126296250385 11275772721991594722187789)
  ·
    refine ⟨4228414770746848020820421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11275772721991594722187789 4228414770746848020820421)
    ·
      refine ⟨792827769515034003903829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4228414770746848020820421 792827769515034003903829)
      ·
        refine ⟨145171100375067261457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 792827769515034003903829 145171100375067261457)
        ·
          rfl

theorem cell23_618308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 14].length) (baseStart_618308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618308 prefixEnd_618308 := by exact prefixLift 618308
  have htrace : WordTrace (prefixWord ++ tailWord_618308) baseStart_618308 baseEnd_618308 := by
    simpa [prefixWord, tailWord_618308, baseEnd_618308] using wordTrace_append hprefix tailTrace_618308
  have hstable : (prefixWord ++ tailWord_618308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618308).length < 2 ^ (prefixWord ++ tailWord_618308).sum := by decide
  have hdescent : baseEnd_618308 < baseStart_618308 := by decide
  rcases family_descends (prefixWord ++ tailWord_618308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618312 : List Nat := [2, 1, 3, 1, 1, 5, 2, 2, 2, 4]
def baseStart_618312 : Nat := 118140960795 + 618312 * 2 ^ 59
def prefixEnd_618312 : Nat := 4983230072969 + 3 ^ 40 * 618312 * 2
def baseEnd_618312 : Nat := 105830416814296695052147

theorem tailTrace_618312 : CollatzResearch.WordTrace tailWord_618312 prefixEnd_618312 105830416814296695052147 := by
  unfold tailWord_618312
  simp only [CollatzResearch.WordTrace]
  refine ⟨11275845667984349063760595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15034460890645798751680793 11275845667984349063760595)
  ·
    refine ⟨16913768501976523595640893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11275845667984349063760595 16913768501976523595640893)
    ·
      refine ⟨6342663188241196348365335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16913768501976523595640893 6342663188241196348365335)
      ·
        refine ⟨9513994782361794522548003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6342663188241196348365335 9513994782361794522548003)
        ·
          refine ⟨14270992173542691783822005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9513994782361794522548003 14270992173542691783822005)
          ·
            refine ⟨1337905516269627354733313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14270992173542691783822005 1337905516269627354733313)
            ·
              refine ⟨1003429137202220516049985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1337905516269627354733313 1003429137202220516049985)
              ·
                refine ⟨752571852901665387037489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003429137202220516049985 752571852901665387037489)
                ·
                  refine ⟨564428889676249040278117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 752571852901665387037489 564428889676249040278117)
                  ·
                    refine ⟨105830416814296695052147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 564428889676249040278117 105830416814296695052147)
                    ·
                      rfl

theorem cell23_618312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_618312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618312 prefixEnd_618312 := by exact prefixLift 618312
  have htrace : WordTrace (prefixWord ++ tailWord_618312) baseStart_618312 baseEnd_618312 := by
    simpa [prefixWord, tailWord_618312, baseEnd_618312] using wordTrace_append hprefix tailTrace_618312
  have hstable : (prefixWord ++ tailWord_618312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618312).length < 2 ^ (prefixWord ++ tailWord_618312).sum := by decide
  have hdescent : baseEnd_618312 < baseStart_618312 := by decide
  rcases family_descends (prefixWord ++ tailWord_618312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618325 : List Nat := [1, 3, 2, 2, 2, 4, 1, 8]
def baseStart_618325 : Nat := 118140960795 + 618325 * 2 ^ 59
def prefixEnd_618325 : Nat := 4983230072969 + 3 ^ 40 * 618325 * 2
def baseEnd_618325 : Nat := 11759182433014760529403

theorem tailTrace_618325 : CollatzResearch.WordTrace tailWord_618325 prefixEnd_618325 11759182433014760529403 := by
  unfold tailWord_618325
  simp only [CollatzResearch.WordTrace]
  refine ⟨22552165484921601347744429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15034776989947734231829619 22552165484921601347744429)
  ·
    refine ⟨8457062056845600505404161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22552165484921601347744429 8457062056845600505404161)
    ·
      refine ⟨6342796542634200379053121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8457062056845600505404161 6342796542634200379053121)
      ·
        refine ⟨4757097406975650284289841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6342796542634200379053121 4757097406975650284289841)
        ·
          refine ⟨3567823055231737713217381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4757097406975650284289841 3567823055231737713217381)
          ·
            refine ⟨668966822855950821228259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3567823055231737713217381 668966822855950821228259)
            ·
              refine ⟨1003450234283926231842389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668966822855950821228259 1003450234283926231842389)
              ·
                refine ⟨11759182433014760529403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1003450234283926231842389 11759182433014760529403)
                ·
                  rfl

theorem cell23_618325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 8].length) (baseStart_618325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618325 prefixEnd_618325 := by exact prefixLift 618325
  have htrace : WordTrace (prefixWord ++ tailWord_618325) baseStart_618325 baseEnd_618325 := by
    simpa [prefixWord, tailWord_618325, baseEnd_618325] using wordTrace_append hprefix tailTrace_618325
  have hstable : (prefixWord ++ tailWord_618325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618325).length < 2 ^ (prefixWord ++ tailWord_618325).sum := by decide
  have hdescent : baseEnd_618325 < baseStart_618325 := by decide
  rcases family_descends (prefixWord ++ tailWord_618325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618335 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 3]
def baseStart_618335 : Nat := 118140960795 + 618335 * 2 ^ 59
def prefixEnd_618335 : Nat := 4983230072969 + 3 ^ 40 * 618335 * 2
def baseEnd_618335 : Nat := 317503060497943495168835

theorem tailTrace_618335 : CollatzResearch.WordTrace tailWord_618335 prefixEnd_618335 317503060497943495168835 := by
  unfold tailWord_618335
  simp only [CollatzResearch.WordTrace]
  refine ⟨22552530214885373055608459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15035020143256915370405639 22552530214885373055608459)
  ·
    refine ⟨33828795322328059583412689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22552530214885373055608459 33828795322328059583412689)
    ·
      refine ⟨25371596491746044687559517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33828795322328059583412689 25371596491746044687559517)
      ·
        refine ⟨9514348684404766757834819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25371596491746044687559517 9514348684404766757834819)
        ·
          refine ⟨14271523026607150136752229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9514348684404766757834819 14271523026607150136752229)
          ·
            refine ⟨2675910567488840650641043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14271523026607150136752229 2675910567488840650641043)
            ·
              refine ⟨4013865851233260975961565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2675910567488840650641043 4013865851233260975961565)
              ·
                refine ⟨1505199694212472865985587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4013865851233260975961565 1505199694212472865985587)
                ·
                  refine ⟨2257799541318709298978381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505199694212472865985587 2257799541318709298978381)
                  ·
                    refine ⟨846674827994515987116893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2257799541318709298978381 846674827994515987116893)
                    ·
                      refine ⟨317503060497943495168835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 846674827994515987116893 317503060497943495168835)
                      ·
                        rfl

theorem cell23_618335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_618335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618335 prefixEnd_618335 := by exact prefixLift 618335
  have htrace : WordTrace (prefixWord ++ tailWord_618335) baseStart_618335 baseEnd_618335 := by
    simpa [prefixWord, tailWord_618335, baseEnd_618335] using wordTrace_append hprefix tailTrace_618335
  have hstable : (prefixWord ++ tailWord_618335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618335).length < 2 ^ (prefixWord ++ tailWord_618335).sum := by decide
  have hdescent : baseEnd_618335 < baseStart_618335 := by decide
  rcases family_descends (prefixWord ++ tailWord_618335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618368 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 4, 6]
def baseStart_618368 : Nat := 118140960795 + 618368 * 2 ^ 59
def prefixEnd_618368 : Nat := 4983230072969 + 3 ^ 40 * 618368 * 2
def baseEnd_618368 : Nat := 105840001786513955352061

theorem tailTrace_618368 : CollatzResearch.WordTrace tailWord_618368 prefixEnd_618368 105840001786513955352061 := by
  unfold tailWord_618368
  simp only [CollatzResearch.WordTrace]
  refine ⟨11276866911882909845779879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15035822549177213127706505 11276866911882909845779879)
  ·
    refine ⟨16915300367824364768669819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11276866911882909845779879 16915300367824364768669819)
    ·
      refine ⟨25372950551736547153004729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16915300367824364768669819 25372950551736547153004729)
      ·
        refine ⟨19029712913802410364753547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25372950551736547153004729 19029712913802410364753547)
        ·
          refine ⟨28544569370703615547130321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19029712913802410364753547 28544569370703615547130321)
          ·
            refine ⟨21408427028027711660347741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28544569370703615547130321 21408427028027711660347741)
            ·
              refine ⟨8028160135510391872630403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21408427028027711660347741 8028160135510391872630403)
              ·
                refine ⟨12042240203265587808945605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8028160135510391872630403 12042240203265587808945605)
                ·
                  refine ⟨2257920038112297714177301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12042240203265587808945605 2257920038112297714177301)
                  ·
                    refine ⟨105840001786513955352061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2257920038112297714177301 105840001786513955352061)
                    ·
                      rfl

theorem cell23_618368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4, 6].length) (baseStart_618368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618368 prefixEnd_618368 := by exact prefixLift 618368
  have htrace : WordTrace (prefixWord ++ tailWord_618368) baseStart_618368 baseEnd_618368 := by
    simpa [prefixWord, tailWord_618368, baseEnd_618368] using wordTrace_append hprefix tailTrace_618368
  have hstable : (prefixWord ++ tailWord_618368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618368).length < 2 ^ (prefixWord ++ tailWord_618368).sum := by decide
  have hdescent : baseEnd_618368 < baseStart_618368 := by decide
  rcases family_descends (prefixWord ++ tailWord_618368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618396 : List Nat := [2, 2, 3, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_618396 : Nat := 118140960795 + 618396 * 2 ^ 59
def prefixEnd_618396 : Nat := 4983230072969 + 3 ^ 40 * 618396 * 2
def baseEnd_618396 : Nat := 317534382817867756506055

theorem tailTrace_618396 : CollatzResearch.WordTrace tailWord_618396 prefixEnd_618396 317534382817867756506055 := by
  unfold tailWord_618396
  simp only [CollatzResearch.WordTrace]
  refine ⟨11277377533832190236789521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15036503378442920315719361 11277377533832190236789521)
  ·
    refine ⟨8458033150374142677592141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11277377533832190236789521 8458033150374142677592141)
    ·
      refine ⟨3171762431390303504097053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8458033150374142677592141 3171762431390303504097053)
      ·
        refine ⟨1189410911771363814036395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3171762431390303504097053 1189410911771363814036395)
        ·
          refine ⟨1784116367657045721054593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1189410911771363814036395 1784116367657045721054593)
          ·
            refine ⟨1338087275742784290790945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1784116367657045721054593 1338087275742784290790945)
            ·
              refine ⟨1003565456807088218093209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1338087275742784290790945 1003565456807088218093209)
              ·
                refine ⟨752674092605316163569907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003565456807088218093209 752674092605316163569907)
                ·
                  refine ⟨1129011138907974245354861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 752674092605316163569907 1129011138907974245354861)
                  ·
                    refine ⟨423379177090490342008073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1129011138907974245354861 423379177090490342008073)
                    ·
                      refine ⟨317534382817867756506055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 423379177090490342008073 317534382817867756506055)
                      ·
                        rfl

theorem cell23_618396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_618396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618396 prefixEnd_618396 := by exact prefixLift 618396
  have htrace : WordTrace (prefixWord ++ tailWord_618396) baseStart_618396 baseEnd_618396 := by
    simpa [prefixWord, tailWord_618396, baseEnd_618396] using wordTrace_append hprefix tailTrace_618396
  have hstable : (prefixWord ++ tailWord_618396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618396).length < 2 ^ (prefixWord ++ tailWord_618396).sum := by decide
  have hdescent : baseEnd_618396 < baseStart_618396 := by decide
  rcases family_descends (prefixWord ++ tailWord_618396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618465 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_618465 : Nat := 118140960795 + 618465 * 2 ^ 59
def prefixEnd_618465 : Nat := 4983230072969 + 3 ^ 40 * 618465 * 2
def baseEnd_618465 : Nat := 317569812983027986543237

theorem tailTrace_618465 : CollatzResearch.WordTrace tailWord_618465 prefixEnd_618465 317569812983027986543237 := by
  unfold tailWord_618465
  simp only [CollatzResearch.WordTrace]
  refine ⟨22557271704414405257840849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15038181136276270171893899 22557271704414405257840849)
  ·
    refine ⟨16917953778310803943380637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22557271704414405257840849 16917953778310803943380637)
    ·
      refine ⟨6344232666866551478767739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16917953778310803943380637 6344232666866551478767739)
      ·
        refine ⟨9516349000299827218151609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6344232666866551478767739 9516349000299827218151609)
        ·
          refine ⟨7137261750224870413613707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9516349000299827218151609 7137261750224870413613707)
          ·
            refine ⟨10705892625337305620420561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7137261750224870413613707 10705892625337305620420561)
            ·
              refine ⟨8029419469002979215315421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10705892625337305620420561 8029419469002979215315421)
              ·
                refine ⟨3011032300876117205743283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8029419469002979215315421 3011032300876117205743283)
                ·
                  refine ⟨4516548451314175808614925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011032300876117205743283 4516548451314175808614925)
                  ·
                    refine ⟨1693705669242815928230597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4516548451314175808614925 1693705669242815928230597)
                    ·
                      refine ⟨317569812983027986543237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1693705669242815928230597 317569812983027986543237)
                      ·
                        rfl

theorem cell23_618465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_618465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618465 prefixEnd_618465 := by exact prefixLift 618465
  have htrace : WordTrace (prefixWord ++ tailWord_618465) baseStart_618465 baseEnd_618465 := by
    simpa [prefixWord, tailWord_618465, baseEnd_618465] using wordTrace_append hprefix tailTrace_618465
  have hstable : (prefixWord ++ tailWord_618465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618465).length < 2 ^ (prefixWord ++ tailWord_618465).sum := by decide
  have hdescent : baseEnd_618465 < baseStart_618465 := by decide
  rcases family_descends (prefixWord ++ tailWord_618465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618492 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 3, 4]
def baseStart_618492 : Nat := 118140960795 + 618492 * 2 ^ 59
def prefixEnd_618492 : Nat := 4983230072969 + 3 ^ 40 * 618492 * 2
def baseEnd_618492 : Nat := 105861225653566460301871

theorem tailTrace_618492 : CollatzResearch.WordTrace tailWord_618492 prefixEnd_618492 105861225653566460301871 := by
  unfold tailWord_618492
  simp only [CollatzResearch.WordTrace]
  refine ⟨11279128237658294434536865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15038837650211059246049153 11279128237658294434536865)
  ·
    refine ⟨8459346178243720825902649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11279128237658294434536865 8459346178243720825902649)
    ·
      refine ⟨6344509633682790619426987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8459346178243720825902649 6344509633682790619426987)
      ·
        refine ⟨9516764450524185929140481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6344509633682790619426987 9516764450524185929140481)
        ·
          refine ⟨7137573337893139446855361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9516764450524185929140481 7137573337893139446855361)
          ·
            refine ⟨5353180003419854585141521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7137573337893139446855361 5353180003419854585141521)
            ·
              refine ⟨4014885002564890938856141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5353180003419854585141521 4014885002564890938856141)
              ·
                refine ⟨1505581875961834102071053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4014885002564890938856141 1505581875961834102071053)
                ·
                  refine ⟨564593203485687788276645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1505581875961834102071053 564593203485687788276645)
                  ·
                    refine ⟨105861225653566460301871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 564593203485687788276645 105861225653566460301871)
                    ·
                      rfl

theorem cell23_618492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_618492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618492 prefixEnd_618492 := by exact prefixLift 618492
  have htrace : WordTrace (prefixWord ++ tailWord_618492) baseStart_618492 baseEnd_618492 := by
    simpa [prefixWord, tailWord_618492, baseEnd_618492] using wordTrace_append hprefix tailTrace_618492
  have hstable : (prefixWord ++ tailWord_618492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618492).length < 2 ^ (prefixWord ++ tailWord_618492).sum := by decide
  have hdescent : baseEnd_618492 < baseStart_618492 := by decide
  rcases family_descends (prefixWord ++ tailWord_618492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618516 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_618516 : Nat := 118140960795 + 618516 * 2 ^ 59
def prefixEnd_618516 : Nat := 4983230072969 + 3 ^ 40 * 618516 * 2
def baseEnd_618516 : Nat := 317596000496407287005503

theorem tailTrace_618516 : CollatzResearch.WordTrace tailWord_618516 prefixEnd_618516 317596000496407287005503 := by
  unfold tailWord_618516
  simp only [CollatzResearch.WordTrace]
  refine ⟨11279565913614820483973701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15039421218153093978631601 11279565913614820483973701)
  ·
    refine ⟨2114918608802778840745069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11279565913614820483973701 2114918608802778840745069)
    ·
      refine ⟨793094478301042065279401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2114918608802778840745069 793094478301042065279401)
      ·
        refine ⟨594820858725781548959551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 793094478301042065279401 594820858725781548959551)
        ·
          refine ⟨892231288088672323439327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594820858725781548959551 892231288088672323439327)
          ·
            refine ⟨1338346932133008485158991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892231288088672323439327 1338346932133008485158991)
            ·
              refine ⟨2007520398199512727738487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338346932133008485158991 2007520398199512727738487)
              ·
                refine ⟨3011280597299269091607731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2007520398199512727738487 3011280597299269091607731)
                ·
                  refine ⟨4516920895948903637411597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011280597299269091607731 4516920895948903637411597)
                  ·
                    refine ⟨1693845335980838864029349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4516920895948903637411597 1693845335980838864029349)
                    ·
                      refine ⟨317596000496407287005503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1693845335980838864029349 317596000496407287005503)
                      ·
                        rfl

theorem cell23_618516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_618516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618516 prefixEnd_618516 := by exact prefixLift 618516
  have htrace : WordTrace (prefixWord ++ tailWord_618516) baseStart_618516 baseEnd_618516 := by
    simpa [prefixWord, tailWord_618516, baseEnd_618516] using wordTrace_append hprefix tailTrace_618516
  have hstable : (prefixWord ++ tailWord_618516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618516).length < 2 ^ (prefixWord ++ tailWord_618516).sum := by decide
  have hdescent : baseEnd_618516 < baseStart_618516 := by decide
  rcases family_descends (prefixWord ++ tailWord_618516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618519 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 3]
def baseStart_618519 : Nat := 118140960795 + 618519 * 2 ^ 59
def prefixEnd_618519 : Nat := 4983230072969 + 3 ^ 40 * 618519 * 2
def baseEnd_618519 : Nat := 317597540938370775267989

theorem tailTrace_618519 : CollatzResearch.WordTrace tailWord_618519 prefixEnd_618519 317597540938370775267989 := by
  unfold tailWord_618519
  simp only [CollatzResearch.WordTrace]
  refine ⟨22559241246218772480306611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15039494164145848320204407 22559241246218772480306611)
  ·
    refine ⟨33838861869328158720459917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22559241246218772480306611 33838861869328158720459917)
    ·
      refine ⟨12689573200998059520172469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33838861869328158720459917 12689573200998059520172469)
      ·
        refine ⟨1189647487593568080016169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12689573200998059520172469 1189647487593568080016169)
        ·
          refine ⟨892235615695176060012127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1189647487593568080016169 892235615695176060012127)
          ·
            refine ⟨1338353423542764090018191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892235615695176060012127 1338353423542764090018191)
            ·
              refine ⟨2007530135314146135027287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338353423542764090018191 2007530135314146135027287)
              ·
                refine ⟨3011295202971219202540931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2007530135314146135027287 3011295202971219202540931)
                ·
                  refine ⟨4516942804456828803811397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011295202971219202540931 4516942804456828803811397)
                  ·
                    refine ⟨846926775835655400714637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4516942804456828803811397 846926775835655400714637)
                    ·
                      refine ⟨317597540938370775267989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 846926775835655400714637 317597540938370775267989)
                      ·
                        rfl

theorem cell23_618519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_618519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618519 prefixEnd_618519 := by exact prefixLift 618519
  have htrace : WordTrace (prefixWord ++ tailWord_618519) baseStart_618519 baseEnd_618519 := by
    simpa [prefixWord, tailWord_618519, baseEnd_618519] using wordTrace_append hprefix tailTrace_618519
  have hstable : (prefixWord ++ tailWord_618519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618519).length < 2 ^ (prefixWord ++ tailWord_618519).sum := by decide
  have hdescent : baseEnd_618519 < baseStart_618519 := by decide
  rcases family_descends (prefixWord ++ tailWord_618519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618542 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_618542 : Nat := 118140960795 + 618542 * 2 ^ 59
def prefixEnd_618542 : Nat := 4983230072969 + 3 ^ 40 * 618542 * 2
def baseEnd_618542 : Nat := 317609350993424185280383

theorem tailTrace_618542 : CollatzResearch.WordTrace tailWord_618542 prefixEnd_618542 317609350993424185280383 := by
  unfold tailWord_618542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820010015641930926049235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15040053416756964938929253 2820010015641930926049235)
  ·
    refine ⟨4230015023462896389073853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2820010015641930926049235 4230015023462896389073853)
    ·
      refine ⟨1586255633798586145902695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4230015023462896389073853 1586255633798586145902695)
      ·
        refine ⟨2379383450697879218854043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1586255633798586145902695 2379383450697879218854043)
        ·
          refine ⟨3569075176046818828281065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379383450697879218854043 3569075176046818828281065)
          ·
            refine ⟨2676806382035114121210799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3569075176046818828281065 2676806382035114121210799)
            ·
              refine ⟨4015209573052671181816199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2676806382035114121210799 4015209573052671181816199)
              ·
                refine ⟨6022814359579006772724299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4015209573052671181816199 6022814359579006772724299)
                ·
                  refine ⟨9034221539368510159086449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6022814359579006772724299 9034221539368510159086449)
                  ·
                    refine ⟨6775666154526382619314837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9034221539368510159086449 6775666154526382619314837)
                    ·
                      refine ⟨317609350993424185280383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6775666154526382619314837 317609350993424185280383)
                      ·
                        rfl

theorem cell23_618542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_618542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618542 prefixEnd_618542 := by exact prefixLift 618542
  have htrace : WordTrace (prefixWord ++ tailWord_618542) baseStart_618542 baseEnd_618542 := by
    simpa [prefixWord, tailWord_618542, baseEnd_618542] using wordTrace_append hprefix tailTrace_618542
  have hstable : (prefixWord ++ tailWord_618542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618542).length < 2 ^ (prefixWord ++ tailWord_618542).sum := by decide
  have hdescent : baseEnd_618542 < baseStart_618542 := by decide
  rcases family_descends (prefixWord ++ tailWord_618542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618549 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_618549 : Nat := 118140960795 + 618549 * 2 ^ 59
def prefixEnd_618549 : Nat := 4983230072969 + 3 ^ 40 * 618549 * 2
def baseEnd_618549 : Nat := 317612945358005657892851

theorem tailTrace_618549 : CollatzResearch.WordTrace tailWord_618549 prefixEnd_618549 317612945358005657892851 := by
  unfold tailWord_618549
  simp only [CollatzResearch.WordTrace]
  refine ⟨22560335436110087603898701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15040223624073391735932467 22560335436110087603898701)
  ·
    refine ⟨8460125788541282851462013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22560335436110087603898701 8460125788541282851462013)
    ·
      refine ⟨3172547170702981069298255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8460125788541282851462013 3172547170702981069298255)
      ·
        refine ⟨4758820756054471603947383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3172547170702981069298255 4758820756054471603947383)
        ·
          refine ⟨7138231134081707405921075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4758820756054471603947383 7138231134081707405921075)
          ·
            refine ⟨10707346701122561108881613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7138231134081707405921075 10707346701122561108881613)
            ·
              refine ⟨4015255012920960415830605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10707346701122561108881613 4015255012920960415830605)
              ·
                refine ⟨1505720629845360155936477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4015255012920960415830605 1505720629845360155936477)
                ·
                  refine ⟨564645236192010058476179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1505720629845360155936477 564645236192010058476179)
                  ·
                    refine ⟨846967854288015087714269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 564645236192010058476179 846967854288015087714269)
                    ·
                      refine ⟨317612945358005657892851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 846967854288015087714269 317612945358005657892851)
                      ·
                        rfl

theorem cell23_618549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_618549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618549 prefixEnd_618549 := by exact prefixLift 618549
  have htrace : WordTrace (prefixWord ++ tailWord_618549) baseStart_618549 baseEnd_618549 := by
    simpa [prefixWord, tailWord_618549, baseEnd_618549] using wordTrace_append hprefix tailTrace_618549
  have hstable : (prefixWord ++ tailWord_618549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618549).length < 2 ^ (prefixWord ++ tailWord_618549).sum := by decide
  have hdescent : baseEnd_618549 < baseStart_618549 := by decide
  rcases family_descends (prefixWord ++ tailWord_618549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618572 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 3, 1, 4]
def baseStart_618572 : Nat := 118140960795 + 618572 * 2 ^ 59
def prefixEnd_618572 : Nat := 4983230072969 + 3 ^ 40 * 618572 * 2
def baseEnd_618572 : Nat := 317624755413059067905245

theorem tailTrace_618572 : CollatzResearch.WordTrace tailWord_618572 prefixEnd_618572 317624755413059067905245 := by
  unfold tailWord_618572
  simp only [CollatzResearch.WordTrace]
  refine ⟨11280587157513381265992985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15040782876684508354657313 11280587157513381265992985)
  ·
    refine ⟨8460440368135035949494739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11280587157513381265992985 8460440368135035949494739)
    ·
      refine ⟨12690660552202553924242109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8460440368135035949494739 12690660552202553924242109)
      ·
        refine ⟨4758997707075957721590791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12690660552202553924242109 4758997707075957721590791)
        ·
          refine ⟨7138496560613936582386187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4758997707075957721590791 7138496560613936582386187)
          ·
            refine ⟨10707744840920904873579281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7138496560613936582386187 10707744840920904873579281)
            ·
              refine ⟨8030808630690678655184461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10707744840920904873579281 8030808630690678655184461)
              ·
                refine ⟨3011553236509004495694173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8030808630690678655184461 3011553236509004495694173)
                ·
                  refine ⟨1129332463690876685885315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3011553236509004495694173 1129332463690876685885315)
                  ·
                    refine ⟨1693998695536315028827973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1129332463690876685885315 1693998695536315028827973)
                    ·
                      refine ⟨317624755413059067905245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1693998695536315028827973 317624755413059067905245)
                      ·
                        rfl

theorem cell23_618572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_618572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618572 prefixEnd_618572 := by exact prefixLift 618572
  have htrace : WordTrace (prefixWord ++ tailWord_618572) baseStart_618572 baseEnd_618572 := by
    simpa [prefixWord, tailWord_618572, baseEnd_618572] using wordTrace_append hprefix tailTrace_618572
  have hstable : (prefixWord ++ tailWord_618572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618572).length < 2 ^ (prefixWord ++ tailWord_618572).sum := by decide
  have hdescent : baseEnd_618572 < baseStart_618572 := by decide
  rcases family_descends (prefixWord ++ tailWord_618572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618592 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 5]
def baseStart_618592 : Nat := 118140960795 + 618592 * 2 ^ 59
def prefixEnd_618592 : Nat := 4983230072969 + 3 ^ 40 * 618592 * 2
def baseEnd_618592 : Nat := 317635025026148989655153

theorem tailTrace_618592 : CollatzResearch.WordTrace tailWord_618592 prefixEnd_618592 317635025026148989655153 := by
  unfold tailWord_618592
  simp only [CollatzResearch.WordTrace]
  refine ⟨11280951887477152973857015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15041269183302870631809353 11280951887477152973857015)
  ·
    refine ⟨16921427831215729460785523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11280951887477152973857015 16921427831215729460785523)
    ·
      refine ⟨25382141746823594191178285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16921427831215729460785523 25382141746823594191178285)
      ·
        refine ⟨9518303155058847821691857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25382141746823594191178285 9518303155058847821691857)
        ·
          refine ⟨7138727366294135866268893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9518303155058847821691857 7138727366294135866268893)
          ·
            refine ⟨2677022762360300949850835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7138727366294135866268893 2677022762360300949850835)
            ·
              refine ⟨4015534143540451424776253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2677022762360300949850835 4015534143540451424776253)
              ·
                refine ⟨1505825303827669284291095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4015534143540451424776253 1505825303827669284291095)
                ·
                  refine ⟨2258737955741503926436643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505825303827669284291095 2258737955741503926436643)
                  ·
                    refine ⟨3388106933612255889654965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2258737955741503926436643 3388106933612255889654965)
                    ·
                      refine ⟨317635025026148989655153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3388106933612255889654965 317635025026148989655153)
                      ·
                        rfl

theorem cell23_618592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_618592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618592 prefixEnd_618592 := by exact prefixLift 618592
  have htrace : WordTrace (prefixWord ++ tailWord_618592) baseStart_618592 baseEnd_618592 := by
    simpa [prefixWord, tailWord_618592, baseEnd_618592] using wordTrace_append hprefix tailTrace_618592
  have hstable : (prefixWord ++ tailWord_618592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618592).length < 2 ^ (prefixWord ++ tailWord_618592).sum := by decide
  have hdescent : baseEnd_618592 < baseStart_618592 := by decide
  rcases family_descends (prefixWord ++ tailWord_618592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618595 : List Nat := [1, 1, 1, 5, 1, 1, 13]
def baseStart_618595 : Nat := 118140960795 + 618595 * 2 ^ 59
def prefixEnd_618595 : Nat := 4983230072969 + 3 ^ 40 * 618595 * 2
def baseEnd_618595 : Nat := 3921439079853240468119

theorem tailTrace_618595 : CollatzResearch.WordTrace tailWord_618595 prefixEnd_618595 3921439079853240468119 := by
  unfold tailWord_618595
  simp only [CollatzResearch.WordTrace]
  refine ⟨22562013193943437460073239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15041342129295624973382159 22562013193943437460073239)
  ·
    refine ⟨33843019790915156190109859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22562013193943437460073239 33843019790915156190109859)
    ·
      refine ⟨50764529686372734285164789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33843019790915156190109859 50764529686372734285164789)
      ·
        refine ⟨4759174658097443839234199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50764529686372734285164789 4759174658097443839234199)
        ·
          refine ⟨7138761987146165758851299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4759174658097443839234199 7138761987146165758851299)
          ·
            refine ⟨10708142980719248638276949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7138761987146165758851299 10708142980719248638276949)
            ·
              refine ⟨3921439079853240468119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 10708142980719248638276949 3921439079853240468119)
              ·
                rfl

theorem cell23_618595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 13].length) (baseStart_618595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618595 prefixEnd_618595 := by exact prefixLift 618595
  have htrace : WordTrace (prefixWord ++ tailWord_618595) baseStart_618595 baseEnd_618595 := by
    simpa [prefixWord, tailWord_618595, baseEnd_618595] using wordTrace_append hprefix tailTrace_618595
  have hstable : (prefixWord ++ tailWord_618595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618595).length < 2 ^ (prefixWord ++ tailWord_618595).sum := by decide
  have hdescent : baseEnd_618595 < baseStart_618595 := by decide
  rcases family_descends (prefixWord ++ tailWord_618595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618599 : List Nat := [1, 1, 5, 1, 1, 2, 2, 4, 2, 4]
def baseStart_618599 : Nat := 118140960795 + 618599 * 2 ^ 59
def prefixEnd_618599 : Nat := 4983230072969 + 3 ^ 40 * 618599 * 2
def baseEnd_618599 : Nat := 105879539796910154089207

theorem tailTrace_618599 : CollatzResearch.WordTrace tailWord_618599 prefixEnd_618599 105879539796910154089207 := by
  unfold tailWord_618599
  simp only [CollatzResearch.WordTrace]
  refine ⟨22562159085928946143218851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15041439390619297428812567 22562159085928946143218851)
  ·
    refine ⟨33843238628893419214828277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22562159085928946143218851 33843238628893419214828277)
    ·
      refine ⟨3172803621458758051390151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33843238628893419214828277 3172803621458758051390151)
      ·
        refine ⟨4759205432188137077085227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3172803621458758051390151 4759205432188137077085227)
        ·
          refine ⟨7138808148282205615627841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4759205432188137077085227 7138808148282205615627841)
          ·
            refine ⟨5354106111211654211720881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7138808148282205615627841 5354106111211654211720881)
            ·
              refine ⟨4015579583408740658790661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5354106111211654211720881 4015579583408740658790661)
              ·
                refine ⟨752921171889138873523249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4015579583408740658790661 752921171889138873523249)
                ·
                  refine ⟨564690878916854155142437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 752921171889138873523249 564690878916854155142437)
                  ·
                    refine ⟨105879539796910154089207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 564690878916854155142437 105879539796910154089207)
                    ·
                      rfl

theorem cell23_618599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_618599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618599 prefixEnd_618599 := by exact prefixLift 618599
  have htrace : WordTrace (prefixWord ++ tailWord_618599) baseStart_618599 baseEnd_618599 := by
    simpa [prefixWord, tailWord_618599, baseEnd_618599] using wordTrace_append hprefix tailTrace_618599
  have hstable : (prefixWord ++ tailWord_618599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618599).length < 2 ^ (prefixWord ++ tailWord_618599).sum := by decide
  have hdescent : baseEnd_618599 < baseStart_618599 := by decide
  rcases family_descends (prefixWord ++ tailWord_618599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618656 : List Nat := [2, 1, 1, 4, 2, 2, 1, 4, 2, 1, 3]
def baseStart_618656 : Nat := 118140960795 + 618656 * 2 ^ 59
def prefixEnd_618656 : Nat := 4983230072969 + 3 ^ 40 * 618656 * 2
def baseEnd_618656 : Nat := 317667887788036739254859

theorem tailTrace_618656 : CollatzResearch.WordTrace tailWord_618656 prefixEnd_618656 317667887788036739254859 := by
  unfold tailWord_618656
  simp only [CollatzResearch.WordTrace]
  refine ⟨11282119023361222439021911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15042825364481629918695881 11282119023361222439021911)
  ·
    refine ⟨16923178535041833658532867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11282119023361222439021911 16923178535041833658532867)
    ·
      refine ⟨25384767802562750487799301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16923178535041833658532867 25384767802562750487799301)
      ·
        refine ⟨4759643962980515716462369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25384767802562750487799301 4759643962980515716462369)
        ·
          refine ⟨3569732972235386787346777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4759643962980515716462369 3569732972235386787346777)
          ·
            refine ⟨2677299729176540090510083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3569732972235386787346777 2677299729176540090510083)
            ·
              refine ⟨4015949593764810135765125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2677299729176540090510083 4015949593764810135765125)
              ·
                refine ⟨752990548830901900455961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4015949593764810135765125 752990548830901900455961)
                ·
                  refine ⟨564742911623176425341971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 752990548830901900455961 564742911623176425341971)
                  ·
                    refine ⟨847114367434764638012957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 564742911623176425341971 847114367434764638012957)
                    ·
                      refine ⟨317667887788036739254859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 847114367434764638012957 317667887788036739254859)
                      ·
                        rfl

theorem cell23_618656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_618656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618656 prefixEnd_618656 := by exact prefixLift 618656
  have htrace : WordTrace (prefixWord ++ tailWord_618656) baseStart_618656 baseEnd_618656 := by
    simpa [prefixWord, tailWord_618656, baseEnd_618656] using wordTrace_append hprefix tailTrace_618656
  have hstable : (prefixWord ++ tailWord_618656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618656).length < 2 ^ (prefixWord ++ tailWord_618656).sum := by decide
  have hdescent : baseEnd_618656 < baseStart_618656 := by decide
  rcases family_descends (prefixWord ++ tailWord_618656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618657 : List Nat := [1, 2, 3, 3, 1, 4, 2, 2, 1, 2, 2]
def baseStart_618657 : Nat := 118140960795 + 618657 * 2 ^ 59
def prefixEnd_618657 : Nat := 4983230072969 + 3 ^ 40 * 618657 * 2
def baseEnd_618657 : Nat := 317668401268691235342355

theorem tailTrace_618657 : CollatzResearch.WordTrace tailWord_618657 prefixEnd_618657 317668401268691235342355 := by
  unfold tailWord_618657
  simp only [CollatzResearch.WordTrace]
  refine ⟨22564274519718822048830225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15042849679812548032553483 22564274519718822048830225)
  ·
    refine ⟨16923205889789116536622669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22564274519718822048830225 16923205889789116536622669)
    ·
      refine ⟨6346202208670918701233501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16923205889789116536622669 6346202208670918701233501)
      ·
        refine ⟨2379825828251594512962563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6346202208670918701233501 2379825828251594512962563)
        ·
          refine ⟨3569738742377391769443845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379825828251594512962563 3569738742377391769443845)
          ·
            refine ⟨669326014195760956770721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3569738742377391769443845 669326014195760956770721)
            ·
              refine ⟨501994510646820717578041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 669326014195760956770721 501994510646820717578041)
              ·
                refine ⟨376495882985115538183531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501994510646820717578041 376495882985115538183531)
                ·
                  refine ⟨564743824477673307275297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 376495882985115538183531 564743824477673307275297)
                  ·
                    refine ⟨423557868358254980456473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 564743824477673307275297 423557868358254980456473)
                    ·
                      refine ⟨317668401268691235342355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 423557868358254980456473 317668401268691235342355)
                      ·
                        rfl

theorem cell23_618657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_618657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618657 prefixEnd_618657 := by exact prefixLift 618657
  have htrace : WordTrace (prefixWord ++ tailWord_618657) baseStart_618657 baseEnd_618657 := by
    simpa [prefixWord, tailWord_618657, baseEnd_618657] using wordTrace_append hprefix tailTrace_618657
  have hstable : (prefixWord ++ tailWord_618657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618657).length < 2 ^ (prefixWord ++ tailWord_618657).sum := by decide
  have hdescent : baseEnd_618657 < baseStart_618657 := by decide
  rcases family_descends (prefixWord ++ tailWord_618657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618682 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_618682 : Nat := 118140960795 + 618682 * 2 ^ 59
def prefixEnd_618682 : Nat := 4983230072969 + 3 ^ 40 * 618682 * 2
def baseEnd_618682 : Nat := 317681238285053637529739

theorem tailTrace_618682 : CollatzResearch.WordTrace tailWord_618682 prefixEnd_618682 317681238285053637529739 := by
  unfold tailWord_618682
  simp only [CollatzResearch.WordTrace]
  refine ⟨5641296586157062829622575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15043457563085500878993533 5641296586157062829622575)
  ·
    refine ⟨8461944879235594244433863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5641296586157062829622575 8461944879235594244433863)
    ·
      refine ⟨12692917318853391366650795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8461944879235594244433863 12692917318853391366650795)
      ·
        refine ⟨19039375978280087049976193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12692917318853391366650795 19039375978280087049976193)
        ·
          refine ⟨14279531983710065287482145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19039375978280087049976193 14279531983710065287482145)
          ·
            refine ⟨10709648987782548965611609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14279531983710065287482145 10709648987782548965611609)
            ·
              refine ⟨8032236740836911724208707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10709648987782548965611609 8032236740836911724208707)
              ·
                refine ⟨12048355111255367586313061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8032236740836911724208707 12048355111255367586313061)
                ·
                  refine ⟨2259066583360381422433699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12048355111255367586313061 2259066583360381422433699)
                  ·
                    refine ⟨3388599875040572133650549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2259066583360381422433699 3388599875040572133650549)
                    ·
                      refine ⟨317681238285053637529739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3388599875040572133650549 317681238285053637529739)
                      ·
                        rfl

theorem cell23_618682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_618682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618682 prefixEnd_618682 := by exact prefixLift 618682
  have htrace : WordTrace (prefixWord ++ tailWord_618682) baseStart_618682 baseEnd_618682 := by
    simpa [prefixWord, tailWord_618682, baseEnd_618682] using wordTrace_append hprefix tailTrace_618682
  have hstable : (prefixWord ++ tailWord_618682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618682).length < 2 ^ (prefixWord ++ tailWord_618682).sum := by decide
  have hdescent : baseEnd_618682 < baseStart_618682 := by decide
  rcases family_descends (prefixWord ++ tailWord_618682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618696 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 4, 2, 2]
def baseStart_618696 : Nat := 118140960795 + 618696 * 2 ^ 59
def prefixEnd_618696 : Nat := 4983230072969 + 3 ^ 40 * 618696 * 2
def baseEnd_618696 : Nat := 317688427014216582754675

theorem tailTrace_618696 : CollatzResearch.WordTrace tailWord_618696 prefixEnd_618696 317688427014216582754675 := by
  unfold tailWord_618696
  simp only [CollatzResearch.WordTrace]
  refine ⟨11282848483288765854749971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15043797977718354472999961 11282848483288765854749971)
  ·
    refine ⟨16924272724933148782124957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11282848483288765854749971 16924272724933148782124957)
    ·
      refine ⟨6346602271849930793296859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16924272724933148782124957 6346602271849930793296859)
      ·
        refine ⟨9519903407774896189945289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6346602271849930793296859 9519903407774896189945289)
        ·
          refine ⟨7139927555831172142458967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9519903407774896189945289 7139927555831172142458967)
          ·
            refine ⟨10709891333746758213688451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7139927555831172142458967 10709891333746758213688451)
            ·
              refine ⟨16064837000620137320532677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10709891333746758213688451 16064837000620137320532677)
              ·
                refine ⟨3012156937616275747599877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16064837000620137320532677 3012156937616275747599877)
                ·
                  refine ⟨564779425803051702674977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3012156937616275747599877 564779425803051702674977)
                  ·
                    refine ⟨423584569352288777006233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 564779425803051702674977 423584569352288777006233)
                    ·
                      refine ⟨317688427014216582754675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 423584569352288777006233 317688427014216582754675)
                      ·
                        rfl

theorem cell23_618696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_618696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618696 prefixEnd_618696 := by exact prefixLift 618696
  have htrace : WordTrace (prefixWord ++ tailWord_618696) baseStart_618696 baseEnd_618696 := by
    simpa [prefixWord, tailWord_618696, baseEnd_618696] using wordTrace_append hprefix tailTrace_618696
  have hstable : (prefixWord ++ tailWord_618696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618696).length < 2 ^ (prefixWord ++ tailWord_618696).sum := by decide
  have hdescent : baseEnd_618696 < baseStart_618696 := by decide
  rcases family_descends (prefixWord ++ tailWord_618696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618700 : List Nat := [2, 2, 1, 6, 1, 1, 1, 3, 1, 3, 2]
def baseStart_618700 : Nat := 118140960795 + 618700 * 2 ^ 59
def prefixEnd_618700 : Nat := 4983230072969 + 3 ^ 40 * 618700 * 2
def baseEnd_618700 : Nat := 317690480936834567104657

theorem tailTrace_618700 : CollatzResearch.WordTrace tailWord_618700 prefixEnd_618700 317690480936834567104657 := by
  unfold tailWord_618700
  simp only [CollatzResearch.WordTrace]
  refine ⟨11282921429281520196322777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15043895239042026928430369 11282921429281520196322777)
  ·
    refine ⟨8462191071961140147242083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11282921429281520196322777 8462191071961140147242083)
    ·
      refine ⟨12693286607941710220863125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8462191071961140147242083 12693286607941710220863125)
      ·
        refine ⟨594997809747267666602959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12693286607941710220863125 594997809747267666602959)
        ·
          refine ⟨892496714620901499904439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594997809747267666602959 892496714620901499904439)
          ·
            refine ⟨1338745071931352249856659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892496714620901499904439 1338745071931352249856659)
            ·
              refine ⟨2008117607897028374784989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338745071931352249856659 2008117607897028374784989)
              ·
                refine ⟨753044102961385640544371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2008117607897028374784989 753044102961385640544371)
                ·
                  refine ⟨1129566154442078460816557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753044102961385640544371 1129566154442078460816557)
                  ·
                    refine ⟨423587307915779422806209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1129566154442078460816557 423587307915779422806209)
                    ·
                      refine ⟨317690480936834567104657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 423587307915779422806209 317690480936834567104657)
                      ·
                        rfl

theorem cell23_618700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_618700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618700 prefixEnd_618700 := by exact prefixLift 618700
  have htrace : WordTrace (prefixWord ++ tailWord_618700) baseStart_618700 baseEnd_618700 := by
    simpa [prefixWord, tailWord_618700, baseEnd_618700] using wordTrace_append hprefix tailTrace_618700
  have hstable : (prefixWord ++ tailWord_618700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618700).length < 2 ^ (prefixWord ++ tailWord_618700).sum := by decide
  have hdescent : baseEnd_618700 < baseStart_618700 := by decide
  rcases family_descends (prefixWord ++ tailWord_618700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618713 : List Nat := [1, 2, 1, 2, 3, 1, 5, 2, 2, 2, 2]
def baseStart_618713 : Nat := 118140960795 + 618713 * 2 ^ 59
def prefixEnd_618713 : Nat := 4983230072969 + 3 ^ 40 * 618713 * 2
def baseEnd_618713 : Nat := 317697156185343016242097

theorem tailTrace_618713 : CollatzResearch.WordTrace tailWord_618713 prefixEnd_618713 317697156185343016242097 := by
  unfold tailWord_618713
  simp only [CollatzResearch.WordTrace]
  refine ⟨22566317007515943612868793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15044211338343962408579195 22566317007515943612868793)
  ·
    refine ⟨16924737755636957709651595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22566317007515943612868793 16924737755636957709651595)
    ·
      refine ⟨25387106633455436564477393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16924737755636957709651595 25387106633455436564477393)
      ·
        refine ⟨19040329975091577423358045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25387106633455436564477393 19040329975091577423358045)
        ·
          refine ⟨7140123740659341533759267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19040329975091577423358045 7140123740659341533759267)
          ·
            refine ⟨10710185610989012300638901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7140123740659341533759267 10710185610989012300638901)
            ·
              refine ⟨1004079901030219903184897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10710185610989012300638901 1004079901030219903184897)
              ·
                refine ⟨753059925772664927388673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004079901030219903184897 753059925772664927388673)
                ·
                  refine ⟨564794944329498695541505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 753059925772664927388673 564794944329498695541505)
                  ·
                    refine ⟨423596208247124021656129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 564794944329498695541505 423596208247124021656129)
                    ·
                      refine ⟨317697156185343016242097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 423596208247124021656129 317697156185343016242097)
                      ·
                        rfl

theorem cell23_618713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 2, 2].length) (baseStart_618713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618713 prefixEnd_618713 := by exact prefixLift 618713
  have htrace : WordTrace (prefixWord ++ tailWord_618713) baseStart_618713 baseEnd_618713 := by
    simpa [prefixWord, tailWord_618713, baseEnd_618713] using wordTrace_append hprefix tailTrace_618713
  have hstable : (prefixWord ++ tailWord_618713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618713).length < 2 ^ (prefixWord ++ tailWord_618713).sum := by decide
  have hdescent : baseEnd_618713 < baseStart_618713 := by decide
  rcases family_descends (prefixWord ++ tailWord_618713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618730 : List Nat := [3, 1, 3, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_618730 : Nat := 118140960795 + 618730 * 2 ^ 59
def prefixEnd_618730 : Nat := 4983230072969 + 3 ^ 40 * 618730 * 2
def baseEnd_618730 : Nat := 317705885356469449729519

theorem tailTrace_618730 : CollatzResearch.WordTrace tailWord_618730 prefixEnd_618730 317705885356469449729519 := by
  unfold tailWord_618730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5641734262113588879059411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15044624698969570344158429 5641734262113588879059411)
  ·
    refine ⟨8462601393170383318589117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5641734262113588879059411 8462601393170383318589117)
    ·
      refine ⟨3173475522438893744470919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8462601393170383318589117 3173475522438893744470919)
      ·
        refine ⟨4760213283658340616706379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3173475522438893744470919 4760213283658340616706379)
        ·
          refine ⟨7140319925487510925059569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4760213283658340616706379 7140319925487510925059569)
          ·
            refine ⟨5355239944115633193794677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7140319925487510925059569 5355239944115633193794677)
            ·
              refine ⟨502053744760840611918251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5355239944115633193794677 502053744760840611918251)
              ·
                refine ⟨753080617141260917877377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502053744760840611918251 753080617141260917877377)
                ·
                  refine ⟨564810462855945688408033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 753080617141260917877377 564810462855945688408033)
                  ·
                    refine ⟨423607847141959266306025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 564810462855945688408033 423607847141959266306025)
                    ·
                      refine ⟨317705885356469449729519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 423607847141959266306025 317705885356469449729519)
                      ·
                        rfl

theorem cell23_618730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_618730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618730 prefixEnd_618730 := by exact prefixLift 618730
  have htrace : WordTrace (prefixWord ++ tailWord_618730) baseStart_618730 baseEnd_618730 := by
    simpa [prefixWord, tailWord_618730, baseEnd_618730] using wordTrace_append hprefix tailTrace_618730
  have hstable : (prefixWord ++ tailWord_618730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618730).length < 2 ^ (prefixWord ++ tailWord_618730).sum := by decide
  have hdescent : baseEnd_618730 < baseStart_618730 := by decide
  rcases family_descends (prefixWord ++ tailWord_618730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618732 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 3, 7]
def baseStart_618732 : Nat := 118140960795 + 618732 * 2 ^ 59
def prefixEnd_618732 : Nat := 4983230072969 + 3 ^ 40 * 618732 * 2
def baseEnd_618732 : Nat := 105902304105926147301503

theorem tailTrace_618732 : CollatzResearch.WordTrace tailWord_618732 prefixEnd_618732 105902304105926147301503 := by
  unfold tailWord_618732
  simp only [CollatzResearch.WordTrace]
  refine ⟨11283504997223554928905225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15044673329631406571873633 11283504997223554928905225)
  ·
    refine ⟨8462628747917666196678919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11283504997223554928905225 8462628747917666196678919)
    ·
      refine ⟨12693943121876499295018379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8462628747917666196678919 12693943121876499295018379)
      ·
        refine ⟨19040914682814748942527569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12693943121876499295018379 19040914682814748942527569)
        ·
          refine ⟨14280686012111061706895677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19040914682814748942527569 14280686012111061706895677)
          ·
            refine ⟨5355257254541648140085879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14280686012111061706895677 5355257254541648140085879)
            ·
              refine ⟨8032885881812472210128819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5355257254541648140085879 8032885881812472210128819)
              ·
                refine ⟨12049328822718708315193229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8032885881812472210128819 12049328822718708315193229)
                ·
                  refine ⟨4518498308519515618197461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12049328822718708315193229 4518498308519515618197461)
                  ·
                    refine ⟨105902304105926147301503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4518498308519515618197461 105902304105926147301503)
                    ·
                      rfl

theorem cell23_618732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_618732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618732 prefixEnd_618732 := by exact prefixLift 618732
  have htrace : WordTrace (prefixWord ++ tailWord_618732) baseStart_618732 baseEnd_618732 := by
    simpa [prefixWord, tailWord_618732, baseEnd_618732] using wordTrace_append hprefix tailTrace_618732
  have hstable : (prefixWord ++ tailWord_618732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618732).length < 2 ^ (prefixWord ++ tailWord_618732).sum := by decide
  have hdescent : baseEnd_618732 < baseStart_618732 := by decide
  rcases family_descends (prefixWord ++ tailWord_618732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618769 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 4]
def baseStart_618769 : Nat := 118140960795 + 618769 * 2 ^ 59
def prefixEnd_618769 : Nat := 4983230072969 + 3 ^ 40 * 618769 * 2
def baseEnd_618769 : Nat := 317725911101994797141839

theorem tailTrace_618769 : CollatzResearch.WordTrace tailWord_618769 prefixEnd_618769 317725911101994797141839 := by
  unfold tailWord_618769
  simp only [CollatzResearch.WordTrace]
  refine ⟨22568359495313065176907361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15045572996875376784604907 22568359495313065176907361)
  ·
    refine ⟨16926269621484798882680521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22568359495313065176907361 16926269621484798882680521)
    ·
      refine ⟨12694702216113599162010391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16926269621484798882680521 12694702216113599162010391)
      ·
        refine ⟨19042053324170398743015587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12694702216113599162010391 19042053324170398743015587)
        ·
          refine ⟨28563079986255598114523381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19042053324170398743015587 28563079986255598114523381)
          ·
            refine ⟨2677788748711462323236567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28563079986255598114523381 2677788748711462323236567)
            ·
              refine ⟨4016683123067193484854851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2677788748711462323236567 4016683123067193484854851)
              ·
                refine ⟨6025024684600790227282277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4016683123067193484854851 6025024684600790227282277)
                ·
                  refine ⟨1129692128362648167615427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6025024684600790227282277 1129692128362648167615427)
                  ·
                    refine ⟨1694538192543972251423141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1129692128362648167615427 1694538192543972251423141)
                    ·
                      refine ⟨317725911101994797141839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1694538192543972251423141 317725911101994797141839)
                      ·
                        rfl

theorem cell23_618769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_618769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618769 prefixEnd_618769 := by exact prefixLift 618769
  have htrace : WordTrace (prefixWord ++ tailWord_618769) baseStart_618769 baseEnd_618769 := by
    simpa [prefixWord, tailWord_618769, baseEnd_618769] using wordTrace_append hprefix tailTrace_618769
  have hstable : (prefixWord ++ tailWord_618769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618769).length < 2 ^ (prefixWord ++ tailWord_618769).sum := by decide
  have hdescent : baseEnd_618769 < baseStart_618769 := by decide
  rcases family_descends (prefixWord ++ tailWord_618769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618839 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 5, 5]
def baseStart_618839 : Nat := 118140960795 + 618839 * 2 ^ 59
def prefixEnd_618839 : Nat := 4983230072969 + 3 ^ 40 * 618839 * 2
def baseEnd_618839 : Nat := 105920618249269841088839

theorem tailTrace_618839 : CollatzResearch.WordTrace tailWord_618839 prefixEnd_618839 105920618249269841088839 := by
  unfold tailWord_618839
  simp only [CollatzResearch.WordTrace]
  refine ⟨22570912605059467131955571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15047275070039644754637047 22570912605059467131955571)
  ·
    refine ⟨33856368907589200697933357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22570912605059467131955571 33856368907589200697933357)
    ·
      refine ⟨12696138340345950261725009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33856368907589200697933357 12696138340345950261725009)
      ·
        refine ⟨9522103755259462696293757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12696138340345950261725009 9522103755259462696293757)
        ·
          refine ⟨3570788908222298511110159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9522103755259462696293757 3570788908222298511110159)
          ·
            refine ⟨5356183362333447766665239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3570788908222298511110159 5356183362333447766665239)
            ·
              refine ⟨8034275043500171649997859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5356183362333447766665239 8034275043500171649997859)
              ·
                refine ⟨12051412565250257474996789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8034275043500171649997859 12051412565250257474996789)
                ·
                  refine ⟨1129819927992211638280949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12051412565250257474996789 1129819927992211638280949)
                  ·
                    refine ⟨105920618249269841088839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1129819927992211638280949 105920618249269841088839)
                    ·
                      rfl

theorem cell23_618839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_618839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618839 prefixEnd_618839 := by exact prefixLift 618839
  have htrace : WordTrace (prefixWord ++ tailWord_618839) baseStart_618839 baseEnd_618839 := by
    simpa [prefixWord, tailWord_618839, baseEnd_618839] using wordTrace_append hprefix tailTrace_618839
  have hstable : (prefixWord ++ tailWord_618839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618839).length < 2 ^ (prefixWord ++ tailWord_618839).sum := by decide
  have hdescent : baseEnd_618839 < baseStart_618839 := by decide
  rcases family_descends (prefixWord ++ tailWord_618839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618853 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 3, 1, 3]
def baseStart_618853 : Nat := 118140960795 + 618853 * 2 ^ 59
def prefixEnd_618853 : Nat := 4983230072969 + 3 ^ 40 * 618853 * 2
def baseEnd_618853 : Nat := 317769043476972468491453

theorem tailTrace_618853 : CollatzResearch.WordTrace tailWord_618853 prefixEnd_618853 317769043476972468491453 := by
  unfold tailWord_618853
  simp only [CollatzResearch.WordTrace]
  refine ⟨22571423227008747522965213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15047615484672498348643475 22571423227008747522965213)
  ·
    refine ⟨8464283710128280321111955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22571423227008747522965213 8464283710128280321111955)
    ·
      refine ⟨12696425565192420481667933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8464283710128280321111955 12696425565192420481667933)
      ·
        refine ⟨4761159586947157680625475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12696425565192420481667933 4761159586947157680625475)
        ·
          refine ⟨7141739380420736520938213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4761159586947157680625475 7141739380420736520938213)
          ·
            refine ⟨1339076133828888097675915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7141739380420736520938213 1339076133828888097675915)
            ·
              refine ⟨2008614200743332146513873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1339076133828888097675915 2008614200743332146513873)
              ·
                refine ⟨1506460650557499109885405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2008614200743332146513873 1506460650557499109885405)
                ·
                  refine ⟨564922743959062166207027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1506460650557499109885405 564922743959062166207027)
                  ·
                    refine ⟨847384115938593249310541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 564922743959062166207027 847384115938593249310541)
                    ·
                      refine ⟨317769043476972468491453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 847384115938593249310541 317769043476972468491453)
                      ·
                        rfl

theorem cell23_618853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_618853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618853 prefixEnd_618853 := by exact prefixLift 618853
  have htrace : WordTrace (prefixWord ++ tailWord_618853) baseStart_618853 baseEnd_618853 := by
    simpa [prefixWord, tailWord_618853, baseEnd_618853] using wordTrace_append hprefix tailTrace_618853
  have hstable : (prefixWord ++ tailWord_618853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618853).length < 2 ^ (prefixWord ++ tailWord_618853).sum := by decide
  have hdescent : baseEnd_618853 < baseStart_618853 := by decide
  rcases family_descends (prefixWord ++ tailWord_618853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618856 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 3, 5]
def baseStart_618856 : Nat := 118140960795 + 618856 * 2 ^ 59
def prefixEnd_618856 : Nat := 4983230072969 + 3 ^ 40 * 618856 * 2
def baseEnd_618856 : Nat := 105923527972978652251313

theorem tailTrace_618856 : CollatzResearch.WordTrace tailWord_618856 prefixEnd_618856 105923527972978652251313 := by
  unfold tailWord_618856
  simp only [CollatzResearch.WordTrace]
  refine ⟨11285766322998939517662211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15047688430665252690216281 11285766322998939517662211)
  ·
    refine ⟨16928649484498409276493317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11285766322998939517662211 16928649484498409276493317)
    ·
      refine ⟨3174121778343451739342497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16928649484498409276493317 3174121778343451739342497)
      ·
        refine ⟨2380591333757588804506873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3174121778343451739342497 2380591333757588804506873)
        ·
          refine ⟨1785443500318191603380155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2380591333757588804506873 1785443500318191603380155)
          ·
            refine ⟨2678165250477287405070233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785443500318191603380155 2678165250477287405070233)
            ·
              refine ⟨2008623937857965553802675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2678165250477287405070233 2008623937857965553802675)
              ·
                refine ⟨3012935906786948330704013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008623937857965553802675 3012935906786948330704013)
                ·
                  refine ⟨1129850965045105624014005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3012935906786948330704013 1129850965045105624014005)
                  ·
                    refine ⟨105923527972978652251313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1129850965045105624014005 105923527972978652251313)
                    ·
                      rfl

theorem cell23_618856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_618856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618856 prefixEnd_618856 := by exact prefixLift 618856
  have htrace : WordTrace (prefixWord ++ tailWord_618856) baseStart_618856 baseEnd_618856 := by
    simpa [prefixWord, tailWord_618856, baseEnd_618856] using wordTrace_append hprefix tailTrace_618856
  have hstable : (prefixWord ++ tailWord_618856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618856).length < 2 ^ (prefixWord ++ tailWord_618856).sum := by decide
  have hdescent : baseEnd_618856 < baseStart_618856 := by decide
  rcases family_descends (prefixWord ++ tailWord_618856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618906 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6]
def baseStart_618906 : Nat := 118140960795 + 618906 * 2 ^ 59
def prefixEnd_618906 : Nat := 4983230072969 + 3 ^ 40 * 618906 * 2
def baseEnd_618906 : Nat := 317796257951660761128709

theorem tailTrace_618906 : CollatzResearch.WordTrace tailWord_618906 prefixEnd_618906 317796257951660761128709 := by
  unfold tailWord_618906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5643339073954184393661143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15048904197211158383096381 5643339073954184393661143)
  ·
    refine ⟨8465008610931276590491715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5643339073954184393661143 8465008610931276590491715)
    ·
      refine ⟨12697512916396914885737573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8465008610931276590491715 12697512916396914885737573)
      ·
        refine ⟨2380783671824421541075795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12697512916396914885737573 2380783671824421541075795)
        ·
          refine ⟨3571175507736632311613693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2380783671824421541075795 3571175507736632311613693)
          ·
            refine ⟨1339190815401237116855135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3571175507736632311613693 1339190815401237116855135)
            ·
              refine ⟨2008786223101855675282703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1339190815401237116855135 2008786223101855675282703)
              ·
                refine ⟨3013179334652783512924055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008786223101855675282703 3013179334652783512924055)
                ·
                  refine ⟨4519769001979175269386083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013179334652783512924055 4519769001979175269386083)
                  ·
                    refine ⟨6779653502968762904079125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4519769001979175269386083 6779653502968762904079125)
                    ·
                      refine ⟨317796257951660761128709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6779653502968762904079125 317796257951660761128709)
                      ·
                        rfl

theorem cell23_618906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_618906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618906 prefixEnd_618906 := by exact prefixLift 618906
  have htrace : WordTrace (prefixWord ++ tailWord_618906) baseStart_618906 baseEnd_618906 := by
    simpa [prefixWord, tailWord_618906, baseEnd_618906] using wordTrace_append hprefix tailTrace_618906
  have hstable : (prefixWord ++ tailWord_618906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618906).length < 2 ^ (prefixWord ++ tailWord_618906).sum := by decide
  have hdescent : baseEnd_618906 < baseStart_618906 := by decide
  rcases family_descends (prefixWord ++ tailWord_618906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618910 : List Nat := [4, 3, 1, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_618910 : Nat := 118140960795 + 618910 * 2 ^ 59
def prefixEnd_618910 : Nat := 4983230072969 + 3 ^ 40 * 618910 * 2
def baseEnd_618910 : Nat := 317798311874278745478691

theorem tailTrace_618910 : CollatzResearch.WordTrace tailWord_618910 prefixEnd_618910 317798311874278745478691 := by
  unfold tailWord_618910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2821687773475280782223773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15049001458534830838526789 2821687773475280782223773)
  ·
    refine ⟨1058132915053230293333915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2821687773475280782223773 1058132915053230293333915)
    ·
      refine ⟨1587199372579845440000873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1058132915053230293333915 1587199372579845440000873)
      ·
        refine ⟨1190399529434884080000655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1587199372579845440000873 1190399529434884080000655)
        ·
          refine ⟨1785599294152326120000983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1190399529434884080000655 1785599294152326120000983)
          ·
            refine ⟨2678398941228489180001475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785599294152326120000983 2678398941228489180001475)
            ·
              refine ⟨4017598411842733770002213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2678398941228489180001475 4017598411842733770002213)
              ·
                refine ⟨753299702220512581875415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4017598411842733770002213 753299702220512581875415)
                ·
                  refine ⟨1129949553330768872813123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753299702220512581875415 1129949553330768872813123)
                  ·
                    refine ⟨1694924329996153309219685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1129949553330768872813123 1694924329996153309219685)
                    ·
                      refine ⟨317798311874278745478691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1694924329996153309219685 317798311874278745478691)
                      ·
                        rfl

theorem cell23_618910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_618910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618910 prefixEnd_618910 := by exact prefixLift 618910
  have htrace : WordTrace (prefixWord ++ tailWord_618910) baseStart_618910 baseEnd_618910 := by
    simpa [prefixWord, tailWord_618910, baseEnd_618910] using wordTrace_append hprefix tailTrace_618910
  have hstable : (prefixWord ++ tailWord_618910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618910).length < 2 ^ (prefixWord ++ tailWord_618910).sum := by decide
  have hdescent : baseEnd_618910 < baseStart_618910 := by decide
  rcases family_descends (prefixWord ++ tailWord_618910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618916 : List Nat := [2, 3, 1, 2, 1, 1, 6, 7]
def baseStart_618916 : Nat := 118140960795 + 618916 * 2 ^ 59
def prefixEnd_618916 : Nat := 4983230072969 + 3 ^ 40 * 618916 * 2
def baseEnd_618916 : Nat := 11770421954007619333469

theorem tailTrace_618916 : CollatzResearch.WordTrace tailWord_618916 prefixEnd_618916 11770421954007619333469 := by
  unfold tailWord_618916
  simp only [CollatzResearch.WordTrace]
  refine ⟨11286860512890254641254301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15049147350520339521672401 11286860512890254641254301)
  ·
    refine ⟨4232572692333845490470363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11286860512890254641254301 4232572692333845490470363)
    ·
      refine ⟨6348859038500768235705545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4232572692333845490470363 6348859038500768235705545)
      ·
        refine ⟨4761644278875576176779159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6348859038500768235705545 4761644278875576176779159)
        ·
          refine ⟨7142466418313364265168739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4761644278875576176779159 7142466418313364265168739)
          ·
            refine ⟨10713699627470046397753109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7142466418313364265168739 10713699627470046397753109)
            ·
              refine ⟨502204670037658424894677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10713699627470046397753109 502204670037658424894677)
              ·
                refine ⟨11770421954007619333469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 502204670037658424894677 11770421954007619333469)
                ·
                  rfl

theorem cell23_618916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 7].length) (baseStart_618916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618916 prefixEnd_618916 := by exact prefixLift 618916
  have htrace : WordTrace (prefixWord ++ tailWord_618916) baseStart_618916 baseEnd_618916 := by
    simpa [prefixWord, tailWord_618916, baseEnd_618916] using wordTrace_append hprefix tailTrace_618916
  have hstable : (prefixWord ++ tailWord_618916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618916).length < 2 ^ (prefixWord ++ tailWord_618916).sum := by decide
  have hdescent : baseEnd_618916 < baseStart_618916 := by decide
  rcases family_descends (prefixWord ++ tailWord_618916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618933 : List Nat := [1, 3, 3, 2, 4, 1, 9]
def baseStart_618933 : Nat := 118140960795 + 618933 * 2 ^ 59
def prefixEnd_618933 : Nat := 4983230072969 + 3 ^ 40 * 618933 * 2
def baseEnd_618933 : Nat := 3923581752213977228285

theorem tailTrace_618933 : CollatzResearch.WordTrace tailWord_618933 prefixEnd_618933 3923581752213977228285 := by
  unfold tailWord_618933
  simp only [CollatzResearch.WordTrace]
  refine ⟨22574341066718921185877453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15049560711145947457251635 22574341066718921185877453)
  ·
    refine ⟨8465377900019595444704045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22574341066718921185877453 8465377900019595444704045)
    ·
      refine ⟨3174516712507348291764017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8465377900019595444704045 3174516712507348291764017)
      ·
        refine ⟨2380887534380511218823013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3174516712507348291764017 2380887534380511218823013)
        ·
          refine ⟨446416412696345853529315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2380887534380511218823013 446416412696345853529315)
          ·
            refine ⟨669624619044518780293973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446416412696345853529315 669624619044518780293973)
            ·
              refine ⟨3923581752213977228285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 669624619044518780293973 3923581752213977228285)
              ·
                rfl

theorem cell23_618933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 9].length) (baseStart_618933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618933 prefixEnd_618933 := by exact prefixLift 618933
  have htrace : WordTrace (prefixWord ++ tailWord_618933) baseStart_618933 baseEnd_618933 := by
    simpa [prefixWord, tailWord_618933, baseEnd_618933] using wordTrace_append hprefix tailTrace_618933
  have hstable : (prefixWord ++ tailWord_618933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618933).length < 2 ^ (prefixWord ++ tailWord_618933).sum := by decide
  have hdescent : baseEnd_618933 < baseStart_618933 := by decide
  rcases family_descends (prefixWord ++ tailWord_618933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618959 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 1, 8]
def baseStart_618959 : Nat := 118140960795 + 618959 * 2 ^ 59
def prefixEnd_618959 : Nat := 4983230072969 + 3 ^ 40 * 618959 * 2
def baseEnd_618959 : Nat := 105941157475449684588655

theorem tailTrace_618959 : CollatzResearch.WordTrace tailWord_618959 prefixEnd_618959 105941157475449684588655 := by
  unfold tailWord_618959
  simp only [CollatzResearch.WordTrace]
  refine ⟨22575289364624727626323931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15050192909749818417549287 22575289364624727626323931)
  ·
    refine ⟨33862934046937091439485897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22575289364624727626323931 33862934046937091439485897)
    ·
      refine ⟨25397200535202818579614423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33862934046937091439485897 25397200535202818579614423)
      ·
        refine ⟨38095800802804227869421635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25397200535202818579614423 38095800802804227869421635)
        ·
          refine ⟨57143701204206341804132453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38095800802804227869421635 57143701204206341804132453)
          ·
            refine ⟨10714443975788689088274835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57143701204206341804132453 10714443975788689088274835)
            ·
              refine ⟨16071665963683033632412253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10714443975788689088274835 16071665963683033632412253)
              ·
                refine ⟨6026874736381137612154595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16071665963683033632412253 6026874736381137612154595)
                ·
                  refine ⟨9040312104571706418231893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6026874736381137612154595 9040312104571706418231893)
                  ·
                    refine ⟨105941157475449684588655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9040312104571706418231893 105941157475449684588655)
                    ·
                      rfl

theorem cell23_618959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_618959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_618959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_618959 prefixEnd_618959 := by exact prefixLift 618959
  have htrace : WordTrace (prefixWord ++ tailWord_618959) baseStart_618959 baseEnd_618959 := by
    simpa [prefixWord, tailWord_618959, baseEnd_618959] using wordTrace_append hprefix tailTrace_618959
  have hstable : (prefixWord ++ tailWord_618959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618959).length < 2 ^ (prefixWord ++ tailWord_618959).sum := by decide
  have hdescent : baseEnd_618959 < baseStart_618959 := by decide
  rcases family_descends (prefixWord ++ tailWord_618959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619010 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_619010 : Nat := 118140960795 + 619010 * 2 ^ 59
def prefixEnd_619010 : Nat := 4983230072969 + 3 ^ 40 * 619010 * 2
def baseEnd_619010 : Nat := 105949886646576118076077

theorem tailTrace_619010 : CollatzResearch.WordTrace tailWord_619010 prefixEnd_619010 105949886646576118076077 := by
  unfold tailWord_619010
  simp only [CollatzResearch.WordTrace]
  refine ⟨5644287371859990834107621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15051432991626642224286989 5644287371859990834107621)
  ·
    refine ⟨1058303882223748281395179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5644287371859990834107621 1058303882223748281395179)
    ·
      refine ⟨1587455823335622422092769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1058303882223748281395179 1587455823335622422092769)
      ·
        refine ⟨1190591867501716816569577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1587455823335622422092769 1190591867501716816569577)
        ·
          refine ⟨892943900626287612427183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1190591867501716816569577 892943900626287612427183)
          ·
            refine ⟨1339415850939431418640775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892943900626287612427183 1339415850939431418640775)
            ·
              refine ⟨2009123776409147127961163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1339415850939431418640775 2009123776409147127961163)
              ·
                refine ⟨3013685664613720691941745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009123776409147127961163 3013685664613720691941745)
                ·
                  refine ⟨2260264248460290518956309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3013685664613720691941745 2260264248460290518956309)
                  ·
                    refine ⟨105949886646576118076077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2260264248460290518956309 105949886646576118076077)
                    ·
                      rfl

theorem cell23_619010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_619010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619010 prefixEnd_619010 := by exact prefixLift 619010
  have htrace : WordTrace (prefixWord ++ tailWord_619010) baseStart_619010 baseEnd_619010 := by
    simpa [prefixWord, tailWord_619010, baseEnd_619010] using wordTrace_append hprefix tailTrace_619010
  have hstable : (prefixWord ++ tailWord_619010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619010).length < 2 ^ (prefixWord ++ tailWord_619010).sum := by decide
  have hdescent : baseEnd_619010 < baseStart_619010 := by decide
  rcases family_descends (prefixWord ++ tailWord_619010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619073 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_619073 : Nat := 118140960795 + 619073 * 2 ^ 59
def prefixEnd_619073 : Nat := 4983230072969 + 3 ^ 40 * 619073 * 2
def baseEnd_619073 : Nat := 317882009220961607740441

theorem tailTrace_619073 : CollatzResearch.WordTrace tailWord_619073 prefixEnd_619073 317882009220961607740441 := by
  unfold tailWord_619073
  simp only [CollatzResearch.WordTrace]
  refine ⟨22579447286211725095973873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15052964857474483397315915 22579447286211725095973873)
  ·
    refine ⟨16934585464658793821980405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22579447286211725095973873 16934585464658793821980405)
    ·
      refine ⟨1587617387311761920810663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16934585464658793821980405 1587617387311761920810663)
      ·
        refine ⟨2381426080967642881215995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587617387311761920810663 2381426080967642881215995)
        ·
          refine ⟨3572139121451464321823993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2381426080967642881215995 3572139121451464321823993)
          ·
            refine ⟨2679104341088598241367995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3572139121451464321823993 2679104341088598241367995)
            ·
              refine ⟨4018656511632897362051993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2679104341088598241367995 4018656511632897362051993)
              ·
                refine ⟨3013992383724673021538995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4018656511632897362051993 3013992383724673021538995)
                ·
                  refine ⟨4520988575587009532308493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013992383724673021538995 4520988575587009532308493)
                  ·
                    refine ⟨1695370715845128574615685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4520988575587009532308493 1695370715845128574615685)
                    ·
                      refine ⟨317882009220961607740441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1695370715845128574615685 317882009220961607740441)
                      ·
                        rfl

theorem cell23_619073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_619073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619073 prefixEnd_619073 := by exact prefixLift 619073
  have htrace : WordTrace (prefixWord ++ tailWord_619073) baseStart_619073 baseEnd_619073 := by
    simpa [prefixWord, tailWord_619073, baseEnd_619073] using wordTrace_append hprefix tailTrace_619073
  have hstable : (prefixWord ++ tailWord_619073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619073).length < 2 ^ (prefixWord ++ tailWord_619073).sum := by decide
  have hdescent : baseEnd_619073 < baseStart_619073 := by decide
  rcases family_descends (prefixWord ++ tailWord_619073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619083 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 3, 4]
def baseStart_619083 : Nat := 118140960795 + 619083 * 2 ^ 59
def prefixEnd_619083 : Nat := 4983230072969 + 3 ^ 40 * 619083 * 2
def baseEnd_619083 : Nat := 105962381342502189538465

theorem tailTrace_619083 : CollatzResearch.WordTrace tailWord_619083 prefixEnd_619083 105962381342502189538465 := by
  unfold tailWord_619083
  simp only [CollatzResearch.WordTrace]
  refine ⟨22579812016175496803837903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15053208010783664535891935 22579812016175496803837903)
  ·
    refine ⟨33869718024263245205756855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22579812016175496803837903 33869718024263245205756855)
    ·
      refine ⟨50804577036394867808635283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33869718024263245205756855 50804577036394867808635283)
      ·
        refine ⟨76206865554592301712952925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50804577036394867808635283 76206865554592301712952925)
        ·
          refine ⟨28577574582972113142357347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76206865554592301712952925 28577574582972113142357347)
          ·
            refine ⟨42866361874458169713536021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28577574582972113142357347 42866361874458169713536021)
            ·
              refine ⟨2009360712865226705322001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42866361874458169713536021 2009360712865226705322001)
              ·
                refine ⟨1507020534648920028991501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2009360712865226705322001 1507020534648920028991501)
                ·
                  refine ⟨565132700493345010871813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1507020534648920028991501 565132700493345010871813)
                  ·
                    refine ⟨105962381342502189538465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 565132700493345010871813 105962381342502189538465)
                    ·
                      rfl

theorem cell23_619083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 4].length) (baseStart_619083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619083 prefixEnd_619083 := by exact prefixLift 619083
  have htrace : WordTrace (prefixWord ++ tailWord_619083) baseStart_619083 baseEnd_619083 := by
    simpa [prefixWord, tailWord_619083, baseEnd_619083] using wordTrace_append hprefix tailTrace_619083
  have hstable : (prefixWord ++ tailWord_619083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619083).length < 2 ^ (prefixWord ++ tailWord_619083).sum := by decide
  have hdescent : baseEnd_619083 < baseStart_619083 := by decide
  rcases family_descends (prefixWord ++ tailWord_619083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619093 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_619093 : Nat := 118140960795 + 619093 * 2 ^ 59
def prefixEnd_619093 : Nat := 4983230072969 + 3 ^ 40 * 619093 * 2
def baseEnd_619093 : Nat := 317892278834051529490349

theorem tailTrace_619093 : CollatzResearch.WordTrace tailWord_619093 prefixEnd_619093 317892278834051529490349 := by
  unfold tailWord_619093
  simp only [CollatzResearch.WordTrace]
  refine ⟨22580176746139268511701933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15053451164092845674467955 22580176746139268511701933)
  ·
    refine ⟨8467566279802225691888225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22580176746139268511701933 8467566279802225691888225)
    ·
      refine ⟨6350674709851669268916169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8467566279802225691888225 6350674709851669268916169)
      ·
        refine ⟨4763006032388751951687127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6350674709851669268916169 4763006032388751951687127)
        ·
          refine ⟨7144509048583127927530691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4763006032388751951687127 7144509048583127927530691)
          ·
            refine ⟨10716763572874691891296037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7144509048583127927530691 10716763572874691891296037)
            ·
              refine ⟨2009393169914004729618007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10716763572874691891296037 2009393169914004729618007)
              ·
                refine ⟨3014089754871007094427011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009393169914004729618007 3014089754871007094427011)
                ·
                  refine ⟨4521134632306510641640517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3014089754871007094427011 4521134632306510641640517)
                  ·
                    refine ⟨847712743557470745307597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4521134632306510641640517 847712743557470745307597)
                    ·
                      refine ⟨317892278834051529490349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 847712743557470745307597 317892278834051529490349)
                      ·
                        rfl

theorem cell23_619093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_619093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619093 prefixEnd_619093 := by exact prefixLift 619093
  have htrace : WordTrace (prefixWord ++ tailWord_619093) baseStart_619093 baseEnd_619093 := by
    simpa [prefixWord, tailWord_619093, baseEnd_619093] using wordTrace_append hprefix tailTrace_619093
  have hstable : (prefixWord ++ tailWord_619093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619093).length < 2 ^ (prefixWord ++ tailWord_619093).sum := by decide
  have hdescent : baseEnd_619093 < baseStart_619093 := by decide
  rcases family_descends (prefixWord ++ tailWord_619093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619096 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 8]
def baseStart_619096 : Nat := 118140960795 + 619096 * 2 ^ 59
def prefixEnd_619096 : Nat := 4983230072969 + 3 ^ 40 * 619096 * 2
def baseEnd_619096 : Nat := 35321535475112779750315

theorem tailTrace_619096 : CollatzResearch.WordTrace tailWord_619096 prefixEnd_619096 35321535475112779750315 := by
  unfold tailWord_619096
  simp only [CollatzResearch.WordTrace]
  refine ⟨11290143082564200012030571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15053524110085600016040761 11290143082564200012030571)
  ·
    refine ⟨16935214623846300018045857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11290143082564200012030571 16935214623846300018045857)
    ·
      refine ⟨12701410967884725013534393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16935214623846300018045857 12701410967884725013534393)
      ·
        refine ⟨9526058225913543760150795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12701410967884725013534393 9526058225913543760150795)
        ·
          refine ⟨14289087338870315640226193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9526058225913543760150795 14289087338870315640226193)
          ·
            refine ⟨10716815504152736730169645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14289087338870315640226193 10716815504152736730169645)
            ·
              refine ⟨4018805814057276273813617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10716815504152736730169645 4018805814057276273813617)
              ·
                refine ⟨3014104360542957205360213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4018805814057276273813617 3014104360542957205360213)
                ·
                  refine ⟨35321535475112779750315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3014104360542957205360213 35321535475112779750315)
                  ·
                    rfl

theorem cell23_619096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 8].length) (baseStart_619096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619096 prefixEnd_619096 := by exact prefixLift 619096
  have htrace : WordTrace (prefixWord ++ tailWord_619096) baseStart_619096 baseEnd_619096 := by
    simpa [prefixWord, tailWord_619096, baseEnd_619096] using wordTrace_append hprefix tailTrace_619096
  have hstable : (prefixWord ++ tailWord_619096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619096).length < 2 ^ (prefixWord ++ tailWord_619096).sum := by decide
  have hdescent : baseEnd_619096 < baseStart_619096 := by decide
  rcases family_descends (prefixWord ++ tailWord_619096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619116 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_619116 : Nat := 118140960795 + 619116 * 2 ^ 59
def prefixEnd_619116 : Nat := 4983230072969 + 3 ^ 40 * 619116 * 2
def baseEnd_619116 : Nat := 317904088889104939502743

theorem tailTrace_619116 : CollatzResearch.WordTrace tailWord_619116 prefixEnd_619116 317904088889104939502743 := by
  unfold tailWord_619116
  simp only [CollatzResearch.WordTrace]
  refine ⟨11290507812527971719894601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15054010416703962293192801 11290507812527971719894601)
  ·
    refine ⟨8467880859395978789920951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11290507812527971719894601 8467880859395978789920951)
    ·
      refine ⟨12701821289093968184881427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8467880859395978789920951 12701821289093968184881427)
      ·
        refine ⟨19052731933640952277322141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12701821289093968184881427 19052731933640952277322141)
        ·
          refine ⟨7144774475115357103995803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19052731933640952277322141 7144774475115357103995803)
          ·
            refine ⟨10717161712673035655993705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7144774475115357103995803 10717161712673035655993705)
            ·
              refine ⟨8037871284504776741995279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10717161712673035655993705 8037871284504776741995279)
              ·
                refine ⟨12056806926757165112992919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8037871284504776741995279 12056806926757165112992919)
                ·
                  refine ⟨18085210390135747669489379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12056806926757165112992919 18085210390135747669489379)
                  ·
                    refine ⟨27127815585203621504234069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18085210390135747669489379 27127815585203621504234069)
                    ·
                      refine ⟨317904088889104939502743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 27127815585203621504234069 317904088889104939502743)
                      ·
                        rfl

theorem cell23_619116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_619116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619116 prefixEnd_619116 := by exact prefixLift 619116
  have htrace : WordTrace (prefixWord ++ tailWord_619116) baseStart_619116 baseEnd_619116 := by
    simpa [prefixWord, tailWord_619116, baseEnd_619116] using wordTrace_append hprefix tailTrace_619116
  have hstable : (prefixWord ++ tailWord_619116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619116).length < 2 ^ (prefixWord ++ tailWord_619116).sum := by decide
  have hdescent : baseEnd_619116 < baseStart_619116 := by decide
  rcases family_descends (prefixWord ++ tailWord_619116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619117 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_619117 : Nat := 118140960795 + 619117 * 2 ^ 59
def prefixEnd_619117 : Nat := 4983230072969 + 3 ^ 40 * 619117 * 2
def baseEnd_619117 : Nat := 105968200789919811863413

theorem tailTrace_619117 : CollatzResearch.WordTrace tailWord_619117 prefixEnd_619117 105968200789919811863413 := by
  unfold tailWord_619117
  simp only [CollatzResearch.WordTrace]
  refine ⟨22581052098052320610575605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15054034732034880407050403 22581052098052320610575605)
  ·
    refine ⟨2116973634192405057241463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22581052098052320610575605 2116973634192405057241463)
    ·
      refine ⟨3175460451288607585862195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2116973634192405057241463 3175460451288607585862195)
      ·
        refine ⟨4763190676932911378793293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3175460451288607585862195 4763190676932911378793293)
        ·
          refine ⟨1786196503849841767047485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4763190676932911378793293 1786196503849841767047485)
          ·
            refine ⟨669823688943690662642807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1786196503849841767047485 669823688943690662642807)
            ·
              refine ⟨1004735533415535993964211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669823688943690662642807 1004735533415535993964211)
              ·
                refine ⟨1507103300123303990946317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004735533415535993964211 1507103300123303990946317)
                ·
                  refine ⟨565163737546238996604869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1507103300123303990946317 565163737546238996604869)
                  ·
                    refine ⟨105968200789919811863413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 565163737546238996604869 105968200789919811863413)
                    ·
                      rfl

theorem cell23_619117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_619117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619117 prefixEnd_619117 := by exact prefixLift 619117
  have htrace : WordTrace (prefixWord ++ tailWord_619117) baseStart_619117 baseEnd_619117 := by
    simpa [prefixWord, tailWord_619117, baseEnd_619117] using wordTrace_append hprefix tailTrace_619117
  have hstable : (prefixWord ++ tailWord_619117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619117).length < 2 ^ (prefixWord ++ tailWord_619117).sum := by decide
  have hdescent : baseEnd_619117 < baseStart_619117 := by decide
  rcases family_descends (prefixWord ++ tailWord_619117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619143 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 3, 5]
def baseStart_619143 : Nat := 118140960795 + 619143 * 2 ^ 59
def prefixEnd_619143 : Nat := 4983230072969 + 3 ^ 40 * 619143 * 2
def baseEnd_619143 : Nat := 105972650955592111288373

theorem tailTrace_619143 : CollatzResearch.WordTrace tailWord_619143 prefixEnd_619143 105972650955592111288373 := by
  unfold tailWord_619143
  simp only [CollatzResearch.WordTrace]
  refine ⟨22582000395958127051022083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15054666930638751367348055 22582000395958127051022083)
  ·
    refine ⟨33873000593937190576533125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22582000395958127051022083 33873000593937190576533125)
    ·
      refine ⟨6351187611363223233099961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33873000593937190576533125 6351187611363223233099961)
      ·
        refine ⟨4763390708522417424824971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6351187611363223233099961 4763390708522417424824971)
        ·
          refine ⟨7145086062783626137237457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4763390708522417424824971 7145086062783626137237457)
          ·
            refine ⟨5358814547087719602928093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7145086062783626137237457 5358814547087719602928093)
            ·
              refine ⟨2009555455157894851098035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5358814547087719602928093 2009555455157894851098035)
              ·
                refine ⟨3014333182736842276647053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009555455157894851098035 3014333182736842276647053)
                ·
                  refine ⟨1130374943526315853742645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3014333182736842276647053 1130374943526315853742645)
                  ·
                    refine ⟨105972650955592111288373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1130374943526315853742645 105972650955592111288373)
                    ·
                      rfl

theorem cell23_619143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_619143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619143 prefixEnd_619143 := by exact prefixLift 619143
  have htrace : WordTrace (prefixWord ++ tailWord_619143) baseStart_619143 baseEnd_619143 := by
    simpa [prefixWord, tailWord_619143, baseEnd_619143] using wordTrace_append hprefix tailTrace_619143
  have hstable : (prefixWord ++ tailWord_619143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619143).length < 2 ^ (prefixWord ++ tailWord_619143).sum := by decide
  have hdescent : baseEnd_619143 < baseStart_619143 := by decide
  rcases family_descends (prefixWord ++ tailWord_619143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619197 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 5, 2, 2]
def baseStart_619197 : Nat := 118140960795 + 619197 * 2 ^ 59
def prefixEnd_619197 : Nat := 4983230072969 + 3 ^ 40 * 619197 * 2
def baseEnd_619197 : Nat := 317945680822119122589871

theorem tailTrace_619197 : CollatzResearch.WordTrace tailWord_619197 prefixEnd_619197 317945680822119122589871 := by
  unfold tailWord_619197
  simp only [CollatzResearch.WordTrace]
  refine ⟨22583969937762494273487845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15055979958508329515658563 22583969937762494273487845)
  ·
    refine ⟨4234494363330467676278971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22583969937762494273487845 4234494363330467676278971)
    ·
      refine ⟨6351741544995701514418457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4234494363330467676278971 6351741544995701514418457)
      ·
        refine ⟨4763806158746776135813843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6351741544995701514418457 4763806158746776135813843)
        ·
          refine ⟨7145709238120164203720765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4763806158746776135813843 7145709238120164203720765)
          ·
            refine ⟨2679640964295061576395287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7145709238120164203720765 2679640964295061576395287)
            ·
              refine ⟨4019461446442592364592931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2679640964295061576395287 4019461446442592364592931)
              ·
                refine ⟨6029192169663888546889397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019461446442592364592931 6029192169663888546889397)
                ·
                  refine ⟨565236765905989551270881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6029192169663888546889397 565236765905989551270881)
                  ·
                    refine ⟨423927574429492163453161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 565236765905989551270881 423927574429492163453161)
                    ·
                      refine ⟨317945680822119122589871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 423927574429492163453161 317945680822119122589871)
                      ·
                        rfl

theorem cell23_619197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_619197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619197 prefixEnd_619197 := by exact prefixLift 619197
  have htrace : WordTrace (prefixWord ++ tailWord_619197) baseStart_619197 baseEnd_619197 := by
    simpa [prefixWord, tailWord_619197, baseEnd_619197] using wordTrace_append hprefix tailTrace_619197
  have hstable : (prefixWord ++ tailWord_619197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619197).length < 2 ^ (prefixWord ++ tailWord_619197).sum := by decide
  have hdescent : baseEnd_619197 < baseStart_619197 := by decide
  rcases family_descends (prefixWord ++ tailWord_619197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619200 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 3]
def baseStart_619200 : Nat := 118140960795 + 619200 * 2 ^ 59
def prefixEnd_619200 : Nat := 4983230072969 + 3 ^ 40 * 619200 * 2
def baseEnd_619200 : Nat := 317947221264082610852357

theorem tailTrace_619200 : CollatzResearch.WordTrace tailWord_619200 prefixEnd_619200 317947221264082610852357 := by
  unfold tailWord_619200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11292039678375812892923527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15056052904501083857231369 11292039678375812892923527)
  ·
    refine ⟨16938059517563719339385291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11292039678375812892923527 16938059517563719339385291)
    ·
      refine ⟨25407089276345579009077937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16938059517563719339385291 25407089276345579009077937)
      ·
        refine ⟨19055316957259184256808453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25407089276345579009077937 19055316957259184256808453)
        ·
          refine ⟨3572871929486097048151585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19055316957259184256808453 3572871929486097048151585)
          ·
            refine ⟨2679653947114572786113689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3572871929486097048151585 2679653947114572786113689)
            ·
              refine ⟨2009740460335929589585267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2679653947114572786113689 2009740460335929589585267)
              ·
                refine ⟨3014610690503894384377901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009740460335929589585267 3014610690503894384377901)
                ·
                  refine ⟨1130479008938960394141713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3014610690503894384377901 1130479008938960394141713)
                  ·
                    refine ⟨847859256704220295606285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1130479008938960394141713 847859256704220295606285)
                    ·
                      refine ⟨317947221264082610852357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 847859256704220295606285 317947221264082610852357)
                      ·
                        rfl

theorem cell23_619200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_619200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619200 prefixEnd_619200 := by exact prefixLift 619200
  have htrace : WordTrace (prefixWord ++ tailWord_619200) baseStart_619200 baseEnd_619200 := by
    simpa [prefixWord, tailWord_619200, baseEnd_619200] using wordTrace_append hprefix tailTrace_619200
  have hstable : (prefixWord ++ tailWord_619200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619200).length < 2 ^ (prefixWord ++ tailWord_619200).sum := by decide
  have hdescent : baseEnd_619200 < baseStart_619200 := by decide
  rcases family_descends (prefixWord ++ tailWord_619200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619210 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_619210 : Nat := 118140960795 + 619210 * 2 ^ 59
def prefixEnd_619210 : Nat := 4983230072969 + 3 ^ 40 * 619210 * 2
def baseEnd_619210 : Nat := 317952356070627571727311

theorem tailTrace_619210 : CollatzResearch.WordTrace tailWord_619210 prefixEnd_619210 317952356070627571727311 := by
  unfold tailWord_619210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5646111021678849373427771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15056296057810264995807389 5646111021678849373427771)
  ·
    refine ⟨8469166532518274060141657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5646111021678849373427771 8469166532518274060141657)
    ·
      refine ⟨6351874899388705545106243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8469166532518274060141657 6351874899388705545106243)
      ·
        refine ⟨9527812349083058317659365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6351874899388705545106243 9527812349083058317659365)
        ·
          refine ⟨1786464815453073434561131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9527812349083058317659365 1786464815453073434561131)
          ·
            refine ⟨2679697223179610151841697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786464815453073434561131 2679697223179610151841697)
            ·
              refine ⟨2009772917384707613881273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2679697223179610151841697 2009772917384707613881273)
              ·
                refine ⟨1507329688038530710410955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2009772917384707613881273 1507329688038530710410955)
                ·
                  refine ⟨2260994532057796065616433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1507329688038530710410955 2260994532057796065616433)
                  ·
                    refine ⟨1695745899043347049212325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2260994532057796065616433 1695745899043347049212325)
                    ·
                      refine ⟨317952356070627571727311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1695745899043347049212325 317952356070627571727311)
                      ·
                        rfl

theorem cell23_619210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_619210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619210 prefixEnd_619210 := by exact prefixLift 619210
  have htrace : WordTrace (prefixWord ++ tailWord_619210) baseStart_619210 baseEnd_619210 := by
    simpa [prefixWord, tailWord_619210, baseEnd_619210] using wordTrace_append hprefix tailTrace_619210
  have hstable : (prefixWord ++ tailWord_619210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619210).length < 2 ^ (prefixWord ++ tailWord_619210).sum := by decide
  have hdescent : baseEnd_619210 < baseStart_619210 := by decide
  rcases family_descends (prefixWord ++ tailWord_619210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619214 : List Nat := [4, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4]
def baseStart_619214 : Nat := 118140960795 + 619214 * 2 ^ 59
def prefixEnd_619214 : Nat := 4983230072969 + 3 ^ 40 * 619214 * 2
def baseEnd_619214 : Nat := 317954409993245556077293

theorem tailTrace_619214 : CollatzResearch.WordTrace tailWord_619214 prefixEnd_619214 317954409993245556077293 := by
  unfold tailWord_619214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2823073747337613272107087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15056393319133937451237797 2823073747337613272107087)
  ·
    refine ⟨4234610621006419908160631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2823073747337613272107087 4234610621006419908160631)
    ·
      refine ⟨6351915931509629862240947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4234610621006419908160631 6351915931509629862240947)
      ·
        refine ⟨9527873897264444793361421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6351915931509629862240947 9527873897264444793361421)
        ·
          refine ⟨3572952711474166797510533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9527873897264444793361421 3572952711474166797510533)
          ·
            refine ⟨669928633401406274533225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3572952711474166797510533 669928633401406274533225)
            ·
              refine ⟨502446475051054705899919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 669928633401406274533225 502446475051054705899919)
              ·
                refine ⟨753669712576582058849879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502446475051054705899919 753669712576582058849879)
                ·
                  refine ⟨1130504568864873088274819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753669712576582058849879 1130504568864873088274819)
                  ·
                    refine ⟨1695756853297309632412229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1130504568864873088274819 1695756853297309632412229)
                    ·
                      refine ⟨317954409993245556077293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1695756853297309632412229 317954409993245556077293)
                      ·
                        rfl

theorem cell23_619214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_619214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619214 prefixEnd_619214 := by exact prefixLift 619214
  have htrace : WordTrace (prefixWord ++ tailWord_619214) baseStart_619214 baseEnd_619214 := by
    simpa [prefixWord, tailWord_619214, baseEnd_619214] using wordTrace_append hprefix tailTrace_619214
  have hstable : (prefixWord ++ tailWord_619214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619214).length < 2 ^ (prefixWord ++ tailWord_619214).sum := by decide
  have hdescent : baseEnd_619214 < baseStart_619214 := by decide
  rcases family_descends (prefixWord ++ tailWord_619214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619220 : List Nat := [2, 4, 1, 3, 2, 1, 10]
def baseStart_619220 : Nat := 118140960795 + 619220 * 2 ^ 59
def prefixEnd_619220 : Nat := 4983230072969 + 3 ^ 40 * 619220 * 2
def baseEnd_619220 : Nat := 3925401121940401637065

theorem tailTrace_619220 : CollatzResearch.WordTrace tailWord_619220 prefixEnd_619220 3925401121940401637065 := by
  unfold tailWord_619220
  simp only [CollatzResearch.WordTrace]
  refine ⟨11292404408339584600787557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15056539211119446134383409 11292404408339584600787557)
  ·
    refine ⟨2117325826563672112647667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11292404408339584600787557 2117325826563672112647667)
    ·
      refine ⟨3175988739845508168971501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2117325826563672112647667 3175988739845508168971501)
      ·
        refine ⟨1190995777442065563364313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3175988739845508168971501 1190995777442065563364313)
        ·
          refine ⟨893246833081549172523235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1190995777442065563364313 893246833081549172523235)
          ·
            refine ⟨1339870249622323758784853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893246833081549172523235 1339870249622323758784853)
            ·
              refine ⟨3925401121940401637065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1339870249622323758784853 3925401121940401637065)
              ·
                rfl

theorem cell23_619220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 10].length) (baseStart_619220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619220 prefixEnd_619220 := by exact prefixLift 619220
  have htrace : WordTrace (prefixWord ++ tailWord_619220) baseStart_619220 baseEnd_619220 := by
    simpa [prefixWord, tailWord_619220, baseEnd_619220] using wordTrace_append hprefix tailTrace_619220
  have hstable : (prefixWord ++ tailWord_619220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619220).length < 2 ^ (prefixWord ++ tailWord_619220).sum := by decide
  have hdescent : baseEnd_619220 < baseStart_619220 := by decide
  rcases family_descends (prefixWord ++ tailWord_619220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619247 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 1, 3, 3]
def baseStart_619247 : Nat := 118140960795 + 619247 * 2 ^ 59
def prefixEnd_619247 : Nat := 4983230072969 + 3 ^ 40 * 619247 * 2
def baseEnd_619247 : Nat := 317971354854843926964641

theorem tailTrace_619247 : CollatzResearch.WordTrace tailWord_619247 prefixEnd_619247 317971354854843926964641 := by
  unfold tailWord_619247
  simp only [CollatzResearch.WordTrace]
  refine ⟨22585793587581352812807995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15057195725054235208538663 22585793587581352812807995)
  ·
    refine ⟨33878690381372029219211993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22585793587581352812807995 33878690381372029219211993)
    ·
      refine ⟨25409017786029021914408995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33878690381372029219211993 25409017786029021914408995)
      ·
        refine ⟨38113526679043532871613493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25409017786029021914408995 38113526679043532871613493)
        ·
          refine ⟨3573143126160331206713765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38113526679043532871613493 3573143126160331206713765)
          ·
            refine ⟨669964336155062101258831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3573143126160331206713765 669964336155062101258831)
            ·
              refine ⟨1004946504232593151888247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669964336155062101258831 1004946504232593151888247)
              ·
                refine ⟨1507419756348889727832371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004946504232593151888247 1507419756348889727832371)
                ·
                  refine ⟨2261129634523334591748557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1507419756348889727832371 2261129634523334591748557)
                  ·
                    refine ⟨847923612946250471905709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2261129634523334591748557 847923612946250471905709)
                    ·
                      refine ⟨317971354854843926964641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 847923612946250471905709 317971354854843926964641)
                      ·
                        rfl

theorem cell23_619247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 3, 3].length) (baseStart_619247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619247 prefixEnd_619247 := by exact prefixLift 619247
  have htrace : WordTrace (prefixWord ++ tailWord_619247) baseStart_619247 baseEnd_619247 := by
    simpa [prefixWord, tailWord_619247, baseEnd_619247] using wordTrace_append hprefix tailTrace_619247
  have hstable : (prefixWord ++ tailWord_619247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619247).length < 2 ^ (prefixWord ++ tailWord_619247).sum := by decide
  have hdescent : baseEnd_619247 < baseStart_619247 := by decide
  rcases family_descends (prefixWord ++ tailWord_619247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619273 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 1, 3, 5]
def baseStart_619273 : Nat := 118140960795 + 619273 * 2 ^ 59
def prefixEnd_619273 : Nat := 4983230072969 + 3 ^ 40 * 619273 * 2
def baseEnd_619273 : Nat := 317984705351860825239521

theorem tailTrace_619273 : CollatzResearch.WordTrace tailWord_619273 prefixEnd_619273 317984705351860825239521 := by
  unfold tailWord_619273
  simp only [CollatzResearch.WordTrace]
  refine ⟨22586741885487159253254473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15057827923658106168836315 22586741885487159253254473)
  ·
    refine ⟨16940056414115369439940855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22586741885487159253254473 16940056414115369439940855)
    ·
      refine ⟨25410084621173054159911283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16940056414115369439940855 25410084621173054159911283)
      ·
        refine ⟨38115126931759581239866925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25410084621173054159911283 38115126931759581239866925)
        ·
          refine ⟨14293172599409842964950097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38115126931759581239866925 14293172599409842964950097)
          ·
            refine ⟨10719879449557382223712573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14293172599409842964950097 10719879449557382223712573)
            ·
              refine ⟨4019954793584018333892215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10719879449557382223712573 4019954793584018333892215)
              ·
                refine ⟨6029932190376027500838323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019954793584018333892215 6029932190376027500838323)
                ·
                  refine ⟨9044898285564041251257485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6029932190376027500838323 9044898285564041251257485)
                  ·
                    refine ⟨3391836857086515469221557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9044898285564041251257485 3391836857086515469221557)
                    ·
                      refine ⟨317984705351860825239521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3391836857086515469221557 317984705351860825239521)
                      ·
                        rfl

theorem cell23_619273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_619273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619273 prefixEnd_619273 := by exact prefixLift 619273
  have htrace : WordTrace (prefixWord ++ tailWord_619273) baseStart_619273 baseEnd_619273 := by
    simpa [prefixWord, tailWord_619273, baseEnd_619273] using wordTrace_append hprefix tailTrace_619273
  have hstable : (prefixWord ++ tailWord_619273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619273).length < 2 ^ (prefixWord ++ tailWord_619273).sum := by decide
  have hdescent : baseEnd_619273 < baseStart_619273 := by decide
  rcases family_descends (prefixWord ++ tailWord_619273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619290 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3]
def baseStart_619290 : Nat := 118140960795 + 619290 * 2 ^ 59
def prefixEnd_619290 : Nat := 4983230072969 + 3 ^ 40 * 619290 * 2
def baseEnd_619290 : Nat := 317993434522987258726943

theorem tailTrace_619290 : CollatzResearch.WordTrace tailWord_619290 prefixEnd_619290 317993434522987258726943 := by
  unfold tailWord_619290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5646840481606392789155831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15058241284283714104415549 5646840481606392789155831)
  ·
    refine ⟨8470260722409589183733747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5646840481606392789155831 8470260722409589183733747)
    ·
      refine ⟨12705391083614383775600621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8470260722409589183733747 12705391083614383775600621)
      ·
        refine ⟨4764521656355393915850233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12705391083614383775600621 4764521656355393915850233)
        ·
          refine ⟨3573391242266545436887675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4764521656355393915850233 3573391242266545436887675)
          ·
            refine ⟨5360086863399818155331513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573391242266545436887675 5360086863399818155331513)
            ·
              refine ⟨4020065147549863616498635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5360086863399818155331513 4020065147549863616498635)
              ·
                refine ⟨6030097721324795424747953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4020065147549863616498635 6030097721324795424747953)
                ·
                  refine ⟨4522573290993596568560965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6030097721324795424747953 4522573290993596568560965)
                  ·
                    refine ⟨847982492061299356605181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4522573290993596568560965 847982492061299356605181)
                    ·
                      refine ⟨317993434522987258726943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 847982492061299356605181 317993434522987258726943)
                      ·
                        rfl

theorem cell23_619290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_619290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619290 prefixEnd_619290 := by exact prefixLift 619290
  have htrace : WordTrace (prefixWord ++ tailWord_619290) baseStart_619290 baseEnd_619290 := by
    simpa [prefixWord, tailWord_619290, baseEnd_619290] using wordTrace_append hprefix tailTrace_619290
  have hstable : (prefixWord ++ tailWord_619290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619290).length < 2 ^ (prefixWord ++ tailWord_619290).sum := by decide
  have hdescent : baseEnd_619290 < baseStart_619290 := by decide
  rcases family_descends (prefixWord ++ tailWord_619290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619360 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 4]
def baseStart_619360 : Nat := 118140960795 + 619360 * 2 ^ 59
def prefixEnd_619360 : Nat := 4983230072969 + 3 ^ 40 * 619360 * 2
def baseEnd_619360 : Nat := 318029378168801984851621

theorem tailTrace_619360 : CollatzResearch.WordTrace tailWord_619360 prefixEnd_619360 318029378168801984851621 := by
  unfold tailWord_619360
  simp only [CollatzResearch.WordTrace]
  refine ⟨11294957518085986555835767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15059943357447982074447689 11294957518085986555835767)
  ·
    refine ⟨16942436277128979833753651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11294957518085986555835767 16942436277128979833753651)
    ·
      refine ⟨25413654415693469750630477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16942436277128979833753651 25413654415693469750630477)
      ·
        refine ⟨9530120405885051156486429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25413654415693469750630477 9530120405885051156486429)
        ·
          refine ⟨3573795152206894183682411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9530120405885051156486429 3573795152206894183682411)
          ·
            refine ⟨5360692728310341275523617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573795152206894183682411 5360692728310341275523617)
            ·
              refine ⟨4020519546232755956642713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5360692728310341275523617 4020519546232755956642713)
              ·
                refine ⟨3015389659674566967482035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4020519546232755956642713 3015389659674566967482035)
                ·
                  refine ⟨4523084489511850451223053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3015389659674566967482035 4523084489511850451223053)
                  ·
                    refine ⟨1696156683566943919208645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4523084489511850451223053 1696156683566943919208645)
                    ·
                      refine ⟨318029378168801984851621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1696156683566943919208645 318029378168801984851621)
                      ·
                        rfl

theorem cell23_619360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_619360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619360 prefixEnd_619360 := by exact prefixLift 619360
  have htrace : WordTrace (prefixWord ++ tailWord_619360) baseStart_619360 baseEnd_619360 := by
    simpa [prefixWord, tailWord_619360, baseEnd_619360] using wordTrace_append hprefix tailTrace_619360
  have hstable : (prefixWord ++ tailWord_619360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619360).length < 2 ^ (prefixWord ++ tailWord_619360).sum := by decide
  have hdescent : baseEnd_619360 < baseStart_619360 := by decide
  rcases family_descends (prefixWord ++ tailWord_619360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619377 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 2, 1, 4]
def baseStart_619377 : Nat := 118140960795 + 619377 * 2 ^ 59
def prefixEnd_619377 : Nat := 4983230072969 + 3 ^ 40 * 619377 * 2
def baseEnd_619377 : Nat := 318038107339928418339043

theorem tailTrace_619377 : CollatzResearch.WordTrace tailWord_619377 prefixEnd_619377 318038107339928418339043 := by
  unfold tailWord_619377
  simp only [CollatzResearch.WordTrace]
  refine ⟨22590535077110385015040385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15060356718073590010026923 22590535077110385015040385)
  ·
    refine ⟨16942901307832788761280289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22590535077110385015040385 16942901307832788761280289)
    ·
      refine ⟨12707175980874591570960217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16942901307832788761280289 12707175980874591570960217)
      ·
        refine ⟨9530381985655943678220163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12707175980874591570960217 9530381985655943678220163)
        ·
          refine ⟨14295572978483915517330245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9530381985655943678220163 14295572978483915517330245)
          ·
            refine ⟨2680419933465734159499421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14295572978483915517330245 2680419933465734159499421)
            ·
              refine ⟨1005157475049650309812283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2680419933465734159499421 1005157475049650309812283)
              ·
                refine ⟨1507736212574475464718425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005157475049650309812283 1507736212574475464718425)
                ·
                  refine ⟨1130802159430856598538819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1507736212574475464718425 1130802159430856598538819)
                  ·
                    refine ⟨1696203239146284897808229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1130802159430856598538819 1696203239146284897808229)
                    ·
                      refine ⟨318038107339928418339043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1696203239146284897808229 318038107339928418339043)
                      ·
                        rfl

theorem cell23_619377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_619377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619377 prefixEnd_619377 := by exact prefixLift 619377
  have htrace : WordTrace (prefixWord ++ tailWord_619377) baseStart_619377 baseEnd_619377 := by
    simpa [prefixWord, tailWord_619377, baseEnd_619377] using wordTrace_append hprefix tailTrace_619377
  have hstable : (prefixWord ++ tailWord_619377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619377).length < 2 ^ (prefixWord ++ tailWord_619377).sum := by decide
  have hdescent : baseEnd_619377 < baseStart_619377 := by decide
  rcases family_descends (prefixWord ++ tailWord_619377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619404 : List Nat := [2, 2, 1, 2, 1, 2, 4, 4, 1, 4]
def baseStart_619404 : Nat := 118140960795 + 619404 * 2 ^ 59
def prefixEnd_619404 : Nat := 4983230072969 + 3 ^ 40 * 619404 * 2
def baseEnd_619404 : Nat := 106017323772533270900473

theorem tailTrace_619404 : CollatzResearch.WordTrace tailWord_619404 prefixEnd_619404 106017323772533270900473 := by
  unfold tailWord_619404
  simp only [CollatzResearch.WordTrace]
  refine ⟨11295759924006284313136633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15061013232008379084182177 11295759924006284313136633)
  ·
    refine ⟨8471819943004713234852475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11295759924006284313136633 8471819943004713234852475)
    ·
      refine ⟨12707729914507069852278713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8471819943004713234852475 12707729914507069852278713)
      ·
        refine ⟨9530797435880302389209035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12707729914507069852278713 9530797435880302389209035)
        ·
          refine ⟨14296196153820453583813553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9530797435880302389209035 14296196153820453583813553)
          ·
            refine ⟨10722147115365340187860165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14296196153820453583813553 10722147115365340187860165)
            ·
              refine ⟨2010402584131001285223781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10722147115365340187860165 2010402584131001285223781)
              ·
                refine ⟨376950484524562740979459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2010402584131001285223781 376950484524562740979459)
                ·
                  refine ⟨565425726786844111469189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 376950484524562740979459 565425726786844111469189)
                  ·
                    refine ⟨106017323772533270900473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 565425726786844111469189 106017323772533270900473)
                    ·
                      rfl

theorem cell23_619404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_619404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619404 prefixEnd_619404 := by exact prefixLift 619404
  have htrace : WordTrace (prefixWord ++ tailWord_619404) baseStart_619404 baseEnd_619404 := by
    simpa [prefixWord, tailWord_619404, baseEnd_619404] using wordTrace_append hprefix tailTrace_619404
  have hstable : (prefixWord ++ tailWord_619404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619404).length < 2 ^ (prefixWord ++ tailWord_619404).sum := by decide
  have hdescent : baseEnd_619404 < baseStart_619404 := by decide
  rcases family_descends (prefixWord ++ tailWord_619404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619447 : List Nat := [1, 1, 3, 1, 3, 1, 4, 3, 1, 5]
def baseStart_619447 : Nat := 118140960795 + 619447 * 2 ^ 59
def prefixEnd_619447 : Nat := 4983230072969 + 3 ^ 40 * 619447 * 2
def baseEnd_619447 : Nat := 106024683661914381487907

theorem tailTrace_619447 : CollatzResearch.WordTrace tailWord_619447 prefixEnd_619447 106024683661914381487907 := by
  unfold tailWord_619447
  simp only [CollatzResearch.WordTrace]
  refine ⟨22593088186856786970088595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15062058791237857980059063 22593088186856786970088595)
  ·
    refine ⟨33889632280285180455132893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22593088186856786970088595 33889632280285180455132893)
    ·
      refine ⟨12708612105106942670674835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33889632280285180455132893 12708612105106942670674835)
      ·
        refine ⟨19062918157660414006012253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12708612105106942670674835 19062918157660414006012253)
        ·
          refine ⟨7148594309122655252254595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19062918157660414006012253 7148594309122655252254595)
          ·
            refine ⟨10722891463683982878381893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7148594309122655252254595 10722891463683982878381893)
            ·
              refine ⟨2010542149440746789696605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10722891463683982878381893 2010542149440746789696605)
              ·
                refine ⟨753953306040280046136227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2010542149440746789696605 753953306040280046136227)
                ·
                  refine ⟨1130929959060420069204341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753953306040280046136227 1130929959060420069204341)
                  ·
                    refine ⟨106024683661914381487907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1130929959060420069204341 106024683661914381487907)
                    ·
                      rfl

theorem cell23_619447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_619447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619447 prefixEnd_619447 := by exact prefixLift 619447
  have htrace : WordTrace (prefixWord ++ tailWord_619447) baseStart_619447 baseEnd_619447 := by
    simpa [prefixWord, tailWord_619447, baseEnd_619447] using wordTrace_append hprefix tailTrace_619447
  have hstable : (prefixWord ++ tailWord_619447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619447).length < 2 ^ (prefixWord ++ tailWord_619447).sum := by decide
  have hdescent : baseEnd_619447 < baseStart_619447 := by decide
  rcases family_descends (prefixWord ++ tailWord_619447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619517 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_619517 : Nat := 118140960795 + 619517 * 2 ^ 59
def prefixEnd_619517 : Nat := 4983230072969 + 3 ^ 40 * 619517 * 2
def baseEnd_619517 : Nat := 318109994631557870588399

theorem tailTrace_619517 : CollatzResearch.WordTrace tailWord_619517 prefixEnd_619517 318109994631557870588399 := by
  unfold tailWord_619517
  simp only [CollatzResearch.WordTrace]
  refine ⟨22595641296603188925136805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15063760864402125950091203 22595641296603188925136805)
  ·
    refine ⟨4236682743113097923463151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22595641296603188925136805 4236682743113097923463151)
    ·
      refine ⟨6355024114669646885194727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4236682743113097923463151 6355024114669646885194727)
      ·
        refine ⟨9532536172004470327792091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6355024114669646885194727 9532536172004470327792091)
        ·
          refine ⟨14298804258006705491688137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9532536172004470327792091 14298804258006705491688137)
          ·
            refine ⟨10724103193505029118766103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14298804258006705491688137 10724103193505029118766103)
            ·
              refine ⟨16086154790257543678149155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10724103193505029118766103 16086154790257543678149155)
              ·
                refine ⟨24129232185386315517223733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16086154790257543678149155 24129232185386315517223733)
                ·
                  refine ⟨2262115517379967079739725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24129232185386315517223733 2262115517379967079739725)
                  ·
                    refine ⟨848293319017487654902397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2262115517379967079739725 848293319017487654902397)
                    ·
                      refine ⟨318109994631557870588399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 848293319017487654902397 318109994631557870588399)
                      ·
                        rfl

theorem cell23_619517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_619517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619517 prefixEnd_619517 := by exact prefixLift 619517
  have htrace : WordTrace (prefixWord ++ tailWord_619517) baseStart_619517 baseEnd_619517 := by
    simpa [prefixWord, tailWord_619517, baseEnd_619517] using wordTrace_append hprefix tailTrace_619517
  have hstable : (prefixWord ++ tailWord_619517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619517).length < 2 ^ (prefixWord ++ tailWord_619517).sum := by decide
  have hdescent : baseEnd_619517 < baseStart_619517 := by decide
  rcases family_descends (prefixWord ++ tailWord_619517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619534 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_619534 : Nat := 118140960795 + 619534 * 2 ^ 59
def prefixEnd_619534 : Nat := 4983230072969 + 3 ^ 40 * 619534 * 2
def baseEnd_619534 : Nat := 318118723802684304075821

theorem tailTrace_619534 : CollatzResearch.WordTrace tailWord_619534 prefixEnd_619534 318118723802684304075821 := by
  unfold tailWord_619534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2824532667192700103563207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15064174225027733885670437 2824532667192700103563207)
  ·
    refine ⟨4236799000789050155344811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2824532667192700103563207 4236799000789050155344811)
    ·
      refine ⟨6355198501183575233017217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4236799000789050155344811 6355198501183575233017217)
      ·
        refine ⟨4766398875887681424762913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6355198501183575233017217 4766398875887681424762913)
        ·
          refine ⟨3574799156915761068572185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4766398875887681424762913 3574799156915761068572185)
          ·
            refine ⟨2681099367686820801429139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3574799156915761068572185 2681099367686820801429139)
            ·
              refine ⟨4021649051530231202143709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2681099367686820801429139 4021649051530231202143709)
              ·
                refine ⟨1508118394323836700803891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4021649051530231202143709 1508118394323836700803891)
                ·
                  refine ⟨2262177591485755051205837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508118394323836700803891 2262177591485755051205837)
                  ·
                    refine ⟨848316596807158144202189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2262177591485755051205837 848316596807158144202189)
                    ·
                      refine ⟨318118723802684304075821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 848316596807158144202189 318118723802684304075821)
                      ·
                        rfl

theorem cell23_619534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_619534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619534 prefixEnd_619534 := by exact prefixLift 619534
  have htrace : WordTrace (prefixWord ++ tailWord_619534) baseStart_619534 baseEnd_619534 := by
    simpa [prefixWord, tailWord_619534, baseEnd_619534] using wordTrace_append hprefix tailTrace_619534
  have hstable : (prefixWord ++ tailWord_619534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619534).length < 2 ^ (prefixWord ++ tailWord_619534).sum := by decide
  have hdescent : baseEnd_619534 < baseStart_619534 := by decide
  rcases family_descends (prefixWord ++ tailWord_619534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619552 : List Nat := [2, 1, 1, 7, 1, 1, 2, 3, 1, 2, 2]
def baseStart_619552 : Nat := 118140960795 + 619552 * 2 ^ 59
def prefixEnd_619552 : Nat := 4983230072969 + 3 ^ 40 * 619552 * 2
def baseEnd_619552 : Nat := 318127966454465233650739

theorem tailTrace_619552 : CollatzResearch.WordTrace tailWord_619552 prefixEnd_619552 318127966454465233650739 := by
  unfold tailWord_619552
  simp only [CollatzResearch.WordTrace]
  refine ⟨11298458925738194951330455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15064611900984259935107273 11298458925738194951330455)
  ·
    refine ⟨16947688388607292426995683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11298458925738194951330455 16947688388607292426995683)
    ·
      refine ⟨25421532582910938640493525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16947688388607292426995683 25421532582910938640493525)
      ·
        refine ⟨595817169911975124386567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 25421532582910938640493525 595817169911975124386567)
        ·
          refine ⟨893725754867962686579851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595817169911975124386567 893725754867962686579851)
          ·
            refine ⟨1340588632301944029869777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893725754867962686579851 1340588632301944029869777)
            ·
              refine ⟨1005441474226458022402333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1340588632301944029869777 1005441474226458022402333)
              ·
                refine ⟨377040552834921758400875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1005441474226458022402333 377040552834921758400875)
                ·
                  refine ⟨565560829252382637601313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377040552834921758400875 565560829252382637601313)
                  ·
                    refine ⟨424170621939286978200985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 565560829252382637601313 424170621939286978200985)
                    ·
                      refine ⟨318127966454465233650739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 424170621939286978200985 318127966454465233650739)
                      ·
                        rfl

theorem cell23_619552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_619552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619552 prefixEnd_619552 := by exact prefixLift 619552
  have htrace : WordTrace (prefixWord ++ tailWord_619552) baseStart_619552 baseEnd_619552 := by
    simpa [prefixWord, tailWord_619552, baseEnd_619552] using wordTrace_append hprefix tailTrace_619552
  have hstable : (prefixWord ++ tailWord_619552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619552).length < 2 ^ (prefixWord ++ tailWord_619552).sum := by decide
  have hdescent : baseEnd_619552 < baseStart_619552 := by decide
  rcases family_descends (prefixWord ++ tailWord_619552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619585 : List Nat := [1, 2, 5, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_619585 : Nat := 118140960795 + 619585 * 2 ^ 59
def prefixEnd_619585 : Nat := 4983230072969 + 3 ^ 40 * 619585 * 2
def baseEnd_619585 : Nat := 318144911316063604538087

theorem tailTrace_619585 : CollatzResearch.WordTrace tailWord_619585 prefixEnd_619585 318144911316063604538087 := by
  unfold tailWord_619585
  simp only [CollatzResearch.WordTrace]
  refine ⟨22598121460356836538612209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15065414306904557692408139 22598121460356836538612209)
  ·
    refine ⟨16948591095267627403959157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22598121460356836538612209 16948591095267627403959157)
    ·
      refine ⟨1588930415181340069121171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16948591095267627403959157 1588930415181340069121171)
      ·
        refine ⟨2383395622772010103681757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1588930415181340069121171 2383395622772010103681757)
        ·
          refine ⟨893773358539503788880659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2383395622772010103681757 893773358539503788880659)
          ·
            refine ⟨1340660037809255683320989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893773358539503788880659 1340660037809255683320989)
            ·
              refine ⟨502747514178470881245371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1340660037809255683320989 502747514178470881245371)
              ·
                refine ⟨754121271267706321868057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502747514178470881245371 754121271267706321868057)
                ·
                  refine ⟨565590953450779741401043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 754121271267706321868057 565590953450779741401043)
                  ·
                    refine ⟨848386430176169612101565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 565590953450779741401043 848386430176169612101565)
                    ·
                      refine ⟨318144911316063604538087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 848386430176169612101565 318144911316063604538087)
                      ·
                        rfl

theorem cell23_619585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_619585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619585 prefixEnd_619585 := by exact prefixLift 619585
  have htrace : WordTrace (prefixWord ++ tailWord_619585) baseStart_619585 baseEnd_619585 := by
    simpa [prefixWord, tailWord_619585, baseEnd_619585] using wordTrace_append hprefix tailTrace_619585
  have hstable : (prefixWord ++ tailWord_619585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619585).length < 2 ^ (prefixWord ++ tailWord_619585).sum := by decide
  have hdescent : baseEnd_619585 < baseStart_619585 := by decide
  rcases family_descends (prefixWord ++ tailWord_619585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619587 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 4]
def baseStart_619587 : Nat := 118140960795 + 619587 * 2 ^ 59
def prefixEnd_619587 : Nat := 4983230072969 + 3 ^ 40 * 619587 * 2
def baseEnd_619587 : Nat := 318145938277372596713077

theorem tailTrace_619587 : CollatzResearch.WordTrace tailWord_619587 prefixEnd_619587 318145938277372596713077 := by
  unfold tailWord_619587
  simp only [CollatzResearch.WordTrace]
  refine ⟨22598194406349590880185015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15065462937566393920123343 22598194406349590880185015)
  ·
    refine ⟨33897291609524386320277523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22598194406349590880185015 33897291609524386320277523)
    ·
      refine ⟨50845937414286579480416285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33897291609524386320277523 50845937414286579480416285)
      ·
        refine ⟨19067226530357467305156107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50845937414286579480416285 19067226530357467305156107)
        ·
          refine ⟨28600839795536200957734161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19067226530357467305156107 28600839795536200957734161)
          ·
            refine ⟨21450629846652150718300621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28600839795536200957734161 21450629846652150718300621)
            ·
              refine ⟨8043986192494556519362733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21450629846652150718300621 8043986192494556519362733)
              ·
                refine ⟨3016494822185458694761025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8043986192494556519362733 3016494822185458694761025)
                ·
                  refine ⟨2262371116639094021070769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3016494822185458694761025 2262371116639094021070769)
                  ·
                    refine ⟨1696778337479320515803077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2262371116639094021070769 1696778337479320515803077)
                    ·
                      refine ⟨318145938277372596713077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1696778337479320515803077 318145938277372596713077)
                      ·
                        rfl

theorem cell23_619587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_619587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619587 prefixEnd_619587 := by exact prefixLift 619587
  have htrace : WordTrace (prefixWord ++ tailWord_619587) baseStart_619587 baseEnd_619587 := by
    simpa [prefixWord, tailWord_619587, baseEnd_619587] using wordTrace_append hprefix tailTrace_619587
  have hstable : (prefixWord ++ tailWord_619587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619587).length < 2 ^ (prefixWord ++ tailWord_619587).sum := by decide
  have hdescent : baseEnd_619587 < baseStart_619587 := by decide
  rcases family_descends (prefixWord ++ tailWord_619587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619591 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 1, 4, 2]
def baseStart_619591 : Nat := 118140960795 + 619591 * 2 ^ 59
def prefixEnd_619591 : Nat := 4983230072969 + 3 ^ 40 * 619591 * 2
def baseEnd_619591 : Nat := 318147992199990581063059

theorem tailTrace_619591 : CollatzResearch.WordTrace tailWord_619591 prefixEnd_619591 318147992199990581063059 := by
  unfold tailWord_619591
  simp only [CollatzResearch.WordTrace]
  refine ⟨22598340298335099563330627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15065560198890066375553751 22598340298335099563330627)
  ·
    refine ⟨33897510447502649344995941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22598340298335099563330627 33897510447502649344995941)
    ·
      refine ⟨6355783208906746752186739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33897510447502649344995941 6355783208906746752186739)
      ·
        refine ⟨9533674813360120128280109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6355783208906746752186739 9533674813360120128280109)
        ·
          refine ⟨3575128055010045048105041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9533674813360120128280109 3575128055010045048105041)
          ·
            refine ⟨2681346041257533786078781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3575128055010045048105041 2681346041257533786078781)
            ·
              refine ⟨1005504765471575169779543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2681346041257533786078781 1005504765471575169779543)
              ·
                refine ⟨1508257148207362754669315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005504765471575169779543 1508257148207362754669315)
                ·
                  refine ⟨2262385722311044132003973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508257148207362754669315 2262385722311044132003973)
                  ·
                    refine ⟨424197322933320774750745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2262385722311044132003973 424197322933320774750745)
                    ·
                      refine ⟨318147992199990581063059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 424197322933320774750745 318147992199990581063059)
                      ·
                        rfl

theorem cell23_619591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_619591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619591 prefixEnd_619591 := by exact prefixLift 619591
  have htrace : WordTrace (prefixWord ++ tailWord_619591) baseStart_619591 baseEnd_619591 := by
    simpa [prefixWord, tailWord_619591, baseEnd_619591] using wordTrace_append hprefix tailTrace_619591
  have hstable : (prefixWord ++ tailWord_619591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619591).length < 2 ^ (prefixWord ++ tailWord_619591).sum := by decide
  have hdescent : baseEnd_619591 < baseStart_619591 := by decide
  rcases family_descends (prefixWord ++ tailWord_619591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619631 : List Nat := [1, 1, 2, 1, 3, 3, 5, 2, 5]
def baseStart_619631 : Nat := 118140960795 + 619631 * 2 ^ 59
def prefixEnd_619631 : Nat := 4983230072969 + 3 ^ 40 * 619631 * 2
def baseEnd_619631 : Nat := 35352059047352269395875

theorem tailTrace_619631 : CollatzResearch.WordTrace tailWord_619631 prefixEnd_619631 35352059047352269395875 := by
  unfold tailWord_619631
  simp only [CollatzResearch.WordTrace]
  refine ⟨22599799218190186394786747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15066532812126790929857831 22599799218190186394786747)
  ·
    refine ⟨33899698827285279592180121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22599799218190186394786747 33899698827285279592180121)
    ·
      refine ⟨25424774120463959694135091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33899698827285279592180121 25424774120463959694135091)
      ·
        refine ⟨38137161180695939541202637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25424774120463959694135091 38137161180695939541202637)
        ·
          refine ⟨14301435442760977327950989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38137161180695939541202637 14301435442760977327950989)
          ·
            refine ⟨5363038291035366497981621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14301435442760977327950989 5363038291035366497981621)
            ·
              refine ⟨502784839784565609185777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5363038291035366497981621 502784839784565609185777)
              ·
                refine ⟨377088629838424206889333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502784839784565609185777 377088629838424206889333)
                ·
                  refine ⟨35352059047352269395875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 377088629838424206889333 35352059047352269395875)
                  ·
                    rfl

theorem cell23_619631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 5].length) (baseStart_619631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619631 prefixEnd_619631 := by exact prefixLift 619631
  have htrace : WordTrace (prefixWord ++ tailWord_619631) baseStart_619631 baseEnd_619631 := by
    simpa [prefixWord, tailWord_619631, baseEnd_619631] using wordTrace_append hprefix tailTrace_619631
  have hstable : (prefixWord ++ tailWord_619631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619631).length < 2 ^ (prefixWord ++ tailWord_619631).sum := by decide
  have hdescent : baseEnd_619631 < baseStart_619631 := by decide
  rcases family_descends (prefixWord ++ tailWord_619631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619646 : List Nat := [4, 2, 4, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_619646 : Nat := 118140960795 + 619646 * 2 ^ 59
def prefixEnd_619646 : Nat := 4983230072969 + 3 ^ 40 * 619646 * 2
def baseEnd_619646 : Nat := 318176233635987865875307

theorem tailTrace_619646 : CollatzResearch.WordTrace tailWord_619646 prefixEnd_619646 318176233635987865875307 := by
  unfold tailWord_619646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2825043289141980494572849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15066897542090562637721861 2825043289141980494572849)
  ·
    refine ⟨2118782466856485370929637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2825043289141980494572849 2118782466856485370929637)
    ·
      refine ⟨397271712535591007049307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2118782466856485370929637 397271712535591007049307)
      ·
        refine ⟨595907568803386510573961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397271712535591007049307 595907568803386510573961)
        ·
          refine ⟨446930676602539882930471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595907568803386510573961 446930676602539882930471)
          ·
            refine ⟨670396014903809824395707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446930676602539882930471 670396014903809824395707)
            ·
              refine ⟨1005594022355714736593561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670396014903809824395707 1005594022355714736593561)
              ·
                refine ⟨754195516766786052445171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1005594022355714736593561 754195516766786052445171)
                ·
                  refine ⟨1131293275150179078667757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754195516766786052445171 1131293275150179078667757)
                  ·
                    refine ⟨424234978181317154500409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1131293275150179078667757 424234978181317154500409)
                    ·
                      refine ⟨318176233635987865875307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 424234978181317154500409 318176233635987865875307)
                      ·
                        rfl

theorem cell23_619646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_619646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619646 prefixEnd_619646 := by exact prefixLift 619646
  have htrace : WordTrace (prefixWord ++ tailWord_619646) baseStart_619646 baseEnd_619646 := by
    simpa [prefixWord, tailWord_619646, baseEnd_619646] using wordTrace_append hprefix tailTrace_619646
  have hstable : (prefixWord ++ tailWord_619646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619646).length < 2 ^ (prefixWord ++ tailWord_619646).sum := by decide
  have hdescent : baseEnd_619646 < baseStart_619646 := by decide
  rcases family_descends (prefixWord ++ tailWord_619646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619664 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 3, 6, 2]
def baseStart_619664 : Nat := 118140960795 + 619664 * 2 ^ 59
def prefixEnd_619664 : Nat := 4983230072969 + 3 ^ 40 * 619664 * 2
def baseEnd_619664 : Nat := 318185476287768795450223

theorem tailTrace_619664 : CollatzResearch.WordTrace tailWord_619664 prefixEnd_619664 318185476287768795450223 := by
  unfold tailWord_619664
  simp only [CollatzResearch.WordTrace]
  refine ⟨11300501413535316515369023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15067335218047088687158697 11300501413535316515369023)
  ·
    refine ⟨16950752120302974773053535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11300501413535316515369023 16950752120302974773053535)
    ·
      refine ⟨25426128180454462159580303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16950752120302974773053535 25426128180454462159580303)
      ·
        refine ⟨38139192270681693239370455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25426128180454462159580303 38139192270681693239370455)
        ·
          refine ⟨57208788406022539859055683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38139192270681693239370455 57208788406022539859055683)
          ·
            refine ⟨85813182609033809788583525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57208788406022539859055683 85813182609033809788583525)
            ·
              refine ⟨16089971739193839335359411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85813182609033809788583525 16089971739193839335359411)
              ·
                refine ⟨24134957608790759003039117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16089971739193839335359411 24134957608790759003039117)
                ·
                  refine ⟨9050609103296534626139669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24134957608790759003039117 9050609103296534626139669)
                  ·
                    refine ⟨424247301717025060600297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9050609103296534626139669 424247301717025060600297)
                    ·
                      refine ⟨318185476287768795450223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 424247301717025060600297 318185476287768795450223)
                      ·
                        rfl

theorem cell23_619664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 6, 2].length) (baseStart_619664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619664 prefixEnd_619664 := by exact prefixLift 619664
  have htrace : WordTrace (prefixWord ++ tailWord_619664) baseStart_619664 baseEnd_619664 := by
    simpa [prefixWord, tailWord_619664, baseEnd_619664] using wordTrace_append hprefix tailTrace_619664
  have hstable : (prefixWord ++ tailWord_619664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619664).length < 2 ^ (prefixWord ++ tailWord_619664).sum := by decide
  have hdescent : baseEnd_619664 < baseStart_619664 := by decide
  rcases family_descends (prefixWord ++ tailWord_619664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619681 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 2, 4, 2]
def baseStart_619681 : Nat := 118140960795 + 619681 * 2 ^ 59
def prefixEnd_619681 : Nat := 4983230072969 + 3 ^ 40 * 619681 * 2
def baseEnd_619681 : Nat := 318194205458895228937645

theorem tailTrace_619681 : CollatzResearch.WordTrace tailWord_619681 prefixEnd_619681 318194205458895228937645 := by
  unfold tailWord_619681
  simp only [CollatzResearch.WordTrace]
  refine ⟨22601622868009044934106897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15067748578672696622737931 22601622868009044934106897)
  ·
    refine ⟨16951217151006783700580173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22601622868009044934106897 16951217151006783700580173)
    ·
      refine ⟨6356706431627543887717565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16951217151006783700580173 6356706431627543887717565)
      ·
        refine ⟨2383764911860328957894087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6356706431627543887717565 2383764911860328957894087)
        ·
          refine ⟨3575647367790493436841131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2383764911860328957894087 3575647367790493436841131)
          ·
            refine ⟨5363471051685740155261697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575647367790493436841131 5363471051685740155261697)
            ·
              refine ⟨4022603288764305116446273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5363471051685740155261697 4022603288764305116446273)
              ·
                refine ⟨3016952466573228837334705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4022603288764305116446273 3016952466573228837334705)
                ·
                  refine ⟨2262714349929921628001029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3016952466573228837334705 2262714349929921628001029)
                  ·
                    refine ⟨424258940611860305250193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2262714349929921628001029 424258940611860305250193)
                    ·
                      refine ⟨318194205458895228937645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 424258940611860305250193 318194205458895228937645)
                      ·
                        rfl

theorem cell23_619681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_619681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619681 prefixEnd_619681 := by exact prefixLift 619681
  have htrace : WordTrace (prefixWord ++ tailWord_619681) baseStart_619681 baseEnd_619681 := by
    simpa [prefixWord, tailWord_619681, baseEnd_619681] using wordTrace_append hprefix tailTrace_619681
  have hstable : (prefixWord ++ tailWord_619681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619681).length < 2 ^ (prefixWord ++ tailWord_619681).sum := by decide
  have hdescent : baseEnd_619681 < baseStart_619681 := by decide
  rcases family_descends (prefixWord ++ tailWord_619681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619682 : List Nat := [3, 3, 1, 3, 3, 1, 2, 2, 5]
def baseStart_619682 : Nat := 118140960795 + 619682 * 2 ^ 59
def prefixEnd_619682 : Nat := 4983230072969 + 3 ^ 40 * 619682 * 2
def baseEnd_619682 : Nat := 35354968771061080558349

theorem tailTrace_619682 : CollatzResearch.WordTrace tailWord_619682 prefixEnd_619682 35354968771061080558349 := by
  unfold tailWord_619682
  simp only [CollatzResearch.WordTrace]
  refine ⟨5650414835251355526223325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15067772894003614736595533 5650414835251355526223325)
  ·
    refine ⟨2118905563219258322333747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5650414835251355526223325 2118905563219258322333747)
    ·
      refine ⟨3178358344828887483500621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2118905563219258322333747 3178358344828887483500621)
      ·
        refine ⟨1191884379310832806312733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3178358344828887483500621 1191884379310832806312733)
        ·
          refine ⟨446956642241562302367275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1191884379310832806312733 446956642241562302367275)
          ·
            refine ⟨670434963362343453550913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446956642241562302367275 670434963362343453550913)
            ·
              refine ⟨502826222521757590163185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670434963362343453550913 502826222521757590163185)
              ·
                refine ⟨377119666891318192622389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502826222521757590163185 377119666891318192622389)
                ·
                  refine ⟨35354968771061080558349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 377119666891318192622389 35354968771061080558349)
                  ·
                    rfl

theorem cell23_619682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_619682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619682 prefixEnd_619682 := by exact prefixLift 619682
  have htrace : WordTrace (prefixWord ++ tailWord_619682) baseStart_619682 baseEnd_619682 := by
    simpa [prefixWord, tailWord_619682, baseEnd_619682] using wordTrace_append hprefix tailTrace_619682
  have hstable : (prefixWord ++ tailWord_619682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619682).length < 2 ^ (prefixWord ++ tailWord_619682).sum := by decide
  have hdescent : baseEnd_619682 < baseStart_619682 := by decide
  rcases family_descends (prefixWord ++ tailWord_619682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619707 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 6]
def baseStart_619707 : Nat := 118140960795 + 619707 * 2 ^ 59
def prefixEnd_619707 : Nat := 4983230072969 + 3 ^ 40 * 619707 * 2
def baseEnd_619707 : Nat := 318207555955912127212525

theorem tailTrace_619707 : CollatzResearch.WordTrace tailWord_619707 prefixEnd_619707 318207555955912127212525 := by
  unfold tailWord_619707
  simp only [CollatzResearch.WordTrace]
  refine ⟨22602571165914851374553375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15068380777276567583035583 22602571165914851374553375)
  ·
    refine ⟨33903856748872277061830063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22602571165914851374553375 33903856748872277061830063)
    ·
      refine ⟨50855785123308415592745095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33903856748872277061830063 50855785123308415592745095)
      ·
        refine ⟨76283677684962623389117643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50855785123308415592745095 76283677684962623389117643)
        ·
          refine ⟨114425516527443935083676465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76283677684962623389117643 114425516527443935083676465)
          ·
            refine ⟨85819137395582951312757349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114425516527443935083676465 85819137395582951312757349)
            ·
              refine ⟨16091088261671803371142003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85819137395582951312757349 16091088261671803371142003)
              ·
                refine ⟨24136632392507705056713005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16091088261671803371142003 24136632392507705056713005)
                ·
                  refine ⟨9051237147190389396267377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24136632392507705056713005 9051237147190389396267377)
                  ·
                    refine ⟨6788427860392792047200533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9051237147190389396267377 6788427860392792047200533)
                    ·
                      refine ⟨318207555955912127212525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6788427860392792047200533 318207555955912127212525)
                      ·
                        rfl

theorem cell23_619707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 6].length) (baseStart_619707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619707 prefixEnd_619707 := by exact prefixLift 619707
  have htrace : WordTrace (prefixWord ++ tailWord_619707) baseStart_619707 baseEnd_619707 := by
    simpa [prefixWord, tailWord_619707, baseEnd_619707] using wordTrace_append hprefix tailTrace_619707
  have hstable : (prefixWord ++ tailWord_619707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619707).length < 2 ^ (prefixWord ++ tailWord_619707).sum := by decide
  have hdescent : baseEnd_619707 < baseStart_619707 := by decide
  rcases family_descends (prefixWord ++ tailWord_619707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619825 : List Nat := [1, 2, 2, 3, 3, 3, 1, 2, 1, 2, 3]
def baseStart_619825 : Nat := 118140960795 + 619825 * 2 ^ 59
def prefixEnd_619825 : Nat := 4983230072969 + 3 ^ 40 * 619825 * 2
def baseEnd_619825 : Nat := 318268146673142665536983

theorem tailTrace_619825 : CollatzResearch.WordTrace tailWord_619825 prefixEnd_619825 318268146673142665536983 := by
  unfold tailWord_619825
  simp only [CollatzResearch.WordTrace]
  refine ⟨22606874979487357527348929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15071249986324905018232619 22606874979487357527348929)
  ·
    refine ⟨16955156234615518145511697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22606874979487357527348929 16955156234615518145511697)
    ·
      refine ⟨12716367175961638609133773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16955156234615518145511697 12716367175961638609133773)
      ·
        refine ⟨4768637690985614478425165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12716367175961638609133773 4768637690985614478425165)
        ·
          refine ⟨1788239134119605429409437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4768637690985614478425165 1788239134119605429409437)
          ·
            refine ⟨670589675294852036028539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1788239134119605429409437 670589675294852036028539)
            ·
              refine ⟨1005884512942278054042809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670589675294852036028539 1005884512942278054042809)
              ·
                refine ⟨754413384706708540532107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1005884512942278054042809 754413384706708540532107)
                ·
                  refine ⟨1131620077060062810798161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754413384706708540532107 1131620077060062810798161)
                  ·
                    refine ⟨848715057795047108098621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1131620077060062810798161 848715057795047108098621)
                    ·
                      refine ⟨318268146673142665536983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 848715057795047108098621 318268146673142665536983)
                      ·
                        rfl

theorem cell23_619825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_619825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619825 prefixEnd_619825 := by exact prefixLift 619825
  have htrace : WordTrace (prefixWord ++ tailWord_619825) baseStart_619825 baseEnd_619825 := by
    simpa [prefixWord, tailWord_619825, baseEnd_619825] using wordTrace_append hprefix tailTrace_619825
  have hstable : (prefixWord ++ tailWord_619825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619825).length < 2 ^ (prefixWord ++ tailWord_619825).sum := by decide
  have hdescent : baseEnd_619825 < baseStart_619825 := by decide
  rcases family_descends (prefixWord ++ tailWord_619825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619838 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_619838 : Nat := 118140960795 + 619838 * 2 ^ 59
def prefixEnd_619838 : Nat := 4983230072969 + 3 ^ 40 * 619838 * 2
def baseEnd_619838 : Nat := 318274821921651114674423

theorem tailTrace_619838 : CollatzResearch.WordTrace tailWord_619838 prefixEnd_619838 318274821921651114674423 := by
  unfold tailWord_619838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2825918641055032593446521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15071566085626840498381445 2825918641055032593446521)
  ·
    refine ⟨2119438980791274445084891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2825918641055032593446521 2119438980791274445084891)
    ·
      refine ⟨3179158471186911667627337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2119438980791274445084891 3179158471186911667627337)
      ·
        refine ⟨2384368853390183750720503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3179158471186911667627337 2384368853390183750720503)
        ·
          refine ⟨3576553280085275626080755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384368853390183750720503 3576553280085275626080755)
          ·
            refine ⟨5364829920127913439121133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3576553280085275626080755 5364829920127913439121133)
            ·
              refine ⟨2011811220047967539670425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5364829920127913439121133 2011811220047967539670425)
              ·
                refine ⟨1508858415035975654752819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2011811220047967539670425 1508858415035975654752819)
                ·
                  refine ⟨2263287622553963482129229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508858415035975654752819 2263287622553963482129229)
                  ·
                    refine ⟨848732858457736305798461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2263287622553963482129229 848732858457736305798461)
                    ·
                      refine ⟨318274821921651114674423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 848732858457736305798461 318274821921651114674423)
                      ·
                        rfl

theorem cell23_619838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_619838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619838 prefixEnd_619838 := by exact prefixLift 619838
  have htrace : WordTrace (prefixWord ++ tailWord_619838) baseStart_619838 baseEnd_619838 := by
    simpa [prefixWord, tailWord_619838, baseEnd_619838] using wordTrace_append hprefix tailTrace_619838
  have hstable : (prefixWord ++ tailWord_619838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619838).length < 2 ^ (prefixWord ++ tailWord_619838).sum := by decide
  have hdescent : baseEnd_619838 < baseStart_619838 := by decide
  rcases family_descends (prefixWord ++ tailWord_619838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619861 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_619861 : Nat := 118140960795 + 619861 * 2 ^ 59
def prefixEnd_619861 : Nat := 4983230072969 + 3 ^ 40 * 619861 * 2
def baseEnd_619861 : Nat := 318286631976704524686817

theorem tailTrace_619861 : CollatzResearch.WordTrace tailWord_619861 prefixEnd_619861 318286631976704524686817 := by
  unfold tailWord_619861
  simp only [CollatzResearch.WordTrace]
  refine ⟨22608188007356935675659437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15072125338237957117106291 22608188007356935675659437)
  ·
    refine ⟨8478070502758850878372289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22608188007356935675659437 8478070502758850878372289)
    ·
      refine ⟨6358552877069138158779217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8478070502758850878372289 6358552877069138158779217)
      ·
        refine ⟨4768914657801853619084413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6358552877069138158779217 4768914657801853619084413)
        ·
          refine ⟨1788342996675695107156655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4768914657801853619084413 1788342996675695107156655)
          ·
            refine ⟨2682514495013542660734983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788342996675695107156655 2682514495013542660734983)
            ·
              refine ⟨4023771742520313991102475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2682514495013542660734983 4023771742520313991102475)
              ·
                refine ⟨6035657613780470986653713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4023771742520313991102475 6035657613780470986653713)
                ·
                  refine ⟨4526743210335353239990285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6035657613780470986653713 4526743210335353239990285)
                  ·
                    refine ⟨1697528703875757464996357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4526743210335353239990285 1697528703875757464996357)
                    ·
                      refine ⟨318286631976704524686817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1697528703875757464996357 318286631976704524686817)
                      ·
                        rfl

theorem cell23_619861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_619861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619861 prefixEnd_619861 := by exact prefixLift 619861
  have htrace : WordTrace (prefixWord ++ tailWord_619861) baseStart_619861 baseEnd_619861 := by
    simpa [prefixWord, tailWord_619861, baseEnd_619861] using wordTrace_append hprefix tailTrace_619861
  have hstable : (prefixWord ++ tailWord_619861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619861).length < 2 ^ (prefixWord ++ tailWord_619861).sum := by decide
  have hdescent : baseEnd_619861 < baseStart_619861 := by decide
  rcases family_descends (prefixWord ++ tailWord_619861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619912 : List Nat := [2, 1, 3, 3, 1, 2, 3, 2, 2, 2, 2]
def baseStart_619912 : Nat := 118140960795 + 619912 * 2 ^ 59
def prefixEnd_619912 : Nat := 4983230072969 + 3 ^ 40 * 619912 * 2
def baseEnd_619912 : Nat := 318312819490083825149083

theorem tailTrace_619912 : CollatzResearch.WordTrace tailWord_619912 prefixEnd_619912 318312819490083825149083 := by
  unfold tailWord_619912
  simp only [CollatzResearch.WordTrace]
  refine ⟨11305024065086085692882995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15073365420114780923843993 11305024065086085692882995)
  ·
    refine ⟨16957536097629128539324493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11305024065086085692882995 16957536097629128539324493)
    ·
      refine ⟨6359076036610923202246685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16957536097629128539324493 6359076036610923202246685)
      ·
        refine ⟨2384653513729096200842507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6359076036610923202246685 2384653513729096200842507)
        ·
          refine ⟨3576980270593644301263761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384653513729096200842507 3576980270593644301263761)
          ·
            refine ⟨2682735202945233225947821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3576980270593644301263761 2682735202945233225947821)
            ·
              refine ⟨1006025701104462459730433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2682735202945233225947821 1006025701104462459730433)
              ·
                refine ⟨754519275828346844797825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1006025701104462459730433 754519275828346844797825)
                ·
                  refine ⟨565889456871260133598369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 754519275828346844797825 565889456871260133598369)
                  ·
                    refine ⟨424417092653445100198777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 565889456871260133598369 424417092653445100198777)
                    ·
                      refine ⟨318312819490083825149083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 424417092653445100198777 318312819490083825149083)
                      ·
                        rfl

theorem cell23_619912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_619912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619912 prefixEnd_619912 := by exact prefixLift 619912
  have htrace : WordTrace (prefixWord ++ tailWord_619912) baseStart_619912 baseEnd_619912 := by
    simpa [prefixWord, tailWord_619912, baseEnd_619912] using wordTrace_append hprefix tailTrace_619912
  have hstable : (prefixWord ++ tailWord_619912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619912).length < 2 ^ (prefixWord ++ tailWord_619912).sum := by decide
  have hdescent : baseEnd_619912 < baseStart_619912 := by decide
  rcases family_descends (prefixWord ++ tailWord_619912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619951 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 4]
def baseStart_619951 : Nat := 118140960795 + 619951 * 2 ^ 59
def prefixEnd_619951 : Nat := 4983230072969 + 3 ^ 40 * 619951 * 2
def baseEnd_619951 : Nat := 318332845235609172561403

theorem tailTrace_619951 : CollatzResearch.WordTrace tailWord_619951 prefixEnd_619951 318332845235609172561403 := by
  unfold tailWord_619951
  simp only [CollatzResearch.WordTrace]
  refine ⟨22611470577030881046435707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15074313718020587364290471 22611470577030881046435707)
  ·
    refine ⟨33917205865546321569653561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22611470577030881046435707 33917205865546321569653561)
    ·
      refine ⟨25437904399159741177240171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33917205865546321569653561 25437904399159741177240171)
      ·
        refine ⟨38156856598739611765860257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25437904399159741177240171 38156856598739611765860257)
        ·
          refine ⟨28617642449054708824395193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38156856598739611765860257 28617642449054708824395193)
          ·
            refine ⟨21463231836791031618296395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28617642449054708824395193 21463231836791031618296395)
            ·
              refine ⟨32194847755186547427444593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21463231836791031618296395 32194847755186547427444593)
              ·
                refine ⟨24146135816389910570583445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32194847755186547427444593 24146135816389910570583445)
                ·
                  refine ⟨1131850116393277057996099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24146135816389910570583445 1131850116393277057996099)
                  ·
                    refine ⟨1697775174589915586994149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1131850116393277057996099 1697775174589915586994149)
                    ·
                      refine ⟨318332845235609172561403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1697775174589915586994149 318332845235609172561403)
                      ·
                        rfl

theorem cell23_619951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_619951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619951 prefixEnd_619951 := by exact prefixLift 619951
  have htrace : WordTrace (prefixWord ++ tailWord_619951) baseStart_619951 baseEnd_619951 := by
    simpa [prefixWord, tailWord_619951, baseEnd_619951] using wordTrace_append hprefix tailTrace_619951
  have hstable : (prefixWord ++ tailWord_619951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619951).length < 2 ^ (prefixWord ++ tailWord_619951).sum := by decide
  have hdescent : baseEnd_619951 < baseStart_619951 := by decide
  rcases family_descends (prefixWord ++ tailWord_619951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619968 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 4, 4, 2]
def baseStart_619968 : Nat := 118140960795 + 619968 * 2 ^ 59
def prefixEnd_619968 : Nat := 4983230072969 + 3 ^ 40 * 619968 * 2
def baseEnd_619968 : Nat := 318341574406735606048825

theorem tailTrace_619968 : CollatzResearch.WordTrace tailWord_619968 prefixEnd_619968 318341574406735606048825 := by
  unfold tailWord_619968
  simp only [CollatzResearch.WordTrace]
  refine ⟨11306045308984646474902279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15074727078646195299869705 11306045308984646474902279)
  ·
    refine ⟨16959067963476969712353419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11306045308984646474902279 16959067963476969712353419)
    ·
      refine ⟨25438601945215454568530129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16959067963476969712353419 25438601945215454568530129)
      ·
        refine ⟨19078951458911590926397597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25438601945215454568530129 19078951458911590926397597)
        ·
          refine ⟨7154606797091846597399099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19078951458911590926397597 7154606797091846597399099)
          ·
            refine ⟨10731910195637769896098649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7154606797091846597399099 10731910195637769896098649)
            ·
              refine ⟨8048932646728327422073987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10731910195637769896098649 8048932646728327422073987)
              ·
                refine ⟨12073398970092491133110981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8048932646728327422073987 12073398970092491133110981)
                ·
                  refine ⟨2263762306892342087458309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12073398970092491133110981 2263762306892342087458309)
                  ·
                    refine ⟨424455432542314141398433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2263762306892342087458309 424455432542314141398433)
                    ·
                      refine ⟨318341574406735606048825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 424455432542314141398433 318341574406735606048825)
                      ·
                        rfl

theorem cell23_619968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4, 4, 2].length) (baseStart_619968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_619968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_619968 prefixEnd_619968 := by exact prefixLift 619968
  have htrace : WordTrace (prefixWord ++ tailWord_619968) baseStart_619968 baseEnd_619968 := by
    simpa [prefixWord, tailWord_619968, baseEnd_619968] using wordTrace_append hprefix tailTrace_619968
  have hstable : (prefixWord ++ tailWord_619968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619968).length < 2 ^ (prefixWord ++ tailWord_619968).sum := by decide
  have hdescent : baseEnd_619968 < baseStart_619968 := by decide
  rcases family_descends (prefixWord ++ tailWord_619968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620005 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 2, 2, 3]
def baseStart_620005 : Nat := 118140960795 + 620005 * 2 ^ 59
def prefixEnd_620005 : Nat := 4983230072969 + 3 ^ 40 * 620005 * 2
def baseEnd_620005 : Nat := 318360573190951961286155

theorem tailTrace_620005 : CollatzResearch.WordTrace tailWord_620005 prefixEnd_620005 318360573190951961286155 := by
  unfold tailWord_620005
  simp only [CollatzResearch.WordTrace]
  refine ⟨22613440118835248268901469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15075626745890165512600979 22613440118835248268901469)
  ·
    refine ⟨8480040044563218100838051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22613440118835248268901469 8480040044563218100838051)
    ·
      refine ⟨12720060066844827151257077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8480040044563218100838051 12720060066844827151257077)
      ·
        refine ⟨1192505631266702545430351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12720060066844827151257077 1192505631266702545430351)
        ·
          refine ⟨1788758446900053818145527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1192505631266702545430351 1788758446900053818145527)
          ·
            refine ⟨2683137670350080727218291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788758446900053818145527 2683137670350080727218291)
            ·
              refine ⟨4024706505525121090827437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2683137670350080727218291 4024706505525121090827437)
              ·
                refine ⟨1509264939571920409060289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4024706505525121090827437 1509264939571920409060289)
                ·
                  refine ⟨1131948704678940306795217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1509264939571920409060289 1131948704678940306795217)
                  ·
                    refine ⟨848961528509205230096413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1131948704678940306795217 848961528509205230096413)
                    ·
                      refine ⟨318360573190951961286155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 848961528509205230096413 318360573190951961286155)
                      ·
                        rfl

theorem cell23_620005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_620005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620005 prefixEnd_620005 := by exact prefixLift 620005
  have htrace : WordTrace (prefixWord ++ tailWord_620005) baseStart_620005 baseEnd_620005 := by
    simpa [prefixWord, tailWord_620005, baseEnd_620005] using wordTrace_append hprefix tailTrace_620005
  have hstable : (prefixWord ++ tailWord_620005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620005).length < 2 ^ (prefixWord ++ tailWord_620005).sum := by decide
  have hdescent : baseEnd_620005 < baseStart_620005 := by decide
  rcases family_descends (prefixWord ++ tailWord_620005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620029 : List Nat := [1, 4, 1, 1, 1, 6, 2, 2, 1, 4]
def baseStart_620029 : Nat := 118140960795 + 620029 * 2 ^ 59
def prefixEnd_620029 : Nat := 4983230072969 + 3 ^ 40 * 620029 * 2
def baseEnd_620029 : Nat := 106124298908886622462015

theorem tailTrace_620029 : CollatzResearch.WordTrace tailWord_620029 prefixEnd_620029 106124298908886622462015 := by
  unfold tailWord_620029
  simp only [CollatzResearch.WordTrace]
  refine ⟨22614315470748300367775141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15076210313832200245183427 22614315470748300367775141)
  ·
    refine ⟨4240184150765306318957839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22614315470748300367775141 4240184150765306318957839)
    ·
      refine ⟨6360276226147959478436759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4240184150765306318957839 6360276226147959478436759)
      ·
        refine ⟨9540414339221939217655139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6360276226147959478436759 9540414339221939217655139)
        ·
          refine ⟨14310621508832908826482709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9540414339221939217655139 14310621508832908826482709)
          ·
            refine ⟨670810383226542601241377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14310621508832908826482709 670810383226542601241377)
            ·
              refine ⟨503107787419906950931033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670810383226542601241377 503107787419906950931033)
              ·
                refine ⟨377330840564930213198275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503107787419906950931033 377330840564930213198275)
                ·
                  refine ⟨565996260847395319797413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377330840564930213198275 565996260847395319797413)
                  ·
                    refine ⟨106124298908886622462015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 565996260847395319797413 106124298908886622462015)
                    ·
                      rfl

theorem cell23_620029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_620029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620029 prefixEnd_620029 := by exact prefixLift 620029
  have htrace : WordTrace (prefixWord ++ tailWord_620029) baseStart_620029 baseEnd_620029 := by
    simpa [prefixWord, tailWord_620029, baseEnd_620029] using wordTrace_append hprefix tailTrace_620029
  have hstable : (prefixWord ++ tailWord_620029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620029).length < 2 ^ (prefixWord ++ tailWord_620029).sum := by decide
  have hdescent : baseEnd_620029 < baseStart_620029 := by decide
  rcases family_descends (prefixWord ++ tailWord_620029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620072 : List Nat := [2, 1, 5, 2, 2, 1, 1, 3, 1, 5]
def baseStart_620072 : Nat := 118140960795 + 620072 * 2 ^ 59
def prefixEnd_620072 : Nat := 4983230072969 + 3 ^ 40 * 620072 * 2
def baseEnd_620072 : Nat := 106131658798267733049449

theorem tailTrace_620072 : CollatzResearch.WordTrace tailWord_620072 prefixEnd_620072 106131658798267733049449 := by
  unfold tailWord_620072
  simp only [CollatzResearch.WordTrace]
  refine ⟨11307941904796259355795235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15077255873061679141060313 11307941904796259355795235)
  ·
    refine ⟨16961912857194389033692853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11307941904796259355795235 16961912857194389033692853)
    ·
      refine ⟨1590179330361973971908705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16961912857194389033692853 1590179330361973971908705)
      ·
        refine ⟨1192634497771480478931529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1590179330361973971908705 1192634497771480478931529)
        ·
          refine ⟨894475873328610359198647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1192634497771480478931529 894475873328610359198647)
          ·
            refine ⟨1341713809992915538797971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894475873328610359198647 1341713809992915538797971)
            ·
              refine ⟨2012570714989373308196957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1341713809992915538797971 2012570714989373308196957)
              ·
                refine ⟨754714018121014990573859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2012570714989373308196957 754714018121014990573859)
                ·
                  refine ⟨1132071027181522485860789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754714018121014990573859 1132071027181522485860789)
                  ·
                    refine ⟨106131658798267733049449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1132071027181522485860789 106131658798267733049449)
                    ·
                      rfl

theorem cell23_620072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_620072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620072 prefixEnd_620072 := by exact prefixLift 620072
  have htrace : WordTrace (prefixWord ++ tailWord_620072) baseStart_620072 baseEnd_620072 := by
    simpa [prefixWord, tailWord_620072, baseEnd_620072] using wordTrace_append hprefix tailTrace_620072
  have hstable : (prefixWord ++ tailWord_620072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620072).length < 2 ^ (prefixWord ++ tailWord_620072).sum := by decide
  have hdescent : baseEnd_620072 < baseStart_620072 := by decide
  rcases family_descends (prefixWord ++ tailWord_620072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620085 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 4, 4]
def baseStart_620085 : Nat := 118140960795 + 620085 * 2 ^ 59
def prefixEnd_620085 : Nat := 4983230072969 + 3 ^ 40 * 620085 * 2
def baseEnd_620085 : Nat := 106133883881103882761929

theorem tailTrace_620085 : CollatzResearch.WordTrace tailWord_620085 prefixEnd_620085 106133883881103882761929 := by
  unfold tailWord_620085
  simp only [CollatzResearch.WordTrace]
  refine ⟨22616357958545421931813709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15077571972363614621209139 22616357958545421931813709)
  ·
    refine ⟨8481134234454533224430141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22616357958545421931813709 8481134234454533224430141)
    ·
      refine ⟨3180425337920449959161303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8481134234454533224430141 3180425337920449959161303)
      ·
        refine ⟨4770638006880674938741955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3180425337920449959161303 4770638006880674938741955)
        ·
          refine ⟨7155957010321012408112933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4770638006880674938741955 7155957010321012408112933)
          ·
            refine ⟨1341741939435189826521175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7155957010321012408112933 1341741939435189826521175)
            ·
              refine ⟨2012612909152784739781763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1341741939435189826521175 2012612909152784739781763)
              ·
                refine ⟨3018919363729177109672645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2012612909152784739781763 3018919363729177109672645)
                ·
                  refine ⟨566047380699220708063621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3018919363729177109672645 566047380699220708063621)
                  ·
                    refine ⟨106133883881103882761929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 566047380699220708063621 106133883881103882761929)
                    ·
                      rfl

theorem cell23_620085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_620085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620085 prefixEnd_620085 := by exact prefixLift 620085
  have htrace : WordTrace (prefixWord ++ tailWord_620085) baseStart_620085 baseEnd_620085 := by
    simpa [prefixWord, tailWord_620085, baseEnd_620085] using wordTrace_append hprefix tailTrace_620085
  have hstable : (prefixWord ++ tailWord_620085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620085).length < 2 ^ (prefixWord ++ tailWord_620085).sum := by decide
  have hdescent : baseEnd_620085 < baseStart_620085 := by decide
  rcases family_descends (prefixWord ++ tailWord_620085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620109 : List Nat := [1, 6, 1, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_620109 : Nat := 118140960795 + 620109 * 2 ^ 59
def prefixEnd_620109 : Nat := 4983230072969 + 3 ^ 40 * 620109 * 2
def baseEnd_620109 : Nat := 318413975179019554385677

theorem tailTrace_620109 : CollatzResearch.WordTrace tailWord_620109 prefixEnd_620109 318413975179019554385677 := by
  unfold tailWord_620109
  simp only [CollatzResearch.WordTrace]
  refine ⟨22617233310458474030687381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15078155540305649353791587 22617233310458474030687381)
  ·
    refine ⟨1060182811427740970188471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22617233310458474030687381 1060182811427740970188471)
    ·
      refine ⟨1590274217141611455282707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1060182811427740970188471 1590274217141611455282707)
      ·
        refine ⟨2385411325712417182924061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1590274217141611455282707 2385411325712417182924061)
        ·
          refine ⟨894529247142156443596523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2385411325712417182924061 894529247142156443596523)
          ·
            refine ⟨1341793870713234665394785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894529247142156443596523 1341793870713234665394785)
            ·
              refine ⟨1006345403034925999046089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1341793870713234665394785 1006345403034925999046089)
              ·
                refine ⟨754759052276194499284567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1006345403034925999046089 754759052276194499284567)
                ·
                  refine ⟨1132138578414291748926851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754759052276194499284567 1132138578414291748926851)
                  ·
                    refine ⟨1698207867621437623390277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1132138578414291748926851 1698207867621437623390277)
                    ·
                      refine ⟨318413975179019554385677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1698207867621437623390277 318413975179019554385677)
                      ·
                        rfl

theorem cell23_620109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_620109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620109 prefixEnd_620109 := by exact prefixLift 620109
  have htrace : WordTrace (prefixWord ++ tailWord_620109) baseStart_620109 baseEnd_620109 := by
    simpa [prefixWord, tailWord_620109, baseEnd_620109] using wordTrace_append hprefix tailTrace_620109
  have hstable : (prefixWord ++ tailWord_620109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620109).length < 2 ^ (prefixWord ++ tailWord_620109).sum := by decide
  have hdescent : baseEnd_620109 < baseStart_620109 := by decide
  rcases family_descends (prefixWord ++ tailWord_620109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620205 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 7]
def baseStart_620205 : Nat := 118140960795 + 620205 * 2 ^ 59
def prefixEnd_620205 : Nat := 4983230072969 + 3 ^ 40 * 620205 * 2
def baseEnd_620205 : Nat := 35384807702427908753915

theorem tailTrace_620205 : CollatzResearch.WordTrace tailWord_620205 prefixEnd_620205 35384807702427908753915 := by
  unfold tailWord_620205
  simp only [CollatzResearch.WordTrace]
  refine ⟨22620734718110682426182069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15080489812073788284121379 22620734718110682426182069)
  ·
    refine ⟨2120693879822876477454569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22620734718110682426182069 2120693879822876477454569)
    ·
      refine ⟨1590520409867157358090927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2120693879822876477454569 1590520409867157358090927)
      ·
        refine ⟨2385780614800736037136391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1590520409867157358090927 2385780614800736037136391)
        ·
          refine ⟨3578670922201104055704587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2385780614800736037136391 3578670922201104055704587)
          ·
            refine ⟨5368006383301656083556881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3578670922201104055704587 5368006383301656083556881)
            ·
              refine ⟨4026004787476242062667661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5368006383301656083556881 4026004787476242062667661)
              ·
                refine ⟨1509751795303590773500373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4026004787476242062667661 1509751795303590773500373)
                ·
                  refine ⟨35384807702427908753915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1509751795303590773500373 35384807702427908753915)
                  ·
                    rfl

theorem cell23_620205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_620205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620205 prefixEnd_620205 := by exact prefixLift 620205
  have htrace : WordTrace (prefixWord ++ tailWord_620205) baseStart_620205 baseEnd_620205 := by
    simpa [prefixWord, tailWord_620205, baseEnd_620205] using wordTrace_append hprefix tailTrace_620205
  have hstable : (prefixWord ++ tailWord_620205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620205).length < 2 ^ (prefixWord ++ tailWord_620205).sum := by decide
  have hdescent : baseEnd_620205 < baseStart_620205 := by decide
  rcases family_descends (prefixWord ++ tailWord_620205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620215 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 3]
def baseStart_620215 : Nat := 118140960795 + 620215 * 2 ^ 59
def prefixEnd_620215 : Nat := 4983230072969 + 3 ^ 40 * 620215 * 2
def baseEnd_620215 : Nat := 318468404128396139660189

theorem tailTrace_620215 : CollatzResearch.WordTrace tailWord_620215 prefixEnd_620215 318468404128396139660189 := by
  unfold tailWord_620215
  simp only [CollatzResearch.WordTrace]
  refine ⟨22621099448074454134046099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15080732965382969422697399 22621099448074454134046099)
  ·
    refine ⟨33931649172111681201069149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22621099448074454134046099 33931649172111681201069149)
    ·
      refine ⟨12724368439541880450400931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33931649172111681201069149 12724368439541880450400931)
      ·
        refine ⟨19086552659312820675601397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12724368439541880450400931 19086552659312820675601397)
        ·
          refine ⟨1789364311810576938337631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19086552659312820675601397 1789364311810576938337631)
          ·
            refine ⟨2684046467715865407506447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789364311810576938337631 2684046467715865407506447)
            ·
              refine ⟨4026069701573798111259671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684046467715865407506447 4026069701573798111259671)
              ·
                refine ⟨6039104552360697166889507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026069701573798111259671 6039104552360697166889507)
                ·
                  refine ⟨9058656828541045750334261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6039104552360697166889507 9058656828541045750334261)
                  ·
                    refine ⟨849249077675723039093837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9058656828541045750334261 849249077675723039093837)
                    ·
                      refine ⟨318468404128396139660189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 849249077675723039093837 318468404128396139660189)
                      ·
                        rfl

theorem cell23_620215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_620215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620215 prefixEnd_620215 := by exact prefixLift 620215
  have htrace : WordTrace (prefixWord ++ tailWord_620215) baseStart_620215 baseEnd_620215 := by
    simpa [prefixWord, tailWord_620215, baseEnd_620215] using wordTrace_append hprefix tailTrace_620215
  have hstable : (prefixWord ++ tailWord_620215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620215).length < 2 ^ (prefixWord ++ tailWord_620215).sum := by decide
  have hdescent : baseEnd_620215 < baseStart_620215 := by decide
  rcases family_descends (prefixWord ++ tailWord_620215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620255 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 4]
def baseStart_620255 : Nat := 118140960795 + 620255 * 2 ^ 59
def prefixEnd_620255 : Nat := 4983230072969 + 3 ^ 40 * 620255 * 2
def baseEnd_620255 : Nat := 318488943354575983160005

theorem tailTrace_620255 : CollatzResearch.WordTrace tailWord_620255 prefixEnd_620255 318488943354575983160005 := by
  unfold tailWord_620255
  simp only [CollatzResearch.WordTrace]
  refine ⟨22622558367929540965502219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15081705578619693977001479 22622558367929540965502219)
  ·
    refine ⟨33933837551894311448253329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22622558367929540965502219 33933837551894311448253329)
    ·
      refine ⟨25450378163920733586189997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33933837551894311448253329 25450378163920733586189997)
      ·
        refine ⟨9543891811470275094821249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25450378163920733586189997 9543891811470275094821249)
        ·
          refine ⟨7157918858602706321115937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9543891811470275094821249 7157918858602706321115937)
          ·
            refine ⟨5368439143952029740836953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7157918858602706321115937 5368439143952029740836953)
            ·
              refine ⟨4026329357964022305627715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5368439143952029740836953 4026329357964022305627715)
              ·
                refine ⟨6039494036946033458441573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026329357964022305627715 6039494036946033458441573)
                ·
                  refine ⟨1132405131927381273457795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6039494036946033458441573 1132405131927381273457795)
                  ·
                    refine ⟨1698607697891071910186693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1132405131927381273457795 1698607697891071910186693)
                    ·
                      refine ⟨318488943354575983160005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1698607697891071910186693 318488943354575983160005)
                      ·
                        rfl

theorem cell23_620255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_620255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620255 prefixEnd_620255 := by exact prefixLift 620255
  have htrace : WordTrace (prefixWord ++ tailWord_620255) baseStart_620255 baseEnd_620255 := by
    simpa [prefixWord, tailWord_620255, baseEnd_620255] using wordTrace_append hprefix tailTrace_620255
  have hstable : (prefixWord ++ tailWord_620255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620255).length < 2 ^ (prefixWord ++ tailWord_620255).sum := by decide
  have hdescent : baseEnd_620255 < baseStart_620255 := by decide
  rcases family_descends (prefixWord ++ tailWord_620255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620275 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 3]
def baseStart_620275 : Nat := 118140960795 + 620275 * 2 ^ 59
def prefixEnd_620275 : Nat := 4983230072969 + 3 ^ 40 * 620275 * 2
def baseEnd_620275 : Nat := 318499212967665904909913

theorem tailTrace_620275 : CollatzResearch.WordTrace tailWord_620275 prefixEnd_620275 318499212967665904909913 := by
  unfold tailWord_620275
  simp only [CollatzResearch.WordTrace]
  refine ⟨22623287827857084381230279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15082191885238056254153519 22623287827857084381230279)
  ·
    refine ⟨33934931741785626571845419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22623287827857084381230279 33934931741785626571845419)
    ·
      refine ⟨50902397612678439857768129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33934931741785626571845419 50902397612678439857768129)
      ·
        refine ⟨38176798209508829893326097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50902397612678439857768129 38176798209508829893326097)
        ·
          refine ⟨28632598657131622419994573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38176798209508829893326097 28632598657131622419994573)
          ·
            refine ⟨10737224496424358407497965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28632598657131622419994573 10737224496424358407497965)
            ·
              refine ⟨4026459186159134402811737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10737224496424358407497965 4026459186159134402811737)
              ·
                refine ⟨3019844389619350802108803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4026459186159134402811737 3019844389619350802108803)
                ·
                  refine ⟨4529766584429026203163205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3019844389619350802108803 4529766584429026203163205)
                  ·
                    refine ⟨849331234580442413093101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4529766584429026203163205 849331234580442413093101)
                    ·
                      refine ⟨318499212967665904909913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 849331234580442413093101 318499212967665904909913)
                      ·
                        rfl

theorem cell23_620275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 3].length) (baseStart_620275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620275 prefixEnd_620275 := by exact prefixLift 620275
  have htrace : WordTrace (prefixWord ++ tailWord_620275) baseStart_620275 baseEnd_620275 := by
    simpa [prefixWord, tailWord_620275, baseEnd_620275] using wordTrace_append hprefix tailTrace_620275
  have hstable : (prefixWord ++ tailWord_620275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620275).length < 2 ^ (prefixWord ++ tailWord_620275).sum := by decide
  have hdescent : baseEnd_620275 < baseStart_620275 := by decide
  rcases family_descends (prefixWord ++ tailWord_620275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620292 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_620292 : Nat := 118140960795 + 620292 * 2 ^ 59
def prefixEnd_620292 : Nat := 4983230072969 + 3 ^ 40 * 620292 * 2
def baseEnd_620292 : Nat := 318507942138792338397335

theorem tailTrace_620292 : CollatzResearch.WordTrace tailWord_620292 prefixEnd_620292 318507942138792338397335 := by
  unfold tailWord_620292
  simp only [CollatzResearch.WordTrace]
  refine ⟨11311953934397748142299565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15082605245863664189732753 11311953934397748142299565)
  ·
    refine ⟨4241982725399155553362337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11311953934397748142299565 4241982725399155553362337)
    ·
      refine ⟨3181487044049366665021753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4241982725399155553362337 3181487044049366665021753)
      ·
        refine ⟨2386115283037024998766315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3181487044049366665021753 2386115283037024998766315)
        ·
          refine ⟨3579172924555537498149473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2386115283037024998766315 3579172924555537498149473)
          ·
            refine ⟨2684379693416653123612105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3579172924555537498149473 2684379693416653123612105)
            ·
              refine ⟨2013284770062489842709079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2684379693416653123612105 2013284770062489842709079)
              ·
                refine ⟨3019927155093734764063619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013284770062489842709079 3019927155093734764063619)
                ·
                  refine ⟨4529890732640602146095429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3019927155093734764063619 4529890732640602146095429)
                  ·
                    refine ⟨849354512370112902392893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4529890732640602146095429 849354512370112902392893)
                    ·
                      refine ⟨318507942138792338397335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 849354512370112902392893 318507942138792338397335)
                      ·
                        rfl

theorem cell23_620292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_620292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620292 prefixEnd_620292 := by exact prefixLift 620292
  have htrace : WordTrace (prefixWord ++ tailWord_620292) baseStart_620292 baseEnd_620292 := by
    simpa [prefixWord, tailWord_620292, baseEnd_620292] using wordTrace_append hprefix tailTrace_620292
  have hstable : (prefixWord ++ tailWord_620292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620292).length < 2 ^ (prefixWord ++ tailWord_620292).sum := by decide
  have hdescent : baseEnd_620292 < baseStart_620292 := by decide
  rcases family_descends (prefixWord ++ tailWord_620292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620299 : List Nat := [1, 1, 1, 1, 5, 1, 5, 3, 1, 4]
def baseStart_620299 : Nat := 118140960795 + 620299 * 2 ^ 59
def prefixEnd_620299 : Nat := 4983230072969 + 3 ^ 40 * 620299 * 2
def baseEnd_620299 : Nat := 106170512167791270336601

theorem tailTrace_620299 : CollatzResearch.WordTrace tailWord_620299 prefixEnd_620299 106170512167791270336601 := by
  unfold tailWord_620299
  simp only [CollatzResearch.WordTrace]
  refine ⟨22624163179770136480103951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15082775453180090986735967 22624163179770136480103951)
  ·
    refine ⟨33936244769655204720155927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22624163179770136480103951 33936244769655204720155927)
    ·
      refine ⟨50904367154482807080233891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33936244769655204720155927 50904367154482807080233891)
      ·
        refine ⟨76356550731724210620350837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50904367154482807080233891 76356550731724210620350837)
        ·
          refine ⟨7158426631099144745657891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76356550731724210620350837 7158426631099144745657891)
          ·
            refine ⟨10737639946648717118486837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7158426631099144745657891 10737639946648717118486837)
            ·
              refine ⟨1006653744998317229858141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10737639946648717118486837 1006653744998317229858141)
              ·
                refine ⟨377495154374368961196803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1006653744998317229858141 377495154374368961196803)
                ·
                  refine ⟨566242731561553441795205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377495154374368961196803 566242731561553441795205)
                  ·
                    refine ⟨106170512167791270336601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 566242731561553441795205 106170512167791270336601)
                    ·
                      rfl

theorem cell23_620299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 1, 4].length) (baseStart_620299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620299 prefixEnd_620299 := by exact prefixLift 620299
  have htrace : WordTrace (prefixWord ++ tailWord_620299) baseStart_620299 baseEnd_620299 := by
    simpa [prefixWord, tailWord_620299, baseEnd_620299] using wordTrace_append hprefix tailTrace_620299
  have hstable : (prefixWord ++ tailWord_620299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620299).length < 2 ^ (prefixWord ++ tailWord_620299).sum := by decide
  have hdescent : baseEnd_620299 < baseStart_620299 := by decide
  rcases family_descends (prefixWord ++ tailWord_620299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620316 : List Nat := [2, 2, 3, 1, 1, 2, 5, 2, 1, 4]
def baseStart_620316 : Nat := 118140960795 + 620316 * 2 ^ 59
def prefixEnd_620316 : Nat := 4983230072969 + 3 ^ 40 * 620316 * 2
def baseEnd_620316 : Nat := 106173421891500081499075

theorem tailTrace_620316 : CollatzResearch.WordTrace tailWord_620316 prefixEnd_620316 106173421891500081499075 := by
  unfold tailWord_620316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11312391610354274191736401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15083188813805698922315201 11312391610354274191736401)
  ·
    refine ⟨8484293707765705643802301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11312391610354274191736401 8484293707765705643802301)
    ·
      refine ⟨3181610140412139616425863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8484293707765705643802301 3181610140412139616425863)
      ·
        refine ⟨4772415210618209424638795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3181610140412139616425863 4772415210618209424638795)
        ·
          refine ⟨7158622815927314136958193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4772415210618209424638795 7158622815927314136958193)
          ·
            refine ⟨5368967111945485602718645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7158622815927314136958193 5368967111945485602718645)
            ·
              refine ⟨503340666744889275254873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5368967111945485602718645 503340666744889275254873)
              ·
                refine ⟨377505500058666956441155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503340666744889275254873 377505500058666956441155)
                ·
                  refine ⟨566258250088000434661733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377505500058666956441155 566258250088000434661733)
                  ·
                    refine ⟨106173421891500081499075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 566258250088000434661733 106173421891500081499075)
                    ·
                      rfl

theorem cell23_620316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_620316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620316 prefixEnd_620316 := by exact prefixLift 620316
  have htrace : WordTrace (prefixWord ++ tailWord_620316) baseStart_620316 baseEnd_620316 := by
    simpa [prefixWord, tailWord_620316, baseEnd_620316] using wordTrace_append hprefix tailTrace_620316
  have hstable : (prefixWord ++ tailWord_620316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620316).length < 2 ^ (prefixWord ++ tailWord_620316).sum := by decide
  have hdescent : baseEnd_620316 < baseStart_620316 := by decide
  rcases family_descends (prefixWord ++ tailWord_620316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620355 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 3, 6]
def baseStart_620355 : Nat := 118140960795 + 620355 * 2 ^ 59
def prefixEnd_620355 : Nat := 4983230072969 + 3 ^ 40 * 620355 * 2
def baseEnd_620355 : Nat := 106180097140008530636515

theorem tailTrace_620355 : CollatzResearch.WordTrace tailWord_620355 prefixEnd_620355 106180097140008530636515 := by
  unfold tailWord_620355
  simp only [CollatzResearch.WordTrace]
  refine ⟨22626205667567258044142519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15084137111711505362761679 22626205667567258044142519)
  ·
    refine ⟨33939308501350887066213779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22626205667567258044142519 33939308501350887066213779)
    ·
      refine ⟨50908962752026330599320669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33939308501350887066213779 50908962752026330599320669)
      ·
        refine ⟨19090861032009873974745251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50908962752026330599320669 19090861032009873974745251)
        ·
          refine ⟨28636291548014810962117877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19090861032009873974745251 28636291548014810962117877)
          ·
            refine ⟨2684652332626388527698551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28636291548014810962117877 2684652332626388527698551)
            ·
              refine ⟨4026978498939582791547827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684652332626388527698551 4026978498939582791547827)
              ·
                refine ⟨6040467748409374187321741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026978498939582791547827 6040467748409374187321741)
                ·
                  refine ⟨2265175405653515320245653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6040467748409374187321741 2265175405653515320245653)
                  ·
                    refine ⟨106180097140008530636515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2265175405653515320245653 106180097140008530636515)
                    ·
                      rfl

theorem cell23_620355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 6].length) (baseStart_620355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620355 prefixEnd_620355 := by exact prefixLift 620355
  have htrace : WordTrace (prefixWord ++ tailWord_620355) baseStart_620355 baseEnd_620355 := by
    simpa [prefixWord, tailWord_620355, baseEnd_620355] using wordTrace_append hprefix tailTrace_620355
  have hstable : (prefixWord ++ tailWord_620355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620355).length < 2 ^ (prefixWord ++ tailWord_620355).sum := by decide
  have hdescent : baseEnd_620355 < baseStart_620355 := by decide
  rcases family_descends (prefixWord ++ tailWord_620355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620373 : List Nat := [1, 3, 2, 2, 2, 2, 4, 2, 1, 1, 3]
def baseStart_620373 : Nat := 118140960795 + 620373 * 2 ^ 59
def prefixEnd_620373 : Nat := 4983230072969 + 3 ^ 40 * 620373 * 2
def baseEnd_620373 : Nat := 318549534071806521484463

theorem tailTrace_620373 : CollatzResearch.WordTrace tailWord_620373 prefixEnd_620373 318549534071806521484463 := by
  unfold tailWord_620373
  simp only [CollatzResearch.WordTrace]
  refine ⟨22626862181502047118297773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15084574787668031412198515 22626862181502047118297773)
  ·
    refine ⟨8485073318063267669361665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22626862181502047118297773 8485073318063267669361665)
    ·
      refine ⟨6363804988547450752021249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8485073318063267669361665 6363804988547450752021249)
      ·
        refine ⟨4772853741410588064015937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6363804988547450752021249 4772853741410588064015937)
        ·
          refine ⟨3579640306057941048011953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4772853741410588064015937 3579640306057941048011953)
          ·
            refine ⟨2684730229543455786008965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3579640306057941048011953 2684730229543455786008965)
            ·
              refine ⟨503386918039397959876681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2684730229543455786008965 503386918039397959876681)
              ·
                refine ⟨377540188529548469907511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503386918039397959876681 377540188529548469907511)
                ·
                  refine ⟨566310282794322704861267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377540188529548469907511 566310282794322704861267)
                  ·
                    refine ⟨849465424191484057291901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 566310282794322704861267 849465424191484057291901)
                    ·
                      refine ⟨318549534071806521484463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 849465424191484057291901 318549534071806521484463)
                      ·
                        rfl

theorem cell23_620373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_620373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620373 prefixEnd_620373 := by exact prefixLift 620373
  have htrace : WordTrace (prefixWord ++ tailWord_620373) baseStart_620373 baseEnd_620373 := by
    simpa [prefixWord, tailWord_620373, baseEnd_620373] using wordTrace_append hprefix tailTrace_620373
  have hstable : (prefixWord ++ tailWord_620373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620373).length < 2 ^ (prefixWord ++ tailWord_620373).sum := by decide
  have hdescent : baseEnd_620373 < baseStart_620373 := by decide
  rcases family_descends (prefixWord ++ tailWord_620373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620396 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 3, 2, 2]
def baseStart_620396 : Nat := 118140960795 + 620396 * 2 ^ 59
def prefixEnd_620396 : Nat := 4983230072969 + 3 ^ 40 * 620396 * 2
def baseEnd_620396 : Nat := 318561344126859931496857

theorem tailTrace_620396 : CollatzResearch.WordTrace tailWord_620396 prefixEnd_620396 318561344126859931496857 := by
  unfold tailWord_620396
  simp only [CollatzResearch.WordTrace]
  refine ⟨11313850530209361023192521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15085134040279148030923361 11313850530209361023192521)
  ·
    refine ⟨8485387897657020767394391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11313850530209361023192521 8485387897657020767394391)
    ·
      refine ⟨12728081846485531151091587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8485387897657020767394391 12728081846485531151091587)
      ·
        refine ⟨19092122769728296726637381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12728081846485531151091587 19092122769728296726637381)
        ·
          refine ⟨3579773019324055636244509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19092122769728296726637381 3579773019324055636244509)
          ·
            refine ⟨1342414882246520863591691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3579773019324055636244509 1342414882246520863591691)
            ·
              refine ⟨2013622323369781295387537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342414882246520863591691 2013622323369781295387537)
              ·
                refine ⟨1510216742527335971540653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2013622323369781295387537 1510216742527335971540653)
                ·
                  refine ⟨566331278447750989327745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1510216742527335971540653 566331278447750989327745)
                  ·
                    refine ⟨424748458835813241995809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 566331278447750989327745 424748458835813241995809)
                    ·
                      refine ⟨318561344126859931496857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 424748458835813241995809 318561344126859931496857)
                      ·
                        rfl

theorem cell23_620396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 2, 2].length) (baseStart_620396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620396 prefixEnd_620396 := by exact prefixLift 620396
  have htrace : WordTrace (prefixWord ++ tailWord_620396) baseStart_620396 baseEnd_620396 := by
    simpa [prefixWord, tailWord_620396, baseEnd_620396] using wordTrace_append hprefix tailTrace_620396
  have hstable : (prefixWord ++ tailWord_620396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620396).length < 2 ^ (prefixWord ++ tailWord_620396).sum := by decide
  have hdescent : baseEnd_620396 < baseStart_620396 := by decide
  rcases family_descends (prefixWord ++ tailWord_620396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620423 : List Nat := [1, 1, 4, 2, 5, 1, 1, 2, 2, 4]
def baseStart_620423 : Nat := 118140960795 + 620423 * 2 ^ 59
def prefixEnd_620423 : Nat := 4983230072969 + 3 ^ 40 * 620423 * 2
def baseEnd_620423 : Nat := 106191736034843775286411

theorem tailTrace_620423 : CollatzResearch.WordTrace tailWord_620423 prefixEnd_620423 106191736034843775286411 := by
  unfold tailWord_620423
  simp only [CollatzResearch.WordTrace]
  refine ⟨22628685831320905657617923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15085790554213937105078615 22628685831320905657617923)
  ·
    refine ⟨33943028746981358486426885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22628685831320905657617923 33943028746981358486426885)
    ·
      refine ⟨6364317890059004716205041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33943028746981358486426885 6364317890059004716205041)
      ·
        refine ⟨4773238417544253537153781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6364317890059004716205041 4773238417544253537153781)
        ·
          refine ⟨447491101644773769108167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4773238417544253537153781 447491101644773769108167)
          ·
            refine ⟨671236652467160653662251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447491101644773769108167 671236652467160653662251)
            ·
              refine ⟨1006854978700740980493377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671236652467160653662251 1006854978700740980493377)
              ·
                refine ⟨755141234025555735370033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1006854978700740980493377 755141234025555735370033)
                ·
                  refine ⟨566355925519166801527525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 755141234025555735370033 566355925519166801527525)
                  ·
                    refine ⟨106191736034843775286411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 566355925519166801527525 106191736034843775286411)
                    ·
                      rfl

theorem cell23_620423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_620423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620423 prefixEnd_620423 := by exact prefixLift 620423
  have htrace : WordTrace (prefixWord ++ tailWord_620423) baseStart_620423 baseEnd_620423 := by
    simpa [prefixWord, tailWord_620423, baseEnd_620423] using wordTrace_append hprefix tailTrace_620423
  have hstable : (prefixWord ++ tailWord_620423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620423).length < 2 ^ (prefixWord ++ tailWord_620423).sum := by decide
  have hdescent : baseEnd_620423 < baseStart_620423 := by decide
  rcases family_descends (prefixWord ++ tailWord_620423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620430 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2]
def baseStart_620430 : Nat := 118140960795 + 620430 * 2 ^ 59
def prefixEnd_620430 : Nat := 4983230072969 + 3 ^ 40 * 620430 * 2
def baseEnd_620430 : Nat := 318578802469112798471701

theorem tailTrace_620430 : CollatzResearch.WordTrace tailWord_620430 prefixEnd_620430 318578802469112798471701 := by
  unfold tailWord_620430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2828617642786943231640343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15085960761530363902081829 2828617642786943231640343)
  ·
    refine ⟨4242926464180414847460515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2828617642786943231640343 4242926464180414847460515)
    ·
      refine ⟨6364389696270622271190773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4242926464180414847460515 6364389696270622271190773)
      ·
        refine ⟨596661534025370837924135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6364389696270622271190773 596661534025370837924135)
        ·
          refine ⟨894992301038056256886203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596661534025370837924135 894992301038056256886203)
          ·
            refine ⟨1342488451557084385329305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894992301038056256886203 1342488451557084385329305)
            ·
              refine ⟨1006866338667813288996979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1342488451557084385329305 1006866338667813288996979)
              ·
                refine ⟨1510299508001719933495469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1006866338667813288996979 1510299508001719933495469)
                ·
                  refine ⟨566362315500644975060801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1510299508001719933495469 566362315500644975060801)
                  ·
                    refine ⟨424771736625483731295601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 566362315500644975060801 424771736625483731295601)
                    ·
                      refine ⟨318578802469112798471701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 424771736625483731295601 318578802469112798471701)
                      ·
                        rfl

theorem cell23_620430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_620430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620430 prefixEnd_620430 := by exact prefixLift 620430
  have htrace : WordTrace (prefixWord ++ tailWord_620430) baseStart_620430 baseEnd_620430 := by
    simpa [prefixWord, tailWord_620430, baseEnd_620430] using wordTrace_append hprefix tailTrace_620430
  have hstable : (prefixWord ++ tailWord_620430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620430).length < 2 ^ (prefixWord ++ tailWord_620430).sum := by decide
  have hdescent : baseEnd_620430 < baseStart_620430 := by decide
  rcases family_descends (prefixWord ++ tailWord_620430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620472 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_620472 : Nat := 118140960795 + 620472 * 2 ^ 59
def prefixEnd_620472 : Nat := 4983230072969 + 3 ^ 40 * 620472 * 2
def baseEnd_620472 : Nat := 318600368656601634146507

theorem tailTrace_620472 : CollatzResearch.WordTrace tailWord_620472 prefixEnd_620472 318600368656601634146507 := by
  unfold tailWord_620472
  simp only [CollatzResearch.WordTrace]
  refine ⟨11315236504071693513075835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15086982005428924684101113 11315236504071693513075835)
  ·
    refine ⟨16972854756107540269613753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11315236504071693513075835 16972854756107540269613753)
    ·
      refine ⟨12729641067080655202210315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16972854756107540269613753 12729641067080655202210315)
      ·
        refine ⟨19094461600620982803315473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12729641067080655202210315 19094461600620982803315473)
        ·
          refine ⟨14320846200465737102486605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19094461600620982803315473 14320846200465737102486605)
          ·
            refine ⟨5370317325174651413432477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14320846200465737102486605 5370317325174651413432477)
            ·
              refine ⟨2013868996940494280037179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5370317325174651413432477 2013868996940494280037179)
              ·
                refine ⟨3020803495410741420055769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013868996940494280037179 3020803495410741420055769)
                ·
                  refine ⟨2265602621558056065041827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3020803495410741420055769 2265602621558056065041827)
                  ·
                    refine ⟨3398403932337084097562741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2265602621558056065041827 3398403932337084097562741)
                    ·
                      refine ⟨318600368656601634146507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3398403932337084097562741 318600368656601634146507)
                      ·
                        rfl

theorem cell23_620472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_620472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620472 prefixEnd_620472 := by exact prefixLift 620472
  have htrace : WordTrace (prefixWord ++ tailWord_620472) baseStart_620472 baseEnd_620472 := by
    simpa [prefixWord, tailWord_620472, baseEnd_620472] using wordTrace_append hprefix tailTrace_620472
  have hstable : (prefixWord ++ tailWord_620472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620472).length < 2 ^ (prefixWord ++ tailWord_620472).sum := by decide
  have hdescent : baseEnd_620472 < baseStart_620472 := by decide
  rcases family_descends (prefixWord ++ tailWord_620472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620475 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 11]
def baseStart_620475 : Nat := 118140960795 + 620475 * 2 ^ 59
def prefixEnd_620475 : Nat := 4983230072969 + 3 ^ 40 * 620475 * 2
def baseEnd_620475 : Nat := 35400212122062791378777

theorem tailTrace_620475 : CollatzResearch.WordTrace tailWord_620475 prefixEnd_620475 35400212122062791378777 := by
  unfold tailWord_620475
  simp only [CollatzResearch.WordTrace]
  refine ⟨22630582427132518538510879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15087054951421679025673919 22630582427132518538510879)
  ·
    refine ⟨33945873640698777807766319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22630582427132518538510879 33945873640698777807766319)
    ·
      refine ⟨50918810461048166711649479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33945873640698777807766319 50918810461048166711649479)
      ·
        refine ⟨76378215691572250067474219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50918810461048166711649479 76378215691572250067474219)
        ·
          refine ⟨114567323537358375101211329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76378215691572250067474219 114567323537358375101211329)
          ·
            refine ⟨85925492653018781325908497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114567323537358375101211329 85925492653018781325908497)
            ·
              refine ⟨64444119489764085994431373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85925492653018781325908497 64444119489764085994431373)
              ·
                refine ⟨24166544808661532247911765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64444119489764085994431373 24166544808661532247911765)
                ·
                  refine ⟨35400212122062791378777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 24166544808661532247911765 35400212122062791378777)
                  ·
                    rfl

theorem cell23_620475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 11].length) (baseStart_620475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620475 prefixEnd_620475 := by exact prefixLift 620475
  have htrace : WordTrace (prefixWord ++ tailWord_620475) baseStart_620475 baseEnd_620475 := by
    simpa [prefixWord, tailWord_620475, baseEnd_620475] using wordTrace_append hprefix tailTrace_620475
  have hstable : (prefixWord ++ tailWord_620475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620475).length < 2 ^ (prefixWord ++ tailWord_620475).sum := by decide
  have hdescent : baseEnd_620475 < baseStart_620475 := by decide
  rcases family_descends (prefixWord ++ tailWord_620475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620579 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 3]
def baseStart_620579 : Nat := 118140960795 + 620579 * 2 ^ 59
def prefixEnd_620579 : Nat := 4983230072969 + 3 ^ 40 * 620579 * 2
def baseEnd_620579 : Nat := 318655311086632715508515

theorem tailTrace_620579 : CollatzResearch.WordTrace tailWord_620579 prefixEnd_620579 318655311086632715508515 := by
  unfold tailWord_620579
  simp only [CollatzResearch.WordTrace]
  refine ⟨22634375618755744300296791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15089583745837162866864527 22634375618755744300296791)
  ·
    refine ⟨33951563428133616450445187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22634375618755744300296791 33951563428133616450445187)
    ·
      refine ⟨50927345142200424675667781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33951563428133616450445187 50927345142200424675667781)
      ·
        refine ⟨9548877214162579626687709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50927345142200424675667781 9548877214162579626687709)
        ·
          refine ⟨3580828955310967360007891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9548877214162579626687709 3580828955310967360007891)
          ·
            refine ⟨5371243432966451040011837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3580828955310967360007891 5371243432966451040011837)
            ·
              refine ⟨2014216287362419140004439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5371243432966451040011837 2014216287362419140004439)
              ·
                refine ⟨3021324431043628710006659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2014216287362419140004439 3021324431043628710006659)
                ·
                  refine ⟨4531986646565443065009989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3021324431043628710006659 4531986646565443065009989)
                  ·
                    refine ⟨849747496231020574689373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4531986646565443065009989 849747496231020574689373)
                    ·
                      refine ⟨318655311086632715508515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 849747496231020574689373 318655311086632715508515)
                      ·
                        rfl

theorem cell23_620579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_620579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620579 prefixEnd_620579 := by exact prefixLift 620579
  have htrace : WordTrace (prefixWord ++ tailWord_620579) baseStart_620579 baseEnd_620579 := by
    simpa [prefixWord, tailWord_620579, baseEnd_620579] using wordTrace_append hprefix tailTrace_620579
  have hstable : (prefixWord ++ tailWord_620579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620579).length < 2 ^ (prefixWord ++ tailWord_620579).sum := by decide
  have hdescent : baseEnd_620579 < baseStart_620579 := by decide
  rcases family_descends (prefixWord ++ tailWord_620579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620599 : List Nat := [1, 1, 3, 1, 2, 2, 5, 2, 6]
def baseStart_620599 : Nat := 118140960795 + 620599 * 2 ^ 59
def prefixEnd_620599 : Nat := 4983230072969 + 3 ^ 40 * 620599 * 2
def baseEnd_620599 : Nat := 35407286744413626362047

theorem tailTrace_620599 : CollatzResearch.WordTrace tailWord_620599 prefixEnd_620599 35407286744413626362047 := by
  unfold tailWord_620599
  simp only [CollatzResearch.WordTrace]
  refine ⟨22635105078683287716024851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15090070052455525144016567 22635105078683287716024851)
  ·
    refine ⟨33952657618024931574037277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22635105078683287716024851 33952657618024931574037277)
    ·
      refine ⟨12732246606759349340263979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33952657618024931574037277 12732246606759349340263979)
      ·
        refine ⟨19098369910139024010395969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12732246606759349340263979 19098369910139024010395969)
        ·
          refine ⟨14323777432604268007796977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19098369910139024010395969 14323777432604268007796977)
          ·
            refine ⟨10742833074453201005847733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14323777432604268007796977 10742833074453201005847733)
            ·
              refine ⟨1007140600729987594298225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10742833074453201005847733 1007140600729987594298225)
              ·
                refine ⟨755355450547490695723669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1007140600729987594298225 755355450547490695723669)
                ·
                  refine ⟨35407286744413626362047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 755355450547490695723669 35407286744413626362047)
                  ·
                    rfl

theorem cell23_620599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 6].length) (baseStart_620599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620599 prefixEnd_620599 := by exact prefixLift 620599
  have htrace : WordTrace (prefixWord ++ tailWord_620599) baseStart_620599 baseEnd_620599 := by
    simpa [prefixWord, tailWord_620599, baseEnd_620599] using wordTrace_append hprefix tailTrace_620599
  have hstable : (prefixWord ++ tailWord_620599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620599).length < 2 ^ (prefixWord ++ tailWord_620599).sum := by decide
  have hdescent : baseEnd_620599 < baseStart_620599 := by decide
  rcases family_descends (prefixWord ++ tailWord_620599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620637 : List Nat := [1, 4, 4, 1, 1, 3, 1, 3, 1, 4]
def baseStart_620637 : Nat := 118140960795 + 620637 * 2 ^ 59
def prefixEnd_620637 : Nat := 4983230072969 + 3 ^ 40 * 620637 * 2
def baseEnd_620637 : Nat := 106228364321531162861083

theorem tailTrace_620637 : CollatzResearch.WordTrace tailWord_620637 prefixEnd_620637 106228364321531162861083 := by
  unfold tailWord_620637
  simp only [CollatzResearch.WordTrace]
  refine ⟨22636491052545620205908165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15090994035030413470605443 22636491052545620205908165)
  ·
    refine ⟨4244342072352303788607781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22636491052545620205908165 4244342072352303788607781)
    ·
      refine ⟨795814138566056960363959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4244342072352303788607781 795814138566056960363959)
      ·
        refine ⟨1193721207849085440545939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795814138566056960363959 1193721207849085440545939)
        ·
          refine ⟨1790581811773628160818909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193721207849085440545939 1790581811773628160818909)
          ·
            refine ⟨671468179415110560307091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1790581811773628160818909 671468179415110560307091)
            ·
              refine ⟨1007202269122665840460637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671468179415110560307091 1007202269122665840460637)
              ·
                refine ⟨377700850920999690172739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1007202269122665840460637 377700850920999690172739)
                ·
                  refine ⟨566551276381499535259109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377700850920999690172739 566551276381499535259109)
                  ·
                    refine ⟨106228364321531162861083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 566551276381499535259109 106228364321531162861083)
                    ·
                      rfl

theorem cell23_620637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_620637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620637 prefixEnd_620637 := by exact prefixLift 620637
  have htrace : WordTrace (prefixWord ++ tailWord_620637) baseStart_620637 baseEnd_620637 := by
    simpa [prefixWord, tailWord_620637, baseEnd_620637] using wordTrace_append hprefix tailTrace_620637
  have hstable : (prefixWord ++ tailWord_620637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620637).length < 2 ^ (prefixWord ++ tailWord_620637).sum := by decide
  have hdescent : baseEnd_620637 < baseStart_620637 := by decide
  rcases family_descends (prefixWord ++ tailWord_620637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620653 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_620653 : Nat := 118140960795 + 620653 * 2 ^ 59
def prefixEnd_620653 : Nat := 4983230072969 + 3 ^ 40 * 620653 * 2
def baseEnd_620653 : Nat := 318693308655065425983175

theorem tailTrace_620653 : CollatzResearch.WordTrace tailWord_620653 prefixEnd_620653 318693308655065425983175 := by
  unfold tailWord_620653
  simp only [CollatzResearch.WordTrace]
  refine ⟨22637074620487654938490613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15091383080325103292327075 22637074620487654938490613)
  ·
    refine ⟨2122225745670717650483495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22637074620487654938490613 2122225745670717650483495)
    ·
      refine ⟨3183338618506076475725243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2122225745670717650483495 3183338618506076475725243)
      ·
        refine ⟨4775007927759114713587865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3183338618506076475725243 4775007927759114713587865)
        ·
          refine ⟨3581255945819336035190899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4775007927759114713587865 3581255945819336035190899)
          ·
            refine ⟨5371883918729004052786349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3581255945819336035190899 5371883918729004052786349)
            ·
              refine ⟨2014456469523376519794881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5371883918729004052786349 2014456469523376519794881)
              ·
                refine ⟨1510842352142532389846161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2014456469523376519794881 1510842352142532389846161)
                ·
                  refine ⟨1133131764106899292384621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1510842352142532389846161 1133131764106899292384621)
                  ·
                    refine ⟨424924411540087234644233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1133131764106899292384621 424924411540087234644233)
                    ·
                      refine ⟨318693308655065425983175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 424924411540087234644233 318693308655065425983175)
                      ·
                        rfl

theorem cell23_620653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_620653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620653 prefixEnd_620653 := by exact prefixLift 620653
  have htrace : WordTrace (prefixWord ++ tailWord_620653) baseStart_620653 baseEnd_620653 := by
    simpa [prefixWord, tailWord_620653, baseEnd_620653] using wordTrace_append hprefix tailTrace_620653
  have hstable : (prefixWord ++ tailWord_620653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620653).length < 2 ^ (prefixWord ++ tailWord_620653).sum := by decide
  have hdescent : baseEnd_620653 < baseStart_620653 := by decide
  rcases family_descends (prefixWord ++ tailWord_620653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620679 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_620679 : Nat := 118140960795 + 620679 * 2 ^ 59
def prefixEnd_620679 : Nat := 4983230072969 + 3 ^ 40 * 620679 * 2
def baseEnd_620679 : Nat := 318706659152082324258055

theorem tailTrace_620679 : CollatzResearch.WordTrace tailWord_620679 prefixEnd_620679 318706659152082324258055 := by
  unfold tailWord_620679
  simp only [CollatzResearch.WordTrace]
  refine ⟨22638022918393461378937091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15092015278928974252624727 22638022918393461378937091)
  ·
    refine ⟨33957034377590192068405637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22638022918393461378937091 33957034377590192068405637)
    ·
      refine ⟨6366943945798161012826057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33957034377590192068405637 6366943945798161012826057)
      ·
        refine ⟨4775207959348620759619543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6366943945798161012826057 4775207959348620759619543)
        ·
          refine ⟨7162811939022931139429315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4775207959348620759619543 7162811939022931139429315)
          ·
            refine ⟨10744217908534396709143973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7162811939022931139429315 10744217908534396709143973)
            ·
              refine ⟨2014540857850199382964495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10744217908534396709143973 2014540857850199382964495)
              ·
                refine ⟨3021811286775299074446743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2014540857850199382964495 3021811286775299074446743)
                ·
                  refine ⟨4532716930162948611670115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3021811286775299074446743 4532716930162948611670115)
                  ·
                    refine ⟨6799075395244422917505173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4532716930162948611670115 6799075395244422917505173)
                    ·
                      refine ⟨318706659152082324258055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6799075395244422917505173 318706659152082324258055)
                      ·
                        rfl

theorem cell23_620679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_620679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620679 prefixEnd_620679 := by exact prefixLift 620679
  have htrace : WordTrace (prefixWord ++ tailWord_620679) baseStart_620679 baseEnd_620679 := by
    simpa [prefixWord, tailWord_620679, baseEnd_620679] using wordTrace_append hprefix tailTrace_620679
  have hstable : (prefixWord ++ tailWord_620679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620679).length < 2 ^ (prefixWord ++ tailWord_620679).sum := by decide
  have hdescent : baseEnd_620679 < baseStart_620679 := by decide
  rcases family_descends (prefixWord ++ tailWord_620679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620703 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 1, 1, 5]
def baseStart_620703 : Nat := 118140960795 + 620703 * 2 ^ 59
def prefixEnd_620703 : Nat := 4983230072969 + 3 ^ 40 * 620703 * 2
def baseEnd_620703 : Nat := 318718982687790230357945

theorem tailTrace_620703 : CollatzResearch.WordTrace tailWord_620703 prefixEnd_620703 318718982687790230357945 := by
  unfold tailWord_620703
  simp only [CollatzResearch.WordTrace]
  refine ⟨22638898270306513477810763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15092598846871008985207175 22638898270306513477810763)
  ·
    refine ⟨33958347405459770216716145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22638898270306513477810763 33958347405459770216716145)
    ·
      refine ⟨25468760554094827662537109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33958347405459770216716145 25468760554094827662537109)
      ·
        refine ⟨1193848150973195046681427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25468760554094827662537109 1193848150973195046681427)
        ·
          refine ⟨1790772226459792570022141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193848150973195046681427 1790772226459792570022141)
          ·
            refine ⟨671539584922422213758303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1790772226459792570022141 671539584922422213758303)
            ·
              refine ⟨1007309377383633320637455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671539584922422213758303 1007309377383633320637455)
              ·
                refine ⟨1510964066075449980956183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007309377383633320637455 1510964066075449980956183)
                ·
                  refine ⟨2266446099113174971434275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1510964066075449980956183 2266446099113174971434275)
                  ·
                    refine ⟨3399669148669762457151413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2266446099113174971434275 3399669148669762457151413)
                    ·
                      refine ⟨318718982687790230357945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3399669148669762457151413 318718982687790230357945)
                      ·
                        rfl

theorem cell23_620703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_620703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620703 prefixEnd_620703 := by exact prefixLift 620703
  have htrace : WordTrace (prefixWord ++ tailWord_620703) baseStart_620703 baseEnd_620703 := by
    simpa [prefixWord, tailWord_620703, baseEnd_620703] using wordTrace_append hprefix tailTrace_620703
  have hstable : (prefixWord ++ tailWord_620703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620703).length < 2 ^ (prefixWord ++ tailWord_620703).sum := by decide
  have hdescent : baseEnd_620703 < baseStart_620703 := by decide
  rcases family_descends (prefixWord ++ tailWord_620703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620711 : List Nat := [1, 1, 6, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_620711 : Nat := 118140960795 + 620711 * 2 ^ 59
def prefixEnd_620711 : Nat := 4983230072969 + 3 ^ 40 * 620711 * 2
def baseEnd_620711 : Nat := 318723090533026199057909

theorem tailTrace_620711 : CollatzResearch.WordTrace tailWord_620711 prefixEnd_620711 318723090533026199057909 := by
  unfold tailWord_620711
  simp only [CollatzResearch.WordTrace]
  refine ⟨22639190054277530844101987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15092793369518353896067991 22639190054277530844101987)
  ·
    refine ⟨33958785081416296266152981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22639190054277530844101987 33958785081416296266152981)
    ·
      refine ⟨1591818050691388887475921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33958785081416296266152981 1591818050691388887475921)
      ·
        refine ⟨1193863538018541665606941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1591818050691388887475921 1193863538018541665606941)
        ·
          refine ⟨447698826756953124602603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1193863538018541665606941 447698826756953124602603)
          ·
            refine ⟨671548240135429686903905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447698826756953124602603 671548240135429686903905)
            ·
              refine ⟨503661180101572265177929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 671548240135429686903905 503661180101572265177929)
              ·
                refine ⟨377745885076179198883447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503661180101572265177929 377745885076179198883447)
                ·
                  refine ⟨566618827614268798325171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377745885076179198883447 566618827614268798325171)
                  ·
                    refine ⟨849928241421403197487757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 566618827614268798325171 849928241421403197487757)
                    ·
                      refine ⟨318723090533026199057909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 849928241421403197487757 318723090533026199057909)
                      ·
                        rfl

theorem cell23_620711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_620711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620711 prefixEnd_620711 := by exact prefixLift 620711
  have htrace : WordTrace (prefixWord ++ tailWord_620711) baseStart_620711 baseEnd_620711 := by
    simpa [prefixWord, tailWord_620711, baseEnd_620711] using wordTrace_append hprefix tailTrace_620711
  have hstable : (prefixWord ++ tailWord_620711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620711).length < 2 ^ (prefixWord ++ tailWord_620711).sum := by decide
  have hdescent : baseEnd_620711 < baseStart_620711 := by decide
  rcases family_descends (prefixWord ++ tailWord_620711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620716 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 3]
def baseStart_620716 : Nat := 118140960795 + 620716 * 2 ^ 59
def prefixEnd_620716 : Nat := 4983230072969 + 3 ^ 40 * 620716 * 2
def baseEnd_620716 : Nat := 318725657936298679495385

theorem tailTrace_620716 : CollatzResearch.WordTrace tailWord_620716 prefixEnd_620716 318725657936298679495385 := by
  unfold tailWord_620716
  simp only [CollatzResearch.WordTrace]
  refine ⟨11319686209629708349017001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15092914946172944465356001 11319686209629708349017001)
  ·
    refine ⟨8489764657222281261762751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11319686209629708349017001 8489764657222281261762751)
    ·
      refine ⟨12734646985833421892644127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8489764657222281261762751 12734646985833421892644127)
      ·
        refine ⟨19101970478750132838966191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12734646985833421892644127 19101970478750132838966191)
        ·
          refine ⟨28652955718125199258449287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19101970478750132838966191 28652955718125199258449287)
          ·
            refine ⟨42979433577187798887673931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28652955718125199258449287 42979433577187798887673931)
            ·
              refine ⟨64469150365781698331510897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42979433577187798887673931 64469150365781698331510897)
              ·
                refine ⟨48351862774336273748633173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64469150365781698331510897 48351862774336273748633173)
                ·
                  refine ⟨566623391886753207991795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 48351862774336273748633173 566623391886753207991795)
                  ·
                    refine ⟨849935087830129811987693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 566623391886753207991795 849935087830129811987693)
                    ·
                      refine ⟨318725657936298679495385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 849935087830129811987693 318725657936298679495385)
                      ·
                        rfl

theorem cell23_620716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_620716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620716 prefixEnd_620716 := by exact prefixLift 620716
  have htrace : WordTrace (prefixWord ++ tailWord_620716) baseStart_620716 baseEnd_620716 := by
    simpa [prefixWord, tailWord_620716, baseEnd_620716] using wordTrace_append hprefix tailTrace_620716
  have hstable : (prefixWord ++ tailWord_620716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620716).length < 2 ^ (prefixWord ++ tailWord_620716).sum := by decide
  have hdescent : baseEnd_620716 < baseStart_620716 := by decide
  rcases family_descends (prefixWord ++ tailWord_620716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620759 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_620759 : Nat := 118140960795 + 620759 * 2 ^ 59
def prefixEnd_620759 : Nat := 4983230072969 + 3 ^ 40 * 620759 * 2
def baseEnd_620759 : Nat := 318747737604442011257687

theorem tailTrace_620759 : CollatzResearch.WordTrace tailWord_620759 prefixEnd_620759 318747737604442011257687 := by
  unfold tailWord_620759
  simp only [CollatzResearch.WordTrace]
  refine ⟨22640940758103635041849331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15093960505402423361232887 22640940758103635041849331)
  ·
    refine ⟨33961411137155452562773997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22640940758103635041849331 33961411137155452562773997)
    ·
      refine ⟨12735529176433294711040249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33961411137155452562773997 12735529176433294711040249)
      ·
        refine ⟨9551646882324971033280187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12735529176433294711040249 9551646882324971033280187)
        ·
          refine ⟨14327470323487456549920281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9551646882324971033280187 14327470323487456549920281)
          ·
            refine ⟨10745602742615592412440211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14327470323487456549920281 10745602742615592412440211)
            ·
              refine ⟨16118404113923388618660317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10745602742615592412440211 16118404113923388618660317)
              ·
                refine ⟨6044401542721270731997619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16118404113923388618660317 6044401542721270731997619)
                ·
                  refine ⟨9066602314081906097996429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6044401542721270731997619 9066602314081906097996429)
                  ·
                    refine ⟨3399975867780714786748661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9066602314081906097996429 3399975867780714786748661)
                    ·
                      refine ⟨318747737604442011257687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3399975867780714786748661 318747737604442011257687)
                      ·
                        rfl

theorem cell23_620759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_620759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620759 prefixEnd_620759 := by exact prefixLift 620759
  have htrace : WordTrace (prefixWord ++ tailWord_620759) baseStart_620759 baseEnd_620759 := by
    simpa [prefixWord, tailWord_620759, baseEnd_620759] using wordTrace_append hprefix tailTrace_620759
  have hstable : (prefixWord ++ tailWord_620759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620759).length < 2 ^ (prefixWord ++ tailWord_620759).sum := by decide
  have hdescent : baseEnd_620759 < baseStart_620759 := by decide
  rcases family_descends (prefixWord ++ tailWord_620759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620760 : List Nat := [2, 1, 2, 2, 4, 2, 1, 3, 1, 3, 2]
def baseStart_620760 : Nat := 118140960795 + 620760 * 2 ^ 59
def prefixEnd_620760 : Nat := 4983230072969 + 3 ^ 40 * 620760 * 2
def baseEnd_620760 : Nat := 318748251085096507345183

theorem tailTrace_620760 : CollatzResearch.WordTrace tailWord_620760 prefixEnd_620760 318748251085096507345183 := by
  unfold tailWord_620760
  simp only [CollatzResearch.WordTrace]
  refine ⟨11320488615550006106317867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15093984820733341475090489 11320488615550006106317867)
  ·
    refine ⟨16980732923325009159476801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11320488615550006106317867 16980732923325009159476801)
    ·
      refine ⟨12735549692493756869607601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16980732923325009159476801 12735549692493756869607601)
      ·
        refine ⟨9551662269370317652205701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12735549692493756869607601 9551662269370317652205701)
        ·
          refine ⟨1790936675506934559788569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9551662269370317652205701 1790936675506934559788569)
          ·
            refine ⟨1343202506630200919841427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1790936675506934559788569 1343202506630200919841427)
            ·
              refine ⟨2014803759945301379762141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343202506630200919841427 2014803759945301379762141)
              ·
                refine ⟨755551409979488017410803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2014803759945301379762141 755551409979488017410803)
                ·
                  refine ⟨1133327114969232026116205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 755551409979488017410803 1133327114969232026116205)
                  ·
                    refine ⟨424997668113462009793577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1133327114969232026116205 424997668113462009793577)
                    ·
                      refine ⟨318748251085096507345183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 424997668113462009793577 318748251085096507345183)
                      ·
                        rfl

theorem cell23_620760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_620760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620760 prefixEnd_620760 := by exact prefixLift 620760
  have htrace : WordTrace (prefixWord ++ tailWord_620760) baseStart_620760 baseEnd_620760 := by
    simpa [prefixWord, tailWord_620760, baseEnd_620760] using wordTrace_append hprefix tailTrace_620760
  have hstable : (prefixWord ++ tailWord_620760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620760).length < 2 ^ (prefixWord ++ tailWord_620760).sum := by decide
  have hdescent : baseEnd_620760 < baseStart_620760 := by decide
  rcases family_descends (prefixWord ++ tailWord_620760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620790 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_620790 : Nat := 118140960795 + 620790 * 2 ^ 59
def prefixEnd_620790 : Nat := 4983230072969 + 3 ^ 40 * 620790 * 2
def baseEnd_620790 : Nat := 318763655504731389970045

theorem tailTrace_620790 : CollatzResearch.WordTrace tailWord_620790 prefixEnd_620790 318763655504731389970045 := by
  unfold tailWord_620790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415129463811957958514239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15094714280660884890818549 1415129463811957958514239)
  ·
    refine ⟨2122694195717936937771359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1415129463811957958514239 2122694195717936937771359)
    ·
      refine ⟨3184041293576905406657039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2122694195717936937771359 3184041293576905406657039)
      ·
        refine ⟨4776061940365358109985559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3184041293576905406657039 4776061940365358109985559)
        ·
          refine ⟨7164092910548037164978339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4776061940365358109985559 7164092910548037164978339)
          ·
            refine ⟨10746139365822055747467509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164092910548037164978339 10746139365822055747467509)
            ·
              refine ⟨1007450565545817726325079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10746139365822055747467509 1007450565545817726325079)
              ·
                refine ⟨1511175848318726589487619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007450565545817726325079 1511175848318726589487619)
                ·
                  refine ⟨2266763772478089884231429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511175848318726589487619 2266763772478089884231429)
                  ·
                    refine ⟨425018207339641853293393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2266763772478089884231429 425018207339641853293393)
                    ·
                      refine ⟨318763655504731389970045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 425018207339641853293393 318763655504731389970045)
                      ·
                        rfl

theorem cell23_620790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_620790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620790 prefixEnd_620790 := by exact prefixLift 620790
  have htrace : WordTrace (prefixWord ++ tailWord_620790) baseStart_620790 baseEnd_620790 := by
    simpa [prefixWord, tailWord_620790, baseEnd_620790] using wordTrace_append hprefix tailTrace_620790
  have hstable : (prefixWord ++ tailWord_620790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620790).length < 2 ^ (prefixWord ++ tailWord_620790).sum := by decide
  have hdescent : baseEnd_620790 < baseStart_620790 := by decide
  rcases family_descends (prefixWord ++ tailWord_620790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620796 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 7]
def baseStart_620796 : Nat := 118140960795 + 620796 * 2 ^ 59
def prefixEnd_620796 : Nat := 4983230072969 + 3 ^ 40 * 620796 * 2
def baseEnd_620796 : Nat := 35418526265406485166113

theorem tailTrace_620796 : CollatzResearch.WordTrace tailWord_620796 prefixEnd_620796 35418526265406485166113 := by
  unfold tailWord_620796
  simp only [CollatzResearch.WordTrace]
  refine ⟨11321145129484795180473121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15094860172646393573964161 11321145129484795180473121)
  ·
    refine ⟨8490858847113596385354841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11321145129484795180473121 8490858847113596385354841)
    ·
      refine ⟨6368144135335197289016131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8490858847113596385354841 6368144135335197289016131)
      ·
        refine ⟨9552216203002795933524197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6368144135335197289016131 9552216203002795933524197)
        ·
          refine ⟨1791040538063024237535787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9552216203002795933524197 1791040538063024237535787)
          ·
            refine ⟨2686560807094536356303681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791040538063024237535787 2686560807094536356303681)
            ·
              refine ⟨2014920605320902267227761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2686560807094536356303681 2014920605320902267227761)
              ·
                refine ⟨1511190453990676700420821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2014920605320902267227761 1511190453990676700420821)
                ·
                  refine ⟨35418526265406485166113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1511190453990676700420821 35418526265406485166113)
                  ·
                    rfl

theorem cell23_620796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_620796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620796 prefixEnd_620796 := by exact prefixLift 620796
  have htrace : WordTrace (prefixWord ++ tailWord_620796) baseStart_620796 baseEnd_620796 := by
    simpa [prefixWord, tailWord_620796, baseEnd_620796] using wordTrace_append hprefix tailTrace_620796
  have hstable : (prefixWord ++ tailWord_620796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620796).length < 2 ^ (prefixWord ++ tailWord_620796).sum := by decide
  have hdescent : baseEnd_620796 < baseStart_620796 := by decide
  rcases family_descends (prefixWord ++ tailWord_620796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620819 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 7]
def baseStart_620819 : Nat := 118140960795 + 620819 * 2 ^ 59
def prefixEnd_620819 : Nat := 4983230072969 + 3 ^ 40 * 620819 * 2
def baseEnd_620819 : Nat := 318778546443711776507411

theorem tailTrace_620819 : CollatzResearch.WordTrace tailWord_620819 prefixEnd_620819 318778546443711776507411 := by
  unfold tailWord_620819
  simp only [CollatzResearch.WordTrace]
  refine ⟨22643129137886265289033511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15095419425257510192689007 22643129137886265289033511)
  ·
    refine ⟨33964693706829397933550267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22643129137886265289033511 33964693706829397933550267)
    ·
      refine ⟨50947040560244096900325401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33964693706829397933550267 50947040560244096900325401)
      ·
        refine ⟨38210280420183072675244051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50947040560244096900325401 38210280420183072675244051)
        ·
          refine ⟨57315420630274609012866077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38210280420183072675244051 57315420630274609012866077)
          ·
            refine ⟨21493282736352978379824779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57315420630274609012866077 21493282736352978379824779)
            ·
              refine ⟨32239924104529467569737169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21493282736352978379824779 32239924104529467569737169)
              ·
                refine ⟨24179943078397100677302877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32239924104529467569737169 24179943078397100677302877)
                ·
                  refine ⟨9067478654398912753988579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24179943078397100677302877 9067478654398912753988579)
                  ·
                    refine ⟨13601217981598369130982869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9067478654398912753988579 13601217981598369130982869)
                    ·
                      refine ⟨318778546443711776507411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13601217981598369130982869 318778546443711776507411)
                      ·
                        rfl

theorem cell23_620819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_620819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620819 prefixEnd_620819 := by exact prefixLift 620819
  have htrace : WordTrace (prefixWord ++ tailWord_620819) baseStart_620819 baseEnd_620819 := by
    simpa [prefixWord, tailWord_620819, baseEnd_620819] using wordTrace_append hprefix tailTrace_620819
  have hstable : (prefixWord ++ tailWord_620819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620819).length < 2 ^ (prefixWord ++ tailWord_620819).sum := by decide
  have hdescent : baseEnd_620819 < baseStart_620819 := by decide
  rcases family_descends (prefixWord ++ tailWord_620819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620830 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 7]
def baseStart_620830 : Nat := 118140960795 + 620830 * 2 ^ 59
def prefixEnd_620830 : Nat := 4983230072969 + 3 ^ 40 * 620830 * 2
def baseEnd_620830 : Nat := 35420466081212359274429

theorem tailTrace_620830 : CollatzResearch.WordTrace tailWord_620830 prefixEnd_620830 35420466081212359274429 := by
  unfold tailWord_620830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2830441292605801770960493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15095686893897609445122629 2830441292605801770960493)
  ·
    refine ⟨1061415484727175664110185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2830441292605801770960493 1061415484727175664110185)
    ·
      refine ⟨796061613545381748082639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1061415484727175664110185 796061613545381748082639)
      ·
        refine ⟨1194092420318072622123959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 796061613545381748082639 1194092420318072622123959)
        ·
          refine ⟨1791138630477108933185939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194092420318072622123959 1791138630477108933185939)
          ·
            refine ⟨2686707945715663399778909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791138630477108933185939 2686707945715663399778909)
            ·
              refine ⟨1007515479643373774917091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2686707945715663399778909 1007515479643373774917091)
              ·
                refine ⟨1511273219465060662375637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007515479643373774917091 1511273219465060662375637)
                ·
                  refine ⟨35420466081212359274429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1511273219465060662375637 35420466081212359274429)
                  ·
                    rfl

theorem cell23_620830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_620830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620830 prefixEnd_620830 := by exact prefixLift 620830
  have htrace : WordTrace (prefixWord ++ tailWord_620830) baseStart_620830 baseEnd_620830 := by
    simpa [prefixWord, tailWord_620830, baseEnd_620830] using wordTrace_append hprefix tailTrace_620830
  have hstable : (prefixWord ++ tailWord_620830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620830).length < 2 ^ (prefixWord ++ tailWord_620830).sum := by decide
  have hdescent : baseEnd_620830 < baseStart_620830 := by decide
  rcases family_descends (prefixWord ++ tailWord_620830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620836 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_620836 : Nat := 118140960795 + 620836 * 2 ^ 59
def prefixEnd_620836 : Nat := 4983230072969 + 3 ^ 40 * 620836 * 2
def baseEnd_620836 : Nat := 318787275614838209994833

theorem tailTrace_620836 : CollatzResearch.WordTrace tailWord_620836 prefixEnd_620836 318787275614838209994833 := by
  unfold tailWord_620836
  simp only [CollatzResearch.WordTrace]
  refine ⟨11321874589412338596201181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15095832785883118128268241 11321874589412338596201181)
  ·
    refine ⟨4245702971029626973575443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11321874589412338596201181 4245702971029626973575443)
    ·
      refine ⟨6368554456544440460363165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4245702971029626973575443 6368554456544440460363165)
      ·
        refine ⟨2388207921204165172636187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6368554456544440460363165 2388207921204165172636187)
        ·
          refine ⟨3582311881806247758954281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2388207921204165172636187 3582311881806247758954281)
          ·
            refine ⟨2686733911354685819215711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3582311881806247758954281 2686733911354685819215711)
            ·
              refine ⟨4030100867032028728823567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2686733911354685819215711 4030100867032028728823567)
              ·
                refine ⟨6045151300548043093235351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4030100867032028728823567 6045151300548043093235351)
                ·
                  refine ⟨9067726950822064639853027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6045151300548043093235351 9067726950822064639853027)
                  ·
                    refine ⟨13601590426233096959779541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9067726950822064639853027 13601590426233096959779541)
                    ·
                      refine ⟨318787275614838209994833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13601590426233096959779541 318787275614838209994833)
                      ·
                        rfl

theorem cell23_620836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_620836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620836 prefixEnd_620836 := by exact prefixLift 620836
  have htrace : WordTrace (prefixWord ++ tailWord_620836) baseStart_620836 baseEnd_620836 := by
    simpa [prefixWord, tailWord_620836, baseEnd_620836] using wordTrace_append hprefix tailTrace_620836
  have hstable : (prefixWord ++ tailWord_620836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620836).length < 2 ^ (prefixWord ++ tailWord_620836).sum := by decide
  have hdescent : baseEnd_620836 < baseStart_620836 := by decide
  rcases family_descends (prefixWord ++ tailWord_620836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620863 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 4]
def baseStart_620863 : Nat := 118140960795 + 620863 * 2 ^ 59
def prefixEnd_620863 : Nat := 4983230072969 + 3 ^ 40 * 620863 * 2
def baseEnd_620863 : Nat := 318801139592509604357209

theorem tailTrace_620863 : CollatzResearch.WordTrace tailWord_620863 prefixEnd_620863 318801139592509604357209 := by
  unfold tailWord_620863
  simp only [CollatzResearch.WordTrace]
  refine ⟨22644733949726860803635243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15096489299817907202423495 22644733949726860803635243)
  ·
    refine ⟨33967100924590291205452865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22644733949726860803635243 33967100924590291205452865)
    ·
      refine ⟨25475325693442718404089649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33967100924590291205452865 25475325693442718404089649)
      ·
        refine ⟨19106494270082038803067237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25475325693442718404089649 19106494270082038803067237)
        ·
          refine ⟨3582467675640382275575107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19106494270082038803067237 3582467675640382275575107)
          ·
            refine ⟨5373701513460573413362661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3582467675640382275575107 5373701513460573413362661)
            ·
              refine ⟨1007569033773857515005499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5373701513460573413362661 1007569033773857515005499)
              ·
                refine ⟨1511353550660786272508249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007569033773857515005499 1511353550660786272508249)
                ·
                  refine ⟨1133515162995589704381187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1511353550660786272508249 1133515162995589704381187)
                  ·
                    refine ⟨1700272744493384556571781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1133515162995589704381187 1700272744493384556571781)
                    ·
                      refine ⟨318801139592509604357209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1700272744493384556571781 318801139592509604357209)
                      ·
                        rfl

theorem cell23_620863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_620863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620863 prefixEnd_620863 := by exact prefixLift 620863
  have htrace : WordTrace (prefixWord ++ tailWord_620863) baseStart_620863 baseEnd_620863 := by
    simpa [prefixWord, tailWord_620863, baseEnd_620863] using wordTrace_append hprefix tailTrace_620863
  have hstable : (prefixWord ++ tailWord_620863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620863).length < 2 ^ (prefixWord ++ tailWord_620863).sum := by decide
  have hdescent : baseEnd_620863 < baseStart_620863 := by decide
  rcases family_descends (prefixWord ++ tailWord_620863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620876 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_620876 : Nat := 118140960795 + 620876 * 2 ^ 59
def prefixEnd_620876 : Nat := 4983230072969 + 3 ^ 40 * 620876 * 2
def baseEnd_620876 : Nat := 318807814841018053494649

theorem tailTrace_620876 : CollatzResearch.WordTrace tailWord_620876 prefixEnd_620876 318807814841018053494649 := by
  unfold tailWord_620876
  simp only [CollatzResearch.WordTrace]
  refine ⟨11322604049339882011929241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15096805399119842682572321 11322604049339882011929241)
  ·
    refine ⟨8491953037004911508946931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11322604049339882011929241 8491953037004911508946931)
    ·
      refine ⟨12737929555507367263420397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8491953037004911508946931 12737929555507367263420397)
      ·
        refine ⟨4776723583315262723782649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12737929555507367263420397 4776723583315262723782649)
        ·
          refine ⟨3582542687486447042836987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4776723583315262723782649 3582542687486447042836987)
          ·
            refine ⟨5373814031229670564255481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3582542687486447042836987 5373814031229670564255481)
            ·
              refine ⟨4030360523422252923191611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5373814031229670564255481 4030360523422252923191611)
              ·
                refine ⟨6045540785133379384787417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4030360523422252923191611 6045540785133379384787417)
                ·
                  refine ⟨4534155588850034538590563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6045540785133379384787417 4534155588850034538590563)
                  ·
                    refine ⟨6801233383275051807885845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4534155588850034538590563 6801233383275051807885845)
                    ·
                      refine ⟨318807814841018053494649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6801233383275051807885845 318807814841018053494649)
                      ·
                        rfl

theorem cell23_620876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_620876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620876 prefixEnd_620876 := by exact prefixLift 620876
  have htrace : WordTrace (prefixWord ++ tailWord_620876) baseStart_620876 baseEnd_620876 := by
    simpa [prefixWord, tailWord_620876, baseEnd_620876] using wordTrace_append hprefix tailTrace_620876
  have hstable : (prefixWord ++ tailWord_620876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620876).length < 2 ^ (prefixWord ++ tailWord_620876).sum := by decide
  have hdescent : baseEnd_620876 < baseStart_620876 := by decide
  rcases family_descends (prefixWord ++ tailWord_620876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620903 : List Nat := [1, 1, 5, 1, 3, 1, 2, 3, 6]
def baseStart_620903 : Nat := 118140960795 + 620903 * 2 ^ 59
def prefixEnd_620903 : Nat := 4983230072969 + 3 ^ 40 * 620903 * 2
def baseEnd_620903 : Nat := 35424630979854383095225

theorem tailTrace_620903 : CollatzResearch.WordTrace tailWord_620903 prefixEnd_620903 35424630979854383095225 := by
  unfold tailWord_620903
  simp only [CollatzResearch.WordTrace]
  refine ⟨22646192869581947635091363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15097461913054631756727575 22646192869581947635091363)
  ·
    refine ⟨33969289304372921452637045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22646192869581947635091363 33969289304372921452637045)
    ·
      refine ⟨3184620872284961386184723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33969289304372921452637045 3184620872284961386184723)
      ·
        refine ⟨4776931308427442079277085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3184620872284961386184723 4776931308427442079277085)
        ·
          refine ⟨1791349240660290779728907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4776931308427442079277085 1791349240660290779728907)
          ·
            refine ⟨2687023860990436169593361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791349240660290779728907 2687023860990436169593361)
            ·
              refine ⟨2015267895742827127195021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2687023860990436169593361 2015267895742827127195021)
              ·
                refine ⟨755725460903560172698133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2015267895742827127195021 755725460903560172698133)
                ·
                  refine ⟨35424630979854383095225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 755725460903560172698133 35424630979854383095225)
                  ·
                    rfl

theorem cell23_620903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 6].length) (baseStart_620903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620903 prefixEnd_620903 := by exact prefixLift 620903
  have htrace : WordTrace (prefixWord ++ tailWord_620903) baseStart_620903 baseEnd_620903 := by
    simpa [prefixWord, tailWord_620903, baseEnd_620903] using wordTrace_append hprefix tailTrace_620903
  have hstable : (prefixWord ++ tailWord_620903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620903).length < 2 ^ (prefixWord ++ tailWord_620903).sum := by decide
  have hdescent : baseEnd_620903 < baseStart_620903 := by decide
  rcases family_descends (prefixWord ++ tailWord_620903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620917 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_620917 : Nat := 118140960795 + 620917 * 2 ^ 59
def prefixEnd_620917 : Nat := 4983230072969 + 3 ^ 40 * 620917 * 2
def baseEnd_620917 : Nat := 318828867547852393081961

theorem tailTrace_620917 : CollatzResearch.WordTrace tailWord_620917 prefixEnd_620917 318828867547852393081961 := by
  unfold tailWord_620917
  simp only [CollatzResearch.WordTrace]
  refine ⟨22646703491531228026101005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15097802327687485350734003 22646703491531228026101005)
  ·
    refine ⟨8492513809324210509787877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22646703491531228026101005 8492513809324210509787877)
    ·
      refine ⟨1592346339248289470585227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8492513809324210509787877 1592346339248289470585227)
      ·
        refine ⟨2388519508872434205877841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592346339248289470585227 2388519508872434205877841)
        ·
          refine ⟨1791389631654325654408381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2388519508872434205877841 1791389631654325654408381)
          ·
            refine ⟨671771111870372120403143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1791389631654325654408381 671771111870372120403143)
            ·
              refine ⟨1007656667805558180604715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671771111870372120403143 1007656667805558180604715)
              ·
                refine ⟨1511485001708337270907073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007656667805558180604715 1511485001708337270907073)
                ·
                  refine ⟨1133613751281252953180305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1511485001708337270907073 1133613751281252953180305)
                  ·
                    refine ⟨850210313460939714885229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1133613751281252953180305 850210313460939714885229)
                    ·
                      refine ⟨318828867547852393081961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 850210313460939714885229 318828867547852393081961)
                      ·
                        rfl

theorem cell23_620917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_620917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620917 prefixEnd_620917 := by exact prefixLift 620917
  have htrace : WordTrace (prefixWord ++ tailWord_620917) baseStart_620917 baseEnd_620917 := by
    simpa [prefixWord, tailWord_620917, baseEnd_620917] using wordTrace_append hprefix tailTrace_620917
  have hstable : (prefixWord ++ tailWord_620917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620917).length < 2 ^ (prefixWord ++ tailWord_620917).sum := by decide
  have hdescent : baseEnd_620917 < baseStart_620917 := by decide
  rcases family_descends (prefixWord ++ tailWord_620917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620963 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 1, 6]
def baseStart_620963 : Nat := 118140960795 + 620963 * 2 ^ 59
def prefixEnd_620963 : Nat := 4983230072969 + 3 ^ 40 * 620963 * 2
def baseEnd_620963 : Nat := 106284162552653071035583

theorem tailTrace_620963 : CollatzResearch.WordTrace tailWord_620963 prefixEnd_620963 106284162552653071035583 := by
  unfold tailWord_620963
  simp only [CollatzResearch.WordTrace]
  refine ⟨22648381249364577882275543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15098920832909718588183695 22648381249364577882275543)
  ·
    refine ⟨33972571874046866823413315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22648381249364577882275543 33972571874046866823413315)
    ·
      refine ⟨50958857811070300235119973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33972571874046866823413315 50958857811070300235119973)
      ·
        refine ⟨9554785839575681294084995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50958857811070300235119973 9554785839575681294084995)
        ·
          refine ⟨14332178759363521941127493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9554785839575681294084995 14332178759363521941127493)
          ·
            refine ⟨2687283517380660363961405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14332178759363521941127493 2687283517380660363961405)
            ·
              refine ⟨1007731319017747636485527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2687283517380660363961405 1007731319017747636485527)
              ·
                refine ⟨1511596978526621454728291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007731319017747636485527 1511596978526621454728291)
                ·
                  refine ⟨2267395467789932182092437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511596978526621454728291 2267395467789932182092437)
                  ·
                    refine ⟨106284162552653071035583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2267395467789932182092437 106284162552653071035583)
                    ·
                      rfl

theorem cell23_620963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 6].length) (baseStart_620963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620963 prefixEnd_620963 := by exact prefixLift 620963
  have htrace : WordTrace (prefixWord ++ tailWord_620963) baseStart_620963 baseEnd_620963 := by
    simpa [prefixWord, tailWord_620963, baseEnd_620963] using wordTrace_append hprefix tailTrace_620963
  have hstable : (prefixWord ++ tailWord_620963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620963).length < 2 ^ (prefixWord ++ tailWord_620963).sum := by decide
  have hdescent : baseEnd_620963 < baseStart_620963 := by decide
  rcases family_descends (prefixWord ++ tailWord_620963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620981 : List Nat := [1, 3, 3, 2, 3, 2, 1, 3, 1, 1, 3]
def baseStart_620981 : Nat := 118140960795 + 620981 * 2 ^ 59
def prefixEnd_620981 : Nat := 4983230072969 + 3 ^ 40 * 620981 * 2
def baseEnd_620981 : Nat := 318861730309740142681667

theorem tailTrace_620981 : CollatzResearch.WordTrace tailWord_620981 prefixEnd_620981 318861730309740142681667 := by
  unfold tailWord_620981
  simp only [CollatzResearch.WordTrace]
  refine ⟨22649037763299366956430797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15099358508866244637620531 22649037763299366956430797)
  ·
    refine ⟨8493389161237262608661549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22649037763299366956430797 8493389161237262608661549)
    ·
      refine ⟨3185020935463973478248081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8493389161237262608661549 3185020935463973478248081)
      ·
        refine ⟨2388765701597980108686061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3185020935463973478248081 2388765701597980108686061)
        ·
          refine ⟨895787138099242540757273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2388765701597980108686061 895787138099242540757273)
          ·
            refine ⟨671840353574431905567955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 895787138099242540757273 671840353574431905567955)
            ·
              refine ⟨1007760530361647858351933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671840353574431905567955 1007760530361647858351933)
              ·
                refine ⟨377910198885617946881975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1007760530361647858351933 377910198885617946881975)
                ·
                  refine ⟨566865298328426920322963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377910198885617946881975 566865298328426920322963)
                  ·
                    refine ⟨850297947492640380484445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 566865298328426920322963 850297947492640380484445)
                    ·
                      refine ⟨318861730309740142681667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 850297947492640380484445 318861730309740142681667)
                      ·
                        rfl

theorem cell23_620981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_620981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_620981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_620981 prefixEnd_620981 := by exact prefixLift 620981
  have htrace : WordTrace (prefixWord ++ tailWord_620981) baseStart_620981 baseEnd_620981 := by
    simpa [prefixWord, tailWord_620981, baseEnd_620981] using wordTrace_append hprefix tailTrace_620981
  have hstable : (prefixWord ++ tailWord_620981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620981).length < 2 ^ (prefixWord ++ tailWord_620981).sum := by decide
  have hdescent : baseEnd_620981 < baseStart_620981 := by decide
  rcases family_descends (prefixWord ++ tailWord_620981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621037 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_621037 : Nat := 118140960795 + 621037 * 2 ^ 59
def prefixEnd_621037 : Nat := 4983230072969 + 3 ^ 40 * 621037 * 2
def baseEnd_621037 : Nat := 318890485226391923581409

theorem tailTrace_621037 : CollatzResearch.WordTrace tailWord_621037 prefixEnd_621037 318890485226391923581409 := by
  unfold tailWord_621037
  simp only [CollatzResearch.WordTrace]
  refine ⟨22651080251096488520469365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15100720167397659013646243 22651080251096488520469365)
  ·
    refine ⟨2123538773540295798794003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22651080251096488520469365 2123538773540295798794003)
    ·
      refine ⟨3185308160310443698191005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2123538773540295798794003 3185308160310443698191005)
      ·
        refine ⟨1194490560116416386821627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3185308160310443698191005 1194490560116416386821627)
        ·
          refine ⟨1791735840174624580232441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194490560116416386821627 1791735840174624580232441)
          ·
            refine ⟨1343801880130968435174331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1791735840174624580232441 1343801880130968435174331)
            ·
              refine ⟨2015702820196452652761497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343801880130968435174331 2015702820196452652761497)
              ·
                refine ⟨1511777115147339489571123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2015702820196452652761497 1511777115147339489571123)
                ·
                  refine ⟨2267665672721009234356685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511777115147339489571123 2267665672721009234356685)
                  ·
                    refine ⟨850374627270378462883757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2267665672721009234356685 850374627270378462883757)
                    ·
                      refine ⟨318890485226391923581409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 850374627270378462883757 318890485226391923581409)
                      ·
                        rfl

theorem cell23_621037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_621037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621037 prefixEnd_621037 := by exact prefixLift 621037
  have htrace : WordTrace (prefixWord ++ tailWord_621037) baseStart_621037 baseEnd_621037 := by
    simpa [prefixWord, tailWord_621037, baseEnd_621037] using wordTrace_append hprefix tailTrace_621037
  have hstable : (prefixWord ++ tailWord_621037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621037).length < 2 ^ (prefixWord ++ tailWord_621037).sum := by decide
  have hdescent : baseEnd_621037 < baseStart_621037 := by decide
  rcases family_descends (prefixWord ++ tailWord_621037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621053 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_621053 : Nat := 118140960795 + 621053 * 2 ^ 59
def prefixEnd_621053 : Nat := 4983230072969 + 3 ^ 40 * 621053 * 2
def baseEnd_621053 : Nat := 106299566972287953660445

theorem tailTrace_621053 : CollatzResearch.WordTrace tailWord_621053 prefixEnd_621053 106299566972287953660445 := by
  unfold tailWord_621053
  simp only [CollatzResearch.WordTrace]
  refine ⟨22651663819038523253051813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15101109212692348835367875 22651663819038523253051813)
  ·
    refine ⟨4247186966069723109947215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22651663819038523253051813 4247186966069723109947215)
    ·
      refine ⟨6370780449104584664920823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4247186966069723109947215 6370780449104584664920823)
      ·
        refine ⟨9556170673656876997381235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6370780449104584664920823 9556170673656876997381235)
        ·
          refine ⟨14334256010485315496071853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9556170673656876997381235 14334256010485315496071853)
          ·
            refine ⟨5375346003931993311026945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14334256010485315496071853 5375346003931993311026945)
            ·
              refine ⟨4031509502948994983270209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5375346003931993311026945 4031509502948994983270209)
              ·
                refine ⟨3023632127211746237452657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4031509502948994983270209 3023632127211746237452657)
                ·
                  refine ⟨2267724095408809678089493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3023632127211746237452657 2267724095408809678089493)
                  ·
                    refine ⟨106299566972287953660445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2267724095408809678089493 106299566972287953660445)
                    ·
                      rfl

theorem cell23_621053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_621053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621053 prefixEnd_621053 := by exact prefixLift 621053
  have htrace : WordTrace (prefixWord ++ tailWord_621053) baseStart_621053 baseEnd_621053 := by
    simpa [prefixWord, tailWord_621053, baseEnd_621053] using wordTrace_append hprefix tailTrace_621053
  have hstable : (prefixWord ++ tailWord_621053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621053).length < 2 ^ (prefixWord ++ tailWord_621053).sum := by decide
  have hdescent : baseEnd_621053 < baseStart_621053 := by decide
  rcases family_descends (prefixWord ++ tailWord_621053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621060 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_621060 : Nat := 118140960795 + 621060 * 2 ^ 59
def prefixEnd_621060 : Nat := 4983230072969 + 3 ^ 40 * 621060 * 2
def baseEnd_621060 : Nat := 318902295281445333593803

theorem tailTrace_621060 : CollatzResearch.WordTrace tailWord_621060 prefixEnd_621060 318902295281445333593803 := by
  unfold tailWord_621060
  simp only [CollatzResearch.WordTrace]
  refine ⟨11325959565006581724278317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15101279420008775632371089 11325959565006581724278317)
  ·
    refine ⟨4247234836877468146604369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11325959565006581724278317 4247234836877468146604369)
    ·
      refine ⟨3185426127658101109953277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4247234836877468146604369 3185426127658101109953277)
      ·
        refine ⟨1194534797871787916232479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3185426127658101109953277 1194534797871787916232479)
        ·
          refine ⟨1791802196807681874348719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194534797871787916232479 1791802196807681874348719)
          ·
            refine ⟨2687703295211522811523079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791802196807681874348719 2687703295211522811523079)
            ·
              refine ⟨4031554942817284217284619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687703295211522811523079 4031554942817284217284619)
              ·
                refine ⟨6047332414225926325926929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4031554942817284217284619 6047332414225926325926929)
                ·
                  refine ⟨4535499310669444744445197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6047332414225926325926929 4535499310669444744445197)
                  ·
                    refine ⟨1700812241501041779166949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4535499310669444744445197 1700812241501041779166949)
                    ·
                      refine ⟨318902295281445333593803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1700812241501041779166949 318902295281445333593803)
                      ·
                        rfl

theorem cell23_621060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_621060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621060 prefixEnd_621060 := by exact prefixLift 621060
  have htrace : WordTrace (prefixWord ++ tailWord_621060) baseStart_621060 baseEnd_621060 := by
    simpa [prefixWord, tailWord_621060, baseEnd_621060] using wordTrace_append hprefix tailTrace_621060
  have hstable : (prefixWord ++ tailWord_621060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621060).length < 2 ^ (prefixWord ++ tailWord_621060).sum := by decide
  have hdescent : baseEnd_621060 < baseStart_621060 := by decide
  rcases family_descends (prefixWord ++ tailWord_621060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621070 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_621070 : Nat := 118140960795 + 621070 * 2 ^ 59
def prefixEnd_621070 : Nat := 4983230072969 + 3 ^ 40 * 621070 * 2
def baseEnd_621070 : Nat := 106302476695996764822919

theorem tailTrace_621070 : CollatzResearch.WordTrace tailWord_621070 prefixEnd_621070 106302476695996764822919 := by
  unfold tailWord_621070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2831535482497116894552583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15101522573317956770947109 2831535482497116894552583)
  ·
    refine ⟨4247303223745675341828875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2831535482497116894552583 4247303223745675341828875)
    ·
      refine ⟨6370954835618513012743313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4247303223745675341828875 6370954835618513012743313)
      ·
        refine ⟨4778216126713884759557485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6370954835618513012743313 4778216126713884759557485)
        ·
          refine ⟨1791831047517706784834057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4778216126713884759557485 1791831047517706784834057)
          ·
            refine ⟨1343873285638280088625543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1791831047517706784834057 1343873285638280088625543)
            ·
              refine ⟨2015809928457420132938315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343873285638280088625543 2015809928457420132938315)
              ·
                refine ⟨3023714892686130199407473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015809928457420132938315 3023714892686130199407473)
                ·
                  refine ⟨2267786169514597649555605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3023714892686130199407473 2267786169514597649555605)
                  ·
                    refine ⟨106302476695996764822919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2267786169514597649555605 106302476695996764822919)
                    ·
                      rfl

theorem cell23_621070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_621070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621070 prefixEnd_621070 := by exact prefixLift 621070
  have htrace : WordTrace (prefixWord ++ tailWord_621070) baseStart_621070 baseEnd_621070 := by
    simpa [prefixWord, tailWord_621070, baseEnd_621070] using wordTrace_append hprefix tailTrace_621070
  have hstable : (prefixWord ++ tailWord_621070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621070).length < 2 ^ (prefixWord ++ tailWord_621070).sum := by decide
  have hdescent : baseEnd_621070 < baseStart_621070 := by decide
  rcases family_descends (prefixWord ++ tailWord_621070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621077 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 1, 4, 2]
def baseStart_621077 : Nat := 118140960795 + 621077 * 2 ^ 59
def prefixEnd_621077 : Nat := 4983230072969 + 3 ^ 40 * 621077 * 2
def baseEnd_621077 : Nat := 318911024452571767081225

theorem tailTrace_621077 : CollatzResearch.WordTrace tailWord_621077 prefixEnd_621077 318911024452571767081225 := by
  unfold tailWord_621077
  simp only [CollatzResearch.WordTrace]
  refine ⟨22652539170951575351925485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15101692780634383567950323 22652539170951575351925485)
  ·
    refine ⟨8494702189106840756972057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22652539170951575351925485 8494702189106840756972057)
    ·
      refine ⟨6371026641830130567729043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8494702189106840756972057 6371026641830130567729043)
      ·
        refine ⟨9556539962745195851593565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6371026641830130567729043 9556539962745195851593565)
        ·
          refine ⟨3583702486029448444347587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9556539962745195851593565 3583702486029448444347587)
          ·
            refine ⟨5375553729044172666521381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583702486029448444347587 5375553729044172666521381)
            ·
              refine ⟨1007916324195782374972759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5375553729044172666521381 1007916324195782374972759)
              ·
                refine ⟨1511874486293673562459139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007916324195782374972759 1511874486293673562459139)
                ·
                  refine ⟨2267811729440510343688709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511874486293673562459139 2267811729440510343688709)
                  ·
                    refine ⟨425214699270095689441633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2267811729440510343688709 425214699270095689441633)
                    ·
                      refine ⟨318911024452571767081225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 425214699270095689441633 318911024452571767081225)
                      ·
                        rfl

theorem cell23_621077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_621077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621077 prefixEnd_621077 := by exact prefixLift 621077
  have htrace : WordTrace (prefixWord ++ tailWord_621077) baseStart_621077 baseEnd_621077 := by
    simpa [prefixWord, tailWord_621077, baseEnd_621077] using wordTrace_append hprefix tailTrace_621077
  have hstable : (prefixWord ++ tailWord_621077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621077).length < 2 ^ (prefixWord ++ tailWord_621077).sum := by decide
  have hdescent : baseEnd_621077 < baseStart_621077 := by decide
  rcases family_descends (prefixWord ++ tailWord_621077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621117 : List Nat := [1, 4, 1, 3, 2, 1, 2, 4, 5]
def baseStart_621117 : Nat := 118140960795 + 621117 * 2 ^ 59
def prefixEnd_621117 : Nat := 4983230072969 + 3 ^ 40 * 621117 * 2
def baseEnd_621117 : Nat := 35436840408750178953449

theorem tailTrace_621117 : CollatzResearch.WordTrace tailWord_621117 prefixEnd_621117 35436840408750178953449 := by
  unfold tailWord_621117
  simp only [CollatzResearch.WordTrace]
  refine ⟨22653998090806662183381605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15102665393871108122254403 22653998090806662183381605)
  ·
    refine ⟨4247624642026249159384051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22653998090806662183381605 4247624642026249159384051)
    ·
      refine ⟨6371436963039373739076077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4247624642026249159384051 6371436963039373739076077)
      ·
        refine ⟨2389288861139765152153529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6371436963039373739076077 2389288861139765152153529)
        ·
          refine ⟨1791966645854823864115147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2389288861139765152153529 1791966645854823864115147)
          ·
            refine ⟨2687949968782235796172721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791966645854823864115147 2687949968782235796172721)
            ·
              refine ⟨2015962476586676847129541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2687949968782235796172721 2015962476586676847129541)
              ·
                refine ⟨377992964360001908836789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2015962476586676847129541 377992964360001908836789)
                ·
                  refine ⟨35436840408750178953449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 377992964360001908836789 35436840408750178953449)
                  ·
                    rfl

theorem cell23_621117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_621117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621117 prefixEnd_621117 := by exact prefixLift 621117
  have htrace : WordTrace (prefixWord ++ tailWord_621117) baseStart_621117 baseEnd_621117 := by
    simpa [prefixWord, tailWord_621117, baseEnd_621117] using wordTrace_append hprefix tailTrace_621117
  have hstable : (prefixWord ++ tailWord_621117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621117).length < 2 ^ (prefixWord ++ tailWord_621117).sum := by decide
  have hdescent : baseEnd_621117 < baseStart_621117 := by decide
  rcases family_descends (prefixWord ++ tailWord_621117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621120 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 1, 7, 2]
def baseStart_621120 : Nat := 118140960795 + 621120 * 2 ^ 59
def prefixEnd_621120 : Nat := 4983230072969 + 3 ^ 40 * 621120 * 2
def baseEnd_621120 : Nat := 318933104120715098843527

theorem tailTrace_621120 : CollatzResearch.WordTrace tailWord_621120 prefixEnd_621120 318933104120715098843527 := by
  unfold tailWord_621120
  simp only [CollatzResearch.WordTrace]
  refine ⟨11327053754897896847870407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15102738339863862463827209 11327053754897896847870407)
  ·
    refine ⟨16990580632346845271805611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11327053754897896847870407 16990580632346845271805611)
    ·
      refine ⟨25485870948520267907708417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16990580632346845271805611 25485870948520267907708417)
      ·
        refine ⟨19114403211390200930781313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25485870948520267907708417 19114403211390200930781313)
        ·
          refine ⟨14335802408542650698085985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19114403211390200930781313 14335802408542650698085985)
          ·
            refine ⟨10751851806406988023564489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14335802408542650698085985 10751851806406988023564489)
            ·
              refine ⟨8063888854805241017673367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10751851806406988023564489 8063888854805241017673367)
              ·
                refine ⟨12095833282207861526510051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8063888854805241017673367 12095833282207861526510051)
                ·
                  refine ⟨18143749923311792289765077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12095833282207861526510051 18143749923311792289765077)
                  ·
                    refine ⟨425244138827620131791369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18143749923311792289765077 425244138827620131791369)
                    ·
                      refine ⟨318933104120715098843527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 425244138827620131791369 318933104120715098843527)
                      ·
                        rfl

theorem cell23_621120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 7, 2].length) (baseStart_621120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621120 prefixEnd_621120 := by exact prefixLift 621120
  have htrace : WordTrace (prefixWord ++ tailWord_621120) baseStart_621120 baseEnd_621120 := by
    simpa [prefixWord, tailWord_621120, baseEnd_621120] using wordTrace_append hprefix tailTrace_621120
  have hstable : (prefixWord ++ tailWord_621120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621120).length < 2 ^ (prefixWord ++ tailWord_621120).sum := by decide
  have hdescent : baseEnd_621120 < baseStart_621120 := by decide
  rcases family_descends (prefixWord ++ tailWord_621120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621123 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 5]
def baseStart_621123 : Nat := 118140960795 + 621123 * 2 ^ 59
def prefixEnd_621123 : Nat := 4983230072969 + 3 ^ 40 * 621123 * 2
def baseEnd_621123 : Nat := 318934644562678587106013

theorem tailTrace_621123 : CollatzResearch.WordTrace tailWord_621123 prefixEnd_621123 318934644562678587106013 := by
  unfold tailWord_621123
  simp only [CollatzResearch.WordTrace]
  refine ⟨22654216928784925208100023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15102811285856616805400015 22654216928784925208100023)
  ·
    refine ⟨33981325393177387812150035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22654216928784925208100023 33981325393177387812150035)
    ·
      refine ⟨50971988089766081718225053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33981325393177387812150035 50971988089766081718225053)
      ·
        refine ⟨19114495533662280644334395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50971988089766081718225053 19114495533662280644334395)
        ·
          refine ⟨28671743300493420966501593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19114495533662280644334395 28671743300493420966501593)
          ·
            refine ⟨21503807475370065724876195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28671743300493420966501593 21503807475370065724876195)
            ·
              refine ⟨32255711213055098587314293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21503807475370065724876195 32255711213055098587314293)
              ·
                refine ⟨3023972926223915492560715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32255711213055098587314293 3023972926223915492560715)
                ·
                  refine ⟨4535959389335873238841073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023972926223915492560715 4535959389335873238841073)
                  ·
                    refine ⟨3401969542001904929130805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4535959389335873238841073 3401969542001904929130805)
                    ·
                      refine ⟨318934644562678587106013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3401969542001904929130805 318934644562678587106013)
                      ·
                        rfl

theorem cell23_621123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_621123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621123 prefixEnd_621123 := by exact prefixLift 621123
  have htrace : WordTrace (prefixWord ++ tailWord_621123) baseStart_621123 baseEnd_621123 := by
    simpa [prefixWord, tailWord_621123, baseEnd_621123] using wordTrace_append hprefix tailTrace_621123
  have hstable : (prefixWord ++ tailWord_621123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621123).length < 2 ^ (prefixWord ++ tailWord_621123).sum := by decide
  have hdescent : baseEnd_621123 < baseStart_621123 := by decide
  rcases family_descends (prefixWord ++ tailWord_621123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621143 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 2, 8]
def baseStart_621143 : Nat := 118140960795 + 621143 * 2 ^ 59
def prefixEnd_621143 : Nat := 4983230072969 + 3 ^ 40 * 621143 * 2
def baseEnd_621143 : Nat := 106314971391922836285307

theorem tailTrace_621143 : CollatzResearch.WordTrace tailWord_621143 prefixEnd_621143 106314971391922836285307 := by
  unfold tailWord_621143
  simp only [CollatzResearch.WordTrace]
  refine ⟨22654946388712468623828083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15103297592474979082552055 22654946388712468623828083)
  ·
    refine ⟨33982419583068702935742125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22654946388712468623828083 33982419583068702935742125)
    ·
      refine ⟨12743407343650763600903297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33982419583068702935742125 12743407343650763600903297)
      ·
        refine ⟨9557555507738072700677473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12743407343650763600903297 9557555507738072700677473)
        ·
          refine ⟨7168166630803554525508105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9557555507738072700677473 7168166630803554525508105)
          ·
            refine ⟨5376124973102665894131079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7168166630803554525508105 5376124973102665894131079)
            ·
              refine ⟨8064187459653998841196619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5376124973102665894131079 8064187459653998841196619)
              ·
                refine ⟨12096281189480998261794929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8064187459653998841196619 12096281189480998261794929)
                ·
                  refine ⟨9072210892110748696346197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12096281189480998261794929 9072210892110748696346197)
                  ·
                    refine ⟨106314971391922836285307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9072210892110748696346197 106314971391922836285307)
                    ·
                      rfl

theorem cell23_621143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_621143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621143 prefixEnd_621143 := by exact prefixLift 621143
  have htrace : WordTrace (prefixWord ++ tailWord_621143) baseStart_621143 baseEnd_621143 := by
    simpa [prefixWord, tailWord_621143, baseEnd_621143] using wordTrace_append hprefix tailTrace_621143
  have hstable : (prefixWord ++ tailWord_621143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621143).length < 2 ^ (prefixWord ++ tailWord_621143).sum := by decide
  have hdescent : baseEnd_621143 < baseStart_621143 := by decide
  rcases family_descends (prefixWord ++ tailWord_621143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621163 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 6]
def baseStart_621163 : Nat := 118140960795 + 621163 * 2 ^ 59
def prefixEnd_621163 : Nat := 4983230072969 + 3 ^ 40 * 621163 * 2
def baseEnd_621163 : Nat := 318955183788858430605829

theorem tailTrace_621163 : CollatzResearch.WordTrace tailWord_621163 prefixEnd_621163 318955183788858430605829 := by
  unfold tailWord_621163
  simp only [CollatzResearch.WordTrace]
  refine ⟨22655675848640012039556143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15103783899093341359704095 22655675848640012039556143)
  ·
    refine ⟨33983513772960018059334215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22655675848640012039556143 33983513772960018059334215)
    ·
      refine ⟨50975270659440027089001323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33983513772960018059334215 50975270659440027089001323)
      ·
        refine ⟨76462905989160040633501985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50975270659440027089001323 76462905989160040633501985)
        ·
          refine ⟨57347179491870030475126489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76462905989160040633501985 57347179491870030475126489)
          ·
            refine ⟨43010384618902522856344867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57347179491870030475126489 43010384618902522856344867)
            ·
              refine ⟨64515576928353784284517301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43010384618902522856344867 64515576928353784284517301)
              ·
                refine ⟨6048335337033167276673497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64515576928353784284517301 6048335337033167276673497)
                ·
                  refine ⟨4536251502774875457505123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6048335337033167276673497 4536251502774875457505123)
                  ·
                    refine ⟨6804377254162313186257685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4536251502774875457505123 6804377254162313186257685)
                    ·
                      refine ⟨318955183788858430605829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6804377254162313186257685 318955183788858430605829)
                      ·
                        rfl

theorem cell23_621163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 6].length) (baseStart_621163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621163 prefixEnd_621163 := by exact prefixLift 621163
  have htrace : WordTrace (prefixWord ++ tailWord_621163) baseStart_621163 baseEnd_621163 := by
    simpa [prefixWord, tailWord_621163, baseEnd_621163] using wordTrace_append hprefix tailTrace_621163
  have hstable : (prefixWord ++ tailWord_621163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621163).length < 2 ^ (prefixWord ++ tailWord_621163).sum := by decide
  have hdescent : baseEnd_621163 < baseStart_621163 := by decide
  rcases family_descends (prefixWord ++ tailWord_621163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621177 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 3, 4]
def baseStart_621177 : Nat := 118140960795 + 621177 * 2 ^ 59
def prefixEnd_621177 : Nat := 4983230072969 + 3 ^ 40 * 621177 * 2
def baseEnd_621177 : Nat := 106320790839340458610255

theorem tailTrace_621177 : CollatzResearch.WordTrace tailWord_621177 prefixEnd_621177 106320790839340458610255 := by
  unfold tailWord_621177
  simp only [CollatzResearch.WordTrace]
  refine ⟨22656186470589292430565785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15104124313726194953710523 22656186470589292430565785)
  ·
    refine ⟨16992139852941969322924339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22656186470589292430565785 16992139852941969322924339)
    ·
      refine ⟨25488209779412953984386509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16992139852941969322924339 25488209779412953984386509)
      ·
        refine ⟨9558078667279857744144941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25488209779412953984386509 9558078667279857744144941)
        ·
          refine ⟨3584279500229946654054353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9558078667279857744144941 3584279500229946654054353)
          ·
            refine ⟨2688209625172459990540765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3584279500229946654054353 2688209625172459990540765)
            ·
              refine ⟨1008078609439672496452787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2688209625172459990540765 1008078609439672496452787)
              ·
                refine ⟨1512117914159508744679181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008078609439672496452787 1512117914159508744679181)
                ·
                  refine ⟨567044217809815779254693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1512117914159508744679181 567044217809815779254693)
                  ·
                    refine ⟨106320790839340458610255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 567044217809815779254693 106320790839340458610255)
                    ·
                      rfl

theorem cell23_621177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 4].length) (baseStart_621177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621177 prefixEnd_621177 := by exact prefixLift 621177
  have htrace : WordTrace (prefixWord ++ tailWord_621177) baseStart_621177 baseEnd_621177 := by
    simpa [prefixWord, tailWord_621177, baseEnd_621177] using wordTrace_append hprefix tailTrace_621177
  have hstable : (prefixWord ++ tailWord_621177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621177).length < 2 ^ (prefixWord ++ tailWord_621177).sum := by decide
  have hdescent : baseEnd_621177 < baseStart_621177 := by decide
  rcases family_descends (prefixWord ++ tailWord_621177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621203 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 2, 9]
def baseStart_621203 : Nat := 118140960795 + 621203 * 2 ^ 59
def prefixEnd_621203 : Nat := 4983230072969 + 3 ^ 40 * 621203 * 2
def baseEnd_621203 : Nat := 106325241005012758035215

theorem tailTrace_621203 : CollatzResearch.WordTrace tailWord_621203 prefixEnd_621203 106325241005012758035215 := by
  unfold tailWord_621203
  simp only [CollatzResearch.WordTrace]
  refine ⟨22657134768495098871012263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15104756512330065914008175 22657134768495098871012263)
  ·
    refine ⟨33985702152742648306518395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22657134768495098871012263 33985702152742648306518395)
    ·
      refine ⟨50978553229113972459777593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33985702152742648306518395 50978553229113972459777593)
      ·
        refine ⟨38233914921835479344833195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50978553229113972459777593 38233914921835479344833195)
        ·
          refine ⟨57350872382753219017249793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38233914921835479344833195 57350872382753219017249793)
          ·
            refine ⟨43013154287064914262937345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57350872382753219017249793 43013154287064914262937345)
            ·
              refine ⟨32259865715298685697203009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43013154287064914262937345 32259865715298685697203009)
              ·
                refine ⟨24194899286474014272902257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32259865715298685697203009 24194899286474014272902257)
                ·
                  refine ⟨18146174464855510704676693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24194899286474014272902257 18146174464855510704676693)
                  ·
                    refine ⟨106325241005012758035215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 18146174464855510704676693 106325241005012758035215)
                    ·
                      rfl

theorem cell23_621203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 9].length) (baseStart_621203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621203 prefixEnd_621203 := by exact prefixLift 621203
  have htrace : WordTrace (prefixWord ++ tailWord_621203) baseStart_621203 baseEnd_621203 := by
    simpa [prefixWord, tailWord_621203, baseEnd_621203] using wordTrace_append hprefix tailTrace_621203
  have hstable : (prefixWord ++ tailWord_621203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621203).length < 2 ^ (prefixWord ++ tailWord_621203).sum := by decide
  have hdescent : baseEnd_621203 < baseStart_621203 := by decide
  rcases family_descends (prefixWord ++ tailWord_621203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621204 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_621204 : Nat := 118140960795 + 621204 * 2 ^ 59
def prefixEnd_621204 : Nat := 4983230072969 + 3 ^ 40 * 621204 * 2
def baseEnd_621204 : Nat := 318976236495692770193141

theorem tailTrace_621204 : CollatzResearch.WordTrace tailWord_621204 prefixEnd_621204 318976236495692770193141 := by
  unfold tailWord_621204
  simp only [CollatzResearch.WordTrace]
  refine ⟨11328585620745738020899333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15104780827660984027865777 11328585620745738020899333)
  ·
    refine ⟨2124109803889825878918625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11328585620745738020899333 2124109803889825878918625)
    ·
      refine ⟨1593082352917369409188969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2124109803889825878918625 1593082352917369409188969)
      ·
        refine ⟨1194811764688027056891727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1593082352917369409188969 1194811764688027056891727)
        ·
          refine ⟨1792217647032040585337591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194811764688027056891727 1792217647032040585337591)
          ·
            refine ⟨2688326470548060878006387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792217647032040585337591 2688326470548060878006387)
            ·
              refine ⟨4032489705822091317009581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2688326470548060878006387 4032489705822091317009581)
              ·
                refine ⟨1512183639683284243878593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4032489705822091317009581 1512183639683284243878593)
                ·
                  refine ⟨1134137729762463182908945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1512183639683284243878593 1134137729762463182908945)
                  ·
                    refine ⟨850603297321847387181709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1134137729762463182908945 850603297321847387181709)
                    ·
                      refine ⟨318976236495692770193141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 850603297321847387181709 318976236495692770193141)
                      ·
                        rfl

theorem cell23_621204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_621204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621204 prefixEnd_621204 := by exact prefixLift 621204
  have htrace : WordTrace (prefixWord ++ tailWord_621204) baseStart_621204 baseEnd_621204 := by
    simpa [prefixWord, tailWord_621204, baseEnd_621204] using wordTrace_append hprefix tailTrace_621204
  have hstable : (prefixWord ++ tailWord_621204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621204).length < 2 ^ (prefixWord ++ tailWord_621204).sum := by decide
  have hdescent : baseEnd_621204 < baseStart_621204 := by decide
  rcases family_descends (prefixWord ++ tailWord_621204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
