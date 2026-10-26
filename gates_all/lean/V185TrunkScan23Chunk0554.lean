import V185TrunkScan23Chunk0553

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3274055 : List Nat := [1, 1, 4, 1, 2, 5, 1, 8]
def baseStart_3274055 : Nat := 118140960795 + 3274055 * 2 ^ 59
def prefixEnd_3274055 : Nat := 4983230072969 + 3 ^ 40 * 3274055 * 2
def baseEnd_3274055 : Nat := 62265329787270110313163

theorem tailTrace_3274055 : CollatzResearch.WordTrace tailWord_3274055 prefixEnd_3274055 62265329787270110313163 := by
  unfold tailWord_3274055
  simp only [CollatzResearch.WordTrace]
  refine ⟨119414596153665373921783619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79609730769110249281189079 119414596153665373921783619)
  ·
    refine ⟨179121894230498060882675429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119414596153665373921783619 179121894230498060882675429)
    ·
      refine ⟨33585355168218386415501643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179121894230498060882675429 33585355168218386415501643)
      ·
        refine ⟨50378032752327579623252465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33585355168218386415501643 50378032752327579623252465)
        ·
          refine ⟨37783524564245684717439349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50378032752327579623252465 37783524564245684717439349)
          ·
            refine ⟨3542205427898032942259939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37783524564245684717439349 3542205427898032942259939)
            ·
              refine ⟨5313308141847049413389909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542205427898032942259939 5313308141847049413389909)
              ·
                refine ⟨62265329787270110313163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5313308141847049413389909 62265329787270110313163)
                ·
                  rfl

theorem cell23_3274055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 8].length) (baseStart_3274055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274055 prefixEnd_3274055 := by exact prefixLift 3274055
  have htrace : WordTrace (prefixWord ++ tailWord_3274055) baseStart_3274055 baseEnd_3274055 := by
    simpa [prefixWord, tailWord_3274055, baseEnd_3274055] using wordTrace_append hprefix tailTrace_3274055
  have hstable : (prefixWord ++ tailWord_3274055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274055).length < 2 ^ (prefixWord ++ tailWord_3274055).sum := by decide
  have hdescent : baseEnd_3274055 < baseStart_3274055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274058 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_3274058 : Nat := 118140960795 + 3274058 * 2 ^ 59
def prefixEnd_3274058 : Nat := 4983230072969 + 3 ^ 40 * 3274058 * 2
def baseEnd_3274058 : Nat := 1681165444698256466717887

theorem tailTrace_3274058 : CollatzResearch.WordTrace tailWord_3274058 prefixEnd_3274058 1681165444698256466717887 := by
  unfold tailWord_3274058
  simp only [CollatzResearch.WordTrace]
  refine ⟨29853676393163626358535707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79609803715103003622761885 29853676393163626358535707)
  ·
    refine ⟨44780514589745439537803561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29853676393163626358535707 44780514589745439537803561)
    ·
      refine ⟨33585385942309079653352671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44780514589745439537803561 33585385942309079653352671)
      ·
        refine ⟨50378078913463619480029007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33585385942309079653352671 50378078913463619480029007)
        ·
          refine ⟨75567118370195429220043511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50378078913463619480029007 75567118370195429220043511)
          ·
            refine ⟨113350677555293143830065267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75567118370195429220043511 113350677555293143830065267)
            ·
              refine ⟨170026016332939715745097901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113350677555293143830065267 170026016332939715745097901)
              ·
                refine ⟨63759756124852393404411713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170026016332939715745097901 63759756124852393404411713)
                ·
                  refine ⟨47819817093639295053308785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63759756124852393404411713 47819817093639295053308785)
                  ·
                    refine ⟨35864862820229471289981589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47819817093639295053308785 35864862820229471289981589)
                    ·
                      refine ⟨1681165444698256466717887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35864862820229471289981589 1681165444698256466717887)
                      ·
                        rfl

theorem cell23_3274058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_3274058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274058 prefixEnd_3274058 := by exact prefixLift 3274058
  have htrace : WordTrace (prefixWord ++ tailWord_3274058) baseStart_3274058 baseEnd_3274058 := by
    simpa [prefixWord, tailWord_3274058, baseEnd_3274058] using wordTrace_append hprefix tailTrace_3274058
  have hstable : (prefixWord ++ tailWord_3274058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274058).length < 2 ^ (prefixWord ++ tailWord_3274058).sum := by decide
  have hdescent : baseEnd_3274058 < baseStart_3274058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274082 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_3274082 : Nat := 118140960795 + 3274082 * 2 ^ 59
def prefixEnd_3274082 : Nat := 4983230072969 + 3 ^ 40 * 3274082 * 2
def baseEnd_3274082 : Nat := 1681177768233964372817777

theorem tailTrace_3274082 : CollatzResearch.WordTrace tailWord_3274082 prefixEnd_3274082 1681177768233964372817777 := by
  unfold tailWord_3274082
  simp only [CollatzResearch.WordTrace]
  refine ⟨29853895231141889383254125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79610387283045038355344333 29853895231141889383254125)
  ·
    refine ⟨11195210711678208518720297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29853895231141889383254125 11195210711678208518720297)
    ·
      refine ⟨8396408033758656389040223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11195210711678208518720297 8396408033758656389040223)
      ·
        refine ⟨12594612050637984583560335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8396408033758656389040223 12594612050637984583560335)
        ·
          refine ⟨18891918075956976875340503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12594612050637984583560335 18891918075956976875340503)
          ·
            refine ⟨28337877113935465313010755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18891918075956976875340503 28337877113935465313010755)
            ·
              refine ⟨42506815670903197969516133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28337877113935465313010755 42506815670903197969516133)
              ·
                refine ⟨7970027938294349619284275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42506815670903197969516133 7970027938294349619284275)
                ·
                  refine ⟨11955041907441524428926413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7970027938294349619284275 11955041907441524428926413)
                  ·
                    refine ⟨4483140715290571660847405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11955041907441524428926413 4483140715290571660847405)
                    ·
                      refine ⟨1681177768233964372817777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4483140715290571660847405 1681177768233964372817777)
                      ·
                        rfl

theorem cell23_3274082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_3274082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274082 prefixEnd_3274082 := by exact prefixLift 3274082
  have htrace : WordTrace (prefixWord ++ tailWord_3274082) baseStart_3274082 baseEnd_3274082 := by
    simpa [prefixWord, tailWord_3274082, baseEnd_3274082] using wordTrace_append hprefix tailTrace_3274082
  have hstable : (prefixWord ++ tailWord_3274082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274082).length < 2 ^ (prefixWord ++ tailWord_3274082).sum := by decide
  have hdescent : baseEnd_3274082 < baseStart_3274082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274115 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 2, 6]
def baseStart_3274115 : Nat := 118140960795 + 3274115 * 2 ^ 59
def prefixEnd_3274115 : Nat := 4983230072969 + 3 ^ 40 * 3274115 * 2
def baseEnd_3274115 : Nat := 560398237698520914568375

theorem tailTrace_3274115 : CollatzResearch.WordTrace tailWord_3274115 prefixEnd_3274115 560398237698520914568375 := by
  unfold tailWord_3274115
  simp only [CollatzResearch.WordTrace]
  refine ⟨119416784533448004168967799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79611189688965336112645199 119416784533448004168967799)
  ·
    refine ⟨179125176800172006253451699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119416784533448004168967799 179125176800172006253451699)
    ·
      refine ⟨268687765200258009380177549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179125176800172006253451699 268687765200258009380177549)
      ·
        refine ⟨100757911950096753517566581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268687765200258009380177549 100757911950096753517566581)
        ·
          refine ⟨9446054245321570642271867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100757911950096753517566581 9446054245321570642271867)
          ·
            refine ⟨14169081367982355963407801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9446054245321570642271867 14169081367982355963407801)
            ·
              refine ⟨10626811025986766972555851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14169081367982355963407801 10626811025986766972555851)
              ·
                refine ⟨15940216538980150458833777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10626811025986766972555851 15940216538980150458833777)
                ·
                  refine ⟨11955162404235112844125333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15940216538980150458833777 11955162404235112844125333)
                  ·
                    refine ⟨560398237698520914568375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11955162404235112844125333 560398237698520914568375)
                    ·
                      rfl

theorem cell23_3274115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 6].length) (baseStart_3274115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274115 prefixEnd_3274115 := by exact prefixLift 3274115
  have htrace : WordTrace (prefixWord ++ tailWord_3274115) baseStart_3274115 baseEnd_3274115 := by
    simpa [prefixWord, tailWord_3274115, baseEnd_3274115] using wordTrace_append hprefix tailTrace_3274115
  have hstable : (prefixWord ++ tailWord_3274115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274115).length < 2 ^ (prefixWord ++ tailWord_3274115).sum := by decide
  have hdescent : baseEnd_3274115 < baseStart_3274115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274116 : List Nat := [2, 3, 2, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_3274116 : Nat := 118140960795 + 3274116 * 2 ^ 59
def prefixEnd_3274116 : Nat := 4983230072969 + 3 ^ 40 * 3274116 * 2
def baseEnd_3274116 : Nat := 1681195226576217239792621

theorem tailTrace_3274116 : CollatzResearch.WordTrace tailWord_3274116 prefixEnd_3274116 1681195226576217239792621 := by
  unfold tailWord_3274116
  simp only [CollatzResearch.WordTrace]
  refine ⟨59708410503222190669877101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79611214004296254226502801 59708410503222190669877101)
  ·
    refine ⟨22390653938708321501203913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59708410503222190669877101 22390653938708321501203913)
    ·
      refine ⟨16792990454031241125902935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22390653938708321501203913 16792990454031241125902935)
      ·
        refine ⟨25189485681046861688854403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16792990454031241125902935 25189485681046861688854403)
        ·
          refine ⟨37784228521570292533281605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25189485681046861688854403 37784228521570292533281605)
          ·
            refine ⟨7084542847794429849990301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37784228521570292533281605 7084542847794429849990301)
            ·
              refine ⟨2656703567922911193746363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7084542847794429849990301 2656703567922911193746363)
              ·
                refine ⟨3985055351884366790619545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2656703567922911193746363 3985055351884366790619545)
                ·
                  refine ⟨2988791513913275092964659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3985055351884366790619545 2988791513913275092964659)
                  ·
                    refine ⟨4483187270869912639446989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2988791513913275092964659 4483187270869912639446989)
                    ·
                      refine ⟨1681195226576217239792621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4483187270869912639446989 1681195226576217239792621)
                      ·
                        rfl

theorem cell23_3274116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_3274116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274116 prefixEnd_3274116 := by exact prefixLift 3274116
  have htrace : WordTrace (prefixWord ++ tailWord_3274116) baseStart_3274116 baseEnd_3274116 := by
    simpa [prefixWord, tailWord_3274116, baseEnd_3274116] using wordTrace_append hprefix tailTrace_3274116
  have hstable : (prefixWord ++ tailWord_3274116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274116).length < 2 ^ (prefixWord ++ tailWord_3274116).sum := by decide
  have hdescent : baseEnd_3274116 < baseStart_3274116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274212 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 3, 6, 2]
def baseStart_3274212 : Nat := 118140960795 + 3274212 * 2 ^ 59
def prefixEnd_3274212 : Nat := 4983230072969 + 3 ^ 40 * 3274212 * 2
def baseEnd_3274212 : Nat := 1681244520719048864192179

theorem tailTrace_3274212 : CollatzResearch.WordTrace tailWord_3274212 prefixEnd_3274212 1681244520719048864192179 := by
  unfold tailWord_3274212
  simp only [CollatzResearch.WordTrace]
  refine ⟨59710161207048294867624445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79613548276064393156832593 59710161207048294867624445)
  ·
    refine ⟨22391310452643110575359167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59710161207048294867624445 22391310452643110575359167)
    ·
      refine ⟨33586965678964665863038751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22391310452643110575359167 33586965678964665863038751)
      ·
        refine ⟨50380448518446998794558127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33586965678964665863038751 50380448518446998794558127)
        ·
          refine ⟨75570672777670498191837191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50380448518446998794558127 75570672777670498191837191)
          ·
            refine ⟨113356009166505747287755787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75570672777670498191837191 113356009166505747287755787)
            ·
              refine ⟨170034013749758620931633681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113356009166505747287755787 170034013749758620931633681)
              ·
                refine ⟨127525510312318965698725261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170034013749758620931633681 127525510312318965698725261)
                ·
                  refine ⟨47822066367119612137021973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127525510312318965698725261 47822066367119612137021973)
                  ·
                    refine ⟨2241659360958731818922905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47822066367119612137021973 2241659360958731818922905)
                    ·
                      refine ⟨1681244520719048864192179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2241659360958731818922905 1681244520719048864192179)
                      ·
                        rfl

theorem cell23_3274212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_3274212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274212 prefixEnd_3274212 := by exact prefixLift 3274212
  have htrace : WordTrace (prefixWord ++ tailWord_3274212) baseStart_3274212 baseEnd_3274212 := by
    simpa [prefixWord, tailWord_3274212, baseEnd_3274212] using wordTrace_append hprefix tailTrace_3274212
  have hstable : (prefixWord ++ tailWord_3274212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274212).length < 2 ^ (prefixWord ++ tailWord_3274212).sum := by decide
  have hdescent : baseEnd_3274212 < baseStart_3274212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274272 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3274272 : Nat := 118140960795 + 3274272 * 2 ^ 59
def prefixEnd_3274272 : Nat := 4983230072969 + 3 ^ 40 * 3274272 * 2
def baseEnd_3274272 : Nat := 1681275329558318629441903

theorem tailTrace_3274272 : CollatzResearch.WordTrace tailWord_3274272 prefixEnd_3274272 1681275329558318629441903 := by
  unfold tailWord_3274272
  simp only [CollatzResearch.WordTrace]
  refine ⟨59711255396939609991216535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79615007195919479988288713 59711255396939609991216535)
  ·
    refine ⟨89566883095409414986824803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59711255396939609991216535 89566883095409414986824803)
    ·
      refine ⟨134350324643114122480237205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89566883095409414986824803 134350324643114122480237205)
      ·
        refine ⟨6297671467645974491261119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 134350324643114122480237205 6297671467645974491261119)
        ·
          refine ⟨9446507201468961736891679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6297671467645974491261119 9446507201468961736891679)
          ·
            refine ⟨14169760802203442605337519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9446507201468961736891679 14169760802203442605337519)
            ·
              refine ⟨21254641203305163908006279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14169760802203442605337519 21254641203305163908006279)
              ·
                refine ⟨31881961804957745862009419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21254641203305163908006279 31881961804957745862009419)
                ·
                  refine ⟨47822942707436618793014129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31881961804957745862009419 47822942707436618793014129)
                  ·
                    refine ⟨35867207030577464094760597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47822942707436618793014129 35867207030577464094760597)
                    ·
                      refine ⟨1681275329558318629441903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35867207030577464094760597 1681275329558318629441903)
                      ·
                        rfl

theorem cell23_3274272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3274272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274272 prefixEnd_3274272 := by exact prefixLift 3274272
  have htrace : WordTrace (prefixWord ++ tailWord_3274272) baseStart_3274272 baseEnd_3274272 := by
    simpa [prefixWord, tailWord_3274272, baseEnd_3274272] using wordTrace_append hprefix tailTrace_3274272
  have hstable : (prefixWord ++ tailWord_3274272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274272).length < 2 ^ (prefixWord ++ tailWord_3274272).sum := by decide
  have hdescent : baseEnd_3274272 < baseStart_3274272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274286 : List Nat := [4, 1, 3, 1, 2, 2, 3, 1, 6]
def baseStart_3274286 : Nat := 118140960795 + 3274286 * 2 ^ 59
def prefixEnd_3274286 : Nat := 4983230072969 + 3 ^ 40 * 3274286 * 2
def baseEnd_3274286 : Nat := 186809168698609063851871

theorem tailTrace_3274286 : CollatzResearch.WordTrace tailWord_3274286 prefixEnd_3274286 186809168698609063851871 := by
  unfold tailWord_3274286
  simp only [CollatzResearch.WordTrace]
  refine ⟨14927877676978562546680339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79615347610552333582295141 14927877676978562546680339)
  ·
    refine ⟨22391816515467843820020509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14927877676978562546680339 22391816515467843820020509)
    ·
      refine ⟨8396931193300441432507691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22391816515467843820020509 8396931193300441432507691)
      ·
        refine ⟨12595396789950662148761537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8396931193300441432507691 12595396789950662148761537)
        ·
          refine ⟨9446547592462996611571153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12595396789950662148761537 9446547592462996611571153)
          ·
            refine ⟨7084910694347247458678365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9446547592462996611571153 7084910694347247458678365)
            ·
              refine ⟨2656841510380217797004387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7084910694347247458678365 2656841510380217797004387)
              ·
                refine ⟨3985262265570326695506581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2656841510380217797004387 3985262265570326695506581)
                ·
                  refine ⟨186809168698609063851871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3985262265570326695506581 186809168698609063851871)
                  ·
                    rfl

theorem cell23_3274286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_3274286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274286 prefixEnd_3274286 := by exact prefixLift 3274286
  have htrace : WordTrace (prefixWord ++ tailWord_3274286) baseStart_3274286 baseEnd_3274286 := by
    simpa [prefixWord, tailWord_3274286, baseEnd_3274286] using wordTrace_append hprefix tailTrace_3274286
  have hstable : (prefixWord ++ tailWord_3274286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274286).length < 2 ^ (prefixWord ++ tailWord_3274286).sum := by decide
  have hdescent : baseEnd_3274286 < baseStart_3274286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274346 : List Nat := [3, 1, 3, 2, 1, 3, 1, 3, 2, 4]
def baseStart_3274346 : Nat := 118140960795 + 3274346 * 2 ^ 59
def prefixEnd_3274346 : Nat := 4983230072969 + 3 ^ 40 * 3274346 * 2
def baseEnd_3274346 : Nat := 560437775708917113305521

theorem tailTrace_3274346 : CollatzResearch.WordTrace tailWord_3274346 prefixEnd_3274346 560437775708917113305521 := by
  unfold tailWord_3274346
  simp only [CollatzResearch.WordTrace]
  refine ⟨29856302448902782655156723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79616806530407420413751261 29856302448902782655156723)
  ·
    refine ⟨44784453673354173982735085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29856302448902782655156723 44784453673354173982735085)
    ·
      refine ⟨16794170127507815243525657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44784453673354173982735085 16794170127507815243525657)
      ·
        refine ⟨12595627595630861432644243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16794170127507815243525657 12595627595630861432644243)
        ·
          refine ⟨18893441393446292148966365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12595627595630861432644243 18893441393446292148966365)
          ·
            refine ⟨7085040522542359555862387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18893441393446292148966365 7085040522542359555862387)
            ·
              refine ⟨10627560783813539333793581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7085040522542359555862387 10627560783813539333793581)
              ·
                refine ⟨3985335293930077250172593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10627560783813539333793581 3985335293930077250172593)
                ·
                  refine ⟨2989001470447557937629445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3985335293930077250172593 2989001470447557937629445)
                  ·
                    refine ⟨560437775708917113305521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2989001470447557937629445 560437775708917113305521)
                    ·
                      rfl

theorem cell23_3274346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_3274346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274346 prefixEnd_3274346 := by exact prefixLift 3274346
  have htrace : WordTrace (prefixWord ++ tailWord_3274346) baseStart_3274346 baseEnd_3274346 := by
    simpa [prefixWord, tailWord_3274346, baseEnd_3274346] using wordTrace_append hprefix tailTrace_3274346
  have hstable : (prefixWord ++ tailWord_3274346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274346).length < 2 ^ (prefixWord ++ tailWord_3274346).sum := by decide
  have hdescent : baseEnd_3274346 < baseStart_3274346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274369 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_3274369 : Nat := 118140960795 + 3274369 * 2 ^ 59
def prefixEnd_3274369 : Nat := 4983230072969 + 3 ^ 40 * 3274369 * 2
def baseEnd_3274369 : Nat := 1681325137181804749928957

theorem tailTrace_3274369 : CollatzResearch.WordTrace tailWord_3274369 prefixEnd_3274369 1681325137181804749928957 := by
  unfold tailWord_3274369
  simp only [CollatzResearch.WordTrace]
  refine ⟨119426048674527805548714161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79617365783018537032476107 119426048674527805548714161)
  ·
    refine ⟨89569536505895854161535621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119426048674527805548714161 89569536505895854161535621)
    ·
      refine ⟨16794288094855472655287929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89569536505895854161535621 16794288094855472655287929)
      ·
        refine ⟨12595716071141604491465947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16794288094855472655287929 12595716071141604491465947)
        ·
          refine ⟨18893574106712406737198921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12595716071141604491465947 18893574106712406737198921)
          ·
            refine ⟨14170180580034305052899191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18893574106712406737198921 14170180580034305052899191)
            ·
              refine ⟨21255270870051457579348787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14170180580034305052899191 21255270870051457579348787)
              ·
                refine ⟨31882906305077186369023181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21255270870051457579348787 31882906305077186369023181)
                ·
                  refine ⟨11956089864403944888383693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31882906305077186369023181 11956089864403944888383693)
                  ·
                    refine ⟨4483533699151479333143885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11956089864403944888383693 4483533699151479333143885)
                    ·
                      refine ⟨1681325137181804749928957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4483533699151479333143885 1681325137181804749928957)
                      ·
                        rfl

theorem cell23_3274369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_3274369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274369 prefixEnd_3274369 := by exact prefixLift 3274369
  have htrace : WordTrace (prefixWord ++ tailWord_3274369) baseStart_3274369 baseEnd_3274369 := by
    simpa [prefixWord, tailWord_3274369, baseEnd_3274369] using wordTrace_append hprefix tailTrace_3274369
  have hstable : (prefixWord ++ tailWord_3274369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274369).length < 2 ^ (prefixWord ++ tailWord_3274369).sum := by decide
  have hdescent : baseEnd_3274369 < baseStart_3274369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274413 : List Nat := [1, 5, 2, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_3274413 : Nat := 118140960795 + 3274413 * 2 ^ 59
def prefixEnd_3274413 : Nat := 4983230072969 + 3 ^ 40 * 3274413 * 2
def baseEnd_3274413 : Nat := 1681347730330602577778755

theorem tailTrace_3274413 : CollatzResearch.WordTrace tailWord_3274413 prefixEnd_3274413 1681347730330602577778755 := by
  unfold tailWord_3274413
  simp only [CollatzResearch.WordTrace]
  refine ⟨119427653486368401063315893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79618435657578934042210595 119427653486368401063315893)
  ·
    refine ⟨11196342514347037599685865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119427653486368401063315893 11196342514347037599685865)
    ·
      refine ⟨8397256885760278199764399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11196342514347037599685865 8397256885760278199764399)
      ·
        refine ⟨12595885328640417299646599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8397256885760278199764399 12595885328640417299646599)
        ·
          refine ⟨18893827992960625949469899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12595885328640417299646599 18893827992960625949469899)
          ·
            refine ⟨28340741989440938924204849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18893827992960625949469899 28340741989440938924204849)
            ·
              refine ⟨21255556492080704193153637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28340741989440938924204849 21255556492080704193153637)
              ·
                refine ⟨3985416842265132036216307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21255556492080704193153637 3985416842265132036216307)
                ·
                  refine ⟨5978125263397698054324461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3985416842265132036216307 5978125263397698054324461)
                  ·
                    refine ⟨2241796973774136770371673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5978125263397698054324461 2241796973774136770371673)
                    ·
                      refine ⟨1681347730330602577778755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2241796973774136770371673 1681347730330602577778755)
                      ·
                        rfl

theorem cell23_3274413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_3274413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274413 prefixEnd_3274413 := by exact prefixLift 3274413
  have htrace : WordTrace (prefixWord ++ tailWord_3274413) baseStart_3274413 baseEnd_3274413 := by
    simpa [prefixWord, tailWord_3274413, baseEnd_3274413] using wordTrace_append hprefix tailTrace_3274413
  have hstable : (prefixWord ++ tailWord_3274413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274413).length < 2 ^ (prefixWord ++ tailWord_3274413).sum := by decide
  have hdescent : baseEnd_3274413 < baseStart_3274413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274426 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2]
def baseStart_3274426 : Nat := 118140960795 + 3274426 * 2 ^ 59
def prefixEnd_3274426 : Nat := 4983230072969 + 3 ^ 40 * 3274426 * 2
def baseEnd_3274426 : Nat := 1681354405579111026916195

theorem tailTrace_3274426 : CollatzResearch.WordTrace tailWord_3274426 prefixEnd_3274426 1681354405579111026916195 := by
  unfold tailWord_3274426
  simp only [CollatzResearch.WordTrace]
  refine ⟨29857031908830326070884783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79618751756880869522359421 29857031908830326070884783)
  ·
    refine ⟨44785547863245489106327175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29857031908830326070884783 44785547863245489106327175)
    ·
      refine ⟨67178321794868233659490763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44785547863245489106327175 67178321794868233659490763)
      ·
        refine ⟨100767482692302350489236145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67178321794868233659490763 100767482692302350489236145)
        ·
          refine ⟨75575612019226762866927109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100767482692302350489236145 75575612019226762866927109)
          ·
            refine ⟨14170427253605018037548833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75575612019226762866927109 14170427253605018037548833)
            ·
              refine ⟨10627820440203763528161625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14170427253605018037548833 10627820440203763528161625)
              ·
                refine ⟨7970865330152822646121219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10627820440203763528161625 7970865330152822646121219)
                ·
                  refine ⟨11956297995229233969181829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7970865330152822646121219 11956297995229233969181829)
                  ·
                    refine ⟨2241805874105481369221593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11956297995229233969181829 2241805874105481369221593)
                    ·
                      refine ⟨1681354405579111026916195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2241805874105481369221593 1681354405579111026916195)
                      ·
                        rfl

theorem cell23_3274426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2].length) (baseStart_3274426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274426 prefixEnd_3274426 := by exact prefixLift 3274426
  have htrace : WordTrace (prefixWord ++ tailWord_3274426) baseStart_3274426 baseEnd_3274426 := by
    simpa [prefixWord, tailWord_3274426, baseEnd_3274426] using wordTrace_append hprefix tailTrace_3274426
  have hstable : (prefixWord ++ tailWord_3274426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274426).length < 2 ^ (prefixWord ++ tailWord_3274426).sum := by decide
  have hdescent : baseEnd_3274426 < baseStart_3274426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274430 : List Nat := [4, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_3274430 : Nat := 118140960795 + 3274430 * 2 ^ 59
def prefixEnd_3274430 : Nat := 4983230072969 + 3 ^ 40 * 3274430 * 2
def baseEnd_3274430 : Nat := 1681356459501729011266177

theorem tailTrace_3274430 : CollatzResearch.WordTrace tailWord_3274430 prefixEnd_3274430 1681356459501729011266177 := by
  unfold tailWord_3274430
  simp only [CollatzResearch.WordTrace]
  refine ⟨14928534190913351620835593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79618849018204541977789829 14928534190913351620835593)
  ·
    refine ⟨11196400643185013715626695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14928534190913351620835593 11196400643185013715626695)
    ·
      refine ⟨16794600964777520573440043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11196400643185013715626695 16794600964777520573440043)
      ·
        refine ⟨25191901447166280860160065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16794600964777520573440043 25191901447166280860160065)
        ·
          refine ⟨18893926085374710645120049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25191901447166280860160065 18893926085374710645120049)
          ·
            refine ⟨14170444564031032983840037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18893926085374710645120049 14170444564031032983840037)
            ·
              refine ⟨2656958355755818684470007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14170444564031032983840037 2656958355755818684470007)
              ·
                refine ⟨3985437533633728026705011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2656958355755818684470007 3985437533633728026705011)
                ·
                  refine ⟨5978156300450592040057517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3985437533633728026705011 5978156300450592040057517)
                  ·
                    refine ⟨2241808612668972015021569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5978156300450592040057517 2241808612668972015021569)
                    ·
                      refine ⟨1681356459501729011266177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2241808612668972015021569 1681356459501729011266177)
                      ·
                        rfl

theorem cell23_3274430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_3274430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274430 prefixEnd_3274430 := by exact prefixLift 3274430
  have htrace : WordTrace (prefixWord ++ tailWord_3274430) baseStart_3274430 baseEnd_3274430 := by
    simpa [prefixWord, tailWord_3274430, baseEnd_3274430] using wordTrace_append hprefix tailTrace_3274430
  have hstable : (prefixWord ++ tailWord_3274430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274430).length < 2 ^ (prefixWord ++ tailWord_3274430).sum := by decide
  have hdescent : baseEnd_3274430 < baseStart_3274430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274432 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 9]
def baseStart_3274432 : Nat := 118140960795 + 3274432 * 2 ^ 59
def prefixEnd_3274432 : Nat := 4983230072969 + 3 ^ 40 * 3274432 * 2
def baseEnd_3274432 : Nat := 186817498495893111493463

theorem tailTrace_3274432 : CollatzResearch.WordTrace tailWord_3274432 prefixEnd_3274432 186817498495893111493463 := by
  unfold tailWord_3274432
  simp only [CollatzResearch.WordTrace]
  refine ⟨59714173236649783654128775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79618897648866378205505033 59714173236649783654128775)
  ·
    refine ⟨89571259854974675481193163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59714173236649783654128775 89571259854974675481193163)
    ·
      refine ⟨134356889782462013221789745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89571259854974675481193163 134356889782462013221789745)
      ·
        refine ⟨100767667336846509916342309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134356889782462013221789745 100767667336846509916342309)
        ·
          refine ⟨18893937625658720609314183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100767667336846509916342309 18893937625658720609314183)
          ·
            refine ⟨28340906438488080913971275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18893937625658720609314183 28340906438488080913971275)
            ·
              refine ⟨42511359657732121370956913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28340906438488080913971275 42511359657732121370956913)
              ·
                refine ⟨31883519743299091028217685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42511359657732121370956913 31883519743299091028217685)
                ·
                  refine ⟨186817498495893111493463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31883519743299091028217685 186817498495893111493463)
                  ·
                    rfl

theorem cell23_3274432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 9].length) (baseStart_3274432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274432 prefixEnd_3274432 := by exact prefixLift 3274432
  have htrace : WordTrace (prefixWord ++ tailWord_3274432) baseStart_3274432 baseEnd_3274432 := by
    simpa [prefixWord, tailWord_3274432, baseEnd_3274432] using wordTrace_append hprefix tailTrace_3274432
  have hstable : (prefixWord ++ tailWord_3274432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274432).length < 2 ^ (prefixWord ++ tailWord_3274432).sum := by decide
  have hdescent : baseEnd_3274432 < baseStart_3274432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274449 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 7]
def baseStart_3274449 : Nat := 118140960795 + 3274449 * 2 ^ 59
def prefixEnd_3274449 : Nat := 4983230072969 + 3 ^ 40 * 3274449 * 2
def baseEnd_3274449 : Nat := 186818468403796048547621

theorem tailTrace_3274449 : CollatzResearch.WordTrace tailWord_3274449 prefixEnd_3274449 186818468403796048547621 := by
  unfold tailWord_3274449
  simp only [CollatzResearch.WordTrace]
  refine ⟨119428966514237979211626401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79619311009491986141084267 119428966514237979211626401)
  ·
    refine ⟨89571724885678484408719801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119428966514237979211626401 89571724885678484408719801)
    ·
      refine ⟨67178793664258863306539851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89571724885678484408719801 67178793664258863306539851)
      ·
        refine ⟨100768190496388294959809777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67178793664258863306539851 100768190496388294959809777)
        ·
          refine ⟨75576142872291221219857333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100768190496388294959809777 75576142872291221219857333)
          ·
            refine ⟨7085263394277301989361625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75576142872291221219857333 7085263394277301989361625)
            ·
              refine ⟨5313947545707976492021219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7085263394277301989361625 5313947545707976492021219)
              ·
                refine ⟨7970921318561964738031829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5313947545707976492021219 7970921318561964738031829)
                ·
                  refine ⟨186818468403796048547621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7970921318561964738031829 186818468403796048547621)
                  ·
                    rfl

theorem cell23_3274449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 7].length) (baseStart_3274449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274449 prefixEnd_3274449 := by exact prefixLift 3274449
  have htrace : WordTrace (prefixWord ++ tailWord_3274449) baseStart_3274449 baseEnd_3274449 := by
    simpa [prefixWord, tailWord_3274449, baseEnd_3274449] using wordTrace_append hprefix tailTrace_3274449
  have hstable : (prefixWord ++ tailWord_3274449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274449).length < 2 ^ (prefixWord ++ tailWord_3274449).sum := by decide
  have hdescent : baseEnd_3274449 < baseStart_3274449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274454 : List Nat := [5, 2, 1, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_3274454 : Nat := 118140960795 + 3274454 * 2 ^ 59
def prefixEnd_3274454 : Nat := 4983230072969 + 3 ^ 40 * 3274454 * 2
def baseEnd_3274454 : Nat := 1681368783037436917366067

theorem tailTrace_3274454 : CollatzResearch.WordTrace tailWord_3274454 prefixEnd_3274454 1681368783037436917366067 := by
  unfold tailWord_3274454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7464321804951241566597401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79619432586146576710372277 7464321804951241566597401)
  ·
    refine ⟨5598241353713431174948051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7464321804951241566597401 5598241353713431174948051)
    ·
      refine ⟨8397362030570146762422077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5598241353713431174948051 8397362030570146762422077)
      ·
        refine ⟨3149010761463805035908279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8397362030570146762422077 3149010761463805035908279)
        ·
          refine ⟨4723516142195707553862419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149010761463805035908279 4723516142195707553862419)
          ·
            refine ⟨7085274213293561330793629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4723516142195707553862419 7085274213293561330793629)
            ·
              refine ⟨2656977829985085499047611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7085274213293561330793629 2656977829985085499047611)
              ·
                refine ⟨3985466744977628248571417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2656977829985085499047611 3985466744977628248571417)
                ·
                  refine ⟨2989100058733221186428563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3985466744977628248571417 2989100058733221186428563)
                  ·
                    refine ⟨4483650088099831779642845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2989100058733221186428563 4483650088099831779642845)
                    ·
                      refine ⟨1681368783037436917366067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4483650088099831779642845 1681368783037436917366067)
                      ·
                        rfl

theorem cell23_3274454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_3274454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274454 prefixEnd_3274454 := by exact prefixLift 3274454
  have htrace : WordTrace (prefixWord ++ tailWord_3274454) baseStart_3274454 baseEnd_3274454 := by
    simpa [prefixWord, tailWord_3274454, baseEnd_3274454] using wordTrace_append hprefix tailTrace_3274454
  have hstable : (prefixWord ++ tailWord_3274454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274454).length < 2 ^ (prefixWord ++ tailWord_3274454).sum := by decide
  have hdescent : baseEnd_3274454 < baseStart_3274454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274479 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 2, 5]
def baseStart_3274479 : Nat := 118140960795 + 3274479 * 2 ^ 59
def prefixEnd_3274479 : Nat := 4983230072969 + 3 ^ 40 * 3274479 * 2
def baseEnd_3274479 : Nat := 560460540017933106517817

theorem tailTrace_3274479 : CollatzResearch.WordTrace tailWord_3274479 prefixEnd_3274479 560460540017933106517817 := by
  unfold tailWord_3274479
  simp only [CollatzResearch.WordTrace]
  refine ⟨119430060704129294335218491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79620040469419529556812327 119430060704129294335218491)
  ·
    refine ⟨179145091056193941502827737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119430060704129294335218491 179145091056193941502827737)
    ·
      refine ⟨134358818292145456127120803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179145091056193941502827737 134358818292145456127120803)
      ·
        refine ⟨201538227438218184190681205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134358818292145456127120803 201538227438218184190681205)
        ·
          refine ⟨18894208822332954767876363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201538227438218184190681205 18894208822332954767876363)
          ·
            refine ⟨28341313233499432151814545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18894208822332954767876363 28341313233499432151814545)
            ·
              refine ⟨21255984925124574113860909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28341313233499432151814545 21255984925124574113860909)
              ·
                refine ⟨7970994346921715292697841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21255984925124574113860909 7970994346921715292697841)
                ·
                  refine ⟨5978245760191286469523381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7970994346921715292697841 5978245760191286469523381)
                  ·
                    refine ⟨560460540017933106517817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5978245760191286469523381 560460540017933106517817)
                    ·
                      rfl

theorem cell23_3274479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 5].length) (baseStart_3274479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274479 prefixEnd_3274479 := by exact prefixLift 3274479
  have htrace : WordTrace (prefixWord ++ tailWord_3274479) baseStart_3274479 baseEnd_3274479 := by
    simpa [prefixWord, tailWord_3274479, baseEnd_3274479] using wordTrace_append hprefix tailTrace_3274479
  have hstable : (prefixWord ++ tailWord_3274479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274479).length < 2 ^ (prefixWord ++ tailWord_3274479).sum := by decide
  have hdescent : baseEnd_3274479 < baseStart_3274479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274499 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 4]
def baseStart_3274499 : Nat := 118140960795 + 3274499 * 2 ^ 59
def prefixEnd_3274499 : Nat := 4983230072969 + 3 ^ 40 * 3274499 * 2
def baseEnd_3274499 : Nat := 1681391889666889241303359

theorem tailTrace_3274499 : CollatzResearch.WordTrace tailWord_3274499 prefixEnd_3274499 1681391889666889241303359 := by
  unfold tailWord_3274499
  simp only [CollatzResearch.WordTrace]
  refine ⟨119430790164056837750946551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79620526776037891833964367 119430790164056837750946551)
  ·
    refine ⟨179146185246085256626419827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119430790164056837750946551 179146185246085256626419827)
    ·
      refine ⟨268719277869127884939629741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179146185246085256626419827 268719277869127884939629741)
      ·
        refine ⟨100769729200922956852361153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268719277869127884939629741 100769729200922956852361153)
        ·
          refine ⟨75577296900692217639270865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100769729200922956852361153 75577296900692217639270865)
          ·
            refine ⟨56682972675519163229453149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75577296900692217639270865 56682972675519163229453149)
            ·
              refine ⟨21256114753319686211044931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56682972675519163229453149 21256114753319686211044931)
              ·
                refine ⟨31884172129979529316567397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21256114753319686211044931 31884172129979529316567397)
                ·
                  refine ⟨5978282274371161746856387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31884172129979529316567397 5978282274371161746856387)
                  ·
                    refine ⟨8967423411556742620284581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5978282274371161746856387 8967423411556742620284581)
                    ·
                      refine ⟨1681391889666889241303359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8967423411556742620284581 1681391889666889241303359)
                      ·
                        rfl

theorem cell23_3274499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_3274499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274499 prefixEnd_3274499 := by exact prefixLift 3274499
  have htrace : WordTrace (prefixWord ++ tailWord_3274499) baseStart_3274499 baseEnd_3274499 := by
    simpa [prefixWord, tailWord_3274499, baseEnd_3274499] using wordTrace_append hprefix tailTrace_3274499
  have hstable : (prefixWord ++ tailWord_3274499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274499).length < 2 ^ (prefixWord ++ tailWord_3274499).sum := by decide
  have hdescent : baseEnd_3274499 < baseStart_3274499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274569 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 5, 5]
def baseStart_3274569 : Nat := 118140960795 + 3274569 * 2 ^ 59
def prefixEnd_3274569 : Nat := 4983230072969 + 3 ^ 40 * 3274569 * 2
def baseEnd_3274569 : Nat := 560475944437567989142679

theorem tailTrace_3274569 : CollatzResearch.WordTrace tailWord_3274569 prefixEnd_3274569 560475944437567989142679 := by
  unfold tailWord_3274569
  simp only [CollatzResearch.WordTrace]
  refine ⟨119433343273803239705994761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79622228849202159803996507 119433343273803239705994761)
  ·
    refine ⟨89575007455352429779496071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119433343273803239705994761 89575007455352429779496071)
    ·
      refine ⟨134362511183028644669244107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89575007455352429779496071 134362511183028644669244107)
      ·
        refine ⟨201543766774542967003866161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134362511183028644669244107 201543766774542967003866161)
        ·
          refine ⟨151157825080907225252899621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201543766774542967003866161 151157825080907225252899621)
          ·
            refine ⟨28342092202670104734918679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151157825080907225252899621 28342092202670104734918679)
            ·
              refine ⟨42513138304005157102378019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28342092202670104734918679 42513138304005157102378019)
              ·
                refine ⟨63769707456007735653567029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42513138304005157102378019 63769707456007735653567029)
                ·
                  refine ⟨5978410074000725217521909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63769707456007735653567029 5978410074000725217521909)
                  ·
                    refine ⟨560475944437567989142679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5978410074000725217521909 560475944437567989142679)
                    ·
                      rfl

theorem cell23_3274569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 5].length) (baseStart_3274569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274569 prefixEnd_3274569 := by exact prefixLift 3274569
  have htrace : WordTrace (prefixWord ++ tailWord_3274569) baseStart_3274569 baseEnd_3274569 := by
    simpa [prefixWord, tailWord_3274569, baseEnd_3274569] using wordTrace_append hprefix tailTrace_3274569
  have hstable : (prefixWord ++ tailWord_3274569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274569).length < 2 ^ (prefixWord ++ tailWord_3274569).sum := by decide
  have hdescent : baseEnd_3274569 < baseStart_3274569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274573 : List Nat := [1, 6, 1, 2, 1, 1, 2, 3, 6]
def baseStart_3274573 : Nat := 118140960795 + 3274573 * 2 ^ 59
def prefixEnd_3274573 : Nat := 4983230072969 + 3 ^ 40 * 3274573 * 2
def baseEnd_3274573 : Nat := 186825543026146883530891

theorem tailTrace_3274573 : CollatzResearch.WordTrace tailWord_3274573 prefixEnd_3274573 186825543026146883530891 := by
  unfold tailWord_3274573
  simp only [CollatzResearch.WordTrace]
  refine ⟨119433489165788748389140373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79622326110525832259426915 119433489165788748389140373)
  ·
    refine ⟨5598444804646347580740955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119433489165788748389140373 5598444804646347580740955)
    ·
      refine ⟨8397667206969521371111433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5598444804646347580740955 8397667206969521371111433)
      ·
        refine ⟨6298250405227141028333575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8397667206969521371111433 6298250405227141028333575)
        ·
          refine ⟨9447375607840711542500363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6298250405227141028333575 9447375607840711542500363)
          ·
            refine ⟨14171063411761067313750545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9447375607840711542500363 14171063411761067313750545)
            ·
              refine ⟨10628297558820800485312909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14171063411761067313750545 10628297558820800485312909)
              ·
                refine ⟨3985611584557800181992341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10628297558820800485312909 3985611584557800181992341)
                ·
                  refine ⟨186825543026146883530891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3985611584557800181992341 186825543026146883530891)
                  ·
                    rfl

theorem cell23_3274573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_3274573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274573 prefixEnd_3274573 := by exact prefixLift 3274573
  have htrace : WordTrace (prefixWord ++ tailWord_3274573) baseStart_3274573 baseEnd_3274573 := by
    simpa [prefixWord, tailWord_3274573, baseEnd_3274573] using wordTrace_append hprefix tailTrace_3274573
  have hstable : (prefixWord ++ tailWord_3274573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274573).length < 2 ^ (prefixWord ++ tailWord_3274573).sum := by decide
  have hdescent : baseEnd_3274573 < baseStart_3274573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274576 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 1, 5, 2]
def baseStart_3274576 : Nat := 118140960795 + 3274576 * 2 ^ 59
def prefixEnd_3274576 : Nat := 4983230072969 + 3 ^ 40 * 3274576 * 2
def baseEnd_3274576 : Nat := 1681431427677285440040505

theorem tailTrace_3274576 : CollatzResearch.WordTrace tailWord_3274576 prefixEnd_3274576 1681431427677285440040505 := by
  unfold tailWord_3274576
  simp only [CollatzResearch.WordTrace]
  refine ⟨59716799292388939950749791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79622399056518586600999721 59716799292388939950749791)
  ·
    refine ⟨89575198938583409926124687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59716799292388939950749791 89575198938583409926124687)
    ·
      refine ⟨134362798407875114889187031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89575198938583409926124687 134362798407875114889187031)
      ·
        refine ⟨201544197611812672333780547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134362798407875114889187031 201544197611812672333780547)
        ·
          refine ⟨302316296417719008500670821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201544197611812672333780547 302316296417719008500670821)
          ·
            refine ⟨56684305578322314093875779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302316296417719008500670821 56684305578322314093875779)
            ·
              refine ⟨85026458367483471140813669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56684305578322314093875779 85026458367483471140813669)
              ·
                refine ⟨15942460943903150838902563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85026458367483471140813669 15942460943903150838902563)
                ·
                  refine ⟨23913691415854726258353845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15942460943903150838902563 23913691415854726258353845)
                  ·
                    refine ⟨2241908570236380586720673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23913691415854726258353845 2241908570236380586720673)
                    ·
                      refine ⟨1681431427677285440040505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2241908570236380586720673 1681431427677285440040505)
                      ·
                        rfl

theorem cell23_3274576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 5, 2].length) (baseStart_3274576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274576 prefixEnd_3274576 := by exact prefixLift 3274576
  have htrace : WordTrace (prefixWord ++ tailWord_3274576) baseStart_3274576 baseEnd_3274576 := by
    simpa [prefixWord, tailWord_3274576, baseEnd_3274576] using wordTrace_append hprefix tailTrace_3274576
  have hstable : (prefixWord ++ tailWord_3274576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274576).length < 2 ^ (prefixWord ++ tailWord_3274576).sum := by decide
  have hdescent : baseEnd_3274576 < baseStart_3274576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274586 : List Nat := [3, 1, 1, 2, 1, 3, 2, 4, 1, 5]
def baseStart_3274586 : Nat := 118140960795 + 3274586 * 2 ^ 59
def prefixEnd_3274586 : Nat := 4983230072969 + 3 ^ 40 * 3274586 * 2
def baseEnd_3274586 : Nat := 560478854161276800305153

theorem tailTrace_3274586 : CollatzResearch.WordTrace tailWord_3274586 prefixEnd_3274586 560478854161276800305153 := by
  unfold tailWord_3274586
  simp only [CollatzResearch.WordTrace]
  refine ⟨29858490828685412902340903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79622642209827767739575741 29858490828685412902340903)
  ·
    refine ⟨44787736243028119353511355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29858490828685412902340903 44787736243028119353511355)
    ·
      refine ⟨67181604364542179030267033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44787736243028119353511355 67181604364542179030267033)
      ·
        refine ⟨50386203273406634272700275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67181604364542179030267033 50386203273406634272700275)
        ·
          refine ⟨75579304910109951409050413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50386203273406634272700275 75579304910109951409050413)
          ·
            refine ⟨28342239341291231778393905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75579304910109951409050413 28342239341291231778393905)
            ·
              refine ⟨21256679505968423833795429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28342239341291231778393905 21256679505968423833795429)
              ·
                refine ⟨3985627407369079468836643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21256679505968423833795429 3985627407369079468836643)
                ·
                  refine ⟨5978441111053619203254965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3985627407369079468836643 5978441111053619203254965)
                  ·
                    refine ⟨560478854161276800305153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5978441111053619203254965 560478854161276800305153)
                    ·
                      rfl

theorem cell23_3274586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_3274586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274586 prefixEnd_3274586 := by exact prefixLift 3274586
  have htrace : WordTrace (prefixWord ++ tailWord_3274586) baseStart_3274586 baseEnd_3274586 := by
    simpa [prefixWord, tailWord_3274586, baseEnd_3274586] using wordTrace_append hprefix tailTrace_3274586
  have hstable : (prefixWord ++ tailWord_3274586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274586).length < 2 ^ (prefixWord ++ tailWord_3274586).sum := by decide
  have hdescent : baseEnd_3274586 < baseStart_3274586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274619 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 6]
def baseStart_3274619 : Nat := 118140960795 + 3274619 * 2 ^ 59
def prefixEnd_3274619 : Nat := 4983230072969 + 3 ^ 40 * 3274619 * 2
def baseEnd_3274619 : Nat := 1681453507345428771802807

theorem tailTrace_3274619 : CollatzResearch.WordTrace tailWord_3274619 prefixEnd_3274619 1681453507345428771802807 := by
  unfold tailWord_3274619
  simp only [CollatzResearch.WordTrace]
  refine ⟨119435166923622098245314911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79623444615748065496876607 119435166923622098245314911)
  ·
    refine ⟨179152750385433147367972367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119435166923622098245314911 179152750385433147367972367)
    ·
      refine ⟨268729125578149721051958551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179152750385433147367972367 268729125578149721051958551)
      ·
        refine ⟨403093688367224581577937827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268729125578149721051958551 403093688367224581577937827)
        ·
          refine ⟨604640532550836872366906741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403093688367224581577937827 604640532550836872366906741)
          ·
            refine ⟨56685049926640956784397507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 604640532550836872366906741 56685049926640956784397507)
            ·
              refine ⟨85027574889961435176596261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56685049926640956784397507 85027574889961435176596261)
              ·
                refine ⟨15942670291867769095611799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85027574889961435176596261 15942670291867769095611799)
                ·
                  refine ⟨23914005437801653643417699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15942670291867769095611799 23914005437801653643417699)
                  ·
                    refine ⟨35871008156702480465126549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23914005437801653643417699 35871008156702480465126549)
                    ·
                      refine ⟨1681453507345428771802807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35871008156702480465126549 1681453507345428771802807)
                      ·
                        rfl

theorem cell23_3274619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 6].length) (baseStart_3274619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274619 prefixEnd_3274619 := by exact prefixLift 3274619
  have htrace : WordTrace (prefixWord ++ tailWord_3274619) baseStart_3274619 baseEnd_3274619 := by
    simpa [prefixWord, tailWord_3274619, baseEnd_3274619] using wordTrace_append hprefix tailTrace_3274619
  have hstable : (prefixWord ++ tailWord_3274619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274619).length < 2 ^ (prefixWord ++ tailWord_3274619).sum := by decide
  have hdescent : baseEnd_3274619 < baseStart_3274619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274629 : List Nat := [1, 3, 1, 1, 3, 2, 2, 10]
def baseStart_3274629 : Nat := 118140960795 + 3274629 * 2 ^ 59
def prefixEnd_3274629 : Nat := 4983230072969 + 3 ^ 40 * 3274629 * 2
def baseEnd_3274629 : Nat := 62276246005628656765843

theorem tailTrace_3274629 : CollatzResearch.WordTrace tailWord_3274629 prefixEnd_3274629 62276246005628656765843 := by
  unfold tailWord_3274629
  simp only [CollatzResearch.WordTrace]
  refine ⟨119435531653585869953178941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79623687769057246635452627 119435531653585869953178941)
  ·
    refine ⟨44788324370094701232442103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119435531653585869953178941 44788324370094701232442103)
    ·
      refine ⟨67182486555142051848663155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44788324370094701232442103 67182486555142051848663155)
      ·
        refine ⟨100773729832713077772994733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67182486555142051848663155 100773729832713077772994733)
        ·
          refine ⟨37790148687267404164873025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100773729832713077772994733 37790148687267404164873025)
          ·
            refine ⟨28342611515450553123654769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37790148687267404164873025 28342611515450553123654769)
            ·
              refine ⟨21256958636587914842741077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28342611515450553123654769 21256958636587914842741077)
              ·
                refine ⟨62276246005628656765843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21256958636587914842741077 62276246005628656765843)
                ·
                  rfl

theorem cell23_3274629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 10].length) (baseStart_3274629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274629 prefixEnd_3274629 := by exact prefixLift 3274629
  have htrace : WordTrace (prefixWord ++ tailWord_3274629) baseStart_3274629 baseEnd_3274629 := by
    simpa [prefixWord, tailWord_3274629, baseEnd_3274629] using wordTrace_append hprefix tailTrace_3274629
  have hstable : (prefixWord ++ tailWord_3274629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274629).length < 2 ^ (prefixWord ++ tailWord_3274629).sum := by decide
  have hdescent : baseEnd_3274629 < baseStart_3274629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274656 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 3]
def baseStart_3274656 : Nat := 118140960795 + 3274656 * 2 ^ 59
def prefixEnd_3274656 : Nat := 4983230072969 + 3 ^ 40 * 3274656 * 2
def baseEnd_3274656 : Nat := 1681472506129645127040137

theorem tailTrace_3274656 : CollatzResearch.WordTrace tailWord_3274656 prefixEnd_3274656 1681472506129645127040137 := by
  unfold tailWord_3274656
  simp only [CollatzResearch.WordTrace]
  refine ⟨59718258212244026782205911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79624344282992035709607881 59718258212244026782205911)
  ·
    refine ⟨89577387318366040173308867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59718258212244026782205911 89577387318366040173308867)
    ·
      refine ⟨134366080977549060259963301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89577387318366040173308867 134366080977549060259963301)
      ·
        refine ⟨25193640183290448798743119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134366080977549060259963301 25193640183290448798743119)
        ·
          refine ⟨37790460274935673198114679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25193640183290448798743119 37790460274935673198114679)
          ·
            refine ⟨56685690412403509797172019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37790460274935673198114679 56685690412403509797172019)
            ·
              refine ⟨85028535618605264695758029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56685690412403509797172019 85028535618605264695758029)
              ·
                refine ⟨31885700856976974260909261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85028535618605264695758029 31885700856976974260909261)
                ·
                  refine ⟨11957137821366365347840973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31885700856976974260909261 11957137821366365347840973)
                  ·
                    refine ⟨4483926683012387005440365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11957137821366365347840973 4483926683012387005440365)
                    ·
                      refine ⟨1681472506129645127040137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4483926683012387005440365 1681472506129645127040137)
                      ·
                        rfl

theorem cell23_3274656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_3274656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274656 prefixEnd_3274656 := by exact prefixLift 3274656
  have htrace : WordTrace (prefixWord ++ tailWord_3274656) baseStart_3274656 baseEnd_3274656 := by
    simpa [prefixWord, tailWord_3274656, baseEnd_3274656] using wordTrace_append hprefix tailTrace_3274656
  have hstable : (prefixWord ++ tailWord_3274656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274656).length < 2 ^ (prefixWord ++ tailWord_3274656).sum := by decide
  have hdescent : baseEnd_3274656 < baseStart_3274656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274659 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 1, 9]
def baseStart_3274659 : Nat := 118140960795 + 3274659 * 2 ^ 59
def prefixEnd_3274659 : Nat := 4983230072969 + 3 ^ 40 * 3274659 * 2
def baseEnd_3274659 : Nat := 560491348857202871767541

theorem tailTrace_3274659 : CollatzResearch.WordTrace tailWord_3274659 prefixEnd_3274659 560491348857202871767541 := by
  unfold tailWord_3274659
  simp only [CollatzResearch.WordTrace]
  refine ⟨119436625843477185076771031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79624417228984790051180687 119436625843477185076771031)
  ·
    refine ⟨179154938765215777615156547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119436625843477185076771031 179154938765215777615156547)
    ·
      refine ⟨268732408147823666422734821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179154938765215777615156547 268732408147823666422734821)
      ·
        refine ⟨50387326527716937454262779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268732408147823666422734821 50387326527716937454262779)
        ·
          refine ⟨75580989791575406181394169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50387326527716937454262779 75580989791575406181394169)
          ·
            refine ⟨56685742343681554636045627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75580989791575406181394169 56685742343681554636045627)
            ·
              refine ⟨85028613515522331954068441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56685742343681554636045627 85028613515522331954068441)
              ·
                refine ⟨63771460136641748965551331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85028613515522331954068441 63771460136641748965551331)
                ·
                  refine ⟨95657190204962623448326997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63771460136641748965551331 95657190204962623448326997)
                  ·
                    refine ⟨560491348857202871767541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 95657190204962623448326997 560491348857202871767541)
                    ·
                      rfl

theorem cell23_3274659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 9].length) (baseStart_3274659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274659 prefixEnd_3274659 := by exact prefixLift 3274659
  have htrace : WordTrace (prefixWord ++ tailWord_3274659) baseStart_3274659 baseEnd_3274659 := by
    simpa [prefixWord, tailWord_3274659, baseEnd_3274659] using wordTrace_append hprefix tailTrace_3274659
  have hstable : (prefixWord ++ tailWord_3274659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274659).length < 2 ^ (prefixWord ++ tailWord_3274659).sum := by decide
  have hdescent : baseEnd_3274659 < baseStart_3274659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274684 : List Nat := [2, 2, 2, 5, 1, 2, 2, 1, 2, 4]
def baseStart_3274684 : Nat := 118140960795 + 3274684 * 2 ^ 59
def prefixEnd_3274684 : Nat := 4983230072969 + 3 ^ 40 * 3274684 * 2
def baseEnd_3274684 : Nat := 560495627862657005830003

theorem tailTrace_3274684 : CollatzResearch.WordTrace tailWord_3274684 prefixEnd_3274684 560495627862657005830003 := by
  unfold tailWord_3274684
  simp only [CollatzResearch.WordTrace]
  refine ⟨59718768834193307173215553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79625025112257742897620737 59718768834193307173215553)
  ·
    refine ⟨44789076625644980379911665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59718768834193307173215553 44789076625644980379911665)
    ·
      refine ⟨33591807469233735284933749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44789076625644980379911665 33591807469233735284933749)
      ·
        refine ⟨3149231950240662682962539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33591807469233735284933749 3149231950240662682962539)
        ·
          refine ⟨4723847925360994024443809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149231950240662682962539 4723847925360994024443809)
          ·
            refine ⟨3542885944020745518332857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4723847925360994024443809 3542885944020745518332857)
            ·
              refine ⟨2657164458015559138749643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3542885944020745518332857 2657164458015559138749643)
              ·
                refine ⟨3985746687023338708124465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657164458015559138749643 3985746687023338708124465)
                ·
                  refine ⟨2989310015267504031093349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3985746687023338708124465 2989310015267504031093349)
                  ·
                    refine ⟨560495627862657005830003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2989310015267504031093349 560495627862657005830003)
                    ·
                      rfl

theorem cell23_3274684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_3274684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274684 prefixEnd_3274684 := by exact prefixLift 3274684
  have htrace : WordTrace (prefixWord ++ tailWord_3274684) baseStart_3274684 baseEnd_3274684 := by
    simpa [prefixWord, tailWord_3274684, baseEnd_3274684] using wordTrace_append hprefix tailTrace_3274684
  have hstable : (prefixWord ++ tailWord_3274684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274684).length < 2 ^ (prefixWord ++ tailWord_3274684).sum := by decide
  have hdescent : baseEnd_3274684 < baseStart_3274684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274700 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 3, 3, 2]
def baseStart_3274700 : Nat := 118140960795 + 3274700 * 2 ^ 59
def prefixEnd_3274700 : Nat := 4983230072969 + 3 ^ 40 * 3274700 * 2
def baseEnd_3274700 : Nat := 1681495099278442954889935

theorem tailTrace_3274700 : CollatzResearch.WordTrace tailWord_3274700 prefixEnd_3274700 1681495099278442954889935 := by
  unfold tailWord_3274700
  simp only [CollatzResearch.WordTrace]
  refine ⟨59719060618164324539506777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79625414157552432719342369 59719060618164324539506777)
  ·
    refine ⟨44789295463623243404630083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59719060618164324539506777 44789295463623243404630083)
    ·
      refine ⟨67183943195434865106945125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44789295463623243404630083 67183943195434865106945125)
      ·
        refine ⟨12596989349144037207552211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67183943195434865106945125 12596989349144037207552211)
        ·
          refine ⟨18895484023716055811328317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12596989349144037207552211 18895484023716055811328317)
          ·
            refine ⟨7085806508893520929248119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18895484023716055811328317 7085806508893520929248119)
            ·
              refine ⟨10628709763340281393872179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7085806508893520929248119 10628709763340281393872179)
              ·
                refine ⟨15943064645010422090808269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10628709763340281393872179 15943064645010422090808269)
                ·
                  refine ⟨5978649241878908284053101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15943064645010422090808269 5978649241878908284053101)
                  ·
                    refine ⟨2241993465704590606519913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5978649241878908284053101 2241993465704590606519913)
                    ·
                      refine ⟨1681495099278442954889935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2241993465704590606519913 1681495099278442954889935)
                      ·
                        rfl

theorem cell23_3274700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_3274700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274700 prefixEnd_3274700 := by exact prefixLift 3274700
  have htrace : WordTrace (prefixWord ++ tailWord_3274700) baseStart_3274700 baseEnd_3274700 := by
    simpa [prefixWord, tailWord_3274700, baseEnd_3274700] using wordTrace_append hprefix tailTrace_3274700
  have hstable : (prefixWord ++ tailWord_3274700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274700).length < 2 ^ (prefixWord ++ tailWord_3274700).sum := by decide
  have hdescent : baseEnd_3274700 < baseStart_3274700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274823 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_3274823 : Nat := 118140960795 + 3274823 * 2 ^ 59
def prefixEnd_3274823 : Nat := 4983230072969 + 3 ^ 40 * 3274823 * 2
def baseEnd_3274823 : Nat := 1681558257398945973651869

theorem tailTrace_3274823 : CollatzResearch.WordTrace tailWord_3274823 prefixEnd_3274823 1681558257398945973651869 := by
  unfold tailWord_3274823
  simp only [CollatzResearch.WordTrace]
  refine ⟨119442607414883041085741123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79628404943255360723827415 119442607414883041085741123)
  ·
    refine ⟨179163911122324561628611685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119442607414883041085741123 179163911122324561628611685)
    ·
      refine ⟨33593233335435855305364691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179163911122324561628611685 33593233335435855305364691)
      ·
        refine ⟨50389850003153782958047037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33593233335435855305364691 50389850003153782958047037)
        ·
          refine ⟨18896193751182668609267639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50389850003153782958047037 18896193751182668609267639)
          ·
            refine ⟨28344290626774002913901459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18896193751182668609267639 28344290626774002913901459)
            ·
              refine ⟨42516435940161004370852189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28344290626774002913901459 42516435940161004370852189)
              ·
                refine ⟨15943663477560376639069571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42516435940161004370852189 15943663477560376639069571)
                ·
                  refine ⟨23915495216340564958604357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15943663477560376639069571 23915495216340564958604357)
                  ·
                    refine ⟨4484155353063855929738317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23915495216340564958604357 4484155353063855929738317)
                    ·
                      refine ⟨1681558257398945973651869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4484155353063855929738317 1681558257398945973651869)
                      ·
                        rfl

theorem cell23_3274823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_3274823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274823 prefixEnd_3274823 := by exact prefixLift 3274823
  have htrace : WordTrace (prefixWord ++ tailWord_3274823) baseStart_3274823 baseEnd_3274823 := by
    simpa [prefixWord, tailWord_3274823, baseEnd_3274823] using wordTrace_append hprefix tailTrace_3274823
  have hstable : (prefixWord ++ tailWord_3274823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274823).length < 2 ^ (prefixWord ++ tailWord_3274823).sum := by decide
  have hdescent : baseEnd_3274823 < baseStart_3274823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274840 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 2, 2, 3]
def baseStart_3274840 : Nat := 118140960795 + 3274840 * 2 ^ 59
def prefixEnd_3274840 : Nat := 4983230072969 + 3 ^ 40 * 3274840 * 2
def baseEnd_3274840 : Nat := 1681566986570072407139291

theorem tailTrace_3274840 : CollatzResearch.WordTrace tailWord_3274840 prefixEnd_3274840 1681566986570072407139291 := by
  unfold tailWord_3274840
  simp only [CollatzResearch.WordTrace]
  refine ⟨59721613727910726494554987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79628818303880968659406649 59721613727910726494554987)
  ·
    refine ⟨89582420591866089741832481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59721613727910726494554987 89582420591866089741832481)
    ·
      refine ⟨67186815443899567306374361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89582420591866089741832481 67186815443899567306374361)
      ·
        refine ⟨50390111582924675479780771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67186815443899567306374361 50390111582924675479780771)
        ·
          refine ⟨75585167374387013219671157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50390111582924675479780771 75585167374387013219671157)
          ·
            refine ⟨7086109441348782489344171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75585167374387013219671157 7086109441348782489344171)
            ·
              refine ⟨10629164162023173734016257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7086109441348782489344171 10629164162023173734016257)
              ·
                refine ⟨7971873121517380300512193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10629164162023173734016257 7971873121517380300512193)
                ·
                  refine ⟨5978904841138035225384145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7971873121517380300512193 5978904841138035225384145)
                  ·
                    refine ⟨4484178630853526419038109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5978904841138035225384145 4484178630853526419038109)
                    ·
                      refine ⟨1681566986570072407139291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4484178630853526419038109 1681566986570072407139291)
                      ·
                        rfl

theorem cell23_3274840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_3274840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274840 prefixEnd_3274840 := by exact prefixLift 3274840
  have htrace : WordTrace (prefixWord ++ tailWord_3274840) baseStart_3274840 baseEnd_3274840 := by
    simpa [prefixWord, tailWord_3274840, baseEnd_3274840] using wordTrace_append hprefix tailTrace_3274840
  have hstable : (prefixWord ++ tailWord_3274840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274840).length < 2 ^ (prefixWord ++ tailWord_3274840).sum := by decide
  have hdescent : baseEnd_3274840 < baseStart_3274840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274860 : List Nat := [2, 2, 1, 1, 3, 3, 4, 1, 6]
def baseStart_3274860 : Nat := 118140960795 + 3274860 * 2 ^ 59
def prefixEnd_3274860 : Nat := 4983230072969 + 3 ^ 40 * 3274860 * 2
def baseEnd_3274860 : Nat := 186841917353684703209911

theorem tailTrace_3274860 : CollatzResearch.WordTrace tailWord_3274860 prefixEnd_3274860 186841917353684703209911 := by
  unfold tailWord_3274860
  simp only [CollatzResearch.WordTrace]
  refine ⟨59721978457874498202419017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79629304610499330936558689 59721978457874498202419017)
  ·
    refine ⟨44791483843405873651814263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59721978457874498202419017 44791483843405873651814263)
    ·
      refine ⟨67187225765108810477721395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44791483843405873651814263 67187225765108810477721395)
      ·
        refine ⟨100780838647663215716582093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67187225765108810477721395 100780838647663215716582093)
        ·
          refine ⟨37792814492873705893718285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100780838647663215716582093 37792814492873705893718285)
          ·
            refine ⟨14172305434827639710144357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37792814492873705893718285 14172305434827639710144357)
            ·
              refine ⟨2657307269030182445652067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14172305434827639710144357 2657307269030182445652067)
              ·
                refine ⟨3985960903545273668478101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657307269030182445652067 3985960903545273668478101)
                ·
                  refine ⟨186841917353684703209911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3985960903545273668478101 186841917353684703209911)
                  ·
                    rfl

theorem cell23_3274860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 6].length) (baseStart_3274860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274860 prefixEnd_3274860 := by exact prefixLift 3274860
  have htrace : WordTrace (prefixWord ++ tailWord_3274860) baseStart_3274860 baseEnd_3274860 := by
    simpa [prefixWord, tailWord_3274860, baseEnd_3274860] using wordTrace_append hprefix tailTrace_3274860
  have hstable : (prefixWord ++ tailWord_3274860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274860).length < 2 ^ (prefixWord ++ tailWord_3274860).sum := by decide
  have hdescent : baseEnd_3274860 < baseStart_3274860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274930 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_3274930 : Nat := 118140960795 + 3274930 * 2 ^ 59
def prefixEnd_3274930 : Nat := 4983230072969 + 3 ^ 40 * 3274930 * 2
def baseEnd_3274930 : Nat := 1681613199828977055013877

theorem tailTrace_3274930 : CollatzResearch.WordTrace tailWord_3274930 prefixEnd_3274930 1681613199828977055013877 := by
  unfold tailWord_3274930
  simp only [CollatzResearch.WordTrace]
  refine ⟨29861627506373849589971561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79631006683663598906590829 29861627506373849589971561)
  ·
    refine ⟨22396220629780387192478671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29861627506373849589971561 22396220629780387192478671)
    ·
      refine ⟨33594330944670580788718007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22396220629780387192478671 33594330944670580788718007)
      ·
        refine ⟨50391496417005871183077011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33594330944670580788718007 50391496417005871183077011)
        ·
          refine ⟨75587244625508806774615517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50391496417005871183077011 75587244625508806774615517)
          ·
            refine ⟨28345216734565802540480819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75587244625508806774615517 28345216734565802540480819)
            ·
              refine ⟨42517825101848703810721229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28345216734565802540480819 42517825101848703810721229)
              ·
                refine ⟨15944184413193263929020461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42517825101848703810721229 15944184413193263929020461)
                ·
                  refine ⟨5979069154947473973382673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15944184413193263929020461 5979069154947473973382673)
                  ·
                    refine ⟨4484301866210605480037005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5979069154947473973382673 4484301866210605480037005)
                    ·
                      refine ⟨1681613199828977055013877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4484301866210605480037005 1681613199828977055013877)
                      ·
                        rfl

theorem cell23_3274930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_3274930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274930 prefixEnd_3274930 := by exact prefixLift 3274930
  have htrace : WordTrace (prefixWord ++ tailWord_3274930) baseStart_3274930 baseEnd_3274930 := by
    simpa [prefixWord, tailWord_3274930, baseEnd_3274930] using wordTrace_append hprefix tailTrace_3274930
  have hstable : (prefixWord ++ tailWord_3274930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274930).length < 2 ^ (prefixWord ++ tailWord_3274930).sum := by decide
  have hdescent : baseEnd_3274930 < baseStart_3274930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274944 : List Nat := [2, 1, 1, 2, 5, 3, 2, 1, 1, 1, 4]
def baseStart_3274944 : Nat := 118140960795 + 3274944 * 2 ^ 59
def prefixEnd_3274944 : Nat := 4983230072969 + 3 ^ 40 * 3274944 * 2
def baseEnd_3274944 : Nat := 1681620388558140000238813

theorem tailTrace_3274944 : CollatzResearch.WordTrace tailWord_3274944 prefixEnd_3274944 1681620388558140000238813 := by
  unfold tailWord_3274944
  simp only [CollatzResearch.WordTrace]
  refine ⟨59723510323722339375447943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79631347098296452500597257 59723510323722339375447943)
  ·
    refine ⟨89585265485583509063171915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59723510323722339375447943 89585265485583509063171915)
    ·
      refine ⟨134377898228375263594757873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89585265485583509063171915 134377898228375263594757873)
      ·
        refine ⟨100783423671281447696068405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134377898228375263594757873 100783423671281447696068405)
        ·
          refine ⟨9448445969182635721506413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100783423671281447696068405 9448445969182635721506413)
          ·
            refine ⟨3543167238443488395564905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9448445969182635721506413 3543167238443488395564905)
            ·
              refine ⟨2657375428832616296673679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3543167238443488395564905 2657375428832616296673679)
              ·
                refine ⟨3986063143248924445010519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657375428832616296673679 3986063143248924445010519)
                ·
                  refine ⟨5979094714873386667515779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986063143248924445010519 5979094714873386667515779)
                  ·
                    refine ⟨8968642072310080001273669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5979094714873386667515779 8968642072310080001273669)
                    ·
                      refine ⟨1681620388558140000238813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8968642072310080001273669 1681620388558140000238813)
                      ·
                        rfl

theorem cell23_3274944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 1, 1, 4].length) (baseStart_3274944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274944 prefixEnd_3274944 := by exact prefixLift 3274944
  have htrace : WordTrace (prefixWord ++ tailWord_3274944) baseStart_3274944 baseEnd_3274944 := by
    simpa [prefixWord, tailWord_3274944, baseEnd_3274944] using wordTrace_append hprefix tailTrace_3274944
  have hstable : (prefixWord ++ tailWord_3274944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274944).length < 2 ^ (prefixWord ++ tailWord_3274944).sum := by decide
  have hdescent : baseEnd_3274944 < baseStart_3274944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274978 : List Nat := [3, 3, 4, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3274978 : Nat := 118140960795 + 3274978 * 2 ^ 59
def prefixEnd_3274978 : Nat := 4983230072969 + 3 ^ 40 * 3274978 * 2
def baseEnd_3274978 : Nat := 1681637846900392867213657

theorem tailTrace_3274978 : CollatzResearch.WordTrace tailWord_3274978 prefixEnd_3274978 1681637846900392867213657 := by
  unfold tailWord_3274978
  simp only [CollatzResearch.WordTrace]
  refine ⟨29862065182330375639408397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79632173819547668371755725 29862065182330375639408397)
  ·
    refine ⟨11198274443373890864778149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29862065182330375639408397 11198274443373890864778149)
    ·
      refine ⟨2099676458132604537145903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11198274443373890864778149 2099676458132604537145903)
      ·
        refine ⟨3149514687198906805718855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2099676458132604537145903 3149514687198906805718855)
        ·
          refine ⟨4724272030798360208578283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149514687198906805718855 4724272030798360208578283)
          ·
            refine ⟨7086408046197540312867425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4724272030798360208578283 7086408046197540312867425)
            ·
              refine ⟨5314806034648155234650569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7086408046197540312867425 5314806034648155234650569)
              ·
                refine ⟨3986104525986116425987927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5314806034648155234650569 3986104525986116425987927)
                ·
                  refine ⟨5979156788979174638981891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986104525986116425987927 5979156788979174638981891)
                  ·
                    refine ⟨8968735183468761958472837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5979156788979174638981891 8968735183468761958472837)
                    ·
                      refine ⟨1681637846900392867213657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8968735183468761958472837 1681637846900392867213657)
                      ·
                        rfl

theorem cell23_3274978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3274978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274978 prefixEnd_3274978 := by exact prefixLift 3274978
  have htrace : WordTrace (prefixWord ++ tailWord_3274978) baseStart_3274978 baseEnd_3274978 := by
    simpa [prefixWord, tailWord_3274978, baseEnd_3274978] using wordTrace_append hprefix tailTrace_3274978
  have hstable : (prefixWord ++ tailWord_3274978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274978).length < 2 ^ (prefixWord ++ tailWord_3274978).sum := by decide
  have hdescent : baseEnd_3274978 < baseStart_3274978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3274993 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 1, 8]
def baseStart_3274993 : Nat := 118140960795 + 3274993 * 2 ^ 59
def prefixEnd_3274993 : Nat := 4983230072969 + 3 ^ 40 * 3274993 * 2
def baseEnd_3274993 : Nat := 560548516370070102842029

theorem tailTrace_3274993 : CollatzResearch.WordTrace tailWord_3274993 prefixEnd_3274993 560548516370070102842029 := by
  unfold tailWord_3274993
  simp only [CollatzResearch.WordTrace]
  refine ⟨119448807824267160119429633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79632538549511440079619755 119448807824267160119429633)
  ·
    refine ⟨89586605868200370089572225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119448807824267160119429633 89586605868200370089572225)
    ·
      refine ⟨67189954401150277567179169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89586605868200370089572225 67189954401150277567179169)
      ·
        refine ⟨50392465800862708175384377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67189954401150277567179169 50392465800862708175384377)
        ·
          refine ⟨37794349350647031131538283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50392465800862708175384377 37794349350647031131538283)
          ·
            refine ⟨56691524025970546697307425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37794349350647031131538283 56691524025970546697307425)
            ·
              refine ⟨42518643019477910022980569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56691524025970546697307425 42518643019477910022980569)
              ·
                refine ⟨31888982264608432517235427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42518643019477910022980569 31888982264608432517235427)
                ·
                  refine ⟨47833473396912648775853141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31888982264608432517235427 47833473396912648775853141)
                  ·
                    refine ⟨560548516370070102842029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47833473396912648775853141 560548516370070102842029)
                    ·
                      rfl

theorem cell23_3274993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_3274993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3274993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3274993 prefixEnd_3274993 := by exact prefixLift 3274993
  have htrace : WordTrace (prefixWord ++ tailWord_3274993) baseStart_3274993 baseEnd_3274993 := by
    simpa [prefixWord, tailWord_3274993, baseEnd_3274993] using wordTrace_append hprefix tailTrace_3274993
  have hstable : (prefixWord ++ tailWord_3274993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3274993).length < 2 ^ (prefixWord ++ tailWord_3274993).sum := by decide
  have hdescent : baseEnd_3274993 < baseStart_3274993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3274993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275004 : List Nat := [2, 2, 2, 1, 4, 1, 2, 3, 1, 3, 2]
def baseStart_3275004 : Nat := 118140960795 + 3275004 * 2 ^ 59
def prefixEnd_3275004 : Nat := 4983230072969 + 3 ^ 40 * 3275004 * 2
def baseEnd_3275004 : Nat := 1681651197397409765488537

theorem tailTrace_3275004 : CollatzResearch.WordTrace tailWord_3275004 prefixEnd_3275004 1681651197397409765488537 := by
  unfold tailWord_3275004
  simp only [CollatzResearch.WordTrace]
  refine ⟨59724604513613654499040033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79632806018151539332053377 59724604513613654499040033)
  ·
    refine ⟨44793453385210240874280025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59724604513613654499040033 44793453385210240874280025)
    ·
      refine ⟨33595090038907680655710019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44793453385210240874280025 33595090038907680655710019)
      ·
        refine ⟨50392635058361520983565029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33595090038907680655710019 50392635058361520983565029)
        ·
          refine ⟨9448619073442785184418443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50392635058361520983565029 9448619073442785184418443)
          ·
            refine ⟨14172928610164177776627665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9448619073442785184418443 14172928610164177776627665)
            ·
              refine ⟨10629696457623133332470749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14172928610164177776627665 10629696457623133332470749)
              ·
                refine ⟨3986136171608674999676531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10629696457623133332470749 3986136171608674999676531)
                ·
                  refine ⟨5979204257413012499514797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986136171608674999676531 5979204257413012499514797)
                  ·
                    refine ⟨2242201596529879687318049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5979204257413012499514797 2242201596529879687318049)
                    ·
                      refine ⟨1681651197397409765488537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2242201596529879687318049 1681651197397409765488537)
                      ·
                        rfl

theorem cell23_3275004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_3275004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275004 prefixEnd_3275004 := by exact prefixLift 3275004
  have htrace : WordTrace (prefixWord ++ tailWord_3275004) baseStart_3275004 baseEnd_3275004 := by
    simpa [prefixWord, tailWord_3275004, baseEnd_3275004] using wordTrace_append hprefix tailTrace_3275004
  have hstable : (prefixWord ++ tailWord_3275004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275004).length < 2 ^ (prefixWord ++ tailWord_3275004).sum := by decide
  have hdescent : baseEnd_3275004 < baseStart_3275004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275013 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_3275013 : Nat := 118140960795 + 3275013 * 2 ^ 59
def prefixEnd_3275013 : Nat := 4983230072969 + 3 ^ 40 * 3275013 * 2
def baseEnd_3275013 : Nat := 1681655818723300230275995

theorem tailTrace_3275013 : CollatzResearch.WordTrace tailWord_3275013 prefixEnd_3275013 1681655818723300230275995 := by
  unfold tailWord_3275013
  simp only [CollatzResearch.WordTrace]
  refine ⟨119449537284194703535157693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79633024856129802356771795 119449537284194703535157693)
  ·
    refine ⟨44793576481573013825684135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119449537284194703535157693 44793576481573013825684135)
    ·
      refine ⟨67190364722359520738526203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44793576481573013825684135 67190364722359520738526203)
      ·
        refine ⟨100785547083539281107789305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67190364722359520738526203 100785547083539281107789305)
        ·
          refine ⟨75589160312654460830841979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100785547083539281107789305 75589160312654460830841979)
          ·
            refine ⟨113383740468981691246262969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75589160312654460830841979 113383740468981691246262969)
            ·
              refine ⟨85037805351736268434697227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113383740468981691246262969 85037805351736268434697227)
              ·
                refine ⟨127556708027604402652045841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85037805351736268434697227 127556708027604402652045841)
                ·
                  refine ⟨95667531020703301989034381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127556708027604402652045841 95667531020703301989034381)
                  ·
                    refine ⟨35875324132763738245887893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95667531020703301989034381 35875324132763738245887893)
                    ·
                      refine ⟨1681655818723300230275995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35875324132763738245887893 1681655818723300230275995)
                      ·
                        rfl

theorem cell23_3275013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_3275013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275013 prefixEnd_3275013 := by exact prefixLift 3275013
  have htrace : WordTrace (prefixWord ++ tailWord_3275013) baseStart_3275013 baseEnd_3275013 := by
    simpa [prefixWord, tailWord_3275013, baseEnd_3275013] using wordTrace_append hprefix tailTrace_3275013
  have hstable : (prefixWord ++ tailWord_3275013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275013).length < 2 ^ (prefixWord ++ tailWord_3275013).sum := by decide
  have hdescent : baseEnd_3275013 < baseStart_3275013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275020 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 2, 4, 3]
def baseStart_3275020 : Nat := 118140960795 + 3275020 * 2 ^ 59
def prefixEnd_3275020 : Nat := 4983230072969 + 3 ^ 40 * 3275020 * 2
def baseEnd_3275020 : Nat := 1681659413087881702888463

theorem tailTrace_3275020 : CollatzResearch.WordTrace tailWord_3275020 prefixEnd_3275020 1681659413087881702888463 := by
  unfold tailWord_3275020
  simp only [CollatzResearch.WordTrace]
  refine ⟨59724896297584671865331257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79633195063446229153775009 59724896297584671865331257)
  ·
    refine ⟨44793672223188503898998443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59724896297584671865331257 44793672223188503898998443)
    ·
      refine ⟨67190508334782755848497665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44793672223188503898998443 67190508334782755848497665)
      ·
        refine ⟨50392881251087066886373249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67190508334782755848497665 50392881251087066886373249)
        ·
          refine ⟨37794660938315300164779937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50392881251087066886373249 37794660938315300164779937)
          ·
            refine ⟨28345995703736475123584953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37794660938315300164779937 28345995703736475123584953)
            ·
              refine ⟨21259496777802356342688715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28345995703736475123584953 21259496777802356342688715)
              ·
                refine ⟨31889245166703534514033073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21259496777802356342688715 31889245166703534514033073)
                ·
                  refine ⟨23916933875027650885524805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31889245166703534514033073 23916933875027650885524805)
                  ·
                    refine ⟨4484425101567684541035901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23916933875027650885524805 4484425101567684541035901)
                    ·
                      refine ⟨1681659413087881702888463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4484425101567684541035901 1681659413087881702888463)
                      ·
                        rfl

theorem cell23_3275020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_3275020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275020 prefixEnd_3275020 := by exact prefixLift 3275020
  have htrace : WordTrace (prefixWord ++ tailWord_3275020) baseStart_3275020 baseEnd_3275020 := by
    simpa [prefixWord, tailWord_3275020, baseEnd_3275020] using wordTrace_append hprefix tailTrace_3275020
  have hstable : (prefixWord ++ tailWord_3275020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275020).length < 2 ^ (prefixWord ++ tailWord_3275020).sum := by decide
  have hdescent : baseEnd_3275020 < baseStart_3275020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275038 : List Nat := [4, 3, 2, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_3275038 : Nat := 118140960795 + 3275038 * 2 ^ 59
def prefixEnd_3275038 : Nat := 4983230072969 + 3 ^ 40 * 3275038 * 2
def baseEnd_3275038 : Nat := 1681668655739662632463381

theorem tailTrace_3275038 : CollatzResearch.WordTrace tailWord_3275038 prefixEnd_3275038 1681668655739662632463381 := by
  unfold tailWord_3275038
  simp only [CollatzResearch.WordTrace]
  refine ⟨14931306138638016600602221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79633632739402755203211845 14931306138638016600602221)
  ·
    refine ⟨5599239801989256225225833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14931306138638016600602221 5599239801989256225225833)
    ·
      refine ⟨4199429851491942168919375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5599239801989256225225833 4199429851491942168919375)
      ·
        refine ⟨6299144777237913253379063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4199429851491942168919375 6299144777237913253379063)
        ·
          refine ⟨9448717165856869880068595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6299144777237913253379063 9448717165856869880068595)
          ·
            refine ⟨14173075748785304820102893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9448717165856869880068595 14173075748785304820102893)
            ·
              refine ⟨5314903405794489307538585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14173075748785304820102893 5314903405794489307538585)
              ·
                refine ⟨3986177554345866980653939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5314903405794489307538585 3986177554345866980653939)
                ·
                  refine ⟨5979266331518800470980909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986177554345866980653939 5979266331518800470980909)
                  ·
                    refine ⟨2242224874319550176617841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5979266331518800470980909 2242224874319550176617841)
                    ·
                      refine ⟨1681668655739662632463381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2242224874319550176617841 1681668655739662632463381)
                      ·
                        rfl

theorem cell23_3275038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_3275038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275038 prefixEnd_3275038 := by exact prefixLift 3275038
  have htrace : WordTrace (prefixWord ++ tailWord_3275038) baseStart_3275038 baseEnd_3275038 := by
    simpa [prefixWord, tailWord_3275038, baseEnd_3275038] using wordTrace_append hprefix tailTrace_3275038
  have hstable : (prefixWord ++ tailWord_3275038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275038).length < 2 ^ (prefixWord ++ tailWord_3275038).sum := by decide
  have hdescent : baseEnd_3275038 < baseStart_3275038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275080 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 1, 2, 5]
def baseStart_3275080 : Nat := 118140960795 + 3275080 * 2 ^ 59
def prefixEnd_3275080 : Nat := 4983230072969 + 3 ^ 40 * 3275080 * 2
def baseEnd_3275080 : Nat := 1681690221927151468138187

theorem tailTrace_3275080 : CollatzResearch.WordTrace tailWord_3275080 prefixEnd_3275080 1681690221927151468138187 := by
  unfold tailWord_3275080
  simp only [CollatzResearch.WordTrace]
  refine ⟨59725990487475986988923347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79634653983301315985231129 59725990487475986988923347)
  ·
    refine ⟨89588985731213980483385021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59725990487475986988923347 89588985731213980483385021)
    ·
      refine ⟨33595869649205242681269383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89588985731213980483385021 33595869649205242681269383)
      ·
        refine ⟨50393804473807864021904075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33595869649205242681269383 50393804473807864021904075)
        ·
          refine ⟨75590706710711796032856113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50393804473807864021904075 75590706710711796032856113)
          ·
            refine ⟨56693030033033847024642085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75590706710711796032856113 56693030033033847024642085)
            ·
              refine ⟨10629943131193846317120391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56693030033033847024642085 10629943131193846317120391)
              ·
                refine ⟨15944914696790769475680587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10629943131193846317120391 15944914696790769475680587)
                ·
                  refine ⟨23917372045186154213520881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15944914696790769475680587 23917372045186154213520881)
                  ·
                    refine ⟨17938029033889615660140661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23917372045186154213520881 17938029033889615660140661)
                    ·
                      refine ⟨1681690221927151468138187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17938029033889615660140661 1681690221927151468138187)
                      ·
                        rfl

theorem cell23_3275080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_3275080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275080 prefixEnd_3275080 := by exact prefixLift 3275080
  have htrace : WordTrace (prefixWord ++ tailWord_3275080) baseStart_3275080 baseEnd_3275080 := by
    simpa [prefixWord, tailWord_3275080, baseEnd_3275080] using wordTrace_append hprefix tailTrace_3275080
  have hstable : (prefixWord ++ tailWord_3275080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275080).length < 2 ^ (prefixWord ++ tailWord_3275080).sum := by decide
  have hdescent : baseEnd_3275080 < baseStart_3275080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275104 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 2, 5]
def baseStart_3275104 : Nat := 118140960795 + 3275104 * 2 ^ 59
def prefixEnd_3275104 : Nat := 4983230072969 + 3 ^ 40 * 3275104 * 2
def baseEnd_3275104 : Nat := 560567515154286458079359

theorem tailTrace_3275104 : CollatzResearch.WordTrace tailWord_3275104 prefixEnd_3275104 560567515154286458079359 := by
  unfold tailWord_3275104
  simp only [CollatzResearch.WordTrace]
  refine ⟨59726428163432513038360183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79635237551243350717813577 59726428163432513038360183)
  ·
    refine ⟨89589642245148769557540275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59726428163432513038360183 89589642245148769557540275)
    ·
      refine ⟨134384463367723154336310413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89589642245148769557540275 134384463367723154336310413)
      ·
        refine ⟨50394173762896182876116405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134384463367723154336310413 50394173762896182876116405)
        ·
          refine ⟨4724453790271517144635913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50394173762896182876116405 4724453790271517144635913)
          ·
            refine ⟨3543340342703637858476935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4724453790271517144635913 3543340342703637858476935)
            ·
              refine ⟨5315010514055456787715403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543340342703637858476935 5315010514055456787715403)
              ·
                refine ⟨7972515771083185181573105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5315010514055456787715403 7972515771083185181573105)
                ·
                  refine ⟨5979386828312388886179829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7972515771083185181573105 5979386828312388886179829)
                  ·
                    refine ⟨560567515154286458079359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5979386828312388886179829 560567515154286458079359)
                    ·
                      rfl

theorem cell23_3275104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 2, 5].length) (baseStart_3275104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275104 prefixEnd_3275104 := by exact prefixLift 3275104
  have htrace : WordTrace (prefixWord ++ tailWord_3275104) baseStart_3275104 baseEnd_3275104 := by
    simpa [prefixWord, tailWord_3275104, baseEnd_3275104] using wordTrace_append hprefix tailTrace_3275104
  have hstable : (prefixWord ++ tailWord_3275104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275104).length < 2 ^ (prefixWord ++ tailWord_3275104).sum := by decide
  have hdescent : baseEnd_3275104 < baseStart_3275104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275107 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 1, 6, 2]
def baseStart_3275107 : Nat := 118140960795 + 3275107 * 2 ^ 59
def prefixEnd_3275107 : Nat := 4983230072969 + 3 ^ 40 * 3275107 * 2
def baseEnd_3275107 : Nat := 1681704085904822862500563

theorem tailTrace_3275107 : CollatzResearch.WordTrace tailWord_3275107 prefixEnd_3275107 1681704085904822862500563 := by
  unfold tailWord_3275107
  simp only [CollatzResearch.WordTrace]
  refine ⟨119452965745854157589079575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79635310497236105059386383 119452965745854157589079575)
  ·
    refine ⟨179179448618781236383619363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119452965745854157589079575 179179448618781236383619363)
    ·
      refine ⟨268769172928171854575429045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179179448618781236383619363 268769172928171854575429045)
      ·
        refine ⟨25197109962016111366446473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 268769172928171854575429045 25197109962016111366446473)
        ·
          refine ⟨18897832471512083524834855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25197109962016111366446473 18897832471512083524834855)
          ·
            refine ⟨28346748707268125287252283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18897832471512083524834855 28346748707268125287252283)
            ·
              refine ⟨42520123060902187930878425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28346748707268125287252283 42520123060902187930878425)
              ·
                refine ⟨31890092295676640948158819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42520123060902187930878425 31890092295676640948158819)
                ·
                  refine ⟨47835138443514961422238229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31890092295676640948158819 47835138443514961422238229)
                  ·
                    refine ⟨2242272114539763816667417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47835138443514961422238229 2242272114539763816667417)
                    ·
                      refine ⟨1681704085904822862500563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2242272114539763816667417 1681704085904822862500563)
                      ·
                        rfl

theorem cell23_3275107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_3275107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275107 prefixEnd_3275107 := by exact prefixLift 3275107
  have htrace : WordTrace (prefixWord ++ tailWord_3275107) baseStart_3275107 baseEnd_3275107 := by
    simpa [prefixWord, tailWord_3275107, baseEnd_3275107] using wordTrace_append hprefix tailTrace_3275107
  have hstable : (prefixWord ++ tailWord_3275107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275107).length < 2 ^ (prefixWord ++ tailWord_3275107).sum := by decide
  have hdescent : baseEnd_3275107 < baseStart_3275107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275117 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_3275117 : Nat := 118140960795 + 3275117 * 2 ^ 59
def prefixEnd_3275117 : Nat := 4983230072969 + 3 ^ 40 * 3275117 * 2
def baseEnd_3275117 : Nat := 560569740237122607791839

theorem tailTrace_3275117 : CollatzResearch.WordTrace tailWord_3275117 prefixEnd_3275117 560569740237122607791839 := by
  unfold tailWord_3275117
  simp only [CollatzResearch.WordTrace]
  refine ⟨119453330475817929296943605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79635553650545286197962403 119453330475817929296943605)
  ·
    refine ⟨11198749732107930871588463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119453330475817929296943605 11198749732107930871588463)
    ·
      refine ⟨16798124598161896307382695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11198749732107930871588463 16798124598161896307382695)
      ·
        refine ⟨25197186897242844461074043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16798124598161896307382695 25197186897242844461074043)
        ·
          refine ⟨37795780345864266691611065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25197186897242844461074043 37795780345864266691611065)
          ·
            refine ⟨28346835259398200018708299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37795780345864266691611065 28346835259398200018708299)
            ·
              refine ⟨42520252889097300028062449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28346835259398200018708299 42520252889097300028062449)
              ·
                refine ⟨31890189666822975021046837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42520252889097300028062449 31890189666822975021046837)
                ·
                  refine ⟨2989705281264653908223141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31890189666822975021046837 2989705281264653908223141)
                  ·
                    refine ⟨560569740237122607791839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2989705281264653908223141 560569740237122607791839)
                    ·
                      rfl

theorem cell23_3275117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_3275117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275117 prefixEnd_3275117 := by exact prefixLift 3275117
  have htrace : WordTrace (prefixWord ++ tailWord_3275117) baseStart_3275117 baseEnd_3275117 := by
    simpa [prefixWord, tailWord_3275117, baseEnd_3275117] using wordTrace_append hprefix tailTrace_3275117
  have hstable : (prefixWord ++ tailWord_3275117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275117).length < 2 ^ (prefixWord ++ tailWord_3275117).sum := by decide
  have hdescent : baseEnd_3275117 < baseStart_3275117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275120 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 6]
def baseStart_3275120 : Nat := 118140960795 + 3275120 * 2 ^ 59
def prefixEnd_3275120 : Nat := 4983230072969 + 3 ^ 40 * 3275120 * 2
def baseEnd_3275120 : Nat := 1681710761153331311638003

theorem tailTrace_3275120 : CollatzResearch.WordTrace tailWord_3275120 prefixEnd_3275120 1681710761153331311638003 := by
  unfold tailWord_3275120
  simp only [CollatzResearch.WordTrace]
  refine ⟨59726719947403530404651407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79635626596538040539535209 59726719947403530404651407)
  ·
    refine ⟨89590079921105295606977111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59726719947403530404651407 89590079921105295606977111)
    ·
      refine ⟨134385119881657943410465667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89590079921105295606977111 134385119881657943410465667)
      ·
        refine ⟨201577679822486915115698501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134385119881657943410465667 201577679822486915115698501)
        ·
          refine ⟨37795814966716296584193469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201577679822486915115698501 37795814966716296584193469)
          ·
            refine ⟨14173430612518611219072551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37795814966716296584193469 14173430612518611219072551)
            ·
              refine ⟨21260145918777916828608827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14173430612518611219072551 21260145918777916828608827)
              ·
                refine ⟨31890218878166875242913241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21260145918777916828608827 31890218878166875242913241)
                ·
                  refine ⟨23917664158625156432184931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31890218878166875242913241 23917664158625156432184931)
                  ·
                    refine ⟨35876496237937734648277397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23917664158625156432184931 35876496237937734648277397)
                    ·
                      refine ⟨1681710761153331311638003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35876496237937734648277397 1681710761153331311638003)
                      ·
                        rfl

theorem cell23_3275120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_3275120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275120 prefixEnd_3275120 := by exact prefixLift 3275120
  have htrace : WordTrace (prefixWord ++ tailWord_3275120) baseStart_3275120 baseEnd_3275120 := by
    simpa [prefixWord, tailWord_3275120, baseEnd_3275120] using wordTrace_append hprefix tailTrace_3275120
  have hstable : (prefixWord ++ tailWord_3275120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275120).length < 2 ^ (prefixWord ++ tailWord_3275120).sum := by decide
  have hdescent : baseEnd_3275120 < baseStart_3275120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275191 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 3, 1, 3]
def baseStart_3275191 : Nat := 118140960795 + 3275191 * 2 ^ 59
def prefixEnd_3275191 : Nat := 4983230072969 + 3 ^ 40 * 3275191 * 2
def baseEnd_3275191 : Nat := 1681747218279800533850177

theorem tailTrace_3275191 : CollatzResearch.WordTrace tailWord_3275191 prefixEnd_3275191 1681747218279800533850177 := by
  unfold tailWord_3275191
  simp only [CollatzResearch.WordTrace]
  refine ⟨119456029477549839935137427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79637352985033226623424951 119456029477549839935137427)
  ·
    refine ⟨179184044216324759902706141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119456029477549839935137427 179184044216324759902706141)
    ·
      refine ⟨67194016581121784963514803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179184044216324759902706141 67194016581121784963514803)
      ·
        refine ⟨100791024871682677445272205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67194016581121784963514803 100791024871682677445272205)
        ·
          refine ⟨37796634326881004041977077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100791024871682677445272205 37796634326881004041977077)
          ·
            refine ⟨3543434468145094128935351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37796634326881004041977077 3543434468145094128935351)
            ·
              refine ⟨5315151702217641193403027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543434468145094128935351 5315151702217641193403027)
              ·
                refine ⟨7972727553326461790104541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5315151702217641193403027 7972727553326461790104541)
                ·
                  refine ⟨2989772832497423171289203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7972727553326461790104541 2989772832497423171289203)
                  ·
                    refine ⟨4484659248746134756933805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2989772832497423171289203 4484659248746134756933805)
                    ·
                      refine ⟨1681747218279800533850177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4484659248746134756933805 1681747218279800533850177)
                      ·
                        rfl

theorem cell23_3275191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_3275191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275191 prefixEnd_3275191 := by exact prefixLift 3275191
  have htrace : WordTrace (prefixWord ++ tailWord_3275191) baseStart_3275191 baseEnd_3275191 := by
    simpa [prefixWord, tailWord_3275191, baseEnd_3275191] using wordTrace_append hprefix tailTrace_3275191
  have hstable : (prefixWord ++ tailWord_3275191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275191).length < 2 ^ (prefixWord ++ tailWord_3275191).sum := by decide
  have hdescent : baseEnd_3275191 < baseStart_3275191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275231 : List Nat := [1, 1, 2, 3, 3, 3, 3, 1, 1, 1, 4]
def baseStart_3275231 : Nat := 118140960795 + 3275231 * 2 ^ 59
def prefixEnd_3275231 : Nat := 4983230072969 + 3 ^ 40 * 3275231 * 2
def baseEnd_3275231 : Nat := 1681767757505980377349993

theorem tailTrace_3275231 : CollatzResearch.WordTrace tailWord_3275231 prefixEnd_3275231 1681767757505980377349993 := by
  unfold tailWord_3275231
  simp only [CollatzResearch.WordTrace]
  refine ⟨119457488397404926766593547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79638325598269951177729031 119457488397404926766593547)
  ·
    refine ⟨179186232596107390149890321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119457488397404926766593547 179186232596107390149890321)
    ·
      refine ⟨134389674447080542612417741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179186232596107390149890321 134389674447080542612417741)
      ·
        refine ⟨50396127917655203479656653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134389674447080542612417741 50396127917655203479656653)
        ·
          refine ⟨18898547969120701304871245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50396127917655203479656653 18898547969120701304871245)
          ·
            refine ⟨7086955488420262989326717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18898547969120701304871245 7086955488420262989326717)
            ·
              refine ⟨2657608308157598620997519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7086955488420262989326717 2657608308157598620997519)
              ·
                refine ⟨3986412462236397931496279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657608308157598620997519 3986412462236397931496279)
                ·
                  refine ⟨5979618693354596897244419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3986412462236397931496279 5979618693354596897244419)
                  ·
                    refine ⟨8969428040031895345866629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5979618693354596897244419 8969428040031895345866629)
                    ·
                      refine ⟨1681767757505980377349993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8969428040031895345866629 1681767757505980377349993)
                      ·
                        rfl

theorem cell23_3275231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_3275231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275231 prefixEnd_3275231 := by exact prefixLift 3275231
  have htrace : WordTrace (prefixWord ++ tailWord_3275231) baseStart_3275231 baseEnd_3275231 := by
    simpa [prefixWord, tailWord_3275231, baseEnd_3275231] using wordTrace_append hprefix tailTrace_3275231
  have hstable : (prefixWord ++ tailWord_3275231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275231).length < 2 ^ (prefixWord ++ tailWord_3275231).sum := by decide
  have hdescent : baseEnd_3275231 < baseStart_3275231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275237 : List Nat := [1, 3, 1, 5, 2, 11]
def baseStart_3275237 : Nat := 118140960795 + 3275237 * 2 ^ 59
def prefixEnd_3275237 : Nat := 4983230072969 + 3 ^ 40 * 3275237 * 2
def baseEnd_3275237 : Nat := 6920867647695091991255

theorem tailTrace_3275237 : CollatzResearch.WordTrace tailWord_3275237 prefixEnd_3275237 6920867647695091991255 := by
  unfold tailWord_3275237
  simp only [CollatzResearch.WordTrace]
  refine ⟨119457707235383189791311965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79638471490255459860874643 119457707235383189791311965)
  ·
    refine ⟨44796640213268696171741987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119457707235383189791311965 44796640213268696171741987)
    ·
      refine ⟨67194960319903044257612981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44796640213268696171741987 67194960319903044257612981)
      ·
        refine ⟨6299527529990910399151217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67194960319903044257612981 6299527529990910399151217)
        ·
          refine ⟨4724645647493182799363413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6299527529990910399151217 4724645647493182799363413)
          ·
            refine ⟨6920867647695091991255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4724645647493182799363413 6920867647695091991255)
            ·
              rfl

theorem cell23_3275237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 11].length) (baseStart_3275237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275237 prefixEnd_3275237 := by exact prefixLift 3275237
  have htrace : WordTrace (prefixWord ++ tailWord_3275237) baseStart_3275237 baseEnd_3275237 := by
    simpa [prefixWord, tailWord_3275237, baseEnd_3275237] using wordTrace_append hprefix tailTrace_3275237
  have hstable : (prefixWord ++ tailWord_3275237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275237).length < 2 ^ (prefixWord ++ tailWord_3275237).sum := by decide
  have hdescent : baseEnd_3275237 < baseStart_3275237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275247 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 3]
def baseStart_3275247 : Nat := 118140960795 + 3275247 * 2 ^ 59
def prefixEnd_3275247 : Nat := 4983230072969 + 3 ^ 40 * 3275247 * 2
def baseEnd_3275247 : Nat := 1681775973196452314749919

theorem tailTrace_3275247 : CollatzResearch.WordTrace tailWord_3275247 prefixEnd_3275247 1681775973196452314749919 := by
  unfold tailWord_3275247
  simp only [CollatzResearch.WordTrace]
  refine ⟨119458071965346961499175995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79638714643564640999450663 119458071965346961499175995)
  ·
    refine ⟨179187107948020442248763993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119458071965346961499175995 179187107948020442248763993)
    ·
      refine ⟨134390330961015331686572995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179187107948020442248763993 134390330961015331686572995)
      ·
        refine ⟨201585496441522997529859493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134390330961015331686572995 201585496441522997529859493)
        ·
          refine ⟨37797280582785562036848655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201585496441522997529859493 37797280582785562036848655)
          ·
            refine ⟨56695920874178343055272983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37797280582785562036848655 56695920874178343055272983)
            ·
              refine ⟨85043881311267514582909475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56695920874178343055272983 85043881311267514582909475)
              ·
                refine ⟨127565821966901271874364213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85043881311267514582909475 127565821966901271874364213)
                ·
                  refine ⟨11959295809396994238221645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127565821966901271874364213 11959295809396994238221645)
                  ·
                    refine ⟨4484735928523872839333117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11959295809396994238221645 4484735928523872839333117)
                    ·
                      refine ⟨1681775973196452314749919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4484735928523872839333117 1681775973196452314749919)
                      ·
                        rfl

theorem cell23_3275247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 3].length) (baseStart_3275247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275247 prefixEnd_3275247 := by exact prefixLift 3275247
  have htrace : WordTrace (prefixWord ++ tailWord_3275247) baseStart_3275247 baseEnd_3275247 := by
    simpa [prefixWord, tailWord_3275247, baseEnd_3275247] using wordTrace_append hprefix tailTrace_3275247
  have hstable : (prefixWord ++ tailWord_3275247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275247).length < 2 ^ (prefixWord ++ tailWord_3275247).sum := by decide
  have hdescent : baseEnd_3275247 < baseStart_3275247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275248 : List Nat := [2, 1, 1, 1, 3, 3, 3, 4, 1, 2, 2]
def baseStart_3275248 : Nat := 118140960795 + 3275248 * 2 ^ 59
def prefixEnd_3275248 : Nat := 4983230072969 + 3 ^ 40 * 3275248 * 2
def baseEnd_3275248 : Nat := 1681776486677106810837415

theorem tailTrace_3275248 : CollatzResearch.WordTrace tailWord_3275248 prefixEnd_3275248 1681776486677106810837415 := by
  unfold tailWord_3275248
  simp only [CollatzResearch.WordTrace]
  refine ⟨59729054219171669334981199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79638738958895559113308265 59729054219171669334981199)
  ·
    refine ⟨89593581328757504002471799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59729054219171669334981199 89593581328757504002471799)
    ·
      refine ⟨134390371993136256003707699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89593581328757504002471799 134390371993136256003707699)
      ·
        refine ⟨201585557989704384005561549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134390371993136256003707699 201585557989704384005561549)
        ·
          refine ⟨75594584246139144002085581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201585557989704384005561549 75594584246139144002085581)
          ·
            refine ⟨28347969092302179000782093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75594584246139144002085581 28347969092302179000782093)
            ·
              refine ⟨10630488409613317125293285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28347969092302179000782093 10630488409613317125293285)
              ·
                refine ⟨1993216576802496960992491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10630488409613317125293285 1993216576802496960992491)
                ·
                  refine ⟨2989824865203745441488737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993216576802496960992491 2989824865203745441488737)
                  ·
                    refine ⟨2242368648902809081116553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2989824865203745441488737 2242368648902809081116553)
                    ·
                      refine ⟨1681776486677106810837415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2242368648902809081116553 1681776486677106810837415)
                      ·
                        rfl

theorem cell23_3275248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 1, 2, 2].length) (baseStart_3275248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275248 prefixEnd_3275248 := by exact prefixLift 3275248
  have htrace : WordTrace (prefixWord ++ tailWord_3275248) baseStart_3275248 baseEnd_3275248 := by
    simpa [prefixWord, tailWord_3275248, baseEnd_3275248] using wordTrace_append hprefix tailTrace_3275248
  have hstable : (prefixWord ++ tailWord_3275248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275248).length < 2 ^ (prefixWord ++ tailWord_3275248).sum := by decide
  have hdescent : baseEnd_3275248 < baseStart_3275248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275297 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 4, 6]
def baseStart_3275297 : Nat := 118140960795 + 3275297 * 2 ^ 59
def prefixEnd_3275297 : Nat := 4983230072969 + 3 ^ 40 * 3275297 * 2
def baseEnd_3275297 : Nat := 560600549076392373041563

theorem tailTrace_3275297 : CollatzResearch.WordTrace tailWord_3275297 prefixEnd_3275297 560600549076392373041563 := by
  unfold tailWord_3275297
  simp only [CollatzResearch.WordTrace]
  refine ⟨119459895615165820038496145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79639930410110546692330763 119459895615165820038496145)
  ·
    refine ⟨89594921711374365028872109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119459895615165820038496145 89594921711374365028872109)
    ·
      refine ⟨33598095641765386885827041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89594921711374365028872109 33598095641765386885827041)
      ·
        refine ⟨25198571731324040164370281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33598095641765386885827041 25198571731324040164370281)
        ·
          refine ⟨18898928798493030123277711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25198571731324040164370281 18898928798493030123277711)
          ·
            refine ⟨28348393197739545184916567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18898928798493030123277711 28348393197739545184916567)
            ·
              refine ⟨42522589796609317777374851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28348393197739545184916567 42522589796609317777374851)
              ·
                refine ⟨63783884694913976666062277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42522589796609317777374851 63783884694913976666062277)
                ·
                  refine ⟨11959478380296370624886677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63783884694913976666062277 11959478380296370624886677)
                  ·
                    refine ⟨560600549076392373041563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11959478380296370624886677 560600549076392373041563)
                    ·
                      rfl

theorem cell23_3275297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_3275297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275297 prefixEnd_3275297 := by exact prefixLift 3275297
  have htrace : WordTrace (prefixWord ++ tailWord_3275297) baseStart_3275297 baseEnd_3275297 := by
    simpa [prefixWord, tailWord_3275297, baseEnd_3275297] using wordTrace_append hprefix tailTrace_3275297
  have hstable : (prefixWord ++ tailWord_3275297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275297).length < 2 ^ (prefixWord ++ tailWord_3275297).sum := by decide
  have hdescent : baseEnd_3275297 < baseStart_3275297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275307 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 3]
def baseStart_3275307 : Nat := 118140960795 + 3275307 * 2 ^ 59
def prefixEnd_3275307 : Nat := 4983230072969 + 3 ^ 40 * 3275307 * 2
def baseEnd_3275307 : Nat := 1681806782035722079999643

theorem tailTrace_3275307 : CollatzResearch.WordTrace tailWord_3275307 prefixEnd_3275307 1681806782035722079999643 := by
  unfold tailWord_3275307
  simp only [CollatzResearch.WordTrace]
  refine ⟨119460260345129591746360175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79640173563419727830906783 119460260345129591746360175)
  ·
    refine ⟨179190390517694387619540263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119460260345129591746360175 179190390517694387619540263)
    ·
      refine ⟨268785585776541581429310395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179190390517694387619540263 268785585776541581429310395)
      ·
        refine ⟨403178378664812372143965593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268785585776541581429310395 403178378664812372143965593)
        ·
          refine ⟨302383783998609279107974195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403178378664812372143965593 302383783998609279107974195)
          ·
            refine ⟨453575675997913918661961293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302383783998609279107974195 453575675997913918661961293)
            ·
              refine ⟨170090878499217719498235485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 453575675997913918661961293 170090878499217719498235485)
              ·
                refine ⟨63784079437206644811838307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170090878499217719498235485 63784079437206644811838307)
                ·
                  refine ⟨95676119155809967217757461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63784079437206644811838307 95676119155809967217757461)
                  ·
                    refine ⟨4484818085428592213332381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95676119155809967217757461 4484818085428592213332381)
                    ·
                      refine ⟨1681806782035722079999643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4484818085428592213332381 1681806782035722079999643)
                      ·
                        rfl

theorem cell23_3275307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 3].length) (baseStart_3275307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275307 prefixEnd_3275307 := by exact prefixLift 3275307
  have htrace : WordTrace (prefixWord ++ tailWord_3275307) baseStart_3275307 baseEnd_3275307 := by
    simpa [prefixWord, tailWord_3275307, baseEnd_3275307] using wordTrace_append hprefix tailTrace_3275307
  have hstable : (prefixWord ++ tailWord_3275307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275307).length < 2 ^ (prefixWord ++ tailWord_3275307).sum := by decide
  have hdescent : baseEnd_3275307 < baseStart_3275307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275327 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 7]
def baseStart_3275327 : Nat := 118140960795 + 3275327 * 2 ^ 59
def prefixEnd_3275327 : Nat := 4983230072969 + 3 ^ 40 * 3275327 * 2
def baseEnd_3275327 : Nat := 186868561294312444638839

theorem tailTrace_3275327 : CollatzResearch.WordTrace tailWord_3275327 prefixEnd_3275327 186868561294312444638839 := by
  unfold tailWord_3275327
  simp only [CollatzResearch.WordTrace]
  refine ⟨119460989805057135162088235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79640659870038090108058823 119460989805057135162088235)
  ·
    refine ⟨179191484707585702743132353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119460989805057135162088235 179191484707585702743132353)
    ·
      refine ⟨134393613530689277057349265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179191484707585702743132353 134393613530689277057349265)
      ·
        refine ⟨100795210148016957793011949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134393613530689277057349265 100795210148016957793011949)
        ·
          refine ⟨37798203805506359172379481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100795210148016957793011949 37798203805506359172379481)
          ·
            refine ⟨28348652854129769379284611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37798203805506359172379481 28348652854129769379284611)
            ·
              refine ⟨42522979281194654068926917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28348652854129769379284611 42522979281194654068926917)
              ·
                refine ⟨7973058615223997637923797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42522979281194654068926917 7973058615223997637923797)
                ·
                  refine ⟨186868561294312444638839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7973058615223997637923797 186868561294312444638839)
                  ·
                    rfl

theorem cell23_3275327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 7].length) (baseStart_3275327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275327 prefixEnd_3275327 := by exact prefixLift 3275327
  have htrace : WordTrace (prefixWord ++ tailWord_3275327) baseStart_3275327 baseEnd_3275327 := by
    simpa [prefixWord, tailWord_3275327, baseEnd_3275327] using wordTrace_append hprefix tailTrace_3275327
  have hstable : (prefixWord ++ tailWord_3275327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275327).length < 2 ^ (prefixWord ++ tailWord_3275327).sum := by decide
  have hdescent : baseEnd_3275327 < baseStart_3275327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275341 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_3275341 : Nat := 118140960795 + 3275341 * 2 ^ 59
def prefixEnd_3275341 : Nat := 4983230072969 + 3 ^ 40 * 3275341 * 2
def baseEnd_3275341 : Nat := 1681824240377974946974487

theorem tailTrace_3275341 : CollatzResearch.WordTrace tailWord_3275341 prefixEnd_3275341 1681824240377974946974487 := by
  unfold tailWord_3275341
  simp only [CollatzResearch.WordTrace]
  refine ⟨119461500427006415553097877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79641000284670943702065251 119461500427006415553097877)
  ·
    refine ⟨5599757832515925729051463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119461500427006415553097877 5599757832515925729051463)
    ·
      refine ⟨8399636748773888593577195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5599757832515925729051463 8399636748773888593577195)
      ·
        refine ⟨12599455123160832890365793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8399636748773888593577195 12599455123160832890365793)
        ·
          refine ⟨9449591342370624667774345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12599455123160832890365793 9449591342370624667774345)
          ·
            refine ⟨7087193506777968500830759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9449591342370624667774345 7087193506777968500830759)
            ·
              refine ⟨10630790260166952751246139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7087193506777968500830759 10630790260166952751246139)
              ·
                refine ⟨15946185390250429126869209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10630790260166952751246139 15946185390250429126869209)
                ·
                  refine ⟨11959639042687821845151907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15946185390250429126869209 11959639042687821845151907)
                  ·
                    refine ⟨17939458564031732767727861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11959639042687821845151907 17939458564031732767727861)
                    ·
                      refine ⟨1681824240377974946974487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17939458564031732767727861 1681824240377974946974487)
                      ·
                        rfl

theorem cell23_3275341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_3275341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275341 prefixEnd_3275341 := by exact prefixLift 3275341
  have htrace : WordTrace (prefixWord ++ tailWord_3275341) baseStart_3275341 baseEnd_3275341 := by
    simpa [prefixWord, tailWord_3275341, baseEnd_3275341] using wordTrace_append hprefix tailTrace_3275341
  have hstable : (prefixWord ++ tailWord_3275341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275341).length < 2 ^ (prefixWord ++ tailWord_3275341).sum := by decide
  have hdescent : baseEnd_3275341 < baseStart_3275341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275344 : List Nat := [2, 1, 1, 1, 1, 3, 2, 7, 5]
def baseStart_3275344 : Nat := 118140960795 + 3275344 * 2 ^ 59
def prefixEnd_3275344 : Nat := 4983230072969 + 3 ^ 40 * 3275344 * 2
def baseEnd_3275344 : Nat := 186869531202215381692997

theorem tailTrace_3275344 : CollatzResearch.WordTrace tailWord_3275344 prefixEnd_3275344 186869531202215381692997 := by
  unfold tailWord_3275344
  simp only [CollatzResearch.WordTrace]
  refine ⟨59730804922997773532728543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79641073230663698043638057 59730804922997773532728543)
  ·
    refine ⟨89596207384496660299092815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59730804922997773532728543 89596207384496660299092815)
    ·
      refine ⟨134394311076744990448639223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89596207384496660299092815 134394311076744990448639223)
      ·
        refine ⟨201591466615117485672958835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134394311076744990448639223 201591466615117485672958835)
        ·
          refine ⟨302387199922676228509438253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201591466615117485672958835 302387199922676228509438253)
          ·
            refine ⟨113395199971003585691039345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302387199922676228509438253 113395199971003585691039345)
            ·
              refine ⟨85046399978252689268279509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113395199971003585691039345 85046399978252689268279509)
              ·
                refine ⟨1993274999490297404725301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 85046399978252689268279509 1993274999490297404725301)
                ·
                  refine ⟨186869531202215381692997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1993274999490297404725301 186869531202215381692997)
                  ·
                    rfl

theorem cell23_3275344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 5].length) (baseStart_3275344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275344 prefixEnd_3275344 := by exact prefixLift 3275344
  have htrace : WordTrace (prefixWord ++ tailWord_3275344) baseStart_3275344 baseEnd_3275344 := by
    simpa [prefixWord, tailWord_3275344, baseEnd_3275344] using wordTrace_append hprefix tailTrace_3275344
  have hstable : (prefixWord ++ tailWord_3275344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275344).length < 2 ^ (prefixWord ++ tailWord_3275344).sum := by decide
  have hdescent : baseEnd_3275344 < baseStart_3275344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275404 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 7, 4]
def baseStart_3275404 : Nat := 118140960795 + 3275404 * 2 ^ 59
def prefixEnd_3275404 : Nat := 4983230072969 + 3 ^ 40 * 3275404 * 2
def baseEnd_3275404 : Nat := 560618863219736066828899

theorem tailTrace_3275404 : CollatzResearch.WordTrace tailWord_3275404 prefixEnd_3275404 560618863219736066828899 := by
  unfold tailWord_3275404
  simp only [CollatzResearch.WordTrace]
  refine ⟨59731899112889088656320633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79642532150518784875094177 59731899112889088656320633)
  ·
    refine ⟨44798924334666816492240475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59731899112889088656320633 44798924334666816492240475)
    ·
      refine ⟨67198386502000224738360713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44798924334666816492240475 67198386502000224738360713)
      ·
        refine ⟨50398789876500168553770535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67198386502000224738360713 50398789876500168553770535)
        ·
          refine ⟨75598184814750252830655803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50398789876500168553770535 75598184814750252830655803)
          ·
            refine ⟨113397277222125379245983705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75598184814750252830655803 113397277222125379245983705)
            ·
              refine ⟨85047957916594034434487779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113397277222125379245983705 85047957916594034434487779)
              ·
                refine ⟨127571936874891051651731669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85047957916594034434487779 127571936874891051651731669)
                ·
                  refine ⟨2989967270505259023087461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 127571936874891051651731669 2989967270505259023087461)
                  ·
                    refine ⟨560618863219736066828899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2989967270505259023087461 560618863219736066828899)
                    ·
                      rfl

theorem cell23_3275404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_3275404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275404 prefixEnd_3275404 := by exact prefixLift 3275404
  have htrace : WordTrace (prefixWord ++ tailWord_3275404) baseStart_3275404 baseEnd_3275404 := by
    simpa [prefixWord, tailWord_3275404, baseEnd_3275404] using wordTrace_append hprefix tailTrace_3275404
  have hstable : (prefixWord ++ tailWord_3275404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275404).length < 2 ^ (prefixWord ++ tailWord_3275404).sum := by decide
  have hdescent : baseEnd_3275404 < baseStart_3275404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275407 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 6]
def baseStart_3275407 : Nat := 118140960795 + 3275407 * 2 ^ 59
def prefixEnd_3275407 : Nat := 4983230072969 + 3 ^ 40 * 3275407 * 2
def baseEnd_3275407 : Nat := 1681858130101171688749183

theorem tailTrace_3275407 : CollatzResearch.WordTrace tailWord_3275407 prefixEnd_3275407 1681858130101171688749183 := by
  unfold tailWord_3275407
  simp only [CollatzResearch.WordTrace]
  refine ⟨119463907644767308825000475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79642605096511539216666983 119463907644767308825000475)
  ·
    refine ⟨179195861467150963237500713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119463907644767308825000475 179195861467150963237500713)
    ·
      refine ⟨134396896100363222428125535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179195861467150963237500713 134396896100363222428125535)
      ·
        refine ⟨201595344150544833642188303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134396896100363222428125535 201595344150544833642188303)
        ·
          refine ⟨302393016225817250463282455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201595344150544833642188303 302393016225817250463282455)
          ·
            refine ⟨453589524338725875694923683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302393016225817250463282455 453589524338725875694923683)
            ·
              refine ⟨680384286508088813542385525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453589524338725875694923683 680384286508088813542385525)
              ·
                refine ⟨63786026860133326269598643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 680384286508088813542385525 63786026860133326269598643)
                ·
                  refine ⟨95679040290199989404397965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63786026860133326269598643 95679040290199989404397965)
                  ·
                    refine ⟨35879640108824996026649237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95679040290199989404397965 35879640108824996026649237)
                    ·
                      refine ⟨1681858130101171688749183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35879640108824996026649237 1681858130101171688749183)
                      ·
                        rfl

theorem cell23_3275407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_3275407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275407 prefixEnd_3275407 := by exact prefixLift 3275407
  have htrace : WordTrace (prefixWord ++ tailWord_3275407) baseStart_3275407 baseEnd_3275407 := by
    simpa [prefixWord, tailWord_3275407, baseEnd_3275407] using wordTrace_append hprefix tailTrace_3275407
  have hstable : (prefixWord ++ tailWord_3275407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275407).length < 2 ^ (prefixWord ++ tailWord_3275407).sum := by decide
  have hdescent : baseEnd_3275407 < baseStart_3275407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275438 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3275438 : Nat := 118140960795 + 3275438 * 2 ^ 59
def prefixEnd_3275438 : Nat := 4983230072969 + 3 ^ 40 * 3275438 * 2
def baseEnd_3275438 : Nat := 560624682667153689153847

theorem tailTrace_3275438 : CollatzResearch.WordTrace tailWord_3275438 prefixEnd_3275438 560624682667153689153847 := by
  unfold tailWord_3275438
  simp only [CollatzResearch.WordTrace]
  refine ⟨14933129788456875139922371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79643358871770000746252645 14933129788456875139922371)
  ·
    refine ⟨22399694682685312709883557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14933129788456875139922371 22399694682685312709883557)
    ·
      refine ⟨4199942753003496133103167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22399694682685312709883557 4199942753003496133103167)
      ·
        refine ⟨6299914129505244199654751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4199942753003496133103167 6299914129505244199654751)
        ·
          refine ⟨9449871194257866299482127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6299914129505244199654751 9449871194257866299482127)
          ·
            refine ⟨14174806791386799449223191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9449871194257866299482127 14174806791386799449223191)
            ·
              refine ⟨21262210187080199173834787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14174806791386799449223191 21262210187080199173834787)
              ·
                refine ⟨31893315280620298760752181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21262210187080199173834787 31893315280620298760752181)
                ·
                  refine ⟨2989998307558153008820517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31893315280620298760752181 2989998307558153008820517)
                  ·
                    refine ⟨560624682667153689153847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2989998307558153008820517 560624682667153689153847)
                    ·
                      rfl

theorem cell23_3275438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3275438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275438 prefixEnd_3275438 := by exact prefixLift 3275438
  have htrace : WordTrace (prefixWord ++ tailWord_3275438) baseStart_3275438 baseEnd_3275438 := by
    simpa [prefixWord, tailWord_3275438, baseEnd_3275438] using wordTrace_append hprefix tailTrace_3275438
  have hstable : (prefixWord ++ tailWord_3275438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275438).length < 2 ^ (prefixWord ++ tailWord_3275438).sum := by decide
  have hdescent : baseEnd_3275438 < baseStart_3275438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275468 : List Nat := [2, 2, 1, 5, 1, 3, 1, 2, 6]
def baseStart_3275468 : Nat := 118140960795 + 3275468 * 2 ^ 59
def prefixEnd_3275468 : Nat := 4983230072969 + 3 ^ 40 * 3275468 * 2
def baseEnd_3275468 : Nat := 186876605824566216676267

theorem tailTrace_3275468 : CollatzResearch.WordTrace tailWord_3275468 prefixEnd_3275468 186876605824566216676267 := by
  unfold tailWord_3275468
  simp only [CollatzResearch.WordTrace]
  refine ⟨59733066248773158121485529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79644088331697544161980705 59733066248773158121485529)
  ·
    refine ⟨44799799686579868591114147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59733066248773158121485529 44799799686579868591114147)
    ·
      refine ⟨67199699529869802886671221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44799799686579868591114147 67199699529869802886671221)
      ·
        refine ⟨6299971830925294020625427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67199699529869802886671221 6299971830925294020625427)
        ·
          refine ⟨9449957746387941030938141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6299971830925294020625427 9449957746387941030938141)
          ·
            refine ⟨3543734154895477886601803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9449957746387941030938141 3543734154895477886601803)
            ·
              refine ⟨5315601232343216829902705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543734154895477886601803 5315601232343216829902705)
              ·
                refine ⟨3986700924257412622427029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5315601232343216829902705 3986700924257412622427029)
                ·
                  refine ⟨186876605824566216676267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3986700924257412622427029 186876605824566216676267)
                  ·
                    rfl

theorem cell23_3275468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 6].length) (baseStart_3275468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275468 prefixEnd_3275468 := by exact prefixLift 3275468
  have htrace : WordTrace (prefixWord ++ tailWord_3275468) baseStart_3275468 baseEnd_3275468 := by
    simpa [prefixWord, tailWord_3275468, baseEnd_3275468] using wordTrace_append hprefix tailTrace_3275468
  have hstable : (prefixWord ++ tailWord_3275468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275468).length < 2 ^ (prefixWord ++ tailWord_3275468).sum := by decide
  have hdescent : baseEnd_3275468 < baseStart_3275468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275504 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 5]
def baseStart_3275504 : Nat := 118140960795 + 3275504 * 2 ^ 59
def prefixEnd_3275504 : Nat := 4983230072969 + 3 ^ 40 * 3275504 * 2
def baseEnd_3275504 : Nat := 1681907937724657809236237

theorem tailTrace_3275504 : CollatzResearch.WordTrace tailWord_3275504 prefixEnd_3275504 1681907937724657809236237 := by
  unfold tailWord_3275504
  simp only [CollatzResearch.WordTrace]
  refine ⟨59733722762707947195640783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79644963683610596260854377 59733722762707947195640783)
  ·
    refine ⟨89600584144061920793461175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59733722762707947195640783 89600584144061920793461175)
    ·
      refine ⟨134400876216092881190191763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89600584144061920793461175 134400876216092881190191763)
      ·
        refine ⟨201601314324139321785287645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134400876216092881190191763 201601314324139321785287645)
        ·
          refine ⟨75600492871552245669482867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201601314324139321785287645 75600492871552245669482867)
          ·
            refine ⟨113400739307328368504224301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75600492871552245669482867 113400739307328368504224301)
            ·
              refine ⟨42525277240248138189084113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113400739307328368504224301 42525277240248138189084113)
              ·
                refine ⟨31893957930186103641813085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42525277240248138189084113 31893957930186103641813085)
                ·
                  refine ⟨11960234223819788865679907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31893957930186103641813085 11960234223819788865679907)
                  ·
                    refine ⟨17940351335729683298519861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11960234223819788865679907 17940351335729683298519861)
                    ·
                      refine ⟨1681907937724657809236237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17940351335729683298519861 1681907937724657809236237)
                      ·
                        rfl

theorem cell23_3275504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_3275504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275504 prefixEnd_3275504 := by exact prefixLift 3275504
  have htrace : WordTrace (prefixWord ++ tailWord_3275504) baseStart_3275504 baseEnd_3275504 := by
    simpa [prefixWord, tailWord_3275504, baseEnd_3275504] using wordTrace_append hprefix tailTrace_3275504
  have hstable : (prefixWord ++ tailWord_3275504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275504).length < 2 ^ (prefixWord ++ tailWord_3275504).sum := by decide
  have hdescent : baseEnd_3275504 < baseStart_3275504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275521 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_3275521 : Nat := 118140960795 + 3275521 * 2 ^ 59
def prefixEnd_3275521 : Nat := 4983230072969 + 3 ^ 40 * 3275521 * 2
def baseEnd_3275521 : Nat := 1681916666895784242723659

theorem tailTrace_3275521 : CollatzResearch.WordTrace tailWord_3275521 prefixEnd_3275521 1681916666895784242723659 := by
  unfold tailWord_3275521
  simp only [CollatzResearch.WordTrace]
  refine ⟨119468065566354306294650417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79645377044236204196433611 119468065566354306294650417)
  ·
    refine ⟨89601049174765729720987813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119468065566354306294650417 89601049174765729720987813)
    ·
      refine ⟨16800196720268574322685215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89601049174765729720987813 16800196720268574322685215)
      ·
        refine ⟨25200295080402861484027823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16800196720268574322685215 25200295080402861484027823)
        ·
          refine ⟨37800442620604292226041735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25200295080402861484027823 37800442620604292226041735)
          ·
            refine ⟨56700663930906438339062603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37800442620604292226041735 56700663930906438339062603)
            ·
              refine ⟨85050995896359657508593905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56700663930906438339062603 85050995896359657508593905)
              ·
                refine ⟨63788246922269743131445429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85050995896359657508593905 63788246922269743131445429)
                ·
                  refine ⟨5980148148962788418573009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63788246922269743131445429 5980148148962788418573009)
                  ·
                    refine ⟨4485111111722091313929757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5980148148962788418573009 4485111111722091313929757)
                    ·
                      refine ⟨1681916666895784242723659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4485111111722091313929757 1681916666895784242723659)
                      ·
                        rfl

theorem cell23_3275521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_3275521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275521 prefixEnd_3275521 := by exact prefixLift 3275521
  have htrace : WordTrace (prefixWord ++ tailWord_3275521) baseStart_3275521 baseEnd_3275521 := by
    simpa [prefixWord, tailWord_3275521, baseEnd_3275521] using wordTrace_append hprefix tailTrace_3275521
  have hstable : (prefixWord ++ tailWord_3275521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275521).length < 2 ^ (prefixWord ++ tailWord_3275521).sum := by decide
  have hdescent : baseEnd_3275521 < baseStart_3275521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275544 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3275544 : Nat := 118140960795 + 3275544 * 2 ^ 59
def prefixEnd_3275544 : Nat := 4983230072969 + 3 ^ 40 * 3275544 * 2
def baseEnd_3275544 : Nat := 1681928476950837652736053

theorem tailTrace_3275544 : CollatzResearch.WordTrace tailWord_3275544 prefixEnd_3275544 1681928476950837652736053 := by
  unfold tailWord_3275544
  simp only [CollatzResearch.WordTrace]
  refine ⟨59734452222635490611368843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79645936296847320815158457 59734452222635490611368843)
  ·
    refine ⟨89601678333953235917053265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59734452222635490611368843 89601678333953235917053265)
    ·
      refine ⟨67201258750464926937789949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89601678333953235917053265 67201258750464926937789949)
      ·
        refine ⟨25200472031424347601671231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67201258750464926937789949 25200472031424347601671231)
        ·
          refine ⟨37800708047136521402506847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25200472031424347601671231 37800708047136521402506847)
          ·
            refine ⟨56701062070704782103760271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37800708047136521402506847 56701062070704782103760271)
            ·
              refine ⟨85051593106057173155640407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56701062070704782103760271 85051593106057173155640407)
              ·
                refine ⟨127577389659085759733460611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85051593106057173155640407 127577389659085759733460611)
                ·
                  refine ⟨191366084488628639600190917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127577389659085759733460611 191366084488628639600190917)
                  ·
                    refine ⟨35881140841617869925035797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 191366084488628639600190917 35881140841617869925035797)
                    ·
                      refine ⟨1681928476950837652736053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35881140841617869925035797 1681928476950837652736053)
                      ·
                        rfl

theorem cell23_3275544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3275544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275544 prefixEnd_3275544 := by exact prefixLift 3275544
  have htrace : WordTrace (prefixWord ++ tailWord_3275544) baseStart_3275544 baseEnd_3275544 := by
    simpa [prefixWord, tailWord_3275544, baseEnd_3275544] using wordTrace_append hprefix tailTrace_3275544
  have hstable : (prefixWord ++ tailWord_3275544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275544).length < 2 ^ (prefixWord ++ tailWord_3275544).sum := by decide
  have hdescent : baseEnd_3275544 < baseStart_3275544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275561 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 2, 7, 2]
def baseStart_3275561 : Nat := 118140960795 + 3275561 * 2 ^ 59
def prefixEnd_3275561 : Nat := 4983230072969 + 3 ^ 40 * 3275561 * 2
def baseEnd_3275561 : Nat := 1681937206121964086223475

theorem tailTrace_3275561 : CollatzResearch.WordTrace tailWord_3275561 prefixEnd_3275561 1681937206121964086223475 := by
  unfold tailWord_3275561
  simp only [CollatzResearch.WordTrace]
  refine ⟨119469524486209393126106537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79646349657472928750737691 119469524486209393126106537)
  ·
    refine ⟨89602143364657044844579903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119469524486209393126106537 89602143364657044844579903)
    ·
      refine ⟨134403215046985567266869855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89602143364657044844579903 134403215046985567266869855)
      ·
        refine ⟨201604822570478350900304783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134403215046985567266869855 201604822570478350900304783)
        ·
          refine ⟨302407233855717526350457175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201604822570478350900304783 302407233855717526350457175)
          ·
            refine ⟨453610850783576289525685763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302407233855717526350457175 453610850783576289525685763)
            ·
              refine ⟨680416276175364434288528645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453610850783576289525685763 680416276175364434288528645)
              ·
                refine ⟨127578051782880831429099121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 680416276175364434288528645 127578051782880831429099121)
                ·
                  refine ⟨95683538837160623571824341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127578051782880831429099121 95683538837160623571824341)
                  ·
                    refine ⟨2242582941495952114964633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 95683538837160623571824341 2242582941495952114964633)
                    ·
                      refine ⟨1681937206121964086223475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2242582941495952114964633 1681937206121964086223475)
                      ·
                        rfl

theorem cell23_3275561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 7, 2].length) (baseStart_3275561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275561 prefixEnd_3275561 := by exact prefixLift 3275561
  have htrace : WordTrace (prefixWord ++ tailWord_3275561) baseStart_3275561 baseEnd_3275561 := by
    simpa [prefixWord, tailWord_3275561, baseEnd_3275561] using wordTrace_append hprefix tailTrace_3275561
  have hstable : (prefixWord ++ tailWord_3275561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275561).length < 2 ^ (prefixWord ++ tailWord_3275561).sum := by decide
  have hdescent : baseEnd_3275561 < baseStart_3275561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275572 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_3275572 : Nat := 118140960795 + 3275572 * 2 ^ 59
def prefixEnd_3275572 : Nat := 4983230072969 + 3 ^ 40 * 3275572 * 2
def baseEnd_3275572 : Nat := 1681942854409163543185925

theorem tailTrace_3275572 : CollatzResearch.WordTrace tailWord_3275572 prefixEnd_3275572 1681942854409163543185925 := by
  unfold tailWord_3275572
  simp only [CollatzResearch.WordTrace]
  refine ⟨59734962844584771002378485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79646617126113028003171313 59734962844584771002378485)
  ·
    refine ⟨5600152766679822281472983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59734962844584771002378485 5600152766679822281472983)
    ·
      refine ⟨8400229150019733422209475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5600152766679822281472983 8400229150019733422209475)
      ·
        refine ⟨12600343725029600133314213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8400229150019733422209475 12600343725029600133314213)
        ·
          refine ⟨2362564448443050024996415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12600343725029600133314213 2362564448443050024996415)
          ·
            refine ⟨3543846672664575037494623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2362564448443050024996415 3543846672664575037494623)
            ·
              refine ⟨5315770008996862556241935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543846672664575037494623 5315770008996862556241935)
              ·
                refine ⟨7973655013495293834362903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5315770008996862556241935 7973655013495293834362903)
                ·
                  refine ⟨11960482520242940751544355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7973655013495293834362903 11960482520242940751544355)
                  ·
                    refine ⟨17940723780364411127316533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11960482520242940751544355 17940723780364411127316533)
                    ·
                      refine ⟨1681942854409163543185925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17940723780364411127316533 1681942854409163543185925)
                      ·
                        rfl

theorem cell23_3275572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_3275572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275572 prefixEnd_3275572 := by exact prefixLift 3275572
  have htrace : WordTrace (prefixWord ++ tailWord_3275572) baseStart_3275572 baseEnd_3275572 := by
    simpa [prefixWord, tailWord_3275572, baseEnd_3275572] using wordTrace_append hprefix tailTrace_3275572
  have hstable : (prefixWord ++ tailWord_3275572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275572).length < 2 ^ (prefixWord ++ tailWord_3275572).sum := by decide
  have hdescent : baseEnd_3275572 < baseStart_3275572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275584 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 3, 8]
def baseStart_3275584 : Nat := 118140960795 + 3275584 * 2 ^ 59
def prefixEnd_3275584 : Nat := 4983230072969 + 3 ^ 40 * 3275584 * 2
def baseEnd_3275584 : Nat := 560649672059005832078623

theorem tailTrace_3275584 : CollatzResearch.WordTrace tailWord_3275584 prefixEnd_3275584 560649672059005832078623 := by
  unfold tailWord_3275584
  simp only [CollatzResearch.WordTrace]
  refine ⟨59735181682563034027096903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79646908910084045369462537 59735181682563034027096903)
  ·
    refine ⟨89602772523844551040645355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59735181682563034027096903 89602772523844551040645355)
    ·
      refine ⟨134404158785766826560968033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89602772523844551040645355 134404158785766826560968033)
      ·
        refine ⟨100803119089325119920726025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134404158785766826560968033 100803119089325119920726025)
        ·
          refine ⟨75602339316993839940544519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100803119089325119920726025 75602339316993839940544519)
          ·
            refine ⟨113403508975490759910816779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75602339316993839940544519 113403508975490759910816779)
            ·
              refine ⟨170105263463236139866225169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113403508975490759910816779 170105263463236139866225169)
              ·
                refine ⟨127578947597427104899668877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170105263463236139866225169 127578947597427104899668877)
                ·
                  refine ⟨47842105349035164337375829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127578947597427104899668877 47842105349035164337375829)
                  ·
                    refine ⟨560649672059005832078623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47842105349035164337375829 560649672059005832078623)
                    ·
                      rfl

theorem cell23_3275584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_3275584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275584 prefixEnd_3275584 := by exact prefixLift 3275584
  have htrace : WordTrace (prefixWord ++ tailWord_3275584) baseStart_3275584 baseEnd_3275584 := by
    simpa [prefixWord, tailWord_3275584, baseEnd_3275584] using wordTrace_append hprefix tailTrace_3275584
  have hstable : (prefixWord ++ tailWord_3275584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275584).length < 2 ^ (prefixWord ++ tailWord_3275584).sum := by decide
  have hdescent : baseEnd_3275584 < baseStart_3275584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275682 : List Nat := [3, 3, 1, 2, 2, 3, 1, 3, 5]
def baseStart_3275682 : Nat := 118140960795 + 3275682 * 2 ^ 59
def prefixEnd_3275682 : Nat := 4983230072969 + 3 ^ 40 * 3275682 * 2
def baseEnd_3275682 : Nat := 186888815253462012534491

theorem tailTrace_3275682 : CollatzResearch.WordTrace tailWord_3275682 prefixEnd_3275682 186888815253462012534491 := by
  unfold tailWord_3275682
  simp only [CollatzResearch.WordTrace]
  refine ⟨29868484429692757697815325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79649291812514020527507533 29868484429692757697815325)
  ·
    refine ⟨11200681661134784136680747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29868484429692757697815325 11200681661134784136680747)
    ·
      refine ⟨16801022491702176205021121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11200681661134784136680747 16801022491702176205021121)
      ·
        refine ⟨12600766868776632153765841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16801022491702176205021121 12600766868776632153765841)
        ·
          refine ⟨9450575151582474115324381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12600766868776632153765841 9450575151582474115324381)
          ·
            refine ⟨3543965681843427793246643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9450575151582474115324381 3543965681843427793246643)
            ·
              refine ⟨5315948522765141689869965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543965681843427793246643 5315948522765141689869965)
              ·
                refine ⟨1993480696036928133701237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5315948522765141689869965 1993480696036928133701237)
                ·
                  refine ⟨186888815253462012534491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1993480696036928133701237 186888815253462012534491)
                  ·
                    rfl

theorem cell23_3275682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_3275682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275682 prefixEnd_3275682 := by exact prefixLift 3275682
  have htrace : WordTrace (prefixWord ++ tailWord_3275682) baseStart_3275682 baseEnd_3275682 := by
    simpa [prefixWord, tailWord_3275682, baseEnd_3275682] using wordTrace_append hprefix tailTrace_3275682
  have hstable : (prefixWord ++ tailWord_3275682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275682).length < 2 ^ (prefixWord ++ tailWord_3275682).sum := by decide
  have hdescent : baseEnd_3275682 < baseStart_3275682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275711 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 4]
def baseStart_3275711 : Nat := 118140960795 + 3275711 * 2 ^ 59
def prefixEnd_3275711 : Nat := 4983230072969 + 3 ^ 40 * 3275711 * 2
def baseEnd_3275711 : Nat := 1682014228220138499347785

theorem tailTrace_3275711 : CollatzResearch.WordTrace tailWord_3275711 prefixEnd_3275711 1682014228220138499347785 := by
  unfold tailWord_3275711
  simp only [CollatzResearch.WordTrace]
  refine ⟨119474995435665968744066987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79649996957110645829377991 119474995435665968744066987)
  ·
    refine ⟨179212493153498953116100481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119474995435665968744066987 179212493153498953116100481)
    ·
      refine ⟨134409369865124214837075361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179212493153498953116100481 134409369865124214837075361)
      ·
        refine ⟨100807027398843161127806521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134409369865124214837075361 100807027398843161127806521)
        ·
          refine ⟨75605270549132370845854891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100807027398843161127806521 75605270549132370845854891)
          ·
            refine ⟨113407905823698556268782337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75605270549132370845854891 113407905823698556268782337)
            ·
              refine ⟨85055929367773917201586753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113407905823698556268782337 85055929367773917201586753)
              ·
                refine ⟨63791947025830437901190065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85055929367773917201586753 63791947025830437901190065)
                ·
                  refine ⟨47843960269372828425892549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63791947025830437901190065 47843960269372828425892549)
                  ·
                    refine ⟨8970742550507405329854853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47843960269372828425892549 8970742550507405329854853)
                    ·
                      refine ⟨1682014228220138499347785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8970742550507405329854853 1682014228220138499347785)
                      ·
                        rfl

theorem cell23_3275711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_3275711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275711 prefixEnd_3275711 := by exact prefixLift 3275711
  have htrace : WordTrace (prefixWord ++ tailWord_3275711) baseStart_3275711 baseEnd_3275711 := by
    simpa [prefixWord, tailWord_3275711, baseEnd_3275711] using wordTrace_append hprefix tailTrace_3275711
  have hstable : (prefixWord ++ tailWord_3275711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275711).length < 2 ^ (prefixWord ++ tailWord_3275711).sum := by decide
  have hdescent : baseEnd_3275711 < baseStart_3275711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275759 : List Nat := [1, 1, 2, 1, 4, 5, 2, 2, 1, 4]
def baseStart_3275759 : Nat := 118140960795 + 3275759 * 2 ^ 59
def prefixEnd_3275759 : Nat := 4983230072969 + 3 ^ 40 * 3275759 * 2
def baseEnd_3275759 : Nat := 560679625097184770515855

theorem tailTrace_3275759 : CollatzResearch.WordTrace tailWord_3275759 prefixEnd_3275759 560679625097184770515855 := by
  unfold tailWord_3275759
  simp only [CollatzResearch.WordTrace]
  refine ⟨119476746139492072941814331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79651164092994715294542887 119476746139492072941814331)
  ·
    refine ⟨179215119209238109412721497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119476746139492072941814331 179215119209238109412721497)
    ·
      refine ⟨134411339406928582059541123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179215119209238109412721497 134411339406928582059541123)
      ·
        refine ⟨201617009110392873089311685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134411339406928582059541123 201617009110392873089311685)
        ·
          refine ⟨37803189208198663704245941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201617009110392873089311685 37803189208198663704245941)
          ·
            refine ⟨3544048988268624722273057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37803189208198663704245941 3544048988268624722273057)
            ·
              refine ⟨2658036741201468541704793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3544048988268624722273057 2658036741201468541704793)
              ·
                refine ⟨1993527555901101406278595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2658036741201468541704793 1993527555901101406278595)
                ·
                  refine ⟨2990291333851652109417893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993527555901101406278595 2990291333851652109417893)
                  ·
                    refine ⟨560679625097184770515855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2990291333851652109417893 560679625097184770515855)
                    ·
                      rfl

theorem cell23_3275759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 1, 4].length) (baseStart_3275759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275759 prefixEnd_3275759 := by exact prefixLift 3275759
  have htrace : WordTrace (prefixWord ++ tailWord_3275759) baseStart_3275759 baseEnd_3275759 := by
    simpa [prefixWord, tailWord_3275759, baseEnd_3275759] using wordTrace_append hprefix tailTrace_3275759
  have hstable : (prefixWord ++ tailWord_3275759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275759).length < 2 ^ (prefixWord ++ tailWord_3275759).sum := by decide
  have hdescent : baseEnd_3275759 < baseStart_3275759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275799 : List Nat := [1, 1, 3, 5, 1, 1, 1, 5, 1, 1, 3]
def baseStart_3275799 : Nat := 118140960795 + 3275799 * 2 ^ 59
def prefixEnd_3275799 : Nat := 4983230072969 + 3 ^ 40 * 3275799 * 2
def baseEnd_3275799 : Nat := 1682059414517734155047381

theorem tailTrace_3275799 : CollatzResearch.WordTrace tailWord_3275799 prefixEnd_3275799 1682059414517734155047381 := by
  unfold tailWord_3275799
  simp only [CollatzResearch.WordTrace]
  refine ⟨119478205059347159773270451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79652136706231439848846967 119478205059347159773270451)
  ·
    refine ⟨179217307589020739659905677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119478205059347159773270451 179217307589020739659905677)
    ·
      refine ⟨67206490345882777372464629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179217307589020739659905677 67206490345882777372464629)
      ·
        refine ⟨6300608469926510378668559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67206490345882777372464629 6300608469926510378668559)
        ·
          refine ⟨9450912704889765568002839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6300608469926510378668559 9450912704889765568002839)
          ·
            refine ⟨14176369057334648352004259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9450912704889765568002839 14176369057334648352004259)
            ·
              refine ⟨21264553586001972528006389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14176369057334648352004259 21264553586001972528006389)
              ·
                refine ⟨1993551898687684924500599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21264553586001972528006389 1993551898687684924500599)
                ·
                  refine ⟨2990327848031527386750899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993551898687684924500599 2990327848031527386750899)
                  ·
                    refine ⟨4485491772047291080126349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2990327848031527386750899 4485491772047291080126349)
                    ·
                      refine ⟨1682059414517734155047381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4485491772047291080126349 1682059414517734155047381)
                      ·
                        rfl

theorem cell23_3275799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_3275799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275799 prefixEnd_3275799 := by exact prefixLift 3275799
  have htrace : WordTrace (prefixWord ++ tailWord_3275799) baseStart_3275799 baseEnd_3275799 := by
    simpa [prefixWord, tailWord_3275799, baseEnd_3275799] using wordTrace_append hprefix tailTrace_3275799
  have hstable : (prefixWord ++ tailWord_3275799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275799).length < 2 ^ (prefixWord ++ tailWord_3275799).sum := by decide
  have hdescent : baseEnd_3275799 < baseStart_3275799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275872 : List Nat := [2, 1, 1, 3, 2, 2, 2, 4, 2, 1, 3]
def baseStart_3275872 : Nat := 118140960795 + 3275872 * 2 ^ 59
def prefixEnd_3275872 : Nat := 4983230072969 + 3 ^ 40 * 3275872 * 2
def baseEnd_3275872 : Nat := 1682096898605512369434545

theorem tailTrace_3275872 : CollatzResearch.WordTrace tailWord_3275872 prefixEnd_3275872 1682096898605512369434545 := by
  unfold tailWord_3275872
  simp only [CollatzResearch.WordTrace]
  refine ⟨59740433794041346620338935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79653911725388462160451913 59740433794041346620338935)
  ·
    refine ⟨89610650691062019930508403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59740433794041346620338935 89610650691062019930508403)
    ·
      refine ⟨134415976036593029895762605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89610650691062019930508403 134415976036593029895762605)
      ·
        refine ⟨50405991013722386210910977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134415976036593029895762605 50405991013722386210910977)
        ·
          refine ⟨37804493260291789658183233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50405991013722386210910977 37804493260291789658183233)
          ·
            refine ⟨28353369945218842243637425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37804493260291789658183233 28353369945218842243637425)
            ·
              refine ⟨21265027458914131682728069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28353369945218842243637425 21265027458914131682728069)
              ·
                refine ⟨3987192648546399690511513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21265027458914131682728069 3987192648546399690511513)
                ·
                  refine ⟨2990394486409799767883635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3987192648546399690511513 2990394486409799767883635)
                  ·
                    refine ⟨4485591729614699651825453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2990394486409799767883635 4485591729614699651825453)
                    ·
                      refine ⟨1682096898605512369434545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4485591729614699651825453 1682096898605512369434545)
                      ·
                        rfl

theorem cell23_3275872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_3275872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275872 prefixEnd_3275872 := by exact prefixLift 3275872
  have htrace : WordTrace (prefixWord ++ tailWord_3275872) baseStart_3275872 baseEnd_3275872 := by
    simpa [prefixWord, tailWord_3275872, baseEnd_3275872] using wordTrace_append hprefix tailTrace_3275872
  have hstable : (prefixWord ++ tailWord_3275872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275872).length < 2 ^ (prefixWord ++ tailWord_3275872).sum := by decide
  have hdescent : baseEnd_3275872 < baseStart_3275872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275888 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 1, 8]
def baseStart_3275888 : Nat := 118140960795 + 3275888 * 2 ^ 59
def prefixEnd_3275888 : Nat := 4983230072969 + 3 ^ 40 * 3275888 * 2
def baseEnd_3275888 : Nat := 560701704765328102278157

theorem tailTrace_3275888 : CollatzResearch.WordTrace tailWord_3275888 prefixEnd_3275888 560701704765328102278157 := by
  unfold tailWord_3275888
  simp only [CollatzResearch.WordTrace]
  refine ⟨59740725578012363986630159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79654300770683151982173545 59740725578012363986630159)
  ·
    refine ⟨89611088367018545979945239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59740725578012363986630159 89611088367018545979945239)
    ·
      refine ⟨134416632550527818969917859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89611088367018545979945239 134416632550527818969917859)
      ·
        refine ⟨201624948825791728454876789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134416632550527818969917859 201624948825791728454876789)
        ·
          refine ⟨18902338952417974542644699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201624948825791728454876789 18902338952417974542644699)
          ·
            refine ⟨28353508428626961813967049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18902338952417974542644699 28353508428626961813967049)
            ·
              refine ⟨21265131321470221360475287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28353508428626961813967049 21265131321470221360475287)
              ·
                refine ⟨31897696982205332040712931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21265131321470221360475287 31897696982205332040712931)
                ·
                  refine ⟨47846545473307998061069397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31897696982205332040712931 47846545473307998061069397)
                  ·
                    refine ⟨560701704765328102278157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47846545473307998061069397 560701704765328102278157)
                    ·
                      rfl

theorem cell23_3275888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_3275888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275888 prefixEnd_3275888 := by exact prefixLift 3275888
  have htrace : WordTrace (prefixWord ++ tailWord_3275888) baseStart_3275888 baseEnd_3275888 := by
    simpa [prefixWord, tailWord_3275888, baseEnd_3275888] using wordTrace_append hprefix tailTrace_3275888
  have hstable : (prefixWord ++ tailWord_3275888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275888).length < 2 ^ (prefixWord ++ tailWord_3275888).sum := by decide
  have hdescent : baseEnd_3275888 < baseStart_3275888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275893 : List Nat := [1, 3, 4, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3275893 : Nat := 118140960795 + 3275893 * 2 ^ 59
def prefixEnd_3275893 : Nat := 4983230072969 + 3 ^ 40 * 3275893 * 2
def baseEnd_3275893 : Nat := 1682107681699256787271949

theorem tailTrace_3275893 : CollatzResearch.WordTrace tailWord_3275893 prefixEnd_3275893 1682107681699256787271949 := by
  unfold tailWord_3275893
  simp only [CollatzResearch.WordTrace]
  refine ⟨119481633521006613827192333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79654422347337742551461555 119481633521006613827192333)
  ·
    refine ⟨44805612570377480185197125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119481633521006613827192333 44805612570377480185197125)
    ·
      refine ⟨8401052356945777534724461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44805612570377480185197125 8401052356945777534724461)
      ·
        refine ⟨3150394633854666575521673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8401052356945777534724461 3150394633854666575521673)
        ·
          refine ⟨2362795975390999931641255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3150394633854666575521673 2362795975390999931641255)
          ·
            refine ⟨3544193963086499897461883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2362795975390999931641255 3544193963086499897461883)
            ·
              refine ⟨5316290944629749846192825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3544193963086499897461883 5316290944629749846192825)
              ·
                refine ⟨3987218208472312384644619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5316290944629749846192825 3987218208472312384644619)
                ·
                  refine ⟨5980827312708468576966929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987218208472312384644619 5980827312708468576966929)
                  ·
                    refine ⟨4485620484531351432725197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5980827312708468576966929 4485620484531351432725197)
                    ·
                      refine ⟨1682107681699256787271949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4485620484531351432725197 1682107681699256787271949)
                      ·
                        rfl

theorem cell23_3275893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3275893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275893 prefixEnd_3275893 := by exact prefixLift 3275893
  have htrace : WordTrace (prefixWord ++ tailWord_3275893) baseStart_3275893 baseEnd_3275893 := by
    simpa [prefixWord, tailWord_3275893, baseEnd_3275893] using wordTrace_append hprefix tailTrace_3275893
  have hstable : (prefixWord ++ tailWord_3275893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275893).length < 2 ^ (prefixWord ++ tailWord_3275893).sum := by decide
  have hdescent : baseEnd_3275893 < baseStart_3275893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275946 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_3275946 : Nat := 118140960795 + 3275946 * 2 ^ 59
def prefixEnd_3275946 : Nat := 4983230072969 + 3 ^ 40 * 3275946 * 2
def baseEnd_3275946 : Nat := 1682134896173945079909205

theorem tailTrace_3275946 : CollatzResearch.WordTrace tailWord_3275946 prefixEnd_3275946 1682134896173945079909205 := by
  unfold tailWord_3275946
  simp only [CollatzResearch.WordTrace]
  refine ⟨29870891647453650969717923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79655711059876402585914461 29870891647453650969717923)
  ·
    refine ⟨44806337471180476454576885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29870891647453650969717923 44806337471180476454576885)
    ·
      refine ⟨4200594137923169667616583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44806337471180476454576885 4200594137923169667616583)
      ·
        refine ⟨6300891206884754501424875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4200594137923169667616583 6300891206884754501424875)
        ·
          refine ⟨9451336810327131752137313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6300891206884754501424875 9451336810327131752137313)
          ·
            refine ⟨7088502607745348814102985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9451336810327131752137313 7088502607745348814102985)
            ·
              refine ⟨5316376955809011610577239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7088502607745348814102985 5316376955809011610577239)
              ·
                refine ⟨7974565433713517415865859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5316376955809011610577239 7974565433713517415865859)
                ·
                  refine ⟨11961848150570276123798789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7974565433713517415865859 11961848150570276123798789)
                  ·
                    refine ⟨2242846528231926773212273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11961848150570276123798789 2242846528231926773212273)
                    ·
                      refine ⟨1682134896173945079909205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2242846528231926773212273 1682134896173945079909205)
                      ·
                        rfl

theorem cell23_3275946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_3275946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275946 prefixEnd_3275946 := by exact prefixLift 3275946
  have htrace : WordTrace (prefixWord ++ tailWord_3275946) baseStart_3275946 baseEnd_3275946 := by
    simpa [prefixWord, tailWord_3275946, baseEnd_3275946] using wordTrace_append hprefix tailTrace_3275946
  have hstable : (prefixWord ++ tailWord_3275946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275946).length < 2 ^ (prefixWord ++ tailWord_3275946).sum := by decide
  have hdescent : baseEnd_3275946 < baseStart_3275946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275969 : List Nat := [1, 2, 6, 1, 1, 1, 1, 5, 5]
def baseStart_3275969 : Nat := 118140960795 + 3275969 * 2 ^ 59
def prefixEnd_3275969 : Nat := 4983230072969 + 3 ^ 40 * 3275969 * 2
def baseEnd_3275969 : Nat := 186905189580999832213511

theorem tailTrace_3275969 : CollatzResearch.WordTrace tailWord_3275969 prefixEnd_3275969 186905189580999832213511 := by
  unfold tailWord_3275969
  simp only [CollatzResearch.WordTrace]
  refine ⟨119484405468731278806958961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79656270312487519204639307 119484405468731278806958961)
  ·
    refine ⟨89613304101548459105219221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119484405468731278806958961 89613304101548459105219221)
    ·
      refine ⟨4200623629760084020557151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89613304101548459105219221 4200623629760084020557151)
      ·
        refine ⟨6300935444640126030835727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4200623629760084020557151 6300935444640126030835727)
        ·
          refine ⟨9451403166960189046253591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6300935444640126030835727 9451403166960189046253591)
          ·
            refine ⟨14177104750440283569380387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9451403166960189046253591 14177104750440283569380387)
            ·
              refine ⟨21265657125660425354070581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14177104750440283569380387 21265657125660425354070581)
              ·
                refine ⟨1993655355530664876944117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21265657125660425354070581 1993655355530664876944117)
                ·
                  refine ⟨186905189580999832213511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1993655355530664876944117 186905189580999832213511)
                  ·
                    rfl

theorem cell23_3275969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 5].length) (baseStart_3275969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275969 prefixEnd_3275969 := by exact prefixLift 3275969
  have htrace : WordTrace (prefixWord ++ tailWord_3275969) baseStart_3275969 baseEnd_3275969 := by
    simpa [prefixWord, tailWord_3275969, baseEnd_3275969] using wordTrace_append hprefix tailTrace_3275969
  have hstable : (prefixWord ++ tailWord_3275969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275969).length < 2 ^ (prefixWord ++ tailWord_3275969).sum := by decide
  have hdescent : baseEnd_3275969 < baseStart_3275969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3275985 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 4, 1, 4]
def baseStart_3275985 : Nat := 118140960795 + 3275985 * 2 ^ 59
def prefixEnd_3275985 : Nat := 4983230072969 + 3 ^ 40 * 3275985 * 2
def baseEnd_3275985 : Nat := 1682154921919470427321525

theorem tailTrace_3275985 : CollatzResearch.WordTrace tailWord_3275985 prefixEnd_3275985 1682154921919470427321525 := by
  unfold tailWord_3275985
  simp only [CollatzResearch.WordTrace]
  refine ⟨119484989036673313539541409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79656659357782209026360939 119484989036673313539541409)
  ·
    refine ⟨89613741777504985154656057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119484989036673313539541409 89613741777504985154656057)
    ·
      refine ⟨67210306333128738865992043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89613741777504985154656057 67210306333128738865992043)
      ·
        refine ⟨100815459499693108298988065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67210306333128738865992043 100815459499693108298988065)
        ·
          refine ⟨75611594624769831224241049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100815459499693108298988065 75611594624769831224241049)
          ·
            refine ⟨56708695968577373418180787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75611594624769831224241049 56708695968577373418180787)
            ·
              refine ⟨85063043952866060127271181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56708695968577373418180787 85063043952866060127271181)
              ·
                refine ⟨31898641482324772547726693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85063043952866060127271181 31898641482324772547726693)
                ·
                  refine ⟨5980995277935894852698755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31898641482324772547726693 5980995277935894852698755)
                  ·
                    refine ⟨8971492916903842279048133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5980995277935894852698755 8971492916903842279048133)
                    ·
                      refine ⟨1682154921919470427321525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8971492916903842279048133 1682154921919470427321525)
                      ·
                        rfl

theorem cell23_3275985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_3275985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3275985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3275985 prefixEnd_3275985 := by exact prefixLift 3275985
  have htrace : WordTrace (prefixWord ++ tailWord_3275985) baseStart_3275985 baseEnd_3275985 := by
    simpa [prefixWord, tailWord_3275985, baseEnd_3275985] using wordTrace_append hprefix tailTrace_3275985
  have hstable : (prefixWord ++ tailWord_3275985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3275985).length < 2 ^ (prefixWord ++ tailWord_3275985).sum := by decide
  have hdescent : baseEnd_3275985 < baseStart_3275985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3275985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276012 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 3, 4]
def baseStart_3276012 : Nat := 118140960795 + 3276012 * 2 ^ 59
def prefixEnd_3276012 : Nat := 4983230072969 + 3 ^ 40 * 3276012 * 2
def baseEnd_3276012 : Nat := 560722928632380607227967

theorem tailTrace_3276012 : CollatzResearch.WordTrace tailWord_3276012 prefixEnd_3276012 560722928632380607227967 := by
  unfold tailWord_3276012
  simp only [CollatzResearch.WordTrace]
  refine ⟨59742986903787748575387145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79657315871716998100516193 59742986903787748575387145)
  ·
    refine ⟨44807240177840811431540359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59742986903787748575387145 44807240177840811431540359)
    ·
      refine ⟨67210860266761217147310539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44807240177840811431540359 67210860266761217147310539)
      ·
        refine ⟨100816290400141825720965809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67210860266761217147310539 100816290400141825720965809)
        ·
          refine ⟨75612217800106369290724357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100816290400141825720965809 75612217800106369290724357)
          ·
            refine ⟨14177290837519944242010817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75612217800106369290724357 14177290837519944242010817)
            ·
              refine ⟨10632968128139958181508113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14177290837519944242010817 10632968128139958181508113)
              ·
                refine ⟨7974726096104968636131085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10632968128139958181508113 7974726096104968636131085)
                ·
                  refine ⟨2990522286039363238549157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7974726096104968636131085 2990522286039363238549157)
                  ·
                    refine ⟨560722928632380607227967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2990522286039363238549157 560722928632380607227967)
                    ·
                      rfl

theorem cell23_3276012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_3276012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276012 prefixEnd_3276012 := by exact prefixLift 3276012
  have htrace : WordTrace (prefixWord ++ tailWord_3276012) baseStart_3276012 baseEnd_3276012 := by
    simpa [prefixWord, tailWord_3276012, baseEnd_3276012] using wordTrace_append hprefix tailTrace_3276012
  have hstable : (prefixWord ++ tailWord_3276012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276012).length < 2 ^ (prefixWord ++ tailWord_3276012).sum := by decide
  have hdescent : baseEnd_3276012 < baseStart_3276012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276020 : List Nat := [2, 6, 1, 2, 1, 2, 1, 3, 5]
def baseStart_3276020 : Nat := 118140960795 + 3276020 * 2 ^ 59
def prefixEnd_3276020 : Nat := 4983230072969 + 3 ^ 40 * 3276020 * 2
def baseEnd_3276020 : Nat := 186908099304708643375985

theorem tailTrace_3276020 : CollatzResearch.WordTrace tailWord_3276020 prefixEnd_3276020 186908099304708643375985 := by
  unfold tailWord_3276020
  simp only [CollatzResearch.WordTrace]
  refine ⟨59743132795773257258532757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79657510394364343011377009 59743132795773257258532757)
  ·
    refine ⟨2800459349801871433993723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59743132795773257258532757 2800459349801871433993723)
    ·
      refine ⟨4200689024702807150990585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2800459349801871433993723 4200689024702807150990585)
      ·
        refine ⟨3150516768527105363242939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4200689024702807150990585 3150516768527105363242939)
        ·
          refine ⟨4725775152790658044864409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3150516768527105363242939 4725775152790658044864409)
          ·
            refine ⟨3544331364592993533648307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4725775152790658044864409 3544331364592993533648307)
            ·
              refine ⟨5316497046889490300472461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3544331364592993533648307 5316497046889490300472461)
              ·
                refine ⟨1993686392583558862677173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5316497046889490300472461 1993686392583558862677173)
                ·
                  refine ⟨186908099304708643375985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1993686392583558862677173 186908099304708643375985)
                  ·
                    rfl

theorem cell23_3276020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_3276020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276020 prefixEnd_3276020 := by exact prefixLift 3276020
  have htrace : WordTrace (prefixWord ++ tailWord_3276020) baseStart_3276020 baseEnd_3276020 := by
    simpa [prefixWord, tailWord_3276020, baseEnd_3276020] using wordTrace_append hprefix tailTrace_3276020
  have hstable : (prefixWord ++ tailWord_3276020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276020).length < 2 ^ (prefixWord ++ tailWord_3276020).sum := by decide
  have hdescent : baseEnd_3276020 < baseStart_3276020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276103 : List Nat := [1, 1, 4, 1, 2, 3, 4, 2, 1, 1, 3]
def baseStart_3276103 : Nat := 118140960795 + 3276103 * 2 ^ 59
def prefixEnd_3276103 : Nat := 4983230072969 + 3 ^ 40 * 3276103 * 2
def baseEnd_3276103 : Nat := 1682215512636700965645983

theorem tailTrace_3276103 : CollatzResearch.WordTrace tailWord_3276103 prefixEnd_3276103 1682215512636700965645983 := by
  unfold tailWord_3276103
  simp only [CollatzResearch.WordTrace]
  refine ⟨119489292850245819692336963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79659528566830546461557975 119489292850245819692336963)
  ·
    refine ⟨179233939275368729538505445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119489292850245819692336963 179233939275368729538505445)
    ·
      refine ⟨33606363614131636788469771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179233939275368729538505445 33606363614131636788469771)
      ·
        refine ⟨50409545421197455182704657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33606363614131636788469771 50409545421197455182704657)
        ·
          refine ⟨37807159065898091387028493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50409545421197455182704657 37807159065898091387028493)
          ·
            refine ⟨14177684649711784270135685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37807159065898091387028493 14177684649711784270135685)
            ·
              refine ⟨2658315871820959550650441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14177684649711784270135685 2658315871820959550650441)
              ·
                refine ⟨1993736903865719662987831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2658315871820959550650441 1993736903865719662987831)
                ·
                  refine ⟨2990605355798579494481747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993736903865719662987831 2990605355798579494481747)
                  ·
                    refine ⟨4485908033697869241722621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2990605355798579494481747 4485908033697869241722621)
                    ·
                      refine ⟨1682215512636700965645983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4485908033697869241722621 1682215512636700965645983)
                      ·
                        rfl

theorem cell23_3276103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_3276103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276103 prefixEnd_3276103 := by exact prefixLift 3276103
  have htrace : WordTrace (prefixWord ++ tailWord_3276103) baseStart_3276103 baseEnd_3276103 := by
    simpa [prefixWord, tailWord_3276103, baseEnd_3276103] using wordTrace_append hprefix tailTrace_3276103
  have hstable : (prefixWord ++ tailWord_3276103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276103).length < 2 ^ (prefixWord ++ tailWord_3276103).sum := by decide
  have hdescent : baseEnd_3276103 < baseStart_3276103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276105 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 6]
def baseStart_3276105 : Nat := 118140960795 + 3276105 * 2 ^ 59
def prefixEnd_3276105 : Nat := 4983230072969 + 3 ^ 40 * 3276105 * 2
def baseEnd_3276105 : Nat := 1682216539598009957820973

theorem tailTrace_3276105 : CollatzResearch.WordTrace tailWord_3276105 prefixEnd_3276105 1682216539598009957820973 := by
  unfold tailWord_3276105
  simp only [CollatzResearch.WordTrace]
  refine ⟨119489365796238574033909769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79659577197492382689273179 119489365796238574033909769)
  ·
    refine ⟨89617024347178930525432327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119489365796238574033909769 89617024347178930525432327)
    ·
      refine ⟨134425536520768395788148491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89617024347178930525432327 134425536520768395788148491)
      ·
        refine ⟨201638304781152593682222737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134425536520768395788148491 201638304781152593682222737)
        ·
          refine ⟨151228728585864445261667053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201638304781152593682222737 151228728585864445261667053)
          ·
            refine ⟨56710773219699166973125145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151228728585864445261667053 56710773219699166973125145)
            ·
              refine ⟨42533079914774375229843859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56710773219699166973125145 42533079914774375229843859)
              ·
                refine ⟨63799619872161562844765789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42533079914774375229843859 63799619872161562844765789)
                ·
                  refine ⟨23924857452060586066787171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63799619872161562844765789 23924857452060586066787171)
                  ·
                    refine ⟨35887286178090879100180757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23924857452060586066787171 35887286178090879100180757)
                    ·
                      refine ⟨1682216539598009957820973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35887286178090879100180757 1682216539598009957820973)
                      ·
                        rfl

theorem cell23_3276105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_3276105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276105 prefixEnd_3276105 := by exact prefixLift 3276105
  have htrace : WordTrace (prefixWord ++ tailWord_3276105) baseStart_3276105 baseEnd_3276105 := by
    simpa [prefixWord, tailWord_3276105, baseEnd_3276105] using wordTrace_append hprefix tailTrace_3276105
  have hstable : (prefixWord ++ tailWord_3276105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276105).length < 2 ^ (prefixWord ++ tailWord_3276105).sum := by decide
  have hdescent : baseEnd_3276105 < baseStart_3276105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276112 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 3]
def baseStart_3276112 : Nat := 118140960795 + 3276112 * 2 ^ 59
def prefixEnd_3276112 : Nat := 4983230072969 + 3 ^ 40 * 3276112 * 2
def baseEnd_3276112 : Nat := 1682220133962591430433441

theorem tailTrace_3276112 : CollatzResearch.WordTrace tailWord_3276112 prefixEnd_3276112 1682220133962591430433441 := by
  unfold tailWord_3276112
  simp only [CollatzResearch.WordTrace]
  refine ⟨59744810553606607114707295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79659747404808809486276393 59744810553606607114707295)
  ·
    refine ⟨89617215830409910672060943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59744810553606607114707295 89617215830409910672060943)
    ·
      refine ⟨134425823745614866008091415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89617215830409910672060943 134425823745614866008091415)
      ·
        refine ⟨201638735618422299012137123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134425823745614866008091415 201638735618422299012137123)
        ·
          refine ⟨302458103427633448518205685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201638735618422299012137123 302458103427633448518205685)
          ·
            refine ⟨28355447196340635798581783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 302458103427633448518205685 28355447196340635798581783)
            ·
              refine ⟨42533170794510953697872675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28355447196340635798581783 42533170794510953697872675)
              ·
                refine ⟨63799756191766430546809013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42533170794510953697872675 63799756191766430546809013)
                ·
                  refine ⟨5981227142978102863763345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63799756191766430546809013 5981227142978102863763345)
                  ·
                    refine ⟨4485920357233577147822509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5981227142978102863763345 4485920357233577147822509)
                    ·
                      refine ⟨1682220133962591430433441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4485920357233577147822509 1682220133962591430433441)
                      ·
                        rfl

theorem cell23_3276112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 3].length) (baseStart_3276112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276112 prefixEnd_3276112 := by exact prefixLift 3276112
  have htrace : WordTrace (prefixWord ++ tailWord_3276112) baseStart_3276112 baseEnd_3276112 := by
    simpa [prefixWord, tailWord_3276112, baseEnd_3276112] using wordTrace_append hprefix tailTrace_3276112
  have hstable : (prefixWord ++ tailWord_3276112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276112).length < 2 ^ (prefixWord ++ tailWord_3276112).sum := by decide
  have hdescent : baseEnd_3276112 < baseStart_3276112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276119 : List Nat := [1, 1, 3, 2, 3, 2, 2, 3, 2, 4]
def baseStart_3276119 : Nat := 118140960795 + 3276119 * 2 ^ 59
def prefixEnd_3276119 : Nat := 4983230072969 + 3 ^ 40 * 3276119 * 2
def baseEnd_3276119 : Nat := 560741242775724301015303

theorem tailTrace_3276119 : CollatzResearch.WordTrace tailWord_3276119 prefixEnd_3276119 560741242775724301015303 := by
  unfold tailWord_3276119
  simp only [CollatzResearch.WordTrace]
  refine ⟨119489876418187854424919411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79659917612125236283279607 119489876418187854424919411)
  ·
    refine ⟨179234814627281781637379117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119489876418187854424919411 179234814627281781637379117)
    ·
      refine ⟨67213055485230668114017169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179234814627281781637379117 67213055485230668114017169)
      ·
        refine ⟨50409791613923001085512877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67213055485230668114017169 50409791613923001085512877)
        ·
          refine ⟨18903671855221125407067329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50409791613923001085512877 18903671855221125407067329)
          ·
            refine ⟨14177753891415844055300497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18903671855221125407067329 14177753891415844055300497)
            ·
              refine ⟨10633315418561883041475373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14177753891415844055300497 10633315418561883041475373)
              ·
                refine ⟨3987493281960706140553265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10633315418561883041475373 3987493281960706140553265)
                ·
                  refine ⟨2990619961470529605414949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3987493281960706140553265 2990619961470529605414949)
                  ·
                    refine ⟨560741242775724301015303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2990619961470529605414949 560741242775724301015303)
                    ·
                      rfl

theorem cell23_3276119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_3276119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276119 prefixEnd_3276119 := by exact prefixLift 3276119
  have htrace : WordTrace (prefixWord ++ tailWord_3276119) baseStart_3276119 baseEnd_3276119 := by
    simpa [prefixWord, tailWord_3276119, baseEnd_3276119] using wordTrace_append hprefix tailTrace_3276119
  have hstable : (prefixWord ++ tailWord_3276119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276119).length < 2 ^ (prefixWord ++ tailWord_3276119).sum := by decide
  have hdescent : baseEnd_3276119 < baseStart_3276119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276122 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4]
def baseStart_3276122 : Nat := 118140960795 + 3276122 * 2 ^ 59
def prefixEnd_3276122 : Nat := 4983230072969 + 3 ^ 40 * 3276122 * 2
def baseEnd_3276122 : Nat := 1682225268769136391308395

theorem tailTrace_3276122 : CollatzResearch.WordTrace tailWord_3276122 prefixEnd_3276122 1682225268769136391308395 := by
  unfold tailWord_3276122
  simp only [CollatzResearch.WordTrace]
  refine ⟨29872496459294246484319655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79659990558117990624852413 29872496459294246484319655)
  ·
    refine ⟨44808744688941369726479483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29872496459294246484319655 44808744688941369726479483)
    ·
      refine ⟨67213117033412054589719225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44808744688941369726479483 67213117033412054589719225)
      ·
        refine ⟨50409837775059040942289419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67213117033412054589719225 50409837775059040942289419)
        ·
          refine ⟨75614756662588561413434129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50409837775059040942289419 75614756662588561413434129)
          ·
            refine ⟨56711067496941421060075597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75614756662588561413434129 56711067496941421060075597)
            ·
              refine ⟨21266650311353032897528349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56711067496941421060075597 21266650311353032897528349)
              ·
                refine ⟨7974993866757387336573131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21266650311353032897528349 7974993866757387336573131)
                ·
                  refine ⟨11962490800136081004859697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7974993866757387336573131 11962490800136081004859697)
                  ·
                    refine ⟨8971868100102060753644773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11962490800136081004859697 8971868100102060753644773)
                    ·
                      refine ⟨1682225268769136391308395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8971868100102060753644773 1682225268769136391308395)
                      ·
                        rfl

theorem cell23_3276122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_3276122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276122 prefixEnd_3276122 := by exact prefixLift 3276122
  have htrace : WordTrace (prefixWord ++ tailWord_3276122) baseStart_3276122 baseEnd_3276122 := by
    simpa [prefixWord, tailWord_3276122, baseEnd_3276122] using wordTrace_append hprefix tailTrace_3276122
  have hstable : (prefixWord ++ tailWord_3276122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276122).length < 2 ^ (prefixWord ++ tailWord_3276122).sum := by decide
  have hdescent : baseEnd_3276122 < baseStart_3276122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276143 : List Nat := [1, 1, 2, 1, 3, 1, 6, 3, 1, 2, 2]
def baseStart_3276143 : Nat := 118140960795 + 3276143 * 2 ^ 59
def prefixEnd_3276143 : Nat := 4983230072969 + 3 ^ 40 * 3276143 * 2
def baseEnd_3276143 : Nat := 1682236051862880809145799

theorem tailTrace_3276143 : CollatzResearch.WordTrace tailWord_3276143 prefixEnd_3276143 1682236051862880809145799 := by
  unfold tailWord_3276143
  simp only [CollatzResearch.WordTrace]
  refine ⟨119490751770100906523793083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79660501180067271015862055 119490751770100906523793083)
  ·
    refine ⟨179236127655151359785689625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119490751770100906523793083 179236127655151359785689625)
    ·
      refine ⟨134427095741363519839267219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179236127655151359785689625 134427095741363519839267219)
      ·
        refine ⟨201640643612045279758900829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134427095741363519839267219 201640643612045279758900829)
        ·
          refine ⟨75615241354516979909587811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201640643612045279758900829 75615241354516979909587811)
          ·
            refine ⟨113422862031775469864381717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75615241354516979909587811 113422862031775469864381717)
            ·
              refine ⟨5316696657739475149892893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 113422862031775469864381717 5316696657739475149892893)
              ·
                refine ⟨1993761246652303181209835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5316696657739475149892893 1993761246652303181209835)
                ·
                  refine ⟨2990641869978454771814753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1993761246652303181209835 2990641869978454771814753)
                  ·
                    refine ⟨2242981402483841078861065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2990641869978454771814753 2242981402483841078861065)
                    ·
                      refine ⟨1682236051862880809145799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2242981402483841078861065 1682236051862880809145799)
                      ·
                        rfl

theorem cell23_3276143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 1, 2, 2].length) (baseStart_3276143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276143 prefixEnd_3276143 := by exact prefixLift 3276143
  have htrace : WordTrace (prefixWord ++ tailWord_3276143) baseStart_3276143 baseEnd_3276143 := by
    simpa [prefixWord, tailWord_3276143, baseEnd_3276143] using wordTrace_append hprefix tailTrace_3276143
  have hstable : (prefixWord ++ tailWord_3276143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276143).length < 2 ^ (prefixWord ++ tailWord_3276143).sum := by decide
  have hdescent : baseEnd_3276143 < baseStart_3276143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276216 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 4, 2, 2]
def baseStart_3276216 : Nat := 118140960795 + 3276216 * 2 ^ 59
def prefixEnd_3276216 : Nat := 4983230072969 + 3 ^ 40 * 3276216 * 2
def baseEnd_3276216 : Nat := 1682273535950659023532963

theorem tailTrace_3276216 : CollatzResearch.WordTrace tailWord_3276216 prefixEnd_3276216 1682273535950659023532963 := by
  unfold tailWord_3276216
  simp only [CollatzResearch.WordTrace]
  refine ⟨59746707149418219995600251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79662276199224293327467001 59746707149418219995600251)
  ·
    refine ⟨89620060724127329993400377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59746707149418219995600251 89620060724127329993400377)
    ·
      refine ⟨67215045543095497495050283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89620060724127329993400377 67215045543095497495050283)
      ·
        refine ⟨100822568314643246242575425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67215045543095497495050283 100822568314643246242575425)
        ·
          refine ⟨75616926235982434681931569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100822568314643246242575425 75616926235982434681931569)
          ·
            refine ⟨56712694676986826011448677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75616926235982434681931569 56712694676986826011448677)
            ·
              refine ⟨10633630251935029877146627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56712694676986826011448677 10633630251935029877146627)
              ·
                refine ⟨15950445377902544815719941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10633630251935029877146627 15950445377902544815719941)
                ·
                  refine ⟨2990708508356727152947489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15950445377902544815719941 2990708508356727152947489)
                  ·
                    refine ⟨2243031381267545364710617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2990708508356727152947489 2243031381267545364710617)
                    ·
                      refine ⟨1682273535950659023532963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2243031381267545364710617 1682273535950659023532963)
                      ·
                        rfl

theorem cell23_3276216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 4, 2, 2].length) (baseStart_3276216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276216 prefixEnd_3276216 := by exact prefixLift 3276216
  have htrace : WordTrace (prefixWord ++ tailWord_3276216) baseStart_3276216 baseEnd_3276216 := by
    simpa [prefixWord, tailWord_3276216, baseEnd_3276216] using wordTrace_append hprefix tailTrace_3276216
  have hstable : (prefixWord ++ tailWord_3276216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276216).length < 2 ^ (prefixWord ++ tailWord_3276216).sum := by decide
  have hdescent : baseEnd_3276216 < baseStart_3276216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276273 : List Nat := [1, 2, 2, 2, 3, 4, 2, 2, 5]
def baseStart_3276273 : Nat := 118140960795 + 3276273 * 2 ^ 59
def prefixEnd_3276273 : Nat := 4983230072969 + 3 ^ 40 * 3276273 * 2
def baseEnd_3276273 : Nat := 186922533816440588946689

theorem tailTrace_3276273 : CollatzResearch.WordTrace tailWord_3276273 prefixEnd_3276273 186922533816440588946689 := by
  unfold tailWord_3276273
  simp only [CollatzResearch.WordTrace]
  refine ⟨119495493259629938726025473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79663662173086625817350315 119495493259629938726025473)
  ·
    refine ⟨89621619944722454044519105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119495493259629938726025473 89621619944722454044519105)
    ·
      refine ⟨67216214958541840533389329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89621619944722454044519105 67216214958541840533389329)
      ·
        refine ⟨50412161218906380400041997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67216214958541840533389329 50412161218906380400041997)
        ·
          refine ⟨18904560457089892650015749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50412161218906380400041997 18904560457089892650015749)
          ·
            refine ⟨3544605085704354871877953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18904560457089892650015749 3544605085704354871877953)
            ·
              refine ⟨2658453814278266153908465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3544605085704354871877953 2658453814278266153908465)
              ·
                refine ⟨1993840360708699615431349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2658453814278266153908465 1993840360708699615431349)
                ·
                  refine ⟨186922533816440588946689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1993840360708699615431349 186922533816440588946689)
                  ·
                    rfl

theorem cell23_3276273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 2, 5].length) (baseStart_3276273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276273 prefixEnd_3276273 := by exact prefixLift 3276273
  have htrace : WordTrace (prefixWord ++ tailWord_3276273) baseStart_3276273 baseEnd_3276273 := by
    simpa [prefixWord, tailWord_3276273, baseEnd_3276273] using wordTrace_append hprefix tailTrace_3276273
  have hstable : (prefixWord ++ tailWord_3276273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276273).length < 2 ^ (prefixWord ++ tailWord_3276273).sum := by decide
  have hdescent : baseEnd_3276273 < baseStart_3276273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276318 : List Nat := [4, 3, 3, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_3276318 : Nat := 118140960795 + 3276318 * 2 ^ 59
def prefixEnd_3276318 : Nat := 4983230072969 + 3 ^ 40 * 3276318 * 2
def baseEnd_3276318 : Nat := 1682325910977417624457495

theorem tailTrace_3276318 : CollatzResearch.WordTrace tailWord_3276318 prefixEnd_3276318 1682325910977417624457495 := by
  unfold tailWord_3276318
  simp only [CollatzResearch.WordTrace]
  refine ⟨14937141818058363926426701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79664756362977940940942405 14937141818058363926426701)
  ·
    refine ⟨5601428181771886472410013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14937141818058363926426701 5601428181771886472410013)
    ·
      refine ⟨2100535568164457427153755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5601428181771886472410013 2100535568164457427153755)
      ·
        refine ⟨3150803352246686140730633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2100535568164457427153755 3150803352246686140730633)
        ·
          refine ⟨2363102514185014605547975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3150803352246686140730633 2363102514185014605547975)
          ·
            refine ⟨3544653771277521908321963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2363102514185014605547975 3544653771277521908321963)
            ·
              refine ⟨5316980656916282862482945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3544653771277521908321963 5316980656916282862482945)
              ·
                refine ⟨3987735492687212146862209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5316980656916282862482945 3987735492687212146862209)
                ·
                  refine ⟨2990801619515409110146657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3987735492687212146862209 2990801619515409110146657)
                  ·
                    refine ⟨2243101214636556832609993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2990801619515409110146657 2243101214636556832609993)
                    ·
                      refine ⟨1682325910977417624457495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2243101214636556832609993 1682325910977417624457495)
                      ·
                        rfl

theorem cell23_3276318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_3276318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276318 prefixEnd_3276318 := by exact prefixLift 3276318
  have htrace : WordTrace (prefixWord ++ tailWord_3276318) baseStart_3276318 baseEnd_3276318 := by
    simpa [prefixWord, tailWord_3276318, baseEnd_3276318] using wordTrace_append hprefix tailTrace_3276318
  have hstable : (prefixWord ++ tailWord_3276318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276318).length < 2 ^ (prefixWord ++ tailWord_3276318).sum := by decide
  have hdescent : baseEnd_3276318 < baseStart_3276318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276346 : List Nat := [3, 1, 1, 1, 3, 2, 5, 1, 6]
def baseStart_3276346 : Nat := 118140960795 + 3276346 * 2 ^ 59
def prefixEnd_3276346 : Nat := 4983230072969 + 3 ^ 40 * 3276346 * 2
def baseEnd_3276346 : Nat := 186926698715082612767485

theorem tailTrace_3276346 : CollatzResearch.WordTrace tailWord_3276346 prefixEnd_3276346 186926698715082612767485 := by
  unfold tailWord_3276346
  simp only [CollatzResearch.WordTrace]
  refine ⟨29874538947091368048358223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79665437192243648128955261 29874538947091368048358223)
  ·
    refine ⟨44811808420637052072537335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29874538947091368048358223 44811808420637052072537335)
    ·
      refine ⟨67217712630955578108806003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44811808420637052072537335 67217712630955578108806003)
      ·
        refine ⟨100826568946433367163209005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67217712630955578108806003 100826568946433367163209005)
        ·
          refine ⟨37809963354912512686203377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100826568946433367163209005 37809963354912512686203377)
          ·
            refine ⟨28357472516184384514652533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37809963354912512686203377 28357472516184384514652533)
            ·
              refine ⟨2658513048392286048248675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28357472516184384514652533 2658513048392286048248675)
              ·
                refine ⟨3987769572588429072373013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2658513048392286048248675 3987769572588429072373013)
                ·
                  refine ⟨186926698715082612767485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3987769572588429072373013 186926698715082612767485)
                  ·
                    rfl

theorem cell23_3276346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 6].length) (baseStart_3276346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276346 prefixEnd_3276346 := by exact prefixLift 3276346
  have htrace : WordTrace (prefixWord ++ tailWord_3276346) baseStart_3276346 baseEnd_3276346 := by
    simpa [prefixWord, tailWord_3276346, baseEnd_3276346] using wordTrace_append hprefix tailTrace_3276346
  have hstable : (prefixWord ++ tailWord_3276346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276346).length < 2 ^ (prefixWord ++ tailWord_3276346).sum := by decide
  have hdescent : baseEnd_3276346 < baseStart_3276346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276399 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 3]
def baseStart_3276399 : Nat := 118140960795 + 3276399 * 2 ^ 59
def prefixEnd_3276399 : Nat := 4983230072969 + 3 ^ 40 * 3276399 * 2
def baseEnd_3276399 : Nat := 1682367502910431807544621

theorem tailTrace_3276399 : CollatzResearch.WordTrace tailWord_3276399 prefixEnd_3276399 1682367502910431807544621 := by
  unfold tailWord_3276399
  simp only [CollatzResearch.WordTrace]
  refine ⟨119500088857173462245112251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79666725904782308163408167 119500088857173462245112251)
  ·
    refine ⟨179250133285760193367668377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119500088857173462245112251 179250133285760193367668377)
    ·
      refine ⟨134437599964320145025751283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179250133285760193367668377 134437599964320145025751283)
      ·
        refine ⟨201656399946480217538626925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134437599964320145025751283 201656399946480217538626925)
        ·
          refine ⟨75621149979930081576985097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201656399946480217538626925 75621149979930081576985097)
          ·
            refine ⟨56715862484947561182738823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75621149979930081576985097 56715862484947561182738823)
            ·
              refine ⟨85073793727421341774108235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56715862484947561182738823 85073793727421341774108235)
              ·
                refine ⟨127610690591132012661162353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85073793727421341774108235 127610690591132012661162353)
                ·
                  refine ⟨95708017943349009495871765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127610690591132012661162353 95708017943349009495871765)
                  ·
                    refine ⟨4486313341094484820118989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95708017943349009495871765 4486313341094484820118989)
                    ·
                      refine ⟨1682367502910431807544621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4486313341094484820118989 1682367502910431807544621)
                      ·
                        rfl

theorem cell23_3276399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 6, 3].length) (baseStart_3276399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276399 prefixEnd_3276399 := by exact prefixLift 3276399
  have htrace : WordTrace (prefixWord ++ tailWord_3276399) baseStart_3276399 baseEnd_3276399 := by
    simpa [prefixWord, tailWord_3276399, baseEnd_3276399] using wordTrace_append hprefix tailTrace_3276399
  have hstable : (prefixWord ++ tailWord_3276399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276399).length < 2 ^ (prefixWord ++ tailWord_3276399).sum := by decide
  have hdescent : baseEnd_3276399 < baseStart_3276399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276409 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 6]
def baseStart_3276409 : Nat := 118140960795 + 3276409 * 2 ^ 59
def prefixEnd_3276409 : Nat := 4983230072969 + 3 ^ 40 * 3276409 * 2
def baseEnd_3276409 : Nat := 1682372637716976768419575

theorem tailTrace_3276409 : CollatzResearch.WordTrace tailWord_3276409 prefixEnd_3276409 1682372637716976768419575 := by
  unfold tailWord_3276409
  simp only [CollatzResearch.WordTrace]
  refine ⟨119500453587137233952976281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79666969058091489301984187 119500453587137233952976281)
  ·
    refine ⟨89625340190352925464732211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119500453587137233952976281 89625340190352925464732211)
    ·
      refine ⟨134438010285529388197098317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89625340190352925464732211 134438010285529388197098317)
      ·
        refine ⟨50414253857073520573911869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134438010285529388197098317 50414253857073520573911869)
        ·
          refine ⟨18905345196402570215216951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50414253857073520573911869 18905345196402570215216951)
          ·
            refine ⟨28358017794603855322825427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18905345196402570215216951 28358017794603855322825427)
            ·
              refine ⟨42537026691905782984238141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28358017794603855322825427 42537026691905782984238141)
              ·
                refine ⟨15951385009464668619089303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42537026691905782984238141 15951385009464668619089303)
                ·
                  refine ⟨23927077514197002928633955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15951385009464668619089303 23927077514197002928633955)
                  ·
                    refine ⟨35890616271295504392950933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23927077514197002928633955 35890616271295504392950933)
                    ·
                      refine ⟨1682372637716976768419575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35890616271295504392950933 1682372637716976768419575)
                      ·
                        rfl

theorem cell23_3276409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_3276409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276409 prefixEnd_3276409 := by exact prefixLift 3276409
  have htrace : WordTrace (prefixWord ++ tailWord_3276409) baseStart_3276409 baseEnd_3276409 := by
    simpa [prefixWord, tailWord_3276409, baseEnd_3276409] using wordTrace_append hprefix tailTrace_3276409
  have hstable : (prefixWord ++ tailWord_3276409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276409).length < 2 ^ (prefixWord ++ tailWord_3276409).sum := by decide
  have hdescent : baseEnd_3276409 < baseStart_3276409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276413 : List Nat := [1, 4, 1, 1, 4, 1, 3, 2, 1, 1, 4]
def baseStart_3276413 : Nat := 118140960795 + 3276413 * 2 ^ 59
def prefixEnd_3276413 : Nat := 4983230072969 + 3 ^ 40 * 3276413 * 2
def baseEnd_3276413 : Nat := 1682374691639594752769557

theorem tailTrace_3276413 : CollatzResearch.WordTrace tailWord_3276413 prefixEnd_3276413 1682374691639594752769557 := by
  unfold tailWord_3276413
  simp only [CollatzResearch.WordTrace]
  refine ⟨119500599479122742636121893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79667066319415161757414595 119500599479122742636121893)
  ·
    refine ⟨22406362402335514244272855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119500599479122742636121893 22406362402335514244272855)
    ·
      refine ⟨33609543603503271366409283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22406362402335514244272855 33609543603503271366409283)
      ·
        refine ⟨50414315405254907049613925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33609543603503271366409283 50414315405254907049613925)
        ·
          refine ⟨9452684138485295071802611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50414315405254907049613925 9452684138485295071802611)
          ·
            refine ⟨14179026207727942607703917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9452684138485295071802611 14179026207727942607703917)
            ·
              refine ⟨5317134827897978477888969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14179026207727942607703917 5317134827897978477888969)
              ·
                refine ⟨3987851120923483858416727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5317134827897978477888969 3987851120923483858416727)
                ·
                  refine ⟨5981776681385225787625091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987851120923483858416727 5981776681385225787625091)
                  ·
                    refine ⟨8972665022077838681437637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5981776681385225787625091 8972665022077838681437637)
                    ·
                      refine ⟨1682374691639594752769557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8972665022077838681437637 1682374691639594752769557)
                      ·
                        rfl

theorem cell23_3276413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_3276413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276413 prefixEnd_3276413 := by exact prefixLift 3276413
  have htrace : WordTrace (prefixWord ++ tailWord_3276413) baseStart_3276413 baseEnd_3276413 := by
    simpa [prefixWord, tailWord_3276413, baseEnd_3276413] using wordTrace_append hprefix tailTrace_3276413
  have hstable : (prefixWord ++ tailWord_3276413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276413).length < 2 ^ (prefixWord ++ tailWord_3276413).sum := by decide
  have hdescent : baseEnd_3276413 < baseStart_3276413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276416 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 3]
def baseStart_3276416 : Nat := 118140960795 + 3276416 * 2 ^ 59
def prefixEnd_3276416 : Nat := 4983230072969 + 3 ^ 40 * 3276416 * 2
def baseEnd_3276416 : Nat := 1682376232081558241032043

theorem tailTrace_3276416 : CollatzResearch.WordTrace tailWord_3276416 prefixEnd_3276416 1682376232081558241032043 := by
  unfold tailWord_3276416
  simp only [CollatzResearch.WordTrace]
  refine ⟨59750354449055937074240551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79667139265407916098987401 59750354449055937074240551)
  ·
    refine ⟨89625531673583905611360827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59750354449055937074240551 89625531673583905611360827)
    ·
      refine ⟨134438297510375858417041241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89625531673583905611360827 134438297510375858417041241)
      ·
        refine ⟨100828723132781893812780931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134438297510375858417041241 100828723132781893812780931)
        ·
          refine ⟨151243084699172840719171397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100828723132781893812780931 151243084699172840719171397)
          ·
            refine ⟨28358078381094907634844637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151243084699172840719171397 28358078381094907634844637)
            ·
              refine ⟨10634279392910590363066739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28358078381094907634844637 10634279392910590363066739)
              ·
                refine ⟨15951419089365885544600109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10634279392910590363066739 15951419089365885544600109)
                ·
                  refine ⟨5981782158512207079225041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15951419089365885544600109 5981782158512207079225041)
                  ·
                    refine ⟨4486336618884155309418781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5981782158512207079225041 4486336618884155309418781)
                    ·
                      refine ⟨1682376232081558241032043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4486336618884155309418781 1682376232081558241032043)
                      ·
                        rfl

theorem cell23_3276416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_3276416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276416 prefixEnd_3276416 := by exact prefixLift 3276416
  have htrace : WordTrace (prefixWord ++ tailWord_3276416) baseStart_3276416 baseEnd_3276416 := by
    simpa [prefixWord, tailWord_3276416, baseEnd_3276416] using wordTrace_append hprefix tailTrace_3276416
  have hstable : (prefixWord ++ tailWord_3276416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276416).length < 2 ^ (prefixWord ++ tailWord_3276416).sum := by decide
  have hdescent : baseEnd_3276416 < baseStart_3276416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276426 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3276426 : Nat := 118140960795 + 3276426 * 2 ^ 59
def prefixEnd_3276426 : Nat := 4983230072969 + 3 ^ 40 * 3276426 * 2
def baseEnd_3276426 : Nat := 1682381366888103201906997

theorem tailTrace_3276426 : CollatzResearch.WordTrace tailWord_3276426 prefixEnd_3276426 1682381366888103201906997 := by
  unfold tailWord_3276426
  simp only [CollatzResearch.WordTrace]
  refine ⟨29875268407018911464086283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79667382418717097237563421 29875268407018911464086283)
  ·
    refine ⟨44812902610528367196129425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29875268407018911464086283 44812902610528367196129425)
    ·
      refine ⟨33609676957896275397097069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44812902610528367196129425 33609676957896275397097069)
      ·
        refine ⟨12603628859211103273911401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33609676957896275397097069 12603628859211103273911401)
        ·
          refine ⟨9452721644408327455433551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12603628859211103273911401 9452721644408327455433551)
          ·
            refine ⟨14179082466612491183150327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9452721644408327455433551 14179082466612491183150327)
            ·
              refine ⟨21268623699918736774725491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14179082466612491183150327 21268623699918736774725491)
              ·
                refine ⟨31902935549878105162088237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21268623699918736774725491 31902935549878105162088237)
                ·
                  refine ⟨11963600831204289435783089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31902935549878105162088237 11963600831204289435783089)
                  ·
                    refine ⟨8972700623403217076837317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11963600831204289435783089 8972700623403217076837317)
                    ·
                      refine ⟨1682381366888103201906997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8972700623403217076837317 1682381366888103201906997)
                      ·
                        rfl

theorem cell23_3276426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3276426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276426 prefixEnd_3276426 := by exact prefixLift 3276426
  have htrace : WordTrace (prefixWord ++ tailWord_3276426) baseStart_3276426 baseEnd_3276426 := by
    simpa [prefixWord, tailWord_3276426, baseEnd_3276426] using wordTrace_append hprefix tailTrace_3276426
  have hstable : (prefixWord ++ tailWord_3276426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276426).length < 2 ^ (prefixWord ++ tailWord_3276426).sum := by decide
  have hdescent : baseEnd_3276426 < baseStart_3276426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276430 : List Nat := [4, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4]
def baseStart_3276430 : Nat := 118140960795 + 3276430 * 2 ^ 59
def prefixEnd_3276430 : Nat := 4983230072969 + 3 ^ 40 * 3276430 * 2
def baseEnd_3276430 : Nat := 1682383420810721186256979

theorem tailTrace_3276430 : CollatzResearch.WordTrace tailWord_3276430 prefixEnd_3276430 1682383420810721186256979 := by
  unfold tailWord_3276430
  simp only [CollatzResearch.WordTrace]
  refine ⟨14937652440007644317436343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79667479680040769692993829 14937652440007644317436343)
  ·
    refine ⟨22406478660011466476154515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14937652440007644317436343 22406478660011466476154515)
    ·
      refine ⟨33609717990017199714231773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22406478660011466476154515 33609717990017199714231773)
      ·
        refine ⟨12603644246256449892836915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33609717990017199714231773 12603644246256449892836915)
        ·
          refine ⟨18905466369384674839255373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12603644246256449892836915 18905466369384674839255373)
          ·
            refine ⟨7089549888519253064720765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18905466369384674839255373 7089549888519253064720765)
            ·
              refine ⟨2658581208194719899270287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7089549888519253064720765 2658581208194719899270287)
              ·
                refine ⟨3987871812292079848905431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2658581208194719899270287 3987871812292079848905431)
                ·
                  refine ⟨5981807718438119773358147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3987871812292079848905431 5981807718438119773358147)
                  ·
                    refine ⟨8972711577657179660037221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5981807718438119773358147 8972711577657179660037221)
                    ·
                      refine ⟨1682383420810721186256979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8972711577657179660037221 1682383420810721186256979)
                      ·
                        rfl

theorem cell23_3276430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_3276430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276430 prefixEnd_3276430 := by exact prefixLift 3276430
  have htrace : WordTrace (prefixWord ++ tailWord_3276430) baseStart_3276430 baseEnd_3276430 := by
    simpa [prefixWord, tailWord_3276430, baseEnd_3276430] using wordTrace_append hprefix tailTrace_3276430
  have hstable : (prefixWord ++ tailWord_3276430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276430).length < 2 ^ (prefixWord ++ tailWord_3276430).sum := by decide
  have hdescent : baseEnd_3276430 < baseStart_3276430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276436 : List Nat := [2, 4, 2, 2, 2, 11]
def baseStart_3276436 : Nat := 118140960795 + 3276436 * 2 ^ 59
def prefixEnd_3276436 : Nat := 4983230072969 + 3 ^ 40 * 3276436 * 2
def baseEnd_3276436 : Nat := 6923401241541761986757

theorem tailTrace_3276436 : CollatzResearch.WordTrace tailWord_3276436 prefixEnd_3276436 6923401241541761986757 := by
  unfold tailWord_3276436
  simp only [CollatzResearch.WordTrace]
  refine ⟨59750719179019708782104581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79667625572026278376139441 59750719179019708782104581)
  ·
    refine ⟨11203259846066195396644609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59750719179019708782104581 11203259846066195396644609)
    ·
      refine ⟨8402444884549646547483457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11203259846066195396644609 8402444884549646547483457)
      ·
        refine ⟨6301833663412234910612593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8402444884549646547483457 6301833663412234910612593)
        ·
          refine ⟨4726375247559176182959445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6301833663412234910612593 4726375247559176182959445)
          ·
            refine ⟨6923401241541761986757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4726375247559176182959445 6923401241541761986757)
            ·
              rfl

theorem cell23_3276436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 11].length) (baseStart_3276436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276436 prefixEnd_3276436 := by exact prefixLift 3276436
  have htrace : WordTrace (prefixWord ++ tailWord_3276436) baseStart_3276436 baseEnd_3276436 := by
    simpa [prefixWord, tailWord_3276436, baseEnd_3276436] using wordTrace_append hprefix tailTrace_3276436
  have hstable : (prefixWord ++ tailWord_3276436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276436).length < 2 ^ (prefixWord ++ tailWord_3276436).sum := by decide
  have hdescent : baseEnd_3276436 < baseStart_3276436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276463 : List Nat := [1, 1, 2, 1, 2, 4, 1, 5, 2, 1, 3]
def baseStart_3276463 : Nat := 118140960795 + 3276463 * 2 ^ 59
def prefixEnd_3276463 : Nat := 4983230072969 + 3 ^ 40 * 3276463 * 2
def baseEnd_3276463 : Nat := 1682400365672319557144327

theorem tailTrace_3276463 : CollatzResearch.WordTrace tailWord_3276463 prefixEnd_3276463 1682400365672319557144327 := by
  unfold tailWord_3276463
  simp only [CollatzResearch.WordTrace]
  refine ⟨119502423128941601175442043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79668282085961067450294695 119502423128941601175442043)
  ·
    refine ⟨179253634693412401763163065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119502423128941601175442043 179253634693412401763163065)
    ·
      refine ⟨134440226020059301322372299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179253634693412401763163065 134440226020059301322372299)
      ·
        refine ⟨201660339030088951983558449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134440226020059301322372299 201660339030088951983558449)
        ·
          refine ⟨151245254272566713987668837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201660339030088951983558449 151245254272566713987668837)
          ·
            refine ⟨28358485176106258872687907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151245254272566713987668837 28358485176106258872687907)
            ·
              refine ⟨42537727764159388309031861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28358485176106258872687907 42537727764159388309031861)
              ·
                refine ⟨3987911977889942653971737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42537727764159388309031861 3987911977889942653971737)
                ·
                  refine ⟨2990933983417456990478803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3987911977889942653971737 2990933983417456990478803)
                  ·
                    refine ⟨4486400975126185485718205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2990933983417456990478803 4486400975126185485718205)
                    ·
                      refine ⟨1682400365672319557144327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4486400975126185485718205 1682400365672319557144327)
                      ·
                        rfl

theorem cell23_3276463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 1, 3].length) (baseStart_3276463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276463 prefixEnd_3276463 := by exact prefixLift 3276463
  have htrace : WordTrace (prefixWord ++ tailWord_3276463) baseStart_3276463 baseEnd_3276463 := by
    simpa [prefixWord, tailWord_3276463, baseEnd_3276463] using wordTrace_append hprefix tailTrace_3276463
  have hstable : (prefixWord ++ tailWord_3276463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276463).length < 2 ^ (prefixWord ++ tailWord_3276463).sum := by decide
  have hdescent : baseEnd_3276463 < baseStart_3276463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276470 : List Nat := [5, 1, 3, 1, 1, 2, 3, 7]
def baseStart_3276470 : Nat := 118140960795 + 3276470 * 2 ^ 59
def prefixEnd_3276470 : Nat := 4983230072969 + 3 ^ 40 * 3276470 * 2
def baseEnd_3276470 : Nat := 62311257779144482583585

theorem tailTrace_3276470 : CollatzResearch.WordTrace tailWord_3276470 prefixEnd_3276470 62311257779144482583585 := by
  unfold tailWord_3276470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7468917402494765085684179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79668452293277494247297909 7468917402494765085684179)
  ·
    refine ⟨11203376103742147628526269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7468917402494765085684179 11203376103742147628526269)
    ·
      refine ⟨4201266038903305360697351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11203376103742147628526269 4201266038903305360697351)
      ·
        refine ⟨6301899058354958041046027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4201266038903305360697351 6301899058354958041046027)
        ·
          refine ⟨9452848587532437061569041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6301899058354958041046027 9452848587532437061569041)
          ·
            refine ⟨7089636440649327796176781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9452848587532437061569041 7089636440649327796176781)
            ·
              refine ⟨2658613665243497923566293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7089636440649327796176781 2658613665243497923566293)
              ·
                refine ⟨62311257779144482583585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2658613665243497923566293 62311257779144482583585)
                ·
                  rfl

theorem cell23_3276470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_3276470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276470 prefixEnd_3276470 := by exact prefixLift 3276470
  have htrace : WordTrace (prefixWord ++ tailWord_3276470) baseStart_3276470 baseEnd_3276470 := by
    simpa [prefixWord, tailWord_3276470, baseEnd_3276470] using wordTrace_append hprefix tailTrace_3276470
  have hstable : (prefixWord ++ tailWord_3276470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276470).length < 2 ^ (prefixWord ++ tailWord_3276470).sum := by decide
  have hdescent : baseEnd_3276470 < baseStart_3276470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276473 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 3, 3, 2]
def baseStart_3276473 : Nat := 118140960795 + 3276473 * 2 ^ 59
def prefixEnd_3276473 : Nat := 4983230072969 + 3 ^ 40 * 3276473 * 2
def baseEnd_3276473 : Nat := 1682405500478864518019281

theorem tailTrace_3276473 : CollatzResearch.WordTrace tailWord_3276473 prefixEnd_3276473 1682405500478864518019281 := by
  unfold tailWord_3276473
  simp only [CollatzResearch.WordTrace]
  refine ⟨119502787858905372883306073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79668525239270248588870715 119502787858905372883306073)
  ·
    refine ⟨89627090894179029662479555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119502787858905372883306073 89627090894179029662479555)
    ·
      refine ⟨134440636341268544493719333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89627090894179029662479555 134440636341268544493719333)
      ·
        refine ⟨25207619313987852092572375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134440636341268544493719333 25207619313987852092572375)
        ·
          refine ⟨37811428970981778138858563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25207619313987852092572375 37811428970981778138858563)
          ·
            refine ⟨56717143456472667208287845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37811428970981778138858563 56717143456472667208287845)
            ·
              refine ⟨10634464398088625101553971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56717143456472667208287845 10634464398088625101553971)
              ·
                refine ⟨15951696597132937652330957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10634464398088625101553971 15951696597132937652330957)
                ·
                  refine ⟨5981886223924851619624109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15951696597132937652330957 5981886223924851619624109)
                  ·
                    refine ⟨2243207333971819357359041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5981886223924851619624109 2243207333971819357359041)
                    ·
                      refine ⟨1682405500478864518019281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2243207333971819357359041 1682405500478864518019281)
                      ·
                        rfl

theorem cell23_3276473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_3276473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276473 prefixEnd_3276473 := by exact prefixLift 3276473
  have htrace : WordTrace (prefixWord ++ tailWord_3276473) baseStart_3276473 baseEnd_3276473 := by
    simpa [prefixWord, tailWord_3276473, baseEnd_3276473] using wordTrace_append hprefix tailTrace_3276473
  have hstable : (prefixWord ++ tailWord_3276473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276473).length < 2 ^ (prefixWord ++ tailWord_3276473).sum := by decide
  have hdescent : baseEnd_3276473 < baseStart_3276473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276479 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 1, 8]
def baseStart_3276479 : Nat := 118140960795 + 3276479 * 2 ^ 59
def prefixEnd_3276479 : Nat := 4983230072969 + 3 ^ 40 * 3276479 * 2
def baseEnd_3276479 : Nat := 560802860454263831514751

theorem tailTrace_3276479 : CollatzResearch.WordTrace tailWord_3276479 prefixEnd_3276479 560802860454263831514751 := by
  unfold tailWord_3276479
  simp only [CollatzResearch.WordTrace]
  refine ⟨119503006696883635908024491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79668671131255757272016327 119503006696883635908024491)
  ·
    refine ⟨179254510045325453862036737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119503006696883635908024491 179254510045325453862036737)
    ·
      refine ⟨134440882533994090396527553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179254510045325453862036737 134440882533994090396527553)
      ·
        refine ⟨100830661900495567797395665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134440882533994090396527553 100830661900495567797395665)
        ·
          refine ⟨75622996425371675848046749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100830661900495567797395665 75622996425371675848046749)
          ·
            refine ⟨28358623659514378443017531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75622996425371675848046749 28358623659514378443017531)
            ·
              refine ⟨42537935489271567664526297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28358623659514378443017531 42537935489271567664526297)
              ·
                refine ⟨31903451616953675748394723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42537935489271567664526297 31903451616953675748394723)
                ·
                  refine ⟨47855177425430513622592085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31903451616953675748394723 47855177425430513622592085)
                  ·
                    refine ⟨560802860454263831514751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47855177425430513622592085 560802860454263831514751)
                    ·
                      rfl

theorem cell23_3276479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_3276479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276479 prefixEnd_3276479 := by exact prefixLift 3276479
  have htrace : WordTrace (prefixWord ++ tailWord_3276479) baseStart_3276479 baseEnd_3276479 := by
    simpa [prefixWord, tailWord_3276479, baseEnd_3276479] using wordTrace_append hprefix tailTrace_3276479
  have hstable : (prefixWord ++ tailWord_3276479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276479).length < 2 ^ (prefixWord ++ tailWord_3276479).sum := by decide
  have hdescent : baseEnd_3276479 < baseStart_3276479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276516 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_3276516 : Nat := 118140960795 + 3276516 * 2 ^ 59
def prefixEnd_3276516 : Nat := 4983230072969 + 3 ^ 40 * 3276516 * 2
def baseEnd_3276516 : Nat := 1682427580147007849781583

theorem tailTrace_3276516 : CollatzResearch.WordTrace tailWord_3276516 prefixEnd_3276516 1682427580147007849781583 := by
  unfold tailWord_3276516
  simp only [CollatzResearch.WordTrace]
  refine ⟨59752178098874795613560701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79669570798499727484747601 59752178098874795613560701)
  ·
    refine ⟨22407066787078048355085263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59752178098874795613560701 22407066787078048355085263)
    ·
      refine ⟨33610600180617072532627895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22407066787078048355085263 33610600180617072532627895)
      ·
        refine ⟨50415900270925608798941843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33610600180617072532627895 50415900270925608798941843)
        ·
          refine ⟨75623850406388413198412765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50415900270925608798941843 75623850406388413198412765)
          ·
            refine ⟨28358943902395654949404787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75623850406388413198412765 28358943902395654949404787)
            ·
              refine ⟨42538415853593482424107181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28358943902395654949404787 42538415853593482424107181)
              ·
                refine ⟨15951905945097555909040193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42538415853593482424107181 15951905945097555909040193)
                ·
                  refine ⟨11963929458823166931780145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15951905945097555909040193 11963929458823166931780145)
                  ·
                    refine ⟨8972947094117375198835109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11963929458823166931780145 8972947094117375198835109)
                    ·
                      refine ⟨1682427580147007849781583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8972947094117375198835109 1682427580147007849781583)
                      ·
                        rfl

theorem cell23_3276516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_3276516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276516 prefixEnd_3276516 := by exact prefixLift 3276516
  have htrace : WordTrace (prefixWord ++ tailWord_3276516) baseStart_3276516 baseEnd_3276516 := by
    simpa [prefixWord, tailWord_3276516, baseEnd_3276516] using wordTrace_append hprefix tailTrace_3276516
  have hstable : (prefixWord ++ tailWord_3276516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276516).length < 2 ^ (prefixWord ++ tailWord_3276516).sum := by decide
  have hdescent : baseEnd_3276516 < baseStart_3276516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276520 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_3276520 : Nat := 118140960795 + 3276520 * 2 ^ 59
def prefixEnd_3276520 : Nat := 4983230072969 + 3 ^ 40 * 3276520 * 2
def baseEnd_3276520 : Nat := 1682429634069625834131565

theorem tailTrace_3276520 : CollatzResearch.WordTrace tailWord_3276520 prefixEnd_3276520 1682429634069625834131565 := by
  unfold tailWord_3276520
  simp only [CollatzResearch.WordTrace]
  refine ⟨59752251044867549955133507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79669668059823399940178009 59752251044867549955133507)
  ·
    refine ⟨89628376567301324932700261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59752251044867549955133507 89628376567301324932700261)
    ·
      refine ⟨16805320606368998424881299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89628376567301324932700261 16805320606368998424881299)
      ·
        refine ⟨25207980909553497637321949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16805320606368998424881299 25207980909553497637321949)
        ·
          refine ⟨9452992841082561613995731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25207980909553497637321949 9452992841082561613995731)
          ·
            refine ⟨14179489261623842420993597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9452992841082561613995731 14179489261623842420993597)
            ·
              refine ⟨5317308473108940907872599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14179489261623842420993597 5317308473108940907872599)
              ·
                refine ⟨7975962709663411361808899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5317308473108940907872599 7975962709663411361808899)
                ·
                  refine ⟨11963944064495117042713349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7975962709663411361808899 11963944064495117042713349)
                  ·
                    refine ⟨2243239512092834445508753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11963944064495117042713349 2243239512092834445508753)
                    ·
                      refine ⟨1682429634069625834131565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2243239512092834445508753 1682429634069625834131565)
                      ·
                        rfl

theorem cell23_3276520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_3276520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276520 prefixEnd_3276520 := by exact prefixLift 3276520
  have htrace : WordTrace (prefixWord ++ tailWord_3276520) baseStart_3276520 baseEnd_3276520 := by
    simpa [prefixWord, tailWord_3276520, baseEnd_3276520] using wordTrace_append hprefix tailTrace_3276520
  have hstable : (prefixWord ++ tailWord_3276520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276520).length < 2 ^ (prefixWord ++ tailWord_3276520).sum := by decide
  have hdescent : baseEnd_3276520 < baseStart_3276520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276526 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 7]
def baseStart_3276526 : Nat := 118140960795 + 3276526 * 2 ^ 59
def prefixEnd_3276526 : Nat := 4983230072969 + 3 ^ 40 * 3276526 * 2
def baseEnd_3276526 : Nat := 186936968328172534517393

theorem tailTrace_3276526 : CollatzResearch.WordTrace tailWord_3276526 prefixEnd_3276526 186936968328172534517393 := by
  unfold tailWord_3276526
  simp only [CollatzResearch.WordTrace]
  refine ⟨14938090115964170366873179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79669813951808908623323621 14938090115964170366873179)
  ·
    refine ⟨22407135173946255550309769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14938090115964170366873179 22407135173946255550309769)
    ·
      refine ⟨16805351380459691662732327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22407135173946255550309769 16805351380459691662732327)
      ·
        refine ⟨25208027070689537494098491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16805351380459691662732327 25208027070689537494098491)
        ·
          refine ⟨37812040606034306241147737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25208027070689537494098491 37812040606034306241147737)
          ·
            refine ⟨28359030454525729680860803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37812040606034306241147737 28359030454525729680860803)
            ·
              refine ⟨42538545681788594521291205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28359030454525729680860803 42538545681788594521291205)
              ·
                refine ⟨7975977315335361472742101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42538545681788594521291205 7975977315335361472742101)
                ·
                  refine ⟨186936968328172534517393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7975977315335361472742101 186936968328172534517393)
                  ·
                    rfl

theorem cell23_3276526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_3276526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276526 prefixEnd_3276526 := by exact prefixLift 3276526
  have htrace : WordTrace (prefixWord ++ tailWord_3276526) baseStart_3276526 baseEnd_3276526 := by
    simpa [prefixWord, tailWord_3276526, baseEnd_3276526] using wordTrace_append hprefix tailTrace_3276526
  have hstable : (prefixWord ++ tailWord_3276526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276526).length < 2 ^ (prefixWord ++ tailWord_3276526).sum := by decide
  have hdescent : baseEnd_3276526 < baseStart_3276526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276536 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 4, 3, 3]
def baseStart_3276536 : Nat := 118140960795 + 3276536 * 2 ^ 59
def prefixEnd_3276536 : Nat := 4983230072969 + 3 ^ 40 * 3276536 * 2
def baseEnd_3276536 : Nat := 1682437849760097771531491

theorem tailTrace_3276536 : CollatzResearch.WordTrace tailWord_3276536 prefixEnd_3276536 1682437849760097771531491 := by
  unfold tailWord_3276536
  simp only [CollatzResearch.WordTrace]
  refine ⟨59752542828838567321424731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79670057105118089761899641 59752542828838567321424731)
  ·
    refine ⟨89628814243257850982137097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59752542828838567321424731 89628814243257850982137097)
    ·
      refine ⟨67221610682443388236602823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89628814243257850982137097 67221610682443388236602823)
      ·
        refine ⟨100832416023665082354904235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67221610682443388236602823 100832416023665082354904235)
        ·
          refine ⟨151248624035497623532356353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100832416023665082354904235 151248624035497623532356353)
          ·
            refine ⟨113436468026623217649267265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151248624035497623532356353 113436468026623217649267265)
            ·
              refine ⟨85077351019967413236950449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113436468026623217649267265 85077351019967413236950449)
              ·
                refine ⟨63808013264975559927712837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85077351019967413236950449 63808013264975559927712837)
                ·
                  refine ⟨11964002487182917486446157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63808013264975559927712837 11964002487182917486446157)
                  ·
                    refine ⟨4486500932693594057417309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11964002487182917486446157 4486500932693594057417309)
                    ·
                      refine ⟨1682437849760097771531491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4486500932693594057417309 1682437849760097771531491)
                      ·
                        rfl

theorem cell23_3276536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_3276536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276536 prefixEnd_3276536 := by exact prefixLift 3276536
  have htrace : WordTrace (prefixWord ++ tailWord_3276536) baseStart_3276536 baseEnd_3276536 := by
    simpa [prefixWord, tailWord_3276536, baseEnd_3276536] using wordTrace_append hprefix tailTrace_3276536
  have hstable : (prefixWord ++ tailWord_3276536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276536).length < 2 ^ (prefixWord ++ tailWord_3276536).sum := by decide
  have hdescent : baseEnd_3276536 < baseStart_3276536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276543 : List Nat := [1, 1, 2, 2, 1, 3, 5, 3, 5]
def baseStart_3276543 : Nat := 118140960795 + 3276543 * 2 ^ 59
def prefixEnd_3276543 : Nat := 4983230072969 + 3 ^ 40 * 3276543 * 2
def baseEnd_3276543 : Nat := 186937938236075471571551

theorem tailTrace_3276543 : CollatzResearch.WordTrace tailWord_3276543 prefixEnd_3276543 186937938236075471571551 := by
  unfold tailWord_3276543
  simp only [CollatzResearch.WordTrace]
  refine ⟨119505340968651774838354283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79670227312434516558902855 119505340968651774838354283)
  ·
    refine ⟨179258011452977662257531425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119505340968651774838354283 179258011452977662257531425)
    ·
      refine ⟨134443508589733246693148569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179258011452977662257531425 134443508589733246693148569)
      ·
        refine ⟨100832631442299935019861427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134443508589733246693148569 100832631442299935019861427)
        ·
          refine ⟨151248947163449902529792141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100832631442299935019861427 151248947163449902529792141)
          ·
            refine ⟨56718355186293713448672053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151248947163449902529792141 56718355186293713448672053)
            ·
              refine ⟨5317345798715035635813005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56718355186293713448672053 5317345798715035635813005)
              ·
                refine ⟨1994004674518138363429877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5317345798715035635813005 1994004674518138363429877)
                ·
                  refine ⟨186937938236075471571551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1994004674518138363429877 186937938236075471571551)
                  ·
                    rfl

theorem cell23_3276543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 5].length) (baseStart_3276543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276543 prefixEnd_3276543 := by exact prefixLift 3276543
  have htrace : WordTrace (prefixWord ++ tailWord_3276543) baseStart_3276543 baseEnd_3276543 := by
    simpa [prefixWord, tailWord_3276543, baseEnd_3276543] using wordTrace_append hprefix tailTrace_3276543
  have hstable : (prefixWord ++ tailWord_3276543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276543).length < 2 ^ (prefixWord ++ tailWord_3276543).sum := by decide
  have hdescent : baseEnd_3276543 < baseStart_3276543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276556 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 4, 5]
def baseStart_3276556 : Nat := 118140960795 + 3276556 * 2 ^ 59
def prefixEnd_3276556 : Nat := 4983230072969 + 3 ^ 40 * 3276556 * 2
def baseEnd_3276556 : Nat := 560816039791062564427133

theorem tailTrace_3276556 : CollatzResearch.WordTrace tailWord_3276556 prefixEnd_3276556 560816039791062564427133 := by
  unfold tailWord_3276556
  simp only [CollatzResearch.WordTrace]
  refine ⟨59752907558802339029288761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79670543411736452039051681 59752907558802339029288761)
  ·
    refine ⟨44814680669101754271966571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59752907558802339029288761 44814680669101754271966571)
    ·
      refine ⟨67222021003652631407949857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44814680669101754271966571 67222021003652631407949857)
      ·
        refine ⟨50416515752739473555962393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67222021003652631407949857 50416515752739473555962393)
        ·
          refine ⟨37812386814554605166971795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50416515752739473555962393 37812386814554605166971795)
          ·
            refine ⟨56718580221831907750457693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37812386814554605166971795 56718580221831907750457693)
            ·
              refine ⟨21269467583186965406421635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56718580221831907750457693 21269467583186965406421635)
              ·
                refine ⟨31904201374780448109632453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21269467583186965406421635 31904201374780448109632453)
                ·
                  refine ⟨5982037757771334020556085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31904201374780448109632453 5982037757771334020556085)
                  ·
                    refine ⟨560816039791062564427133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5982037757771334020556085 560816039791062564427133)
                    ·
                      rfl

theorem cell23_3276556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_3276556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276556 prefixEnd_3276556 := by exact prefixLift 3276556
  have htrace : WordTrace (prefixWord ++ tailWord_3276556) baseStart_3276556 baseEnd_3276556 := by
    simpa [prefixWord, tailWord_3276556, baseEnd_3276556] using wordTrace_append hprefix tailTrace_3276556
  have hstable : (prefixWord ++ tailWord_3276556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276556).length < 2 ^ (prefixWord ++ tailWord_3276556).sum := by decide
  have hdescent : baseEnd_3276556 < baseStart_3276556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276593 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 2, 1, 4]
def baseStart_3276593 : Nat := 118140960795 + 3276593 * 2 ^ 59
def prefixEnd_3276593 : Nat := 4983230072969 + 3 ^ 40 * 3276593 * 2
def baseEnd_3276593 : Nat := 1682467118157404048518729

theorem tailTrace_3276593 : CollatzResearch.WordTrace tailWord_3276593 prefixEnd_3276593 1682467118157404048518729 := by
  unfold tailWord_3276593
  simp only [CollatzResearch.WordTrace]
  refine ⟨119507164618470633377674433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79671443078980422251782955 119507164618470633377674433)
  ·
    refine ⟨89630373463852975033255825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119507164618470633377674433 89630373463852975033255825)
    ·
      refine ⟨67222780097889731274941869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89630373463852975033255825 67222780097889731274941869)
      ·
        refine ⟨25208542536708649228103201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67222780097889731274941869 25208542536708649228103201)
        ·
          refine ⟨18906406902531486921077401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25208542536708649228103201 18906406902531486921077401)
          ·
            refine ⟨14179805176898615190808051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18906406902531486921077401 14179805176898615190808051)
            ·
              refine ⟨21269707765347922786212077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14179805176898615190808051 21269707765347922786212077)
              ·
                refine ⟨7976140412005471044829529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21269707765347922786212077 7976140412005471044829529)
                ·
                  refine ⟨5982105309004103283622147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7976140412005471044829529 5982105309004103283622147)
                  ·
                    refine ⟨8973157963506154925433221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5982105309004103283622147 8973157963506154925433221)
                    ·
                      refine ⟨1682467118157404048518729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8973157963506154925433221 1682467118157404048518729)
                      ·
                        rfl

theorem cell23_3276593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_3276593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276593 prefixEnd_3276593 := by exact prefixLift 3276593
  have htrace : WordTrace (prefixWord ++ tailWord_3276593) baseStart_3276593 baseEnd_3276593 := by
    simpa [prefixWord, tailWord_3276593, baseEnd_3276593] using wordTrace_append hprefix tailTrace_3276593
  have hstable : (prefixWord ++ tailWord_3276593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276593).length < 2 ^ (prefixWord ++ tailWord_3276593).sum := by decide
  have hdescent : baseEnd_3276593 < baseStart_3276593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276613 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 2, 2, 3]
def baseStart_3276613 : Nat := 118140960795 + 3276613 * 2 ^ 59
def prefixEnd_3276613 : Nat := 4983230072969 + 3 ^ 40 * 3276613 * 2
def baseEnd_3276613 : Nat := 1682477387770493970268637

theorem tailTrace_3276613 : CollatzResearch.WordTrace tailWord_3276613 prefixEnd_3276613 1682477387770493970268637 := by
  unfold tailWord_3276613
  simp only [CollatzResearch.WordTrace]
  refine ⟨119507894078398176793402493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79671929385598784528934995 119507894078398176793402493)
  ·
    refine ⟨44815460279399316297525935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119507894078398176793402493 44815460279399316297525935)
    ·
      refine ⟨67223190419098974446288903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44815460279399316297525935 67223190419098974446288903)
      ·
        refine ⟨100834785628648461669433355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67223190419098974446288903 100834785628648461669433355)
        ·
          refine ⟨151252178442972692504150033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100834785628648461669433355 151252178442972692504150033)
          ·
            refine ⟨113439133832229519378112525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151252178442972692504150033 113439133832229519378112525)
            ·
              refine ⟨42539675187086069766792197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113439133832229519378112525 42539675187086069766792197)
              ·
                refine ⟨7976189097578638081273537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42539675187086069766792197 7976189097578638081273537)
                ·
                  refine ⟨5982141823183978560955153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7976189097578638081273537 5982141823183978560955153)
                  ·
                    refine ⟨4486606367387983920716365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5982141823183978560955153 4486606367387983920716365)
                    ·
                      refine ⟨1682477387770493970268637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4486606367387983920716365 1682477387770493970268637)
                      ·
                        rfl

theorem cell23_3276613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_3276613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276613 prefixEnd_3276613 := by exact prefixLift 3276613
  have htrace : WordTrace (prefixWord ++ tailWord_3276613) baseStart_3276613 baseEnd_3276613 := by
    simpa [prefixWord, tailWord_3276613, baseEnd_3276613] using wordTrace_append hprefix tailTrace_3276613
  have hstable : (prefixWord ++ tailWord_3276613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276613).length < 2 ^ (prefixWord ++ tailWord_3276613).sum := by decide
  have hdescent : baseEnd_3276613 < baseStart_3276613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276654 : List Nat := [4, 1, 2, 3, 1, 2, 2, 3, 1, 4]
def baseStart_3276654 : Nat := 118140960795 + 3276654 * 2 ^ 59
def prefixEnd_3276654 : Nat := 4983230072969 + 3 ^ 40 * 3276654 * 2
def baseEnd_3276654 : Nat := 560832813492442769951983

theorem tailTrace_3276654 : CollatzResearch.WordTrace tailWord_3276654 prefixEnd_3276654 560832813492442769951983 := by
  unfold tailWord_3276654
  simp only [CollatzResearch.WordTrace]
  refine ⟨14938673683906205099455627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79672926314166427197096677 14938673683906205099455627)
  ·
    refine ⟨22408010525859307649183441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14938673683906205099455627 22408010525859307649183441)
    ·
      refine ⟨16806007894394480736887581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22408010525859307649183441 16806007894394480736887581)
      ·
        refine ⟨6302252960397930276332843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16806007894394480736887581 6302252960397930276332843)
        ·
          refine ⟨9453379440596895414499265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6302252960397930276332843 9453379440596895414499265)
          ·
            refine ⟨7090034580447671560874449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9453379440596895414499265 7090034580447671560874449)
            ·
              refine ⟨5317525935335753670655837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7090034580447671560874449 5317525935335753670655837)
              ·
                refine ⟨1994072225750907626495939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5317525935335753670655837 1994072225750907626495939)
                ·
                  refine ⟨2991108338626361439743909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994072225750907626495939 2991108338626361439743909)
                  ·
                    refine ⟨560832813492442769951983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2991108338626361439743909 560832813492442769951983)
                    ·
                      rfl

theorem cell23_3276654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_3276654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276654 prefixEnd_3276654 := by exact prefixLift 3276654
  have htrace : WordTrace (prefixWord ++ tailWord_3276654) baseStart_3276654 baseEnd_3276654 := by
    simpa [prefixWord, tailWord_3276654, baseEnd_3276654] using wordTrace_append hprefix tailTrace_3276654
  have hstable : (prefixWord ++ tailWord_3276654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276654).length < 2 ^ (prefixWord ++ tailWord_3276654).sum := by decide
  have hdescent : baseEnd_3276654 < baseStart_3276654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276656 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 5]
def baseStart_3276656 : Nat := 118140960795 + 3276656 * 2 ^ 59
def prefixEnd_3276656 : Nat := 4983230072969 + 3 ^ 40 * 3276656 * 2
def baseEnd_3276656 : Nat := 1682499467438637302030939

theorem tailTrace_3276656 : CollatzResearch.WordTrace tailWord_3276656 prefixEnd_3276656 1682499467438637302030939 := by
  unfold tailWord_3276656
  simp only [CollatzResearch.WordTrace]
  refine ⟨59754731208621197568608911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79672974944828263424811881 59754731208621197568608911)
  ·
    refine ⟨89632096812931796352913367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59754731208621197568608911 89632096812931796352913367)
    ·
      refine ⟨134448145219397694529370051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89632096812931796352913367 134448145219397694529370051)
      ·
        refine ⟨201672217829096541794055077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134448145219397694529370051 201672217829096541794055077)
        ·
          refine ⟨37813540842955601586385327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201672217829096541794055077 37813540842955601586385327)
          ·
            refine ⟨56720311264433402379577991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37813540842955601586385327 56720311264433402379577991)
            ·
              refine ⟨85080466896650103569366987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56720311264433402379577991 85080466896650103569366987)
              ·
                refine ⟨127620700344975155354050481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85080466896650103569366987 127620700344975155354050481)
                ·
                  refine ⟨95715525258731366515537861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127620700344975155354050481 95715525258731366515537861)
                  ·
                    refine ⟨17946660986012131221663349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95715525258731366515537861 17946660986012131221663349)
                    ·
                      refine ⟨1682499467438637302030939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17946660986012131221663349 1682499467438637302030939)
                      ·
                        rfl

theorem cell23_3276656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_3276656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276656 prefixEnd_3276656 := by exact prefixLift 3276656
  have htrace : WordTrace (prefixWord ++ tailWord_3276656) baseStart_3276656 baseEnd_3276656 := by
    simpa [prefixWord, tailWord_3276656, baseEnd_3276656] using wordTrace_append hprefix tailTrace_3276656
  have hstable : (prefixWord ++ tailWord_3276656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276656).length < 2 ^ (prefixWord ++ tailWord_3276656).sum := by decide
  have hdescent : baseEnd_3276656 < baseStart_3276656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276670 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3276670 : Nat := 118140960795 + 3276670 * 2 ^ 59
def prefixEnd_3276670 : Nat := 4983230072969 + 3 ^ 40 * 3276670 * 2
def baseEnd_3276670 : Nat := 1682506656167800247255875

theorem tailTrace_3276670 : CollatzResearch.WordTrace tailWord_3276670 prefixEnd_3276670 1682506656167800247255875 := by
  unfold tailWord_3276670
  simp only [CollatzResearch.WordTrace]
  refine ⟨14938746629898959441028433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79673315359461117018818309 14938746629898959441028433)
  ·
    refine ⟨11204059972424219580771325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14938746629898959441028433 11204059972424219580771325)
    ·
      refine ⟨4201522489659082342789247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11204059972424219580771325 4201522489659082342789247)
      ·
        refine ⟨6302283734488623514183871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4201522489659082342789247 6302283734488623514183871)
        ·
          refine ⟨9453425601732935271275807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6302283734488623514183871 9453425601732935271275807)
          ·
            refine ⟨14180138402599402906913711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9453425601732935271275807 14180138402599402906913711)
            ·
              refine ⟨21270207603899104360370567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14180138402599402906913711 21270207603899104360370567)
              ·
                refine ⟨31905311405848656540555851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21270207603899104360370567 31905311405848656540555851)
                ·
                  refine ⟨47857967108772984810833777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31905311405848656540555851 47857967108772984810833777)
                  ·
                    refine ⟨35893475331579738608125333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47857967108772984810833777 35893475331579738608125333)
                    ·
                      refine ⟨1682506656167800247255875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35893475331579738608125333 1682506656167800247255875)
                      ·
                        rfl

theorem cell23_3276670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3276670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276670 prefixEnd_3276670 := by exact prefixLift 3276670
  have htrace : WordTrace (prefixWord ++ tailWord_3276670) baseStart_3276670 baseEnd_3276670 := by
    simpa [prefixWord, tailWord_3276670, baseEnd_3276670] using wordTrace_append hprefix tailTrace_3276670
  have hstable : (prefixWord ++ tailWord_3276670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276670).length < 2 ^ (prefixWord ++ tailWord_3276670).sum := by decide
  have hdescent : baseEnd_3276670 < baseStart_3276670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276677 : List Nat := [1, 3, 1, 1, 3, 2, 1, 6, 1, 1, 3]
def baseStart_3276677 : Nat := 118140960795 + 3276677 * 2 ^ 59
def prefixEnd_3276677 : Nat := 4983230072969 + 3 ^ 40 * 3276677 * 2
def baseEnd_3276677 : Nat := 1682510250532381719868343

theorem tailTrace_3276677 : CollatzResearch.WordTrace tailWord_3276677 prefixEnd_3276677 1682510250532381719868343 := by
  unfold tailWord_3276677
  simp only [CollatzResearch.WordTrace]
  refine ⟨119510228350166315723732285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79673485566777543815821523 119510228350166315723732285)
  ·
    refine ⟨44816335631312368396399607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119510228350166315723732285 44816335631312368396399607)
    ·
      refine ⟨67224503446968552594599411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44816335631312368396399607 67224503446968552594599411)
      ·
        refine ⟨100836755170452828891899117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67224503446968552594599411 100836755170452828891899117)
        ·
          refine ⟨37813783188919810834462169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100836755170452828891899117 37813783188919810834462169)
          ·
            refine ⟨28360337391689858125846627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37813783188919810834462169 28360337391689858125846627)
            ·
              refine ⟨42540506087534787188769941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28360337391689858125846627 42540506087534787188769941)
              ·
                refine ⟨1994086222853193149473591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42540506087534787188769941 1994086222853193149473591)
                ·
                  refine ⟨2991129334279789724210387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994086222853193149473591 2991129334279789724210387)
                  ·
                    refine ⟨4486694001419684586315581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2991129334279789724210387 4486694001419684586315581)
                    ·
                      refine ⟨1682510250532381719868343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4486694001419684586315581 1682510250532381719868343)
                      ·
                        rfl

theorem cell23_3276677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 1, 1, 3].length) (baseStart_3276677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276677 prefixEnd_3276677 := by exact prefixLift 3276677
  have htrace : WordTrace (prefixWord ++ tailWord_3276677) baseStart_3276677 baseEnd_3276677 := by
    simpa [prefixWord, tailWord_3276677, baseEnd_3276677] using wordTrace_append hprefix tailTrace_3276677
  have hstable : (prefixWord ++ tailWord_3276677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276677).length < 2 ^ (prefixWord ++ tailWord_3276677).sum := by decide
  have hdescent : baseEnd_3276677 < baseStart_3276677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276711 : List Nat := [1, 1, 6, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_3276711 : Nat := 118140960795 + 3276711 * 2 ^ 59
def prefixEnd_3276711 : Nat := 4983230072969 + 3 ^ 40 * 3276711 * 2
def baseEnd_3276711 : Nat := 1682527708874634586843187

theorem tailTrace_3276711 : CollatzResearch.WordTrace tailWord_3276711 prefixEnd_3276711 1682527708874634586843187 := by
  unfold tailWord_3276711
  simp only [CollatzResearch.WordTrace]
  refine ⟨119511468432043139530469987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79674312288028759686979991 119511468432043139530469987)
  ·
    refine ⟨179267202648064709295704981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119511468432043139530469987 179267202648064709295704981)
    ·
      refine ⟨8403150124128033248236171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 179267202648064709295704981 8403150124128033248236171)
      ·
        refine ⟨12604725186192049872354257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8403150124128033248236171 12604725186192049872354257)
        ·
          refine ⟨9453543889644037404265693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12604725186192049872354257 9453543889644037404265693)
          ·
            refine ⟨3545078958616514026599635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9453543889644037404265693 3545078958616514026599635)
            ·
              refine ⟨5317618437924771039899453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3545078958616514026599635 5317618437924771039899453)
              ·
                refine ⟨1994106914221789139962295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5317618437924771039899453 1994106914221789139962295)
                ·
                  refine ⟨2991160371332683709943443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994106914221789139962295 2991160371332683709943443)
                  ·
                    refine ⟨4486740556999025564915165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2991160371332683709943443 4486740556999025564915165)
                    ·
                      refine ⟨1682527708874634586843187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4486740556999025564915165 1682527708874634586843187)
                      ·
                        rfl

theorem cell23_3276711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_3276711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276711 prefixEnd_3276711 := by exact prefixLift 3276711
  have htrace : WordTrace (prefixWord ++ tailWord_3276711) baseStart_3276711 baseEnd_3276711 := by
    simpa [prefixWord, tailWord_3276711, baseEnd_3276711] using wordTrace_append hprefix tailTrace_3276711
  have hstable : (prefixWord ++ tailWord_3276711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276711).length < 2 ^ (prefixWord ++ tailWord_3276711).sum := by decide
  have hdescent : baseEnd_3276711 < baseStart_3276711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276734 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_3276734 : Nat := 118140960795 + 3276734 * 2 ^ 59
def prefixEnd_3276734 : Nat := 4983230072969 + 3 ^ 40 * 3276734 * 2
def baseEnd_3276734 : Nat := 1682539518929687996855581

theorem tailTrace_3276734 : CollatzResearch.WordTrace tailWord_3276734 prefixEnd_3276734 1682539518929687996855581 := by
  unfold tailWord_3276734
  simp only [CollatzResearch.WordTrace]
  refine ⟨14939038413869976807319657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79674871540639876305704837 14939038413869976807319657)
  ·
    refine ⟨11204278810402482605489743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14939038413869976807319657 11204278810402482605489743)
    ·
      refine ⟨16806418215603723908234615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11204278810402482605489743 16806418215603723908234615)
      ·
        refine ⟨25209627323405585862351923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16806418215603723908234615 25209627323405585862351923)
        ·
          refine ⟨37814440985108378793527885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25209627323405585862351923 37814440985108378793527885)
          ·
            refine ⟨14180415369415642047572957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37814440985108378793527885 14180415369415642047572957)
            ·
              refine ⟨5317655763530865767839859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14180415369415642047572957 5317655763530865767839859)
              ·
                refine ⟨7976483645296298651759789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5317655763530865767839859 7976483645296298651759789)
                ·
                  refine ⟨2991181366986111994409921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7976483645296298651759789 2991181366986111994409921)
                  ·
                    refine ⟨2243386025239583995807441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2991181366986111994409921 2243386025239583995807441)
                    ·
                      refine ⟨1682539518929687996855581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2243386025239583995807441 1682539518929687996855581)
                      ·
                        rfl

theorem cell23_3276734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_3276734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276734 prefixEnd_3276734 := by exact prefixLift 3276734
  have htrace : WordTrace (prefixWord ++ tailWord_3276734) baseStart_3276734 baseEnd_3276734 := by
    simpa [prefixWord, tailWord_3276734, baseEnd_3276734] using wordTrace_append hprefix tailTrace_3276734
  have hstable : (prefixWord ++ tailWord_3276734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276734).length < 2 ^ (prefixWord ++ tailWord_3276734).sum := by decide
  have hdescent : baseEnd_3276734 < baseStart_3276734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276744 : List Nat := [2, 1, 3, 1, 4, 3, 2, 1, 2, 4]
def baseStart_3276744 : Nat := 118140960795 + 3276744 * 2 ^ 59
def prefixEnd_3276744 : Nat := 4983230072969 + 3 ^ 40 * 3276744 * 2
def baseEnd_3276744 : Nat := 560848217912077652576845

theorem tailTrace_3276744 : CollatzResearch.WordTrace tailWord_3276744 prefixEnd_3276744 560848217912077652576845 := by
  unfold tailWord_3276744
  simp only [CollatzResearch.WordTrace]
  refine ⟨59756336020461793083210643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79675114693949057444280857 59756336020461793083210643)
  ·
    refine ⟨89634504030692689624815965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59756336020461793083210643 89634504030692689624815965)
    ·
      refine ⟨33612939011509758609305987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89634504030692689624815965 33612939011509758609305987)
      ·
        refine ⟨50419408517264637913958981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33612939011509758609305987 50419408517264637913958981)
        ·
          refine ⟨9453639096987119608867309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50419408517264637913958981 9453639096987119608867309)
          ·
            refine ⟨3545114661370169853325241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9453639096987119608867309 3545114661370169853325241)
            ·
              refine ⟨2658835996027627389993931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3545114661370169853325241 2658835996027627389993931)
              ·
                refine ⟨3988253994041441084990897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2658835996027627389993931 3988253994041441084990897)
                ·
                  refine ⟨2991190495531080813743173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3988253994041441084990897 2991190495531080813743173)
                  ·
                    refine ⟨560848217912077652576845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2991190495531080813743173 560848217912077652576845)
                    ·
                      rfl

theorem cell23_3276744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_3276744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276744 prefixEnd_3276744 := by exact prefixLift 3276744
  have htrace : WordTrace (prefixWord ++ tailWord_3276744) baseStart_3276744 baseEnd_3276744 := by
    simpa [prefixWord, tailWord_3276744, baseEnd_3276744] using wordTrace_append hprefix tailTrace_3276744
  have hstable : (prefixWord ++ tailWord_3276744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276744).length < 2 ^ (prefixWord ++ tailWord_3276744).sum := by decide
  have hdescent : baseEnd_3276744 < baseStart_3276744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276750 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_3276750 : Nat := 118140960795 + 3276750 * 2 ^ 59
def prefixEnd_3276750 : Nat := 4983230072969 + 3 ^ 40 * 3276750 * 2
def baseEnd_3276750 : Nat := 1682547734620159934255507

theorem tailTrace_3276750 : CollatzResearch.WordTrace tailWord_3276750 prefixEnd_3276750 1682547734620159934255507 := by
  unfold tailWord_3276750
  simp only [CollatzResearch.WordTrace]
  refine ⟨14939111359862731148892463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79675260585934566127426469 14939111359862731148892463)
  ·
    refine ⟨22408667039794096723338695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14939111359862731148892463 22408667039794096723338695)
    ·
      refine ⟨33613000559691145085008043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22408667039794096723338695 33613000559691145085008043)
      ·
        refine ⟨50419500839536717627512065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33613000559691145085008043 50419500839536717627512065)
        ·
          refine ⟨37814625629652538220634049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50419500839536717627512065 37814625629652538220634049)
          ·
            refine ⟨28360969222239403665475537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37814625629652538220634049 28360969222239403665475537)
            ·
              refine ⟨21270726916679552749106653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28360969222239403665475537 21270726916679552749106653)
              ·
                refine ⟨7976522593754832280914995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21270726916679552749106653 7976522593754832280914995)
                ·
                  refine ⟨11964783890632248421372493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7976522593754832280914995 11964783890632248421372493)
                  ·
                    refine ⟨4486793958987093158014685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11964783890632248421372493 4486793958987093158014685)
                    ·
                      refine ⟨1682547734620159934255507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4486793958987093158014685 1682547734620159934255507)
                      ·
                        rfl

theorem cell23_3276750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_3276750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276750 prefixEnd_3276750 := by exact prefixLift 3276750
  have htrace : WordTrace (prefixWord ++ tailWord_3276750) baseStart_3276750 baseEnd_3276750 := by
    simpa [prefixWord, tailWord_3276750, baseEnd_3276750] using wordTrace_append hprefix tailTrace_3276750
  have hstable : (prefixWord ++ tailWord_3276750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276750).length < 2 ^ (prefixWord ++ tailWord_3276750).sum := by decide
  have hdescent : baseEnd_3276750 < baseStart_3276750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276783 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 2, 6]
def baseStart_3276783 : Nat := 118140960795 + 3276783 * 2 ^ 59
def prefixEnd_3276783 : Nat := 4983230072969 + 3 ^ 40 * 3276783 * 2
def baseEnd_3276783 : Nat := 560854893160586101714285

theorem tailTrace_3276783 : CollatzResearch.WordTrace tailWord_3276783 prefixEnd_3276783 560854893160586101714285 := by
  unfold tailWord_3276783
  simp only [CollatzResearch.WordTrace]
  refine ⟨119514094487782295827091003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79676062991854863884727335 119514094487782295827091003)
  ·
    refine ⟨179271141731673443740636505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119514094487782295827091003 179271141731673443740636505)
    ·
      refine ⟨134453356298755082805477379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179271141731673443740636505 134453356298755082805477379)
      ·
        refine ⟨201680034448132624208216069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134453356298755082805477379 201680034448132624208216069)
        ·
          refine ⟨37815006459024867039040513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201680034448132624208216069 37815006459024867039040513)
          ·
            refine ⟨28361254844268650279280385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37815006459024867039040513 28361254844268650279280385)
            ·
              refine ⟨21270941133201487709460289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28361254844268650279280385 21270941133201487709460289)
              ·
                refine ⟨15953205849901115782095217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21270941133201487709460289 15953205849901115782095217)
                ·
                  refine ⟨11964904387425836836571413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15953205849901115782095217 11964904387425836836571413)
                  ·
                    refine ⟨560854893160586101714285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11964904387425836836571413 560854893160586101714285)
                    ·
                      rfl

theorem cell23_3276783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 6].length) (baseStart_3276783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276783 prefixEnd_3276783 := by exact prefixLift 3276783
  have htrace : WordTrace (prefixWord ++ tailWord_3276783) baseStart_3276783 baseEnd_3276783 := by
    simpa [prefixWord, tailWord_3276783, baseEnd_3276783] using wordTrace_append hprefix tailTrace_3276783
  have hstable : (prefixWord ++ tailWord_3276783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276783).length < 2 ^ (prefixWord ++ tailWord_3276783).sum := by decide
  have hdescent : baseEnd_3276783 < baseStart_3276783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276785 : List Nat := [1, 2, 2, 2, 6, 1, 2, 2, 1, 2, 2]
def baseStart_3276785 : Nat := 118140960795 + 3276785 * 2 ^ 59
def prefixEnd_3276785 : Nat := 4983230072969 + 3 ^ 40 * 3276785 * 2
def baseEnd_3276785 : Nat := 1682565706443067297317847

theorem tailTrace_3276785 : CollatzResearch.WordTrace tailWord_3276785 prefixEnd_3276785 1682565706443067297317847 := by
  unfold tailWord_3276785
  simp only [CollatzResearch.WordTrace]
  refine ⟨119514167433775050168663809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79676111622516700112442539 119514167433775050168663809)
  ·
    refine ⟨89635625575331287626497857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119514167433775050168663809 89635625575331287626497857)
    ·
      refine ⟨67226719181498465719873393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89635625575331287626497857 67226719181498465719873393)
      ·
        refine ⟨50420039386123849289905045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67226719181498465719873393 50420039386123849289905045)
        ·
          refine ⟨2363439346224555435464299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50420039386123849289905045 2363439346224555435464299)
          ·
            refine ⟨3545159019336833153196449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2363439346224555435464299 3545159019336833153196449)
            ·
              refine ⟨2658869264502624864897337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3545159019336833153196449 2658869264502624864897337)
              ·
                refine ⟨1994151948376968648673003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2658869264502624864897337 1994151948376968648673003)
                ·
                  refine ⟨2991227922565452973009505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994151948376968648673003 2991227922565452973009505)
                  ·
                    refine ⟨2243420941924089729757129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2991227922565452973009505 2243420941924089729757129)
                    ·
                      refine ⟨1682565706443067297317847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2243420941924089729757129 1682565706443067297317847)
                      ·
                        rfl

theorem cell23_3276785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_3276785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276785 prefixEnd_3276785 := by exact prefixLift 3276785
  have htrace : WordTrace (prefixWord ++ tailWord_3276785) baseStart_3276785 baseEnd_3276785 := by
    simpa [prefixWord, tailWord_3276785, baseEnd_3276785] using wordTrace_append hprefix tailTrace_3276785
  have hstable : (prefixWord ++ tailWord_3276785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276785).length < 2 ^ (prefixWord ++ tailWord_3276785).sum := by decide
  have hdescent : baseEnd_3276785 < baseStart_3276785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276807 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 1, 4, 2]
def baseStart_3276807 : Nat := 118140960795 + 3276807 * 2 ^ 59
def prefixEnd_3276807 : Nat := 4983230072969 + 3 ^ 40 * 3276807 * 2
def baseEnd_3276807 : Nat := 1682577003017466211242745

theorem tailTrace_3276807 : CollatzResearch.WordTrace tailWord_3276807 prefixEnd_3276807 1682577003017466211242745 := by
  unfold tailWord_3276807
  simp only [CollatzResearch.WordTrace]
  refine ⟨119514969839695347925964675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79676646559796898617309783 119514969839695347925964675)
  ·
    refine ⟨179272454759543021888947013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119514969839695347925964675 179272454759543021888947013)
    ·
      refine ⟨33613585267414316604177565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179272454759543021888947013 33613585267414316604177565)
      ·
        refine ⟨12605094475280368726566587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33613585267414316604177565 12605094475280368726566587)
        ·
          refine ⟨18907641712920553089849881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12605094475280368726566587 18907641712920553089849881)
          ·
            refine ⟨14180731284690414817387411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18907641712920553089849881 14180731284690414817387411)
            ·
              refine ⟨21271096927035622226081117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14180731284690414817387411 21271096927035622226081117)
              ·
                refine ⟨7976661347638358334780419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21271096927035622226081117 7976661347638358334780419)
                ·
                  refine ⟨11964992021457537502170629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7976661347638358334780419 11964992021457537502170629)
                  ·
                    refine ⟨2243436004023288281656993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11964992021457537502170629 2243436004023288281656993)
                    ·
                      refine ⟨1682577003017466211242745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2243436004023288281656993 1682577003017466211242745)
                      ·
                        rfl

theorem cell23_3276807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_3276807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276807 prefixEnd_3276807 := by exact prefixLift 3276807
  have htrace : WordTrace (prefixWord ++ tailWord_3276807) baseStart_3276807 baseEnd_3276807 := by
    simpa [prefixWord, tailWord_3276807, baseEnd_3276807] using wordTrace_append hprefix tailTrace_3276807
  have hstable : (prefixWord ++ tailWord_3276807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276807).length < 2 ^ (prefixWord ++ tailWord_3276807).sum := by decide
  have hdescent : baseEnd_3276807 < baseStart_3276807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276873 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 2, 8]
def baseStart_3276873 : Nat := 118140960795 + 3276873 * 2 ^ 59
def prefixEnd_3276873 : Nat := 4983230072969 + 3 ^ 40 * 3276873 * 2
def baseEnd_3276873 : Nat := 560870297580220984339147

theorem tailTrace_3276873 : CollatzResearch.WordTrace tailWord_3276873 prefixEnd_3276873 560870297580220984339147 := by
  unfold tailWord_3276873
  simp only [CollatzResearch.WordTrace]
  refine ⟨119517377057456241197867273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79678251371637494131911515 119517377057456241197867273)
  ·
    refine ⟨89638032793092180898400455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119517377057456241197867273 89638032793092180898400455)
    ·
      refine ⟨134457049189638271347600683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89638032793092180898400455 134457049189638271347600683)
      ·
        refine ⟨201685573784457407021401025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134457049189638271347600683 201685573784457407021401025)
        ·
          refine ⟨151264180338343055266050769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201685573784457407021401025 151264180338343055266050769)
          ·
            refine ⟨113448135253757291449538077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151264180338343055266050769 113448135253757291449538077)
            ·
              refine ⟨42543050720158984293576779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113448135253757291449538077 42543050720158984293576779)
              ·
                refine ⟨63814576080238476440365169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42543050720158984293576779 63814576080238476440365169)
                ·
                  refine ⟨47860932060178857330273877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63814576080238476440365169 47860932060178857330273877)
                  ·
                    refine ⟨560870297580220984339147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47860932060178857330273877 560870297580220984339147)
                    ·
                      rfl

theorem cell23_3276873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_3276873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276873 prefixEnd_3276873 := by exact prefixLift 3276873
  have htrace : WordTrace (prefixWord ++ tailWord_3276873) baseStart_3276873 baseEnd_3276873 := by
    simpa [prefixWord, tailWord_3276873, baseEnd_3276873] using wordTrace_append hprefix tailTrace_3276873
  have hstable : (prefixWord ++ tailWord_3276873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276873).length < 2 ^ (prefixWord ++ tailWord_3276873).sum := by decide
  have hdescent : baseEnd_3276873 < baseStart_3276873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276877 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_3276877 : Nat := 118140960795 + 3276877 * 2 ^ 59
def prefixEnd_3276877 : Nat := 4983230072969 + 3 ^ 40 * 3276877 * 2
def baseEnd_3276877 : Nat := 560870982221093645789141

theorem tailTrace_3276877 : CollatzResearch.WordTrace tailWord_3276877 prefixEnd_3276877 560870982221093645789141 := by
  unfold tailWord_3276877
  simp only [CollatzResearch.WordTrace]
  refine ⟨119517522949441749881012885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79678348632961166587341923 119517522949441749881012885)
  ·
    refine ⟨5602383888255082025672479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119517522949441749881012885 5602383888255082025672479)
    ·
      refine ⟨8403575832382623038508719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5602383888255082025672479 8403575832382623038508719)
      ·
        refine ⟨12605363748573934557763079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8403575832382623038508719 12605363748573934557763079)
        ·
          refine ⟨18908045622860901836644619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12605363748573934557763079 18908045622860901836644619)
          ·
            refine ⟨28362068434291352754966929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18908045622860901836644619 28362068434291352754966929)
            ·
              refine ⟨21271551325718514566225197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28362068434291352754966929 21271551325718514566225197)
              ·
                refine ⟨7976831747144442962334449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21271551325718514566225197 7976831747144442962334449)
                ·
                  refine ⟨5982623810358332221750837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7976831747144442962334449 5982623810358332221750837)
                  ·
                    refine ⟨560870982221093645789141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5982623810358332221750837 560870982221093645789141)
                    ·
                      rfl

theorem cell23_3276877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_3276877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276877 prefixEnd_3276877 := by exact prefixLift 3276877
  have htrace : WordTrace (prefixWord ++ tailWord_3276877) baseStart_3276877 baseEnd_3276877 := by
    simpa [prefixWord, tailWord_3276877, baseEnd_3276877] using wordTrace_append hprefix tailTrace_3276877
  have hstable : (prefixWord ++ tailWord_3276877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276877).length < 2 ^ (prefixWord ++ tailWord_3276877).sum := by decide
  have hdescent : baseEnd_3276877 < baseStart_3276877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276954 : List Nat := [3, 1, 1, 5, 2, 1, 2, 2, 6]
def baseStart_3276954 : Nat := 118140960795 + 3276954 * 2 ^ 59
def prefixEnd_3276954 : Nat := 4983230072969 + 3 ^ 40 * 3276954 * 2
def baseEnd_3276954 : Nat := 186961387185964126233841

theorem tailTrace_3276954 : CollatzResearch.WordTrace tailWord_3276954 prefixEnd_3276954 186961387185964126233841 := by
  unfold tailWord_3276954
  simp only [CollatzResearch.WordTrace]
  refine ⟨29880082842540698007891479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79680220913441861354377277 29880082842540698007891479)
  ·
    refine ⟨44820124263811047011837219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29880082842540698007891479 44820124263811047011837219)
    ·
      refine ⟨67230186395716570517755829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44820124263811047011837219 67230186395716570517755829)
      ·
        refine ⟨6302829974598428486039609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67230186395716570517755829 6302829974598428486039609)
        ·
          refine ⟨4727122480948821364529707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6302829974598428486039609 4727122480948821364529707)
          ·
            refine ⟨7090683721423232046794561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4727122480948821364529707 7090683721423232046794561)
            ·
              refine ⟨5318012791067424035095921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7090683721423232046794561 5318012791067424035095921)
              ·
                refine ⟨3988509593300568026321941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5318012791067424035095921 3988509593300568026321941)
                ·
                  refine ⟨186961387185964126233841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3988509593300568026321941 186961387185964126233841)
                  ·
                    rfl

theorem cell23_3276954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 6].length) (baseStart_3276954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276954 prefixEnd_3276954 := by exact prefixLift 3276954
  have htrace : WordTrace (prefixWord ++ tailWord_3276954) baseStart_3276954 baseEnd_3276954 := by
    simpa [prefixWord, tailWord_3276954, baseEnd_3276954] using wordTrace_append hprefix tailTrace_3276954
  have hstable : (prefixWord ++ tailWord_3276954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276954).length < 2 ^ (prefixWord ++ tailWord_3276954).sum := by decide
  have hdescent : baseEnd_3276954 < baseStart_3276954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276958 : List Nat := [4, 3, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_3276958 : Nat := 118140960795 + 3276958 * 2 ^ 59
def prefixEnd_3276958 : Nat := 4983230072969 + 3 ^ 40 * 3276958 * 2
def baseEnd_3276958 : Nat := 560884846198765040151517

theorem tailTrace_3276958 : CollatzResearch.WordTrace tailWord_3276958 prefixEnd_3276958 560884846198765040151517 := by
  unfold tailWord_3276958
  simp only [CollatzResearch.WordTrace]
  refine ⟨14940059657768537589338941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79680318174765533809807685 14940059657768537589338941)
  ·
    refine ⟨5602522371663201596002103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14940059657768537589338941 5602522371663201596002103)
    ·
      refine ⟨8403783557494802394003155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5602522371663201596002103 8403783557494802394003155)
      ·
        refine ⟨12605675336242203591004733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8403783557494802394003155 12605675336242203591004733)
        ·
          refine ⟨4727128251090826346626775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12605675336242203591004733 4727128251090826346626775)
          ·
            refine ⟨7090692376636239519940163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4727128251090826346626775 7090692376636239519940163)
            ·
              refine ⟨10636038564954359279910245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7090692376636239519940163 10636038564954359279910245)
              ·
                refine ⟨1994257230928942364983171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10636038564954359279910245 1994257230928942364983171)
                ·
                  refine ⟨2991385846393413547474757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994257230928942364983171 2991385846393413547474757)
                  ·
                    refine ⟨560884846198765040151517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2991385846393413547474757 560884846198765040151517)
                    ·
                      rfl

theorem cell23_3276958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_3276958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276958 prefixEnd_3276958 := by exact prefixLift 3276958
  have htrace : WordTrace (prefixWord ++ tailWord_3276958) baseStart_3276958 baseEnd_3276958 := by
    simpa [prefixWord, tailWord_3276958, baseEnd_3276958] using wordTrace_append hprefix tailTrace_3276958
  have hstable : (prefixWord ++ tailWord_3276958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276958).length < 2 ^ (prefixWord ++ tailWord_3276958).sum := by decide
  have hdescent : baseEnd_3276958 < baseStart_3276958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3276987 : List Nat := [1, 1, 1, 1, 1, 2, 6, 4, 1, 1, 4]
def baseStart_3276987 : Nat := 118140960795 + 3276987 * 2 ^ 59
def prefixEnd_3276987 : Nat := 4983230072969 + 3 ^ 40 * 3276987 * 2
def baseEnd_3276987 : Nat := 1682669429535275506991917

theorem tailTrace_3276987 : CollatzResearch.WordTrace tailWord_3276987 prefixEnd_3276987 1682669429535275506991917 := by
  unfold tailWord_3276987
  simp only [CollatzResearch.WordTrace]
  refine ⟨119521534979043238667517215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79681023319362159111678143 119521534979043238667517215)
  ·
    refine ⟨179282302468564858001275823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119521534979043238667517215 179282302468564858001275823)
    ·
      refine ⟨268923453702847287001913735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179282302468564858001275823 268923453702847287001913735)
      ·
        refine ⟨403385180554270930502870603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268923453702847287001913735 403385180554270930502870603)
        ·
          refine ⟨605077770831406395754305905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403385180554270930502870603 605077770831406395754305905)
          ·
            refine ⟨453808328123554796815729429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605077770831406395754305905 453808328123554796815729429)
            ·
              refine ⟨21272265380791631100737317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 453808328123554796815729429 21272265380791631100737317)
              ·
                refine ⟨3988549758898430831388247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21272265380791631100737317 3988549758898430831388247)
                ·
                  refine ⟨5982824638347646247082371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988549758898430831388247 5982824638347646247082371)
                  ·
                    refine ⟨8974236957521469370623557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5982824638347646247082371 8974236957521469370623557)
                    ·
                      refine ⟨1682669429535275506991917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8974236957521469370623557 1682669429535275506991917)
                      ·
                        rfl

theorem cell23_3276987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 1, 4].length) (baseStart_3276987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3276987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3276987 prefixEnd_3276987 := by exact prefixLift 3276987
  have htrace : WordTrace (prefixWord ++ tailWord_3276987) baseStart_3276987 baseEnd_3276987 := by
    simpa [prefixWord, tailWord_3276987, baseEnd_3276987] using wordTrace_append hprefix tailTrace_3276987
  have hstable : (prefixWord ++ tailWord_3276987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3276987).length < 2 ^ (prefixWord ++ tailWord_3276987).sum := by decide
  have hdescent : baseEnd_3276987 < baseStart_3276987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3276987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277000 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_3277000 : Nat := 118140960795 + 3277000 * 2 ^ 59
def prefixEnd_3277000 : Nat := 4983230072969 + 3 ^ 40 * 3277000 * 2
def baseEnd_3277000 : Nat := 1682676104783783956129357

theorem tailTrace_3277000 : CollatzResearch.WordTrace tailWord_3277000 prefixEnd_3277000 1682676104783783956129357 := by
  unfold tailWord_3277000
  simp only [CollatzResearch.WordTrace]
  refine ⟨59761004563998070943870227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79681339418664094591826969 59761004563998070943870227)
  ·
    refine ⟨89641506845997106415805341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59761004563998070943870227 89641506845997106415805341)
    ·
      refine ⟨33615565067248914905927003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89641506845997106415805341 33615565067248914905927003)
      ·
        refine ⟨50423347600873372358890505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33615565067248914905927003 50423347600873372358890505)
        ·
          refine ⟨37817510700655029269167879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50423347600873372358890505 37817510700655029269167879)
          ·
            refine ⟨56726266050982543903751819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37817510700655029269167879 56726266050982543903751819)
            ·
              refine ⟨85089399076473815855627729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56726266050982543903751819 85089399076473815855627729)
              ·
                refine ⟨63817049307355361891720797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85089399076473815855627729 63817049307355361891720797)
                ·
                  refine ⟨23931393490258260709395299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63817049307355361891720797 23931393490258260709395299)
                  ·
                    refine ⟨35897090235387391064092949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23931393490258260709395299 35897090235387391064092949)
                    ·
                      refine ⟨1682676104783783956129357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35897090235387391064092949 1682676104783783956129357)
                      ·
                        rfl

theorem cell23_3277000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_3277000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277000 prefixEnd_3277000 := by exact prefixLift 3277000
  have htrace : WordTrace (prefixWord ++ tailWord_3277000) baseStart_3277000 baseEnd_3277000 := by
    simpa [prefixWord, tailWord_3277000, baseEnd_3277000] using wordTrace_append hprefix tailTrace_3277000
  have hstable : (prefixWord ++ tailWord_3277000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277000).length < 2 ^ (prefixWord ++ tailWord_3277000).sum := by decide
  have hdescent : baseEnd_3277000 < baseStart_3277000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277040 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 2, 7]
def baseStart_3277040 : Nat := 118140960795 + 3277040 * 2 ^ 59
def prefixEnd_3277040 : Nat := 4983230072969 + 3 ^ 40 * 3277040 * 2
def baseEnd_3277040 : Nat := 560898881336654599876391

theorem tailTrace_3277040 : CollatzResearch.WordTrace tailWord_3277040 prefixEnd_3277040 560898881336654599876391 := by
  unfold tailWord_3277040
  simp only [CollatzResearch.WordTrace]
  refine ⟨59761734023925614359598287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79682312031900819146131049 59761734023925614359598287)
  ·
    refine ⟨89642601035888421539397431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59761734023925614359598287 89642601035888421539397431)
    ·
      refine ⟨134463901553832632309096147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89642601035888421539397431 134463901553832632309096147)
      ·
        refine ⟨201695852330748948463644221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134463901553832632309096147 201695852330748948463644221)
        ·
          refine ⟨75635944624030855673866583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201695852330748948463644221 75635944624030855673866583)
          ·
            refine ⟨113453916936046283510799875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75635944624030855673866583 113453916936046283510799875)
            ·
              refine ⟨170180875404069425266199813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113453916936046283510799875 170180875404069425266199813)
              ·
                refine ⟨31908914138263017237412465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170180875404069425266199813 31908914138263017237412465)
                ·
                  refine ⟨23931685603697262928059349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31908914138263017237412465 23931685603697262928059349)
                  ·
                    refine ⟨560898881336654599876391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23931685603697262928059349 560898881336654599876391)
                    ·
                      rfl

theorem cell23_3277040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_3277040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277040 prefixEnd_3277040 := by exact prefixLift 3277040
  have htrace : WordTrace (prefixWord ++ tailWord_3277040) baseStart_3277040 baseEnd_3277040 := by
    simpa [prefixWord, tailWord_3277040, baseEnd_3277040] using wordTrace_append hprefix tailTrace_3277040
  have hstable : (prefixWord ++ tailWord_3277040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277040).length < 2 ^ (prefixWord ++ tailWord_3277040).sum := by decide
  have hdescent : baseEnd_3277040 < baseStart_3277040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277054 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_3277054 : Nat := 118140960795 + 3277054 * 2 ^ 59
def prefixEnd_3277054 : Nat := 4983230072969 + 3 ^ 40 * 3277054 * 2
def baseEnd_3277054 : Nat := 1682703832739126744854109

theorem tailTrace_3277054 : CollatzResearch.WordTrace tailWord_3277054 prefixEnd_3277054 1682703832739126744854109 := by
  unfold tailWord_3277054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14940497333725063638775777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79682652446533672740137477 14940497333725063638775777)
  ·
    refine ⟨11205373000293797729081833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14940497333725063638775777 11205373000293797729081833)
    ·
      refine ⟨8404029750220348296811375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11205373000293797729081833 8404029750220348296811375)
      ·
        refine ⟨12606044625330522445217063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8404029750220348296811375 12606044625330522445217063)
        ·
          refine ⟨18909066937995783667825595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12606044625330522445217063 18909066937995783667825595)
          ·
            refine ⟨28363600406993675501738393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18909066937995783667825595 28363600406993675501738393)
            ·
              refine ⟨21272700305245256626303795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28363600406993675501738393 21272700305245256626303795)
              ·
                refine ⟨31909050457867884939455693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21272700305245256626303795 31909050457867884939455693)
                ·
                  refine ⟨11965893921700456852295885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31909050457867884939455693 11965893921700456852295885)
                  ·
                    refine ⟨4487210220637671319610957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11965893921700456852295885 4487210220637671319610957)
                    ·
                      refine ⟨1682703832739126744854109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4487210220637671319610957 1682703832739126744854109)
                      ·
                        rfl

theorem cell23_3277054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_3277054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277054 prefixEnd_3277054 := by exact prefixLift 3277054
  have htrace : WordTrace (prefixWord ++ tailWord_3277054) baseStart_3277054 baseEnd_3277054 := by
    simpa [prefixWord, tailWord_3277054, baseEnd_3277054] using wordTrace_append hprefix tailTrace_3277054
  have hstable : (prefixWord ++ tailWord_3277054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277054).length < 2 ^ (prefixWord ++ tailWord_3277054).sum := by decide
  have hdescent : baseEnd_3277054 < baseStart_3277054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277088 : List Nat := [2, 1, 1, 5, 2, 1, 4, 1, 2, 1, 3]
def baseStart_3277088 : Nat := 118140960795 + 3277088 * 2 ^ 59
def prefixEnd_3277088 : Nat := 4983230072969 + 3 ^ 40 * 3277088 * 2
def baseEnd_3277088 : Nat := 1682721291081379611828953

theorem tailTrace_3277088 : CollatzResearch.WordTrace tailWord_3277088 prefixEnd_3277088 1682721291081379611828953 := by
  unfold tailWord_3277088
  simp only [CollatzResearch.WordTrace]
  refine ⟨59762609375838666458471959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79683479167784888611295945 59762609375838666458471959)
  ·
    refine ⟨89643914063757999687707939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59762609375838666458471959 89643914063757999687707939)
    ·
      refine ⟨134465871095636999531561909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89643914063757999687707939 134465871095636999531561909)
      ·
        refine ⟨12606175415215968706083929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134465871095636999531561909 12606175415215968706083929)
        ·
          refine ⟨9454631561411976529562947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12606175415215968706083929 9454631561411976529562947)
          ·
            refine ⟨14181947342117964794344421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9454631561411976529562947 14181947342117964794344421)
            ·
              refine ⟨2659115126647118398939579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14181947342117964794344421 2659115126647118398939579)
              ·
                refine ⟨3988672689970677598409369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659115126647118398939579 3988672689970677598409369)
                ·
                  refine ⟨2991504517478008198807027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3988672689970677598409369 2991504517478008198807027)
                  ·
                    refine ⟨4487256776217012298210541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2991504517478008198807027 4487256776217012298210541)
                    ·
                      refine ⟨1682721291081379611828953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4487256776217012298210541 1682721291081379611828953)
                      ·
                        rfl

theorem cell23_3277088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_3277088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277088 prefixEnd_3277088 := by exact prefixLift 3277088
  have htrace : WordTrace (prefixWord ++ tailWord_3277088) baseStart_3277088 baseEnd_3277088 := by
    simpa [prefixWord, tailWord_3277088, baseEnd_3277088] using wordTrace_append hprefix tailTrace_3277088
  have hstable : (prefixWord ++ tailWord_3277088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277088).length < 2 ^ (prefixWord ++ tailWord_3277088).sum := by decide
  have hdescent : baseEnd_3277088 < baseStart_3277088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277098 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_3277098 : Nat := 118140960795 + 3277098 * 2 ^ 59
def prefixEnd_3277098 : Nat := 4983230072969 + 3 ^ 40 * 3277098 * 2
def baseEnd_3277098 : Nat := 1682726425887924572703907

theorem tailTrace_3277098 : CollatzResearch.WordTrace tailWord_3277098 prefixEnd_3277098 1682726425887924572703907 := by
  unfold tailWord_3277098
  simp only [CollatzResearch.WordTrace]
  refine ⟨29881395870410276156201987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79683722321094069749871965 29881395870410276156201987)
  ·
    refine ⟨44822093805615414234302981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29881395870410276156201987 44822093805615414234302981)
    ·
      refine ⟨8404142588552890168931809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44822093805615414234302981 8404142588552890168931809)
      ·
        refine ⟨6303106941414667626698857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8404142588552890168931809 6303106941414667626698857)
        ·
          refine ⟨4727330206061000720024143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6303106941414667626698857 4727330206061000720024143)
          ·
            refine ⟨7090995309091501080036215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4727330206061000720024143 7090995309091501080036215)
            ·
              refine ⟨10636492963637251620054323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7090995309091501080036215 10636492963637251620054323)
              ·
                refine ⟨15954739445455877430081485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10636492963637251620054323 15954739445455877430081485)
                ·
                  refine ⟨5983027292045954036280557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15954739445455877430081485 5983027292045954036280557)
                  ·
                    refine ⟨2243635234517232763605209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5983027292045954036280557 2243635234517232763605209)
                    ·
                      refine ⟨1682726425887924572703907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2243635234517232763605209 1682726425887924572703907)
                      ·
                        rfl

theorem cell23_3277098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_3277098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277098 prefixEnd_3277098 := by exact prefixLift 3277098
  have htrace : WordTrace (prefixWord ++ tailWord_3277098) baseStart_3277098 baseEnd_3277098 := by
    simpa [prefixWord, tailWord_3277098, baseEnd_3277098] using wordTrace_append hprefix tailTrace_3277098
  have hstable : (prefixWord ++ tailWord_3277098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277098).length < 2 ^ (prefixWord ++ tailWord_3277098).sum := by decide
  have hdescent : baseEnd_3277098 < baseStart_3277098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277164 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 1, 7]
def baseStart_3277164 : Nat := 118140960795 + 3277164 * 2 ^ 59
def prefixEnd_3277164 : Nat := 4983230072969 + 3 ^ 40 * 3277164 * 2
def baseEnd_3277164 : Nat := 560920105203707104826201

theorem tailTrace_3277164 : CollatzResearch.WordTrace tailWord_3277164 prefixEnd_3277164 560920105203707104826201 := by
  unfold tailWord_3277164
  simp only [CollatzResearch.WordTrace]
  refine ⟨59763995349700998948355273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79685327132934665264473697 59763995349700998948355273)
  ·
    refine ⟨44822996512275749211266455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59763995349700998948355273 44822996512275749211266455)
    ·
      refine ⟨67234494768413623816899683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44822996512275749211266455 67234494768413623816899683)
      ·
        refine ⟨100851742152620435725349525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67234494768413623816899683 100851742152620435725349525)
        ·
          refine ⟨4727425413404082924625759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100851742152620435725349525 4727425413404082924625759)
          ·
            refine ⟨7091138120106124386938639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4727425413404082924625759 7091138120106124386938639)
            ·
              refine ⟨10636707180159186580407959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7091138120106124386938639 10636707180159186580407959)
              ·
                refine ⟨15955060770238779870611939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10636707180159186580407959 15955060770238779870611939)
                ·
                  refine ⟨23932591155358169805917909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15955060770238779870611939 23932591155358169805917909)
                  ·
                    refine ⟨560920105203707104826201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23932591155358169805917909 560920105203707104826201)
                    ·
                      rfl

theorem cell23_3277164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_3277164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277164 prefixEnd_3277164 := by exact prefixLift 3277164
  have htrace : WordTrace (prefixWord ++ tailWord_3277164) baseStart_3277164 baseEnd_3277164 := by
    simpa [prefixWord, tailWord_3277164, baseEnd_3277164] using wordTrace_append hprefix tailTrace_3277164
  have hstable : (prefixWord ++ tailWord_3277164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277164).length < 2 ^ (prefixWord ++ tailWord_3277164).sum := by decide
  have hdescent : baseEnd_3277164 < baseStart_3277164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277245 : List Nat := [1, 4, 1, 2, 2, 3, 3, 2, 1, 4]
def baseStart_3277245 : Nat := 118140960795 + 3277245 * 2 ^ 59
def prefixEnd_3277245 : Nat := 4983230072969 + 3 ^ 40 * 3277245 * 2
def baseEnd_3277245 : Nat := 560933969181378499188577

theorem tailTrace_3277245 : CollatzResearch.WordTrace tailWord_3277245 prefixEnd_3277245 560933969181378499188577 := by
  unfold tailWord_3277245
  simp only [CollatzResearch.WordTrace]
  refine ⟨119530945012108548730409189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79687296674739032486939459 119530945012108548730409189)
  ·
    refine ⟨22412052189770352886951723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119530945012108548730409189 22412052189770352886951723)
    ·
      refine ⟨33618078284655529330427585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22412052189770352886951723 33618078284655529330427585)
      ·
        refine ⟨25213558713491646997820689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33618078284655529330427585 25213558713491646997820689)
        ·
          refine ⟨18910169035118735248365517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25213558713491646997820689 18910169035118735248365517)
          ·
            refine ⟨7091313388169525718137069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18910169035118735248365517 7091313388169525718137069)
            ·
              refine ⟨2659242520563572144301401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7091313388169525718137069 2659242520563572144301401)
              ·
                refine ⟨1994431890422679108226051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2659242520563572144301401 1994431890422679108226051)
                ·
                  refine ⟨2991647835634018662339077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994431890422679108226051 2991647835634018662339077)
                  ·
                    refine ⟨560933969181378499188577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2991647835634018662339077 560933969181378499188577)
                    ·
                      rfl

theorem cell23_3277245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_3277245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277245 prefixEnd_3277245 := by exact prefixLift 3277245
  have htrace : WordTrace (prefixWord ++ tailWord_3277245) baseStart_3277245 baseEnd_3277245 := by
    simpa [prefixWord, tailWord_3277245, baseEnd_3277245] using wordTrace_append hprefix tailTrace_3277245
  have hstable : (prefixWord ++ tailWord_3277245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277245).length < 2 ^ (prefixWord ++ tailWord_3277245).sum := by decide
  have hdescent : baseEnd_3277245 < baseStart_3277245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277247 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 7]
def baseStart_3277247 : Nat := 118140960795 + 3277247 * 2 ^ 59
def prefixEnd_3277247 : Nat := 4983230072969 + 3 ^ 40 * 3277247 * 2
def baseEnd_3277247 : Nat := 1682802934505444489740721

theorem tailTrace_3277247 : CollatzResearch.WordTrace tailWord_3277247 prefixEnd_3277247 1682802934505444489740721 := by
  unfold tailWord_3277247
  simp only [CollatzResearch.WordTrace]
  refine ⟨119531017958101303071981995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79687345305400868714654663 119531017958101303071981995)
  ·
    refine ⟨179296526937151954607972993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119531017958101303071981995 179296526937151954607972993)
    ·
      refine ⟨134472395202863965955979745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179296526937151954607972993 134472395202863965955979745)
      ·
        refine ⟨100854296402147974466984809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134472395202863965955979745 100854296402147974466984809)
        ·
          refine ⟨75640722301610980850238607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100854296402147974466984809 75640722301610980850238607)
          ·
            refine ⟨113461083452416471275357911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75640722301610980850238607 113461083452416471275357911)
            ·
              refine ⟨170191625178624706913036867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113461083452416471275357911 170191625178624706913036867)
              ·
                refine ⟨255287437767937060369555301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170191625178624706913036867 255287437767937060369555301)
                ·
                  refine ⟨47866394581488198819291619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255287437767937060369555301 47866394581488198819291619)
                  ·
                    refine ⟨71799591872232298228937429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47866394581488198819291619 71799591872232298228937429)
                    ·
                      refine ⟨1682802934505444489740721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71799591872232298228937429 1682802934505444489740721)
                      ·
                        rfl

theorem cell23_3277247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_3277247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277247 prefixEnd_3277247 := by exact prefixLift 3277247
  have htrace : WordTrace (prefixWord ++ tailWord_3277247) baseStart_3277247 baseEnd_3277247 := by
    simpa [prefixWord, tailWord_3277247, baseEnd_3277247] using wordTrace_append hprefix tailTrace_3277247
  have hstable : (prefixWord ++ tailWord_3277247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277247).length < 2 ^ (prefixWord ++ tailWord_3277247).sum := by decide
  have hdescent : baseEnd_3277247 < baseStart_3277247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277288 : List Nat := [2, 1, 4, 1, 1, 4, 3, 1, 1, 5]
def baseStart_3277288 : Nat := 118140960795 + 3277288 * 2 ^ 59
def prefixEnd_3277288 : Nat := 4983230072969 + 3 ^ 40 * 3277288 * 2
def baseEnd_3277288 : Nat := 560941329070759609776011

theorem tailTrace_3277288 : CollatzResearch.WordTrace tailWord_3277288 prefixEnd_3277288 560941329070759609776011 := by
  unfold tailWord_3277288
  simp only [CollatzResearch.WordTrace]
  refine ⟨59766256675476383537112259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79688342233968511382816345 59766256675476383537112259)
  ·
    refine ⟨89649385013214575305668389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59766256675476383537112259 89649385013214575305668389)
    ·
      refine ⟨16809259689977732869812823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89649385013214575305668389 16809259689977732869812823)
      ·
        refine ⟨25213889534966599304719235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16809259689977732869812823 25213889534966599304719235)
        ·
          refine ⟨37820834302449898957078853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25213889534966599304719235 37820834302449898957078853)
          ·
            refine ⟨7091406431709356054452285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37820834302449898957078853 7091406431709356054452285)
            ·
              refine ⟨2659277411891008520419607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7091406431709356054452285 2659277411891008520419607)
              ·
                refine ⟨3988916117836512780629411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659277411891008520419607 3988916117836512780629411)
                ·
                  refine ⟨5983374176754769170944117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988916117836512780629411 5983374176754769170944117)
                  ·
                    refine ⟨560941329070759609776011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5983374176754769170944117 560941329070759609776011)
                    ·
                      rfl

theorem cell23_3277288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_3277288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277288 prefixEnd_3277288 := by exact prefixLift 3277288
  have htrace : WordTrace (prefixWord ++ tailWord_3277288) baseStart_3277288 baseEnd_3277288 := by
    simpa [prefixWord, tailWord_3277288, baseEnd_3277288] using wordTrace_append hprefix tailTrace_3277288
  have hstable : (prefixWord ++ tailWord_3277288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277288).length < 2 ^ (prefixWord ++ tailWord_3277288).sum := by decide
  have hdescent : baseEnd_3277288 < baseStart_3277288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277304 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_3277304 : Nat := 118140960795 + 3277304 * 2 ^ 59
def prefixEnd_3277304 : Nat := 4983230072969 + 3 ^ 40 * 3277304 * 2
def baseEnd_3277304 : Nat := 1682832202902750766727959

theorem tailTrace_3277304 : CollatzResearch.WordTrace tailWord_3277304 prefixEnd_3277304 1682832202902750766727959 := by
  unfold tailWord_3277304
  simp only [CollatzResearch.WordTrace]
  refine ⟨59766548459447400903403483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79688731279263201204537977 59766548459447400903403483)
  ·
    refine ⟨89649822689171101355105225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59766548459447400903403483 89649822689171101355105225)
    ·
      refine ⟨67237367016878326016328919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89649822689171101355105225 67237367016878326016328919)
      ·
        refine ⟨100856050525317489024493379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67237367016878326016328919 100856050525317489024493379)
        ·
          refine ⟨151284075787976233536740069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100856050525317489024493379 151284075787976233536740069)
          ·
            refine ⟨28365764210245543788138763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151284075787976233536740069 28365764210245543788138763)
            ·
              refine ⟨42548646315368315682208145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28365764210245543788138763 42548646315368315682208145)
              ·
                refine ⟨31911484736526236761656109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42548646315368315682208145 31911484736526236761656109)
                ·
                  refine ⟨11966806776197338785621041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31911484736526236761656109 11966806776197338785621041)
                  ·
                    refine ⟨8975105082148004089215781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11966806776197338785621041 8975105082148004089215781)
                    ·
                      refine ⟨1682832202902750766727959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8975105082148004089215781 1682832202902750766727959)
                      ·
                        rfl

theorem cell23_3277304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_3277304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277304 prefixEnd_3277304 := by exact prefixLift 3277304
  have htrace : WordTrace (prefixWord ++ tailWord_3277304) baseStart_3277304 baseEnd_3277304 := by
    simpa [prefixWord, tailWord_3277304, baseEnd_3277304] using wordTrace_append hprefix tailTrace_3277304
  have hstable : (prefixWord ++ tailWord_3277304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277304).length < 2 ^ (prefixWord ++ tailWord_3277304).sum := by decide
  have hdescent : baseEnd_3277304 < baseStart_3277304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277308 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 3, 2, 2]
def baseStart_3277308 : Nat := 118140960795 + 3277308 * 2 ^ 59
def prefixEnd_3277308 : Nat := 4983230072969 + 3 ^ 40 * 3277308 * 2
def baseEnd_3277308 : Nat := 1682834256825368751077941

theorem tailTrace_3277308 : CollatzResearch.WordTrace tailWord_3277308 prefixEnd_3277308 1682834256825368751077941 := by
  unfold tailWord_3277308
  simp only [CollatzResearch.WordTrace]
  refine ⟨59766621405440155244976289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79688828540586873659968385 59766621405440155244976289)
  ·
    refine ⟨44824966054080116433732217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59766621405440155244976289 44824966054080116433732217)
    ·
      refine ⟨33618724540560087325299163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44824966054080116433732217 33618724540560087325299163)
      ·
        refine ⟨50428086810840130987948745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33618724540560087325299163 50428086810840130987948745)
        ·
          refine ⟨37821065108130098240961559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50428086810840130987948745 37821065108130098240961559)
          ·
            refine ⟨56731597662195147361442339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37821065108130098240961559 56731597662195147361442339)
            ·
              refine ⟨85097396493292721042163509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56731597662195147361442339 85097396493292721042163509)
              ·
                refine ⟨7977880921246192597702829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85097396493292721042163509 7977880921246192597702829)
                ·
                  refine ⟨2991705345467322224138561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7977880921246192597702829 2991705345467322224138561)
                  ·
                    refine ⟨2243779009100491668103921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2991705345467322224138561 2243779009100491668103921)
                    ·
                      refine ⟨1682834256825368751077941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2243779009100491668103921 1682834256825368751077941)
                      ·
                        rfl

theorem cell23_3277308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_3277308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277308 prefixEnd_3277308 := by exact prefixLift 3277308
  have htrace : WordTrace (prefixWord ++ tailWord_3277308) baseStart_3277308 baseEnd_3277308 := by
    simpa [prefixWord, tailWord_3277308, baseEnd_3277308] using wordTrace_append hprefix tailTrace_3277308
  have hstable : (prefixWord ++ tailWord_3277308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277308).length < 2 ^ (prefixWord ++ tailWord_3277308).sum := by decide
  have hdescent : baseEnd_3277308 < baseStart_3277308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277325 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3277325 : Nat := 118140960795 + 3277325 * 2 ^ 59
def prefixEnd_3277325 : Nat := 4983230072969 + 3 ^ 40 * 3277325 * 2
def baseEnd_3277325 : Nat := 1682842985996495184565363

theorem tailTrace_3277325 : CollatzResearch.WordTrace tailWord_3277325 prefixEnd_3277325 1682842985996495184565363 := by
  unfold tailWord_3277325
  simp only [CollatzResearch.WordTrace]
  refine ⟨119533862851818722393321429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79689241901212481595547619 119533862851818722393321429)
  ·
    refine ⟨2801574910589501306093471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 119533862851818722393321429 2801574910589501306093471)
    ·
      refine ⟨4202362365884251959140207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2801574910589501306093471 4202362365884251959140207)
      ·
        refine ⟨6303543548826377938710311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4202362365884251959140207 6303543548826377938710311)
        ·
          refine ⟨9455315323239566908065467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6303543548826377938710311 9455315323239566908065467)
          ·
            refine ⟨14182972984859350362098201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9455315323239566908065467 14182972984859350362098201)
            ·
              refine ⟨10637229738644512771573651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14182972984859350362098201 10637229738644512771573651)
              ·
                refine ⟨15955844607966769157360477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10637229738644512771573651 15955844607966769157360477)
                ·
                  refine ⟨5983441727987538434010179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15955844607966769157360477 5983441727987538434010179)
                  ·
                    refine ⟨8975162591981307651015269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5983441727987538434010179 8975162591981307651015269)
                    ·
                      refine ⟨1682842985996495184565363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8975162591981307651015269 1682842985996495184565363)
                      ·
                        rfl

theorem cell23_3277325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3277325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277325 prefixEnd_3277325 := by exact prefixLift 3277325
  have htrace : WordTrace (prefixWord ++ tailWord_3277325) baseStart_3277325 baseEnd_3277325 := by
    simpa [prefixWord, tailWord_3277325, baseEnd_3277325] using wordTrace_append hprefix tailTrace_3277325
  have hstable : (prefixWord ++ tailWord_3277325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277325).length < 2 ^ (prefixWord ++ tailWord_3277325).sum := by decide
  have hdescent : baseEnd_3277325 < baseStart_3277325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277375 : List Nat := [1, 1, 2, 2, 3, 2, 5, 1, 2, 1, 3]
def baseStart_3277375 : Nat := 118140960795 + 3277375 * 2 ^ 59
def prefixEnd_3277375 : Nat := 4983230072969 + 3 ^ 40 * 3277375 * 2
def baseEnd_3277375 : Nat := 1682868660029219988940133

theorem tailTrace_3277375 : CollatzResearch.WordTrace tailWord_3277375 prefixEnd_3277375 1682868660029219988940133 := by
  unfold tailWord_3277375
  simp only [CollatzResearch.WordTrace]
  refine ⟨119535686501637580932641579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79690457667758387288427719 119535686501637580932641579)
  ·
    refine ⟨179303529752456371398962369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119535686501637580932641579 179303529752456371398962369)
    ·
      refine ⟨134477647314342278549221777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179303529752456371398962369 134477647314342278549221777)
      ·
        refine ⟨100858235485756708911916333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134477647314342278549221777 100858235485756708911916333)
        ·
          refine ⟨37821838307158765841968625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100858235485756708911916333 37821838307158765841968625)
          ·
            refine ⟨28366378730369074381476469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37821838307158765841968625 28366378730369074381476469)
            ·
              refine ⟨2659348005972100723263419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28366378730369074381476469 2659348005972100723263419)
              ·
                refine ⟨3989022008958151084895129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659348005972100723263419 3989022008958151084895129)
                ·
                  refine ⟨2991766506718613313671347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3989022008958151084895129 2991766506718613313671347)
                  ·
                    refine ⟨4487649760077919970507021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2991766506718613313671347 4487649760077919970507021)
                    ·
                      refine ⟨1682868660029219988940133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4487649760077919970507021 1682868660029219988940133)
                      ·
                        rfl

theorem cell23_3277375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 2, 1, 3].length) (baseStart_3277375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277375 prefixEnd_3277375 := by exact prefixLift 3277375
  have htrace : WordTrace (prefixWord ++ tailWord_3277375) baseStart_3277375 baseEnd_3277375 := by
    simpa [prefixWord, tailWord_3277375, baseEnd_3277375] using wordTrace_append hprefix tailTrace_3277375
  have hstable : (prefixWord ++ tailWord_3277375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277375).length < 2 ^ (prefixWord ++ tailWord_3277375).sum := by decide
  have hdescent : baseEnd_3277375 < baseStart_3277375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277384 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_3277384 : Nat := 118140960795 + 3277384 * 2 ^ 59
def prefixEnd_3277384 : Nat := 4983230072969 + 3 ^ 40 * 3277384 * 2
def baseEnd_3277384 : Nat := 1682873281355110453727591

theorem tailTrace_3277384 : CollatzResearch.WordTrace tailWord_3277384 prefixEnd_3277384 1682873281355110453727591 := by
  unfold tailWord_3277384
  simp only [CollatzResearch.WordTrace]
  refine ⟨59768007379302487734859603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79690676505736650313146137 59768007379302487734859603)
  ·
    refine ⟨89652011068953731602289405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59768007379302487734859603 89652011068953731602289405)
    ·
      refine ⟨33619504150857649350858527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89652011068953731602289405 33619504150857649350858527)
      ·
        refine ⟨50429256226286474026287791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33619504150857649350858527 50429256226286474026287791)
        ·
          refine ⟨75643884339429711039431687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50429256226286474026287791 75643884339429711039431687)
          ·
            refine ⟨113465826509144566559147531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75643884339429711039431687 113465826509144566559147531)
            ·
              refine ⟨170198739763716849838721297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113465826509144566559147531 170198739763716849838721297)
              ·
                refine ⟨127649054822787637379040973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170198739763716849838721297 127649054822787637379040973)
                ·
                  refine ⟨47868395558545364017140365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127649054822787637379040973 47868395558545364017140365)
                  ·
                    refine ⟨17950648334454511506427637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47868395558545364017140365 17950648334454511506427637)
                    ·
                      refine ⟨1682873281355110453727591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17950648334454511506427637 1682873281355110453727591)
                      ·
                        rfl

theorem cell23_3277384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_3277384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277384 prefixEnd_3277384 := by exact prefixLift 3277384
  have htrace : WordTrace (prefixWord ++ tailWord_3277384) baseStart_3277384 baseEnd_3277384 := by
    simpa [prefixWord, tailWord_3277384, baseEnd_3277384] using wordTrace_append hprefix tailTrace_3277384
  have hstable : (prefixWord ++ tailWord_3277384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277384).length < 2 ^ (prefixWord ++ tailWord_3277384).sum := by decide
  have hdescent : baseEnd_3277384 < baseStart_3277384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277415 : List Nat := [1, 1, 5, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_3277415 : Nat := 118140960795 + 3277415 * 2 ^ 59
def prefixEnd_3277415 : Nat := 4983230072969 + 3 ^ 40 * 3277415 * 2
def baseEnd_3277415 : Nat := 1682889199255399832439949

theorem tailTrace_3277415 : CollatzResearch.WordTrace tailWord_3277415 prefixEnd_3277415 1682889199255399832439949 := by
  unfold tailWord_3277415
  simp only [CollatzResearch.WordTrace]
  refine ⟨119537145421492667764097699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79691430280995111842731799 119537145421492667764097699)
  ·
    refine ⟨179305718132239001646146549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119537145421492667764097699 179305718132239001646146549)
    ·
      refine ⟨16809911074897406404326239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179305718132239001646146549 16809911074897406404326239)
      ·
        refine ⟨25214866612346109606489359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16809911074897406404326239 25214866612346109606489359)
        ·
          refine ⟨37822299918519164409734039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25214866612346109606489359 37822299918519164409734039)
          ·
            refine ⟨56733449877778746614601059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37822299918519164409734039 56733449877778746614601059)
            ·
              refine ⟨85100174816668119921901589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56733449877778746614601059 85100174816668119921901589)
              ·
                refine ⟨3989070694531318121339137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85100174816668119921901589 3989070694531318121339137)
                ·
                  refine ⟨2991803020898488591004353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3989070694531318121339137 2991803020898488591004353)
                  ·
                    refine ⟨2243852265673866443253265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2991803020898488591004353 2243852265673866443253265)
                    ·
                      refine ⟨1682889199255399832439949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2243852265673866443253265 1682889199255399832439949)
                      ·
                        rfl

theorem cell23_3277415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_3277415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277415 prefixEnd_3277415 := by exact prefixLift 3277415
  have htrace : WordTrace (prefixWord ++ tailWord_3277415) baseStart_3277415 baseEnd_3277415 := by
    simpa [prefixWord, tailWord_3277415, baseEnd_3277415] using wordTrace_append hprefix tailTrace_3277415
  have hstable : (prefixWord ++ tailWord_3277415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277415).length < 2 ^ (prefixWord ++ tailWord_3277415).sum := by decide
  have hdescent : baseEnd_3277415 < baseStart_3277415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277431 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 3]
def baseStart_3277431 : Nat := 118140960795 + 3277431 * 2 ^ 59
def prefixEnd_3277431 : Nat := 4983230072969 + 3 ^ 40 * 3277431 * 2
def baseEnd_3277431 : Nat := 1682897414945871769839875

theorem tailTrace_3277431 : CollatzResearch.WordTrace tailWord_3277431 prefixEnd_3277431 1682897414945871769839875 := by
  unfold tailWord_3277431
  simp only [CollatzResearch.WordTrace]
  refine ⟨119537728989434702496680147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79691819326289801664453431 119537728989434702496680147)
  ·
    refine ⟨179306593484152053745020221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119537728989434702496680147 179306593484152053745020221)
    ·
      refine ⟨67239972556557020154382583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179306593484152053745020221 67239972556557020154382583)
      ·
        refine ⟨100859958834835530231573875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67239972556557020154382583 100859958834835530231573875)
        ·
          refine ⟨151289938252253295347360813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100859958834835530231573875 151289938252253295347360813)
          ·
            refine ⟨56733726844594985755260305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151289938252253295347360813 56733726844594985755260305)
            ·
              refine ⟨42550295133446239316445229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56733726844594985755260305 42550295133446239316445229)
              ·
                refine ⟨15956360675042339743666961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42550295133446239316445229 15956360675042339743666961)
                ·
                  refine ⟨11967270506281754807750221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15956360675042339743666961 11967270506281754807750221)
                  ·
                    refine ⟨4487726439855658052906333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11967270506281754807750221 4487726439855658052906333)
                    ·
                      refine ⟨1682897414945871769839875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4487726439855658052906333 1682897414945871769839875)
                      ·
                        rfl

theorem cell23_3277431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_3277431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277431 prefixEnd_3277431 := by exact prefixLift 3277431
  have htrace : WordTrace (prefixWord ++ tailWord_3277431) baseStart_3277431 baseEnd_3277431 := by
    simpa [prefixWord, tailWord_3277431, baseEnd_3277431] using wordTrace_append hprefix tailTrace_3277431
  have hstable : (prefixWord ++ tailWord_3277431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277431).length < 2 ^ (prefixWord ++ tailWord_3277431).sum := by decide
  have hdescent : baseEnd_3277431 < baseStart_3277431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277468 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 2, 5]
def baseStart_3277468 : Nat := 118140960795 + 3277468 * 2 ^ 59
def prefixEnd_3277468 : Nat := 4983230072969 + 3 ^ 40 * 3277468 * 2
def baseEnd_3277468 : Nat := 560972137910029375025735

theorem tailTrace_3277468 : CollatzResearch.WordTrace tailWord_3277468 prefixEnd_3277468 560972137910029375025735 := by
  unfold tailWord_3277468
  simp only [CollatzResearch.WordTrace]
  refine ⟨59769539245150328907888529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79692718993533771877184705 59769539245150328907888529)
  ·
    refine ⟨44827154433862746680916397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59769539245150328907888529 44827154433862746680916397)
    ·
      refine ⟨16810182912698530005343649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44827154433862746680916397 16810182912698530005343649)
      ·
        refine ⟨12607637184523897504007737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16810182912698530005343649 12607637184523897504007737)
        ·
          refine ⟨9455727888392923128005803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12607637184523897504007737 9455727888392923128005803)
          ·
            refine ⟨14183591832589384692008705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9455727888392923128005803 14183591832589384692008705)
            ·
              refine ⟨10637693874442038519006529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14183591832589384692008705 10637693874442038519006529)
              ·
                refine ⟨7978270405831528889254897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10637693874442038519006529 7978270405831528889254897)
                ·
                  refine ⟨5983702804373646666941173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7978270405831528889254897 5983702804373646666941173)
                  ·
                    refine ⟨560972137910029375025735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5983702804373646666941173 560972137910029375025735)
                    ·
                      rfl

theorem cell23_3277468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_3277468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277468 prefixEnd_3277468 := by exact prefixLift 3277468
  have htrace : WordTrace (prefixWord ++ tailWord_3277468) baseStart_3277468 baseEnd_3277468 := by
    simpa [prefixWord, tailWord_3277468, baseEnd_3277468] using wordTrace_append hprefix tailTrace_3277468
  have hstable : (prefixWord ++ tailWord_3277468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277468).length < 2 ^ (prefixWord ++ tailWord_3277468).sum := by decide
  have hdescent : baseEnd_3277468 < baseStart_3277468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277472 : List Nat := [2, 1, 1, 4, 4, 2, 2, 2, 5]
def baseStart_3277472 : Nat := 118140960795 + 3277472 * 2 ^ 59
def prefixEnd_3277472 : Nat := 4983230072969 + 3 ^ 40 * 3277472 * 2
def baseEnd_3277472 : Nat := 186990940850300678825243

theorem tailTrace_3277472 : CollatzResearch.WordTrace tailWord_3277472 prefixEnd_3277472 186990940850300678825243 := by
  unfold tailWord_3277472
  simp only [CollatzResearch.WordTrace]
  refine ⟨59769612191143083249461335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79692816254857444332615113 59769612191143083249461335)
  ·
    refine ⟨89654418286714624874192003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59769612191143083249461335 89654418286714624874192003)
    ·
      refine ⟨134481627430071937311288005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89654418286714624874192003 134481627430071937311288005)
      ·
        refine ⟨25215305143138488245866501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134481627430071937311288005 25215305143138488245866501)
        ·
          refine ⟨4727869714338466546099969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25215305143138488245866501 4727869714338466546099969)
          ·
            refine ⟨3545902285753849909574977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4727869714338466546099969 3545902285753849909574977)
            ·
              refine ⟨2659426714315387432181233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3545902285753849909574977 2659426714315387432181233)
              ·
                refine ⟨1994570035736540574135925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2659426714315387432181233 1994570035736540574135925)
                ·
                  refine ⟨186990940850300678825243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1994570035736540574135925 186990940850300678825243)
                  ·
                    rfl

theorem cell23_3277472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 5].length) (baseStart_3277472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277472 prefixEnd_3277472 := by exact prefixLift 3277472
  have htrace : WordTrace (prefixWord ++ tailWord_3277472) baseStart_3277472 baseEnd_3277472 := by
    simpa [prefixWord, tailWord_3277472, baseEnd_3277472] using wordTrace_append hprefix tailTrace_3277472
  have hstable : (prefixWord ++ tailWord_3277472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277472).length < 2 ^ (prefixWord ++ tailWord_3277472).sum := by decide
  have hdescent : baseEnd_3277472 < baseStart_3277472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277482 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3277482 : Nat := 118140960795 + 3277482 * 2 ^ 59
def prefixEnd_3277482 : Nat := 4983230072969 + 3 ^ 40 * 3277482 * 2
def baseEnd_3277482 : Nat := 1682923602459251070302141

theorem tailTrace_3277482 : CollatzResearch.WordTrace tailWord_3277482 prefixEnd_3277482 1682923602459251070302141 := by
  unfold tailWord_3277482
  simp only [CollatzResearch.WordTrace]
  refine ⟨29884897278062484551696675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79693059408166625471191133 29884897278062484551696675)
  ·
    refine ⟨44827345917093726827545013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29884897278062484551696675 44827345917093726827545013)
    ·
      refine ⟨4202563679727536890082345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44827345917093726827545013 4202563679727536890082345)
      ·
        refine ⟨3151922759795652667561759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4202563679727536890082345 3151922759795652667561759)
        ·
          refine ⟨4727884139693479001342639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3151922759795652667561759 4727884139693479001342639)
          ·
            refine ⟨7091826209540218502013959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4727884139693479001342639 7091826209540218502013959)
            ·
              refine ⟨10637739314310327753020939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7091826209540218502013959 10637739314310327753020939)
              ·
                refine ⟨15956608971465491629531409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10637739314310327753020939 15956608971465491629531409)
                ·
                  refine ⟨11967456728599118722148557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15956608971465491629531409 11967456728599118722148557)
                  ·
                    refine ⟨4487796273224669520805709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11967456728599118722148557 4487796273224669520805709)
                    ·
                      refine ⟨1682923602459251070302141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4487796273224669520805709 1682923602459251070302141)
                      ·
                        rfl

theorem cell23_3277482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3277482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277482 prefixEnd_3277482 := by exact prefixLift 3277482
  have htrace : WordTrace (prefixWord ++ tailWord_3277482) baseStart_3277482 baseEnd_3277482 := by
    simpa [prefixWord, tailWord_3277482, baseEnd_3277482] using wordTrace_append hprefix tailTrace_3277482
  have hstable : (prefixWord ++ tailWord_3277482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277482).length < 2 ^ (prefixWord ++ tailWord_3277482).sum := by decide
  have hdescent : baseEnd_3277482 < baseStart_3277482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277498 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 3, 4]
def baseStart_3277498 : Nat := 118140960795 + 3277498 * 2 ^ 59
def prefixEnd_3277498 : Nat := 4983230072969 + 3 ^ 40 * 3277498 * 2
def baseEnd_3277498 : Nat := 560977272716574335900689

theorem tailTrace_3277498 : CollatzResearch.WordTrace tailWord_3277498 prefixEnd_3277498 560977272716574335900689 := by
  unfold tailWord_3277498
  simp only [CollatzResearch.WordTrace]
  refine ⟨29885043170047993234842287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79693448453461315292912765 29885043170047993234842287)
  ·
    refine ⟨44827564755071989852263431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29885043170047993234842287 44827564755071989852263431)
    ·
      refine ⟨67241347132607984778395147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44827564755071989852263431 67241347132607984778395147)
      ·
        refine ⟨100862020698911977167592721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67241347132607984778395147 100862020698911977167592721)
        ·
          refine ⟨75646515524183982875694541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100862020698911977167592721 75646515524183982875694541)
          ·
            refine ⟨28367443321568993578385453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75646515524183982875694541 28367443321568993578385453)
            ·
              refine ⟨10637791245588372591894545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28367443321568993578385453 10637791245588372591894545)
              ·
                refine ⟨7978343434191279443920909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10637791245588372591894545 7978343434191279443920909)
                ·
                  refine ⟨2991878787821729791470341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7978343434191279443920909 2991878787821729791470341)
                  ·
                    refine ⟨560977272716574335900689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2991878787821729791470341 560977272716574335900689)
                    ·
                      rfl

theorem cell23_3277498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_3277498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277498 prefixEnd_3277498 := by exact prefixLift 3277498
  have htrace : WordTrace (prefixWord ++ tailWord_3277498) baseStart_3277498 baseEnd_3277498 := by
    simpa [prefixWord, tailWord_3277498, baseEnd_3277498] using wordTrace_append hprefix tailTrace_3277498
  have hstable : (prefixWord ++ tailWord_3277498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277498).length < 2 ^ (prefixWord ++ tailWord_3277498).sum := by decide
  have hdescent : baseEnd_3277498 < baseStart_3277498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277528 : List Nat := [2, 1, 2, 2, 3, 2, 3, 2, 6]
def baseStart_3277528 : Nat := 118140960795 + 3277528 * 2 ^ 59
def prefixEnd_3277528 : Nat := 4983230072969 + 3 ^ 40 * 3277528 * 2
def baseEnd_3277528 : Nat := 186994135841039765591881

theorem tailTrace_3277528 : CollatzResearch.WordTrace tailWord_3277528 prefixEnd_3277528 186994135841039765591881 := by
  unfold tailWord_3277528
  simp only [CollatzResearch.WordTrace]
  refine ⟨59770633435041644031480619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79694177913388858708640825 59770633435041644031480619)
  ·
    refine ⟨89655950152562466047220929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59770633435041644031480619 89655950152562466047220929)
    ·
      refine ⟨67241962614421849535415697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89655950152562466047220929 67241962614421849535415697)
      ·
        refine ⟨50431471960816387151561773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67241962614421849535415697 50431471960816387151561773)
        ·
          refine ⟨18911801985306145181835665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50431471960816387151561773 18911801985306145181835665)
          ·
            refine ⟨14183851488979608886376749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18911801985306145181835665 14183851488979608886376749)
            ·
              refine ⟨5318944308367353332391281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14183851488979608886376749 5318944308367353332391281)
              ·
                refine ⟨3989208231275514999293461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5318944308367353332391281 3989208231275514999293461)
                ·
                  refine ⟨186994135841039765591881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3989208231275514999293461 186994135841039765591881)
                  ·
                    rfl

theorem cell23_3277528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 6].length) (baseStart_3277528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277528 prefixEnd_3277528 := by exact prefixLift 3277528
  have htrace : WordTrace (prefixWord ++ tailWord_3277528) baseStart_3277528 baseEnd_3277528 := by
    simpa [prefixWord, tailWord_3277528, baseEnd_3277528] using wordTrace_append hprefix tailTrace_3277528
  have hstable : (prefixWord ++ tailWord_3277528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277528).length < 2 ^ (prefixWord ++ tailWord_3277528).sum := by decide
  have hdescent : baseEnd_3277528 < baseStart_3277528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277532 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3277532 : Nat := 118140960795 + 3277532 * 2 ^ 59
def prefixEnd_3277532 : Nat := 4983230072969 + 3 ^ 40 * 3277532 * 2
def baseEnd_3277532 : Nat := 560983092163991958225637

theorem tailTrace_3277532 : CollatzResearch.WordTrace tailWord_3277532 prefixEnd_3277532 560983092163991958225637 := by
  unfold tailWord_3277532
  simp only [CollatzResearch.WordTrace]
  refine ⟨59770706381034398373053425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79694275174712531164071233 59770706381034398373053425)
  ·
    refine ⟨44828029785775798779790069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59770706381034398373053425 44828029785775798779790069)
    ·
      refine ⟨4202627792416481135605319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44828029785775798779790069 4202627792416481135605319)
      ·
        refine ⟨6303941688624721703407979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4202627792416481135605319 6303941688624721703407979)
        ·
          refine ⟨9455912532937082555111969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6303941688624721703407979 9455912532937082555111969)
          ·
            refine ⟨7091934399702811916333977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9455912532937082555111969 7091934399702811916333977)
            ·
              refine ⟨5318950799777108937250483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7091934399702811916333977 5318950799777108937250483)
              ·
                refine ⟨7978426199665663405875725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5318950799777108937250483 7978426199665663405875725)
                ·
                  refine ⟨2991909824874623777203397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7978426199665663405875725 2991909824874623777203397)
                  ·
                    refine ⟨560983092163991958225637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2991909824874623777203397 560983092163991958225637)
                    ·
                      rfl

theorem cell23_3277532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3277532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277532 prefixEnd_3277532 := by exact prefixLift 3277532
  have htrace : WordTrace (prefixWord ++ tailWord_3277532) baseStart_3277532 baseEnd_3277532 := by
    simpa [prefixWord, tailWord_3277532, baseEnd_3277532] using wordTrace_append hprefix tailTrace_3277532
  have hstable : (prefixWord ++ tailWord_3277532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277532).length < 2 ^ (prefixWord ++ tailWord_3277532).sum := by decide
  have hdescent : baseEnd_3277532 < baseStart_3277532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277561 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 2, 5, 4]
def baseStart_3277561 : Nat := 118140960795 + 3277561 * 2 ^ 59
def prefixEnd_3277561 : Nat := 4983230072969 + 3 ^ 40 * 3277561 * 2
def baseEnd_3277561 : Nat := 1682964167430956261214277

theorem tailTrace_3277561 : CollatzResearch.WordTrace tailWord_3277561 prefixEnd_3277561 1682964167430956261214277 := by
  unfold tailWord_3277561
  simp only [CollatzResearch.WordTrace]
  refine ⟨119542470478963734698912537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79694980319309156465941691 119542470478963734698912537)
  ·
    refine ⟨89656852859222801024184403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119542470478963734698912537 89656852859222801024184403)
    ·
      refine ⟨134485279288834201536276605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89656852859222801024184403 134485279288834201536276605)
      ·
        refine ⟨50431979733312825576103727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134485279288834201536276605 50431979733312825576103727)
        ·
          refine ⟨75647969599969238364155591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50431979733312825576103727 75647969599969238364155591)
          ·
            refine ⟨113471954399953857546233387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75647969599969238364155591 113471954399953857546233387)
            ·
              refine ⟨170207931599930786319350081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113471954399953857546233387 170207931599930786319350081)
              ·
                refine ⟨127655948699948089739512561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170207931599930786319350081 127655948699948089739512561)
                ·
                  refine ⟨95741961524961067304634421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127655948699948089739512561 95741961524961067304634421)
                  ·
                    refine ⟨8975808892965100059809477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95741961524961067304634421 8975808892965100059809477)
                    ·
                      refine ⟨1682964167430956261214277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8975808892965100059809477 1682964167430956261214277)
                      ·
                        rfl

theorem cell23_3277561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_3277561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277561 prefixEnd_3277561 := by exact prefixLift 3277561
  have htrace : WordTrace (prefixWord ++ tailWord_3277561) baseStart_3277561 baseEnd_3277561 := by
    simpa [prefixWord, tailWord_3277561, baseEnd_3277561] using wordTrace_append hprefix tailTrace_3277561
  have hstable : (prefixWord ++ tailWord_3277561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277561).length < 2 ^ (prefixWord ++ tailWord_3277561).sum := by decide
  have hdescent : baseEnd_3277561 < baseStart_3277561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277565 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 2, 3, 2]
def baseStart_3277565 : Nat := 118140960795 + 3277565 * 2 ^ 59
def prefixEnd_3277565 : Nat := 4983230072969 + 3 ^ 40 * 3277565 * 2
def baseEnd_3277565 : Nat := 1682966221353574245564259

theorem tailTrace_3277565 : CollatzResearch.WordTrace tailWord_3277565 prefixEnd_3277565 1682966221353574245564259 := by
  unfold tailWord_3277565
  simp only [CollatzResearch.WordTrace]
  refine ⟨119542616370949243382058149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79695077580632828921372099 119542616370949243382058149)
  ·
    refine ⟨22414240569552983134135903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119542616370949243382058149 22414240569552983134135903)
    ·
      refine ⟨33621360854329474701203855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22414240569552983134135903 33621360854329474701203855)
      ·
        refine ⟨50432041281494212051805783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33621360854329474701203855 50432041281494212051805783)
        ·
          refine ⟨75648061922241318077708675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50432041281494212051805783 75648061922241318077708675)
          ·
            refine ⟨113472092883361977116563013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75648061922241318077708675 113472092883361977116563013)
            ·
              refine ⟨21276017415630370709355565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113472092883361977116563013 21276017415630370709355565)
              ·
                refine ⟨7978506530861389016008337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21276017415630370709355565 7978506530861389016008337)
                ·
                  refine ⟨5983879898146041762006253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7978506530861389016008337 5983879898146041762006253)
                  ·
                    refine ⟨2243954961804765660752345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5983879898146041762006253 2243954961804765660752345)
                    ·
                      refine ⟨1682966221353574245564259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2243954961804765660752345 1682966221353574245564259)
                      ·
                        rfl

theorem cell23_3277565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_3277565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277565 prefixEnd_3277565 := by exact prefixLift 3277565
  have htrace : WordTrace (prefixWord ++ tailWord_3277565) baseStart_3277565 baseEnd_3277565 := by
    simpa [prefixWord, tailWord_3277565, baseEnd_3277565] using wordTrace_append hprefix tailTrace_3277565
  have hstable : (prefixWord ++ tailWord_3277565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277565).length < 2 ^ (prefixWord ++ tailWord_3277565).sum := by decide
  have hdescent : baseEnd_3277565 < baseStart_3277565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277571 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 3, 6]
def baseStart_3277571 : Nat := 118140960795 + 3277571 * 2 ^ 59
def prefixEnd_3277571 : Nat := 4983230072969 + 3 ^ 40 * 3277571 * 2
def baseEnd_3277571 : Nat := 560989767412500407363077

theorem tailTrace_3277571 : CollatzResearch.WordTrace tailWord_3277571 prefixEnd_3277571 560989767412500407363077 := by
  unfold tailWord_3277571
  simp only [CollatzResearch.WordTrace]
  refine ⟨119542835208927506406776567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79695223472618337604517711 119542835208927506406776567)
  ·
    refine ⟨179314252813391259610164851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119542835208927506406776567 179314252813391259610164851)
    ·
      refine ⟨268971379220086889415247277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179314252813391259610164851 268971379220086889415247277)
      ·
        refine ⟨100864267207532583530717729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268971379220086889415247277 100864267207532583530717729)
        ·
          refine ⟨75648200405649437648038297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100864267207532583530717729 75648200405649437648038297)
          ·
            refine ⟨56736150304237078236028723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75648200405649437648038297 56736150304237078236028723)
            ·
              refine ⟨85104225456355617354043085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56736150304237078236028723 85104225456355617354043085)
              ·
                refine ⟨31914084546133356507766157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85104225456355617354043085 31914084546133356507766157)
                ·
                  refine ⟨11967781704800008690412309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31914084546133356507766157 11967781704800008690412309)
                  ·
                    refine ⟨560989767412500407363077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11967781704800008690412309 560989767412500407363077)
                    ·
                      rfl

theorem cell23_3277571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 6].length) (baseStart_3277571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277571 prefixEnd_3277571 := by exact prefixLift 3277571
  have htrace : WordTrace (prefixWord ++ tailWord_3277571) baseStart_3277571 baseEnd_3277571 := by
    simpa [prefixWord, tailWord_3277571, baseEnd_3277571] using wordTrace_append hprefix tailTrace_3277571
  have hstable : (prefixWord ++ tailWord_3277571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277571).length < 2 ^ (prefixWord ++ tailWord_3277571).sum := by decide
  have hdescent : baseEnd_3277571 < baseStart_3277571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277575 : List Nat := [1, 1, 4, 4, 1, 1, 2, 3, 1, 5]
def baseStart_3277575 : Nat := 118140960795 + 3277575 * 2 ^ 59
def prefixEnd_3277575 : Nat := 4983230072969 + 3 ^ 40 * 3277575 * 2
def baseEnd_3277575 : Nat := 560990452053373068813071

theorem tailTrace_3277575 : CollatzResearch.WordTrace tailWord_3277575 prefixEnd_3277575 560990452053373068813071 := by
  unfold tailWord_3277575
  simp only [CollatzResearch.WordTrace]
  refine ⟨119542981100913015089922179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79695320733942010059948119 119542981100913015089922179)
  ·
    refine ⟨179314471651369522634883269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119542981100913015089922179 179314471651369522634883269)
    ·
      refine ⟨33621463434631785494040613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179314471651369522634883269 33621463434631785494040613)
      ·
        refine ⟨6304024393993459780132615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33621463434631785494040613 6304024393993459780132615)
        ·
          refine ⟨9456036590990189670198923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6304024393993459780132615 9456036590990189670198923)
          ·
            refine ⟨14184054886485284505298385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9456036590990189670198923 14184054886485284505298385)
            ·
              refine ⟨10638041164863963378973789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14184054886485284505298385 10638041164863963378973789)
              ·
                refine ⟨3989265436823986267115171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10638041164863963378973789 3989265436823986267115171)
                ·
                  refine ⟨5983898155235979400672757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3989265436823986267115171 5983898155235979400672757)
                  ·
                    refine ⟨560990452053373068813071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5983898155235979400672757 560990452053373068813071)
                    ·
                      rfl

theorem cell23_3277575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_3277575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277575 prefixEnd_3277575 := by exact prefixLift 3277575
  have htrace : WordTrace (prefixWord ++ tailWord_3277575) baseStart_3277575 baseEnd_3277575 := by
    simpa [prefixWord, tailWord_3277575, baseEnd_3277575] using wordTrace_append hprefix tailTrace_3277575
  have hstable : (prefixWord ++ tailWord_3277575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277575).length < 2 ^ (prefixWord ++ tailWord_3277575).sum := by decide
  have hdescent : baseEnd_3277575 < baseStart_3277575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277589 : List Nat := [1, 3, 2, 1, 2, 2, 5, 2, 1, 1, 3]
def baseStart_3277589 : Nat := 118140960795 + 3277589 * 2 ^ 59
def prefixEnd_3277589 : Nat := 4983230072969 + 3 ^ 40 * 3277589 * 2
def baseEnd_3277589 : Nat := 1682978544889282151664149

theorem tailTrace_3277589 : CollatzResearch.WordTrace tailWord_3277589 prefixEnd_3277589 1682978544889282151664149 := by
  unfold tailWord_3277589
  simp only [CollatzResearch.WordTrace]
  refine ⟨119543491722862295480931821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79695661148574863653954547 119543491722862295480931821)
  ·
    refine ⟨44828809396073360805349433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119543491722862295480931821 44828809396073360805349433)
    ·
      refine ⟨33621607047055020604012075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44828809396073360805349433 33621607047055020604012075)
      ·
        refine ⟨50432410570582530906018113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33621607047055020604012075 50432410570582530906018113)
        ·
          refine ⟨37824307927936898179513585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50432410570582530906018113 37824307927936898179513585)
          ·
            refine ⟨28368230945952673634635189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37824307927936898179513585 28368230945952673634635189)
            ·
              refine ⟨2659521651183063153247049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28368230945952673634635189 2659521651183063153247049)
              ·
                refine ⟨1994641238387297364935287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2659521651183063153247049 1994641238387297364935287)
                ·
                  refine ⟨2991961857580946047402931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994641238387297364935287 2991961857580946047402931)
                  ·
                    refine ⟨4487942786371419071104397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2991961857580946047402931 4487942786371419071104397)
                    ·
                      refine ⟨1682978544889282151664149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4487942786371419071104397 1682978544889282151664149)
                      ·
                        rfl

theorem cell23_3277589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_3277589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277589 prefixEnd_3277589 := by exact prefixLift 3277589
  have htrace : WordTrace (prefixWord ++ tailWord_3277589) baseStart_3277589 baseEnd_3277589 := by
    simpa [prefixWord, tailWord_3277589, baseEnd_3277589] using wordTrace_append hprefix tailTrace_3277589
  have hstable : (prefixWord ++ tailWord_3277589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277589).length < 2 ^ (prefixWord ++ tailWord_3277589).sum := by decide
  have hdescent : baseEnd_3277589 < baseStart_3277589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277605 : List Nat := [1, 3, 1, 2, 3, 1, 3, 3, 2, 4]
def baseStart_3277605 : Nat := 118140960795 + 3277605 * 2 ^ 59
def prefixEnd_3277605 : Nat := 4983230072969 + 3 ^ 40 * 3277605 * 2
def baseEnd_3277605 : Nat := 560995586859918029688025

theorem tailTrace_3277605 : CollatzResearch.WordTrace tailWord_3277605 prefixEnd_3277605 560995586859918029688025 := by
  unfold tailWord_3277605
  simp only [CollatzResearch.WordTrace]
  refine ⟨119544075290804330213514269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79696050193869553475676179 119544075290804330213514269)
  ·
    refine ⟨44829028234051623830067851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119544075290804330213514269 44829028234051623830067851)
    ·
      refine ⟨67243542351077435745101777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44829028234051623830067851 67243542351077435745101777)
      ·
        refine ⟨50432656763308076808826333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67243542351077435745101777 50432656763308076808826333)
        ·
          refine ⟨18912246286240528803309875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50432656763308076808826333 18912246286240528803309875)
          ·
            refine ⟨28368369429360793204964813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18912246286240528803309875 28368369429360793204964813)
            ·
              refine ⟨10638138536010297451861805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28368369429360793204964813 10638138536010297451861805)
              ·
                refine ⟨3989301951003861544448177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10638138536010297451861805 3989301951003861544448177)
                ·
                  refine ⟨2991976463252896158336133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3989301951003861544448177 2991976463252896158336133)
                  ·
                    refine ⟨560995586859918029688025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2991976463252896158336133 560995586859918029688025)
                    ·
                      rfl

theorem cell23_3277605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 4].length) (baseStart_3277605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277605 prefixEnd_3277605 := by exact prefixLift 3277605
  have htrace : WordTrace (prefixWord ++ tailWord_3277605) baseStart_3277605 baseEnd_3277605 := by
    simpa [prefixWord, tailWord_3277605, baseEnd_3277605] using wordTrace_append hprefix tailTrace_3277605
  have hstable : (prefixWord ++ tailWord_3277605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277605).length < 2 ^ (prefixWord ++ tailWord_3277605).sum := by decide
  have hdescent : baseEnd_3277605 < baseStart_3277605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277608 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_3277608 : Nat := 118140960795 + 3277608 * 2 ^ 59
def prefixEnd_3277608 : Nat := 4983230072969 + 3 ^ 40 * 3277608 * 2
def baseEnd_3277608 : Nat := 1682988301021717577326561

theorem tailTrace_3277608 : CollatzResearch.WordTrace tailWord_3277608 prefixEnd_3277608 1682988301021717577326561 := by
  unfold tailWord_3277608
  simp only [CollatzResearch.WordTrace]
  refine ⟨59772092354896730862936739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79696123139862307817248985 59772092354896730862936739)
  ·
    refine ⟨89658138532345096294405109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59772092354896730862936739 89658138532345096294405109)
    ·
      refine ⟨8405450487407352777600479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89658138532345096294405109 8405450487407352777600479)
      ·
        refine ⟨12608175731111029166400719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8405450487407352777600479 12608175731111029166400719)
        ·
          refine ⟨18912263596666543749601079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12608175731111029166400719 18912263596666543749601079)
          ·
            refine ⟨28368395394999815624401619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18912263596666543749601079 28368395394999815624401619)
            ·
              refine ⟨42552593092499723436602429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28368395394999815624401619 42552593092499723436602429)
              ·
                refine ⟨15957222409687396288725911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42552593092499723436602429 15957222409687396288725911)
                ·
                  refine ⟨23935833614531094433088867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15957222409687396288725911 23935833614531094433088867)
                  ·
                    refine ⟨35903750421796641649633301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23935833614531094433088867 35903750421796641649633301)
                    ·
                      refine ⟨1682988301021717577326561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35903750421796641649633301 1682988301021717577326561)
                      ·
                        rfl

theorem cell23_3277608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_3277608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277608 prefixEnd_3277608 := by exact prefixLift 3277608
  have htrace : WordTrace (prefixWord ++ tailWord_3277608) baseStart_3277608 baseEnd_3277608 := by
    simpa [prefixWord, tailWord_3277608, baseEnd_3277608] using wordTrace_append hprefix tailTrace_3277608
  have hstable : (prefixWord ++ tailWord_3277608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277608).length < 2 ^ (prefixWord ++ tailWord_3277608).sum := by decide
  have hdescent : baseEnd_3277608 < baseStart_3277608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277622 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_3277622 : Nat := 118140960795 + 3277622 * 2 ^ 59
def prefixEnd_3277622 : Nat := 4983230072969 + 3 ^ 40 * 3277622 * 2
def baseEnd_3277622 : Nat := 560998496583626840850499

theorem tailTrace_3277622 : CollatzResearch.WordTrace tailWord_3277622 prefixEnd_3277622 560998496583626840850499 := by
  unfold tailWord_3277622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7471543458233921382305195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79696463554495161411255413 7471543458233921382305195)
  ·
    refine ⟨11207315187350882073457793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7471543458233921382305195 11207315187350882073457793)
    ·
      refine ⟨8405486390513161555093345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11207315187350882073457793 8405486390513161555093345)
      ·
        refine ⟨6304114792884871166320009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8405486390513161555093345 6304114792884871166320009)
        ·
          refine ⟨4728086094663653374740007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6304114792884871166320009 4728086094663653374740007)
          ·
            refine ⟨7092129141995480062110011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728086094663653374740007 7092129141995480062110011)
            ·
              refine ⟨10638193712993220093165017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7092129141995480062110011 10638193712993220093165017)
              ·
                refine ⟨7978645284744915069873763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10638193712993220093165017 7978645284744915069873763)
                ·
                  refine ⟨11967967927117372604810645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7978645284744915069873763 11967967927117372604810645)
                  ·
                    refine ⟨560998496583626840850499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11967967927117372604810645 560998496583626840850499)
                    ·
                      rfl

theorem cell23_3277622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_3277622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277622 prefixEnd_3277622 := by exact prefixLift 3277622
  have htrace : WordTrace (prefixWord ++ tailWord_3277622) baseStart_3277622 baseEnd_3277622 := by
    simpa [prefixWord, tailWord_3277622, baseEnd_3277622] using wordTrace_append hprefix tailTrace_3277622
  have hstable : (prefixWord ++ tailWord_3277622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277622).length < 2 ^ (prefixWord ++ tailWord_3277622).sum := by decide
  have hdescent : baseEnd_3277622 < baseStart_3277622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277629 : List Nat := [1, 4, 1, 4, 2, 1, 3, 1, 1, 1, 4]
def baseStart_3277629 : Nat := 118140960795 + 3277629 * 2 ^ 59
def prefixEnd_3277629 : Nat := 4983230072969 + 3 ^ 40 * 3277629 * 2
def baseEnd_3277629 : Nat := 1682999084115461995163965

theorem tailTrace_3277629 : CollatzResearch.WordTrace tailWord_3277629 prefixEnd_3277629 1682999084115461995163965 := by
  unfold tailWord_3277629
  simp only [CollatzResearch.WordTrace]
  refine ⟨119544950642717382312387941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79696633761811588208258627 119544950642717382312387941)
  ·
    refine ⟨22414678245509509183572739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119544950642717382312387941 22414678245509509183572739)
    ·
      refine ⟨33622017368264263775359109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22414678245509509183572739 33622017368264263775359109)
      ·
        refine ⟨6304128256549549457879833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33622017368264263775359109 6304128256549549457879833)
        ·
          refine ⟨4728096192412162093409875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6304128256549549457879833 4728096192412162093409875)
          ·
            refine ⟨7092144288618243140114813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728096192412162093409875 7092144288618243140114813)
            ·
              refine ⟨2659554108231841177543055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7092144288618243140114813 2659554108231841177543055)
              ·
                refine ⟨3989331162347761766314583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659554108231841177543055 3989331162347761766314583)
                ·
                  refine ⟨5983996743521642649471875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3989331162347761766314583 5983996743521642649471875)
                  ·
                    refine ⟨8975995115282463974207813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5983996743521642649471875 8975995115282463974207813)
                    ·
                      refine ⟨1682999084115461995163965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8975995115282463974207813 1682999084115461995163965)
                      ·
                        rfl

theorem cell23_3277629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_3277629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277629 prefixEnd_3277629 := by exact prefixLift 3277629
  have htrace : WordTrace (prefixWord ++ tailWord_3277629) baseStart_3277629 baseEnd_3277629 := by
    simpa [prefixWord, tailWord_3277629, baseEnd_3277629] using wordTrace_append hprefix tailTrace_3277629
  have hstable : (prefixWord ++ tailWord_3277629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277629).length < 2 ^ (prefixWord ++ tailWord_3277629).sum := by decide
  have hdescent : baseEnd_3277629 < baseStart_3277629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277652 : List Nat := [2, 4, 1, 1, 5, 1, 1, 8]
def baseStart_3277652 : Nat := 118140960795 + 3277652 * 2 ^ 59
def prefixEnd_3277652 : Nat := 4983230072969 + 3 ^ 40 * 3277652 * 2
def baseEnd_3277652 : Nat := 62333736821130200191717

theorem tailTrace_3277652 : CollatzResearch.WordTrace tailWord_3277652 prefixEnd_3277652 62333736821130200191717 := by
  unfold tailWord_3277652
  simp only [CollatzResearch.WordTrace]
  refine ⟨59772894760817028620237605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79697193014422704826983473 59772894760817028620237605)
  ·
    refine ⟨11207417767653192866294551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59772894760817028620237605 11207417767653192866294551)
    ·
      refine ⟨16811126651479789299441827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11207417767653192866294551 16811126651479789299441827)
      ·
        refine ⟨25216689977219683949162741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16811126651479789299441827 25216689977219683949162741)
        ·
          refine ⟨2364064685364345370234007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25216689977219683949162741 2364064685364345370234007)
          ·
            refine ⟨3546097028046518055351011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364064685364345370234007 3546097028046518055351011)
            ·
              refine ⟨5319145542069777083026517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3546097028046518055351011 5319145542069777083026517)
              ·
                refine ⟨62333736821130200191717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5319145542069777083026517 62333736821130200191717)
                ·
                  rfl

theorem cell23_3277652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 8].length) (baseStart_3277652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277652 prefixEnd_3277652 := by exact prefixLift 3277652
  have htrace : WordTrace (prefixWord ++ tailWord_3277652) baseStart_3277652 baseEnd_3277652 := by
    simpa [prefixWord, tailWord_3277652, baseEnd_3277652] using wordTrace_append hprefix tailTrace_3277652
  have hstable : (prefixWord ++ tailWord_3277652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277652).length < 2 ^ (prefixWord ++ tailWord_3277652).sum := by decide
  have hdescent : baseEnd_3277652 < baseStart_3277652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277672 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_3277672 : Nat := 118140960795 + 3277672 * 2 ^ 59
def prefixEnd_3277672 : Nat := 4983230072969 + 3 ^ 40 * 3277672 * 2
def baseEnd_3277672 : Nat := 1683021163783605326926267

theorem tailTrace_3277672 : CollatzResearch.WordTrace tailWord_3277672 prefixEnd_3277672 1683021163783605326926267 := by
  unfold tailWord_3277672
  simp only [CollatzResearch.WordTrace]
  refine ⟨59773259490780800328101635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79697679321041067104135513 59773259490780800328101635)
  ·
    refine ⟨89659889236171200492152453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59773259490780800328101635 89659889236171200492152453)
    ·
      refine ⟨16811229231782100092278585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89659889236171200492152453 16811229231782100092278585)
      ·
        refine ⟨12608421923836575069208939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16811229231782100092278585 12608421923836575069208939)
        ·
          refine ⟨18912632885754862603813409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12608421923836575069208939 18912632885754862603813409)
          ·
            refine ⟨14184474664316146952860057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18912632885754862603813409 14184474664316146952860057)
            ·
              refine ⟨10638355998237110214645043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14184474664316146952860057 10638355998237110214645043)
              ·
                refine ⟨15957533997355665321967565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10638355998237110214645043 15957533997355665321967565)
                ·
                  refine ⟨5984075249008374495737837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15957533997355665321967565 5984075249008374495737837)
                  ·
                    refine ⟨2244028218378140435901689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5984075249008374495737837 2244028218378140435901689)
                    ·
                      refine ⟨1683021163783605326926267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2244028218378140435901689 1683021163783605326926267)
                      ·
                        rfl

theorem cell23_3277672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_3277672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277672 prefixEnd_3277672 := by exact prefixLift 3277672
  have htrace : WordTrace (prefixWord ++ tailWord_3277672) baseStart_3277672 baseEnd_3277672 := by
    simpa [prefixWord, tailWord_3277672, baseEnd_3277672] using wordTrace_append hprefix tailTrace_3277672
  have hstable : (prefixWord ++ tailWord_3277672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277672).length < 2 ^ (prefixWord ++ tailWord_3277672).sum := by decide
  have hdescent : baseEnd_3277672 < baseStart_3277672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277688 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 1, 6, 3]
def baseStart_3277688 : Nat := 118140960795 + 3277688 * 2 ^ 59
def prefixEnd_3277688 : Nat := 4983230072969 + 3 ^ 40 * 3277688 * 2
def baseEnd_3277688 : Nat := 1683029379474077264326193

theorem tailTrace_3277688 : CollatzResearch.WordTrace tailWord_3277688 prefixEnd_3277688 1683029379474077264326193 := by
  unfold tailWord_3277688
  simp only [CollatzResearch.WordTrace]
  refine ⟨59773551274751817694392859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79698068366335756925857145 59773551274751817694392859)
  ·
    refine ⟨89660326912127726541589289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59773551274751817694392859 89660326912127726541589289)
    ·
      refine ⟨67245245184095794906191967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89660326912127726541589289 67245245184095794906191967)
      ·
        refine ⟨100867867776143692359287951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67245245184095794906191967 100867867776143692359287951)
        ·
          refine ⟨151301801664215538538931927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100867867776143692359287951 151301801664215538538931927)
          ·
            refine ⟨226952702496323307808397891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151301801664215538538931927 226952702496323307808397891)
            ·
              refine ⟨340429053744484961712596837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226952702496323307808397891 340429053744484961712596837)
              ·
                refine ⟨63830447577090930321111907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 340429053744484961712596837 63830447577090930321111907)
                ·
                  refine ⟨95745671365636395481667861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63830447577090930321111907 95745671365636395481667861)
                  ·
                    refine ⟨4488078345264206038203181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95745671365636395481667861 4488078345264206038203181)
                    ·
                      refine ⟨1683029379474077264326193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4488078345264206038203181 1683029379474077264326193)
                      ·
                        rfl

theorem cell23_3277688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_3277688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277688 prefixEnd_3277688 := by exact prefixLift 3277688
  have htrace : WordTrace (prefixWord ++ tailWord_3277688) baseStart_3277688 baseEnd_3277688 := by
    simpa [prefixWord, tailWord_3277688, baseEnd_3277688] using wordTrace_append hprefix tailTrace_3277688
  have hstable : (prefixWord ++ tailWord_3277688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277688).length < 2 ^ (prefixWord ++ tailWord_3277688).sum := by decide
  have hdescent : baseEnd_3277688 < baseStart_3277688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277689 : List Nat := [1, 2, 1, 3, 2, 3, 4, 1, 1, 3, 2]
def baseStart_3277689 : Nat := 118140960795 + 3277689 * 2 ^ 59
def prefixEnd_3277689 : Nat := 4983230072969 + 3 ^ 40 * 3277689 * 2
def baseEnd_3277689 : Nat := 1683029892954731760413689

theorem tailTrace_3277689 : CollatzResearch.WordTrace tailWord_3277689 prefixEnd_3277689 1683029892954731760413689 := by
  unfold tailWord_3277689
  simp only [CollatzResearch.WordTrace]
  refine ⟨119547139022500012559572121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79698092681666675039714747 119547139022500012559572121)
  ·
    refine ⟨89660354266875009419679091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119547139022500012559572121 89660354266875009419679091)
    ·
      refine ⟨134490531400312514129518637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89660354266875009419679091 134490531400312514129518637)
      ·
        refine ⟨50433949275117192798569489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134490531400312514129518637 50433949275117192798569489)
        ·
          refine ⟨37825461956337894598927117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50433949275117192798569489 37825461956337894598927117)
          ·
            refine ⟨14184548233626710474597669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37825461956337894598927117 14184548233626710474597669)
            ·
              refine ⟨2659602793805008213987063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14184548233626710474597669 2659602793805008213987063)
              ·
                refine ⟨3989404190707512320980595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659602793805008213987063 3989404190707512320980595)
                ·
                  refine ⟨5984106286061268481470893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3989404190707512320980595 5984106286061268481470893)
                  ·
                    refine ⟨2244039857272975680551585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5984106286061268481470893 2244039857272975680551585)
                    ·
                      refine ⟨1683029892954731760413689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2244039857272975680551585 1683029892954731760413689)
                      ·
                        rfl

theorem cell23_3277689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_3277689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277689 prefixEnd_3277689 := by exact prefixLift 3277689
  have htrace : WordTrace (prefixWord ++ tailWord_3277689) baseStart_3277689 baseEnd_3277689 := by
    simpa [prefixWord, tailWord_3277689, baseEnd_3277689] using wordTrace_append hprefix tailTrace_3277689
  have hstable : (prefixWord ++ tailWord_3277689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277689).length < 2 ^ (prefixWord ++ tailWord_3277689).sum := by decide
  have hdescent : baseEnd_3277689 < baseStart_3277689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277708 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 7]
def baseStart_3277708 : Nat := 118140960795 + 3277708 * 2 ^ 59
def prefixEnd_3277708 : Nat := 4983230072969 + 3 ^ 40 * 3277708 * 2
def baseEnd_3277708 : Nat := 187004405454129687341789

theorem tailTrace_3277708 : CollatzResearch.WordTrace tailWord_3277708 prefixEnd_3277708 187004405454129687341789 := by
  unfold tailWord_3277708
  simp only [CollatzResearch.WordTrace]
  refine ⟨59773916004715589402256889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79698554672954119203009185 59773916004715589402256889)
  ·
    refine ⟨44830437003536692051692667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59773916004715589402256889 44830437003536692051692667)
    ·
      refine ⟨67245655505305038077539001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44830437003536692051692667 67245655505305038077539001)
      ·
        refine ⟨50434241628978778558154251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67245655505305038077539001 50434241628978778558154251)
        ·
          refine ⟨75651362443468167837231377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50434241628978778558154251 75651362443468167837231377)
          ·
            refine ⟨56738521832601125877923533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75651362443468167837231377 56738521832601125877923533)
            ·
              refine ⟨21276945687225422204221325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56738521832601125877923533 21276945687225422204221325)
              ·
                refine ⟨7978854632709533326582997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21276945687225422204221325 7978854632709533326582997)
                ·
                  refine ⟨187004405454129687341789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7978854632709533326582997 187004405454129687341789)
                  ·
                    rfl

theorem cell23_3277708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_3277708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277708 prefixEnd_3277708 := by exact prefixLift 3277708
  have htrace : WordTrace (prefixWord ++ tailWord_3277708) baseStart_3277708 baseEnd_3277708 := by
    simpa [prefixWord, tailWord_3277708, baseEnd_3277708] using wordTrace_append hprefix tailTrace_3277708
  have hstable : (prefixWord ++ tailWord_3277708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277708).length < 2 ^ (prefixWord ++ tailWord_3277708).sum := by decide
  have hdescent : baseEnd_3277708 < baseStart_3277708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277866 : List Nat := [3, 1, 4, 1, 4, 1, 1, 2, 6]
def baseStart_3277866 : Nat := 118140960795 + 3277866 * 2 ^ 59
def prefixEnd_3277866 : Nat := 4983230072969 + 3 ^ 40 * 3277866 * 2
def baseEnd_3277866 : Nat := 187013419892286396433375

theorem tailTrace_3277866 : CollatzResearch.WordTrace tailWord_3277866 prefixEnd_3277866 187013419892286396433375 := by
  unfold tailWord_3277866
  simp only [CollatzResearch.WordTrace]
  refine ⟨29888398685714692947191363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79702396495239181192510301 29888398685714692947191363)
  ·
    refine ⟨44832598028572039420787045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29888398685714692947191363 44832598028572039420787045)
    ·
      refine ⟨8406112130357257391397571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44832598028572039420787045 8406112130357257391397571)
      ·
        refine ⟨12609168195535886087096357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8406112130357257391397571 12609168195535886087096357)
        ·
          refine ⟨2364219036662978641330567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12609168195535886087096357 2364219036662978641330567)
          ·
            refine ⟨3546328554994467961995851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364219036662978641330567 3546328554994467961995851)
            ·
              refine ⟨5319492832491701942993777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3546328554994467961995851 5319492832491701942993777)
              ·
                refine ⟨3989619624368776457245333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5319492832491701942993777 3989619624368776457245333)
                ·
                  refine ⟨187013419892286396433375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3989619624368776457245333 187013419892286396433375)
                  ·
                    rfl

theorem cell23_3277866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 6].length) (baseStart_3277866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277866 prefixEnd_3277866 := by exact prefixLift 3277866
  have htrace : WordTrace (prefixWord ++ tailWord_3277866) baseStart_3277866 baseEnd_3277866 := by
    simpa [prefixWord, tailWord_3277866, baseEnd_3277866] using wordTrace_append hprefix tailTrace_3277866
  have hstable : (prefixWord ++ tailWord_3277866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277866).length < 2 ^ (prefixWord ++ tailWord_3277866).sum := by decide
  have hdescent : baseEnd_3277866 < baseStart_3277866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277876 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_3277876 : Nat := 118140960795 + 3277876 * 2 ^ 59
def prefixEnd_3277876 : Nat := 4983230072969 + 3 ^ 40 * 3277876 * 2
def baseEnd_3277876 : Nat := 1683125913837122528775329

theorem tailTrace_3277876 : CollatzResearch.WordTrace tailWord_3277876 prefixEnd_3277876 1683125913837122528775329 := by
  unfold tailWord_3277876
  simp only [CollatzResearch.WordTrace]
  refine ⟨59776979736411271748314741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79702639648548362331086321 59776979736411271748314741)
  ·
    refine ⟨5604091850288556726404507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59776979736411271748314741 5604091850288556726404507)
    ·
      refine ⟨8406137775432835089606761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5604091850288556726404507 8406137775432835089606761)
      ·
        refine ⟨6304603331574626317205071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8406137775432835089606761 6304603331574626317205071)
        ·
          refine ⟨9456904997361939475807607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6304603331574626317205071 9456904997361939475807607)
          ·
            refine ⟨14185357496042909213711411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9456904997361939475807607 14185357496042909213711411)
            ·
              refine ⟨21278036244064363820567117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14185357496042909213711411 21278036244064363820567117)
              ·
                refine ⟨7979263591524136432712669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21278036244064363820567117 7979263591524136432712669)
                ·
                  refine ⟨2992223846821551162267251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7979263591524136432712669 2992223846821551162267251)
                  ·
                    refine ⟨4488335770232326743400877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2992223846821551162267251 4488335770232326743400877)
                    ·
                      refine ⟨1683125913837122528775329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4488335770232326743400877 1683125913837122528775329)
                      ·
                        rfl

theorem cell23_3277876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_3277876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277876 prefixEnd_3277876 := by exact prefixLift 3277876
  have htrace : WordTrace (prefixWord ++ tailWord_3277876) baseStart_3277876 baseEnd_3277876 := by
    simpa [prefixWord, tailWord_3277876, baseEnd_3277876] using wordTrace_append hprefix tailTrace_3277876
  have hstable : (prefixWord ++ tailWord_3277876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277876).length < 2 ^ (prefixWord ++ tailWord_3277876).sum := by decide
  have hdescent : baseEnd_3277876 < baseStart_3277876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277922 : List Nat := [3, 3, 2, 2, 1, 1, 11]
def baseStart_3277922 : Nat := 118140960795 + 3277922 * 2 ^ 59
def prefixEnd_3277922 : Nat := 4983230072969 + 3 ^ 40 * 3277922 * 2
def baseEnd_3277922 : Nat := 20779623875891720355557

theorem tailTrace_3277922 : CollatzResearch.WordTrace tailWord_3277922 prefixEnd_3277922 20779623875891720355557 := by
  unfold tailWord_3277922
  simp only [CollatzResearch.WordTrace]
  refine ⟨29888909307663973338201005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79703758153770595568536013 29888909307663973338201005)
  ·
    refine ⟨11208340990373990001825377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29888909307663973338201005 11208340990373990001825377)
    ·
      refine ⟨8406255742780492501369033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11208340990373990001825377 8406255742780492501369033)
      ·
        refine ⟨6304691807085369376026775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8406255742780492501369033 6304691807085369376026775)
        ·
          refine ⟨9457037710628054064040163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6304691807085369376026775 9457037710628054064040163)
          ·
            refine ⟨14185556565942081096060245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9457037710628054064040163 14185556565942081096060245)
            ·
              refine ⟨20779623875891720355557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14185556565942081096060245 20779623875891720355557)
              ·
                rfl

theorem cell23_3277922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 11].length) (baseStart_3277922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277922 prefixEnd_3277922 := by exact prefixLift 3277922
  have htrace : WordTrace (prefixWord ++ tailWord_3277922) baseStart_3277922 baseEnd_3277922 := by
    simpa [prefixWord, tailWord_3277922, baseEnd_3277922] using wordTrace_append hprefix tailTrace_3277922
  have hstable : (prefixWord ++ tailWord_3277922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277922).length < 2 ^ (prefixWord ++ tailWord_3277922).sum := by decide
  have hdescent : baseEnd_3277922 < baseStart_3277922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277933 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_3277933 : Nat := 118140960795 + 3277933 * 2 ^ 59
def prefixEnd_3277933 : Nat := 4983230072969 + 3 ^ 40 * 3277933 * 2
def baseEnd_3277933 : Nat := 1683155182234428805762567

theorem tailTrace_3277933 : CollatzResearch.WordTrace tailWord_3277933 prefixEnd_3277933 1683155182234428805762567 := by
  unfold tailWord_3277933
  simp only [CollatzResearch.WordTrace]
  refine ⟨119556038433616042231454453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79704025622410694820969635 119556038433616042231454453)
  ·
    refine ⟨11208378603151503959198855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119556038433616042231454453 11208378603151503959198855)
    ·
      refine ⟨16812567904727255938798283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11208378603151503959198855 16812567904727255938798283)
      ·
        refine ⟨25218851857090883908197425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16812567904727255938798283 25218851857090883908197425)
        ·
          refine ⟨18914138892818162931148069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25218851857090883908197425 18914138892818162931148069)
          ·
            refine ⟨3546401042403405549590263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18914138892818162931148069 3546401042403405549590263)
            ·
              refine ⟨5319601563605108324385395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3546401042403405549590263 5319601563605108324385395)
              ·
                refine ⟨7979402345407662486578093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5319601563605108324385395 7979402345407662486578093)
                ·
                  refine ⟨2992275879527873432466785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7979402345407662486578093 2992275879527873432466785)
                  ·
                    refine ⟨2244206909645905074350089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2992275879527873432466785 2244206909645905074350089)
                    ·
                      refine ⟨1683155182234428805762567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2244206909645905074350089 1683155182234428805762567)
                      ·
                        rfl

theorem cell23_3277933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_3277933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277933 prefixEnd_3277933 := by exact prefixLift 3277933
  have htrace : WordTrace (prefixWord ++ tailWord_3277933) baseStart_3277933 baseEnd_3277933 := by
    simpa [prefixWord, tailWord_3277933, baseEnd_3277933] using wordTrace_append hprefix tailTrace_3277933
  have hstable : (prefixWord ++ tailWord_3277933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277933).length < 2 ^ (prefixWord ++ tailWord_3277933).sum := by decide
  have hdescent : baseEnd_3277933 < baseStart_3277933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277935 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 2, 7]
def baseStart_3277935 : Nat := 118140960795 + 3277935 * 2 ^ 59
def prefixEnd_3277935 : Nat := 4983230072969 + 3 ^ 40 * 3277935 * 2
def baseEnd_3277935 : Nat := 561052069731912599312519

theorem tailTrace_3277935 : CollatzResearch.WordTrace tailWord_3277935 prefixEnd_3277935 561052069731912599312519 := by
  unfold tailWord_3277935
  simp only [CollatzResearch.WordTrace]
  refine ⟨119556111379608796573027259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79704074253072531048684839 119556111379608796573027259)
  ·
    refine ⟨179334167069413194859540889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119556111379608796573027259 179334167069413194859540889)
    ·
      refine ⟨134500625302059896144655667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179334167069413194859540889 134500625302059896144655667)
      ·
        refine ⟨201750937953089844216983501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134500625302059896144655667 201750937953089844216983501)
        ·
          refine ⟨75656601732408691581368813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201750937953089844216983501 75656601732408691581368813)
          ·
            refine ⟨28371225649653259343013305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75656601732408691581368813 28371225649653259343013305)
            ·
              refine ⟨21278419237239944507259979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28371225649653259343013305 21278419237239944507259979)
              ·
                refine ⟨31917628855859916760889969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21278419237239944507259979 31917628855859916760889969)
                ·
                  refine ⟨23938221641894937570667477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31917628855859916760889969 23938221641894937570667477)
                  ·
                    refine ⟨561052069731912599312519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23938221641894937570667477 561052069731912599312519)
                    ·
                      rfl

theorem cell23_3277935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_3277935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277935 prefixEnd_3277935 := by exact prefixLift 3277935
  have htrace : WordTrace (prefixWord ++ tailWord_3277935) baseStart_3277935 baseEnd_3277935 := by
    simpa [prefixWord, tailWord_3277935, baseEnd_3277935] using wordTrace_append hprefix tailTrace_3277935
  have hstable : (prefixWord ++ tailWord_3277935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277935).length < 2 ^ (prefixWord ++ tailWord_3277935).sum := by decide
  have hdescent : baseEnd_3277935 < baseStart_3277935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277942 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3277942 : Nat := 118140960795 + 3277942 * 2 ^ 59
def prefixEnd_3277942 : Nat := 4983230072969 + 3 ^ 40 * 3277942 * 2
def baseEnd_3277942 : Nat := 1683159803560319270550025

theorem tailTrace_3277942 : CollatzResearch.WordTrace tailWord_3277942 prefixEnd_3277942 1683159803560319270550025 := by
  unfold tailWord_3277942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7472272918161464798033255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79704244460388957845688053 7472272918161464798033255)
  ·
    refine ⟨11208409377242197197049883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7472272918161464798033255 11208409377242197197049883)
    ·
      refine ⟨16812614065863295795574825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11208409377242197197049883 16812614065863295795574825)
      ·
        refine ⟨12609460549397471846681119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16812614065863295795574825 12609460549397471846681119)
        ·
          refine ⟨18914190824096207770021679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12609460549397471846681119 18914190824096207770021679)
          ·
            refine ⟨28371286236144311655032519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18914190824096207770021679 28371286236144311655032519)
            ·
              refine ⟨42556929354216467482548779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28371286236144311655032519 42556929354216467482548779)
              ·
                refine ⟨63835394031324701223823169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42556929354216467482548779 63835394031324701223823169)
                ·
                  refine ⟨47876545523493525917867377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63835394031324701223823169 47876545523493525917867377)
                  ·
                    refine ⟨35907409142620144438400533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47876545523493525917867377 35907409142620144438400533)
                    ·
                      refine ⟨1683159803560319270550025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35907409142620144438400533 1683159803560319270550025)
                      ·
                        rfl

theorem cell23_3277942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3277942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277942 prefixEnd_3277942 := by exact prefixLift 3277942
  have htrace : WordTrace (prefixWord ++ tailWord_3277942) baseStart_3277942 baseEnd_3277942 := by
    simpa [prefixWord, tailWord_3277942, baseEnd_3277942] using wordTrace_append hprefix tailTrace_3277942
  have hstable : (prefixWord ++ tailWord_3277942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277942).length < 2 ^ (prefixWord ++ tailWord_3277942).sum := by decide
  have hdescent : baseEnd_3277942 < baseStart_3277942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3277983 : List Nat := [1, 1, 2, 6, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3277983 : Nat := 118140960795 + 3277983 * 2 ^ 59
def prefixEnd_3277983 : Nat := 4983230072969 + 3 ^ 40 * 3277983 * 2
def baseEnd_3277983 : Nat := 1683180856267153610137337

theorem tailTrace_3277983 : CollatzResearch.WordTrace tailWord_3277983 prefixEnd_3277983 1683180856267153610137337 := by
  unfold tailWord_3277983
  simp only [CollatzResearch.WordTrace]
  refine ⟨119557862083434900770774603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79705241388956600513849735 119557862083434900770774603)
  ·
    refine ⟨179336793125152351156161905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119557862083434900770774603 179336793125152351156161905)
    ·
      refine ⟨134502594843864263367121429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179336793125152351156161905 134502594843864263367121429)
      ·
        refine ⟨6304809133306137345333817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 134502594843864263367121429 6304809133306137345333817)
        ·
          refine ⟨4728606849979603009000363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6304809133306137345333817 4728606849979603009000363)
          ·
            refine ⟨7092910274969404513500545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728606849979603009000363 7092910274969404513500545)
            ·
              refine ⟨5319682706227053385125409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7092910274969404513500545 5319682706227053385125409)
              ·
                refine ⟨3989762029670290038844057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5319682706227053385125409 3989762029670290038844057)
                ·
                  refine ⟨2992321522252717529133043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3989762029670290038844057 2992321522252717529133043)
                  ·
                    refine ⟨4488482283379076293699565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2992321522252717529133043 4488482283379076293699565)
                    ·
                      refine ⟨1683180856267153610137337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4488482283379076293699565 1683180856267153610137337)
                      ·
                        rfl

theorem cell23_3277983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3277983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3277983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3277983 prefixEnd_3277983 := by exact prefixLift 3277983
  have htrace : WordTrace (prefixWord ++ tailWord_3277983) baseStart_3277983 baseEnd_3277983 := by
    simpa [prefixWord, tailWord_3277983, baseEnd_3277983] using wordTrace_append hprefix tailTrace_3277983
  have hstable : (prefixWord ++ tailWord_3277983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3277983).length < 2 ^ (prefixWord ++ tailWord_3277983).sum := by decide
  have hdescent : baseEnd_3277983 < baseStart_3277983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3277983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278002 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_3278002 : Nat := 118140960795 + 3278002 * 2 ^ 59
def prefixEnd_3278002 : Nat := 4983230072969 + 3 ^ 40 * 3278002 * 2
def baseEnd_3278002 : Nat := 1683190612399589035799749

theorem tailTrace_3278002 : CollatzResearch.WordTrace tailWord_3278002 prefixEnd_3278002 1683190612399589035799749 := by
  unfold tailWord_3278002
  simp only [CollatzResearch.WordTrace]
  refine ⟨29889638767591516753929065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79705703380244044677144173 29889638767591516753929065)
  ·
    refine ⟨22417229075693637565446799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29889638767591516753929065 22417229075693637565446799)
    ·
      refine ⟨33625843613540456348170199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22417229075693637565446799 33625843613540456348170199)
      ·
        refine ⟨50438765420310684522255299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33625843613540456348170199 50438765420310684522255299)
        ·
          refine ⟨75658148130466026783382949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50438765420310684522255299 75658148130466026783382949)
          ·
            refine ⟨14185902774462380021884303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75658148130466026783382949 14185902774462380021884303)
            ·
              refine ⟨21278854161693570032826455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14185902774462380021884303 21278854161693570032826455)
              ·
                refine ⟨31918281242540355049239683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21278854161693570032826455 31918281242540355049239683)
                ·
                  refine ⟨47877421863810532573859525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31918281242540355049239683 47877421863810532573859525)
                  ·
                    refine ⟨8977016599464474857598661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47877421863810532573859525 8977016599464474857598661)
                    ·
                      refine ⟨1683190612399589035799749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8977016599464474857598661 1683190612399589035799749)
                      ·
                        rfl

theorem cell23_3278002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_3278002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278002 prefixEnd_3278002 := by exact prefixLift 3278002
  have htrace : WordTrace (prefixWord ++ tailWord_3278002) baseStart_3278002 baseEnd_3278002 := by
    simpa [prefixWord, tailWord_3278002, baseEnd_3278002] using wordTrace_append hprefix tailTrace_3278002
  have hstable : (prefixWord ++ tailWord_3278002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278002).length < 2 ^ (prefixWord ++ tailWord_3278002).sum := by decide
  have hdescent : baseEnd_3278002 < baseStart_3278002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278012 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 9]
def baseStart_3278012 : Nat := 118140960795 + 3278012 * 2 ^ 59
def prefixEnd_3278012 : Nat := 4983230072969 + 3 ^ 40 * 3278012 * 2
def baseEnd_3278012 : Nat := 187021749689570444074967

theorem tailTrace_3278012 : CollatzResearch.WordTrace tailWord_3278012 prefixEnd_3278012 187021749689570444074967 := by
  unfold tailWord_3278012
  simp only [CollatzResearch.WordTrace]
  refine ⟨59779459900164919361790145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79705946533553225815720193 59779459900164919361790145)
  ·
    refine ⟨44834594925123689521342609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59779459900164919361790145 44834594925123689521342609)
    ·
      refine ⟨33625946193842767141006957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44834594925123689521342609 33625946193842767141006957)
      ·
        refine ⟨12609729822691037677877609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33625946193842767141006957 12609729822691037677877609)
        ·
          refine ⟨9457297367018278258408207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12609729822691037677877609 9457297367018278258408207)
          ·
            refine ⟨14185946050527417387612311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9457297367018278258408207 14185946050527417387612311)
            ·
              refine ⟨21278919075791126081418467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14185946050527417387612311 21278919075791126081418467)
              ·
                refine ⟨31918378613686689122127701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21278919075791126081418467 31918378613686689122127701)
                ·
                  refine ⟨187021749689570444074967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31918378613686689122127701 187021749689570444074967)
                  ·
                    rfl

theorem cell23_3278012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_3278012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278012 prefixEnd_3278012 := by exact prefixLift 3278012
  have htrace : WordTrace (prefixWord ++ tailWord_3278012) baseStart_3278012 baseEnd_3278012 := by
    simpa [prefixWord, tailWord_3278012, baseEnd_3278012] using wordTrace_append hprefix tailTrace_3278012
  have hstable : (prefixWord ++ tailWord_3278012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278012).length < 2 ^ (prefixWord ++ tailWord_3278012).sum := by decide
  have hdescent : baseEnd_3278012 < baseStart_3278012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278040 : List Nat := [2, 1, 2, 2, 5, 2, 1, 2, 2, 2, 2]
def baseStart_3278040 : Nat := 118140960795 + 3278040 * 2 ^ 59
def prefixEnd_3278040 : Nat := 4983230072969 + 3 ^ 40 * 3278040 * 2
def baseEnd_3278040 : Nat := 1683210124664459887124575

theorem tailTrace_3278040 : CollatzResearch.WordTrace tailWord_3278040 prefixEnd_3278040 1683210124664459887124575 := by
  unfold tailWord_3278040
  simp only [CollatzResearch.WordTrace]
  refine ⟨59779970522114199752799787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79706627362818933003733049 59779970522114199752799787)
  ·
    refine ⟨89669955783171299629199681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59779970522114199752799787 89669955783171299629199681)
    ·
      refine ⟨67252466837378474721899761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89669955783171299629199681 67252466837378474721899761)
      ·
        refine ⟨50439350128033856041424821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67252466837378474721899761 50439350128033856041424821)
        ·
          refine ⟨4728689074503174003883577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50439350128033856041424821 4728689074503174003883577)
          ·
            refine ⟨3546516805877380502912683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4728689074503174003883577 3546516805877380502912683)
            ·
              refine ⟨5319775208816070754369025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3546516805877380502912683 5319775208816070754369025)
              ·
                refine ⟨3989831406612053065776769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5319775208816070754369025 3989831406612053065776769)
                ·
                  refine ⟨2992373554959039799332577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3989831406612053065776769 2992373554959039799332577)
                  ·
                    refine ⟨2244280166219279849499433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2992373554959039799332577 2244280166219279849499433)
                    ·
                      refine ⟨1683210124664459887124575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2244280166219279849499433 1683210124664459887124575)
                      ·
                        rfl

theorem cell23_3278040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_3278040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278040 prefixEnd_3278040 := by exact prefixLift 3278040
  have htrace : WordTrace (prefixWord ++ tailWord_3278040) baseStart_3278040 baseEnd_3278040 := by
    simpa [prefixWord, tailWord_3278040, baseEnd_3278040] using wordTrace_append hprefix tailTrace_3278040
  have hstable : (prefixWord ++ tailWord_3278040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278040).length < 2 ^ (prefixWord ++ tailWord_3278040).sum := by decide
  have hdescent : baseEnd_3278040 < baseStart_3278040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278042 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 4, 5]
def baseStart_3278042 : Nat := 118140960795 + 3278042 * 2 ^ 59
def prefixEnd_3278042 : Nat := 4983230072969 + 3 ^ 40 * 3278042 * 2
def baseEnd_3278042 : Nat := 561070383875256293099855

theorem tailTrace_3278042 : CollatzResearch.WordTrace tailWord_3278042 prefixEnd_3278042 561070383875256293099855 := by
  unfold tailWord_3278042
  simp only [CollatzResearch.WordTrace]
  refine ⟨29890003497555288461793095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79706675993480769231448253 29890003497555288461793095)
  ·
    refine ⟨44835005246332932692689643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29890003497555288461793095 44835005246332932692689643)
    ·
      refine ⟨67252507869499399039034465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44835005246332932692689643 67252507869499399039034465)
      ·
        refine ⟨50439380902124549279275849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67252507869499399039034465 50439380902124549279275849)
        ·
          refine ⟨37829535676593411959456887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50439380902124549279275849 37829535676593411959456887)
          ·
            refine ⟨56744303514890117939185331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37829535676593411959456887 56744303514890117939185331)
            ·
              refine ⟨85116455272335176908777997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56744303514890117939185331 85116455272335176908777997)
              ·
                refine ⟨31918670727125691340791749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85116455272335176908777997 31918670727125691340791749)
                ·
                  refine ⟨5984750761336067126398453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31918670727125691340791749 5984750761336067126398453)
                  ·
                    refine ⟨561070383875256293099855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5984750761336067126398453 561070383875256293099855)
                    ·
                      rfl

theorem cell23_3278042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_3278042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278042 prefixEnd_3278042 := by exact prefixLift 3278042
  have htrace : WordTrace (prefixWord ++ tailWord_3278042) baseStart_3278042 baseEnd_3278042 := by
    simpa [prefixWord, tailWord_3278042, baseEnd_3278042] using wordTrace_append hprefix tailTrace_3278042
  have hstable : (prefixWord ++ tailWord_3278042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278042).length < 2 ^ (prefixWord ++ tailWord_3278042).sum := by decide
  have hdescent : baseEnd_3278042 < baseStart_3278042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278052 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_3278052 : Nat := 118140960795 + 3278052 * 2 ^ 59
def prefixEnd_3278052 : Nat := 4983230072969 + 3 ^ 40 * 3278052 * 2
def baseEnd_3278052 : Nat := 1683216286432313840174519

theorem tailTrace_3278052 : CollatzResearch.WordTrace tailWord_3278052 prefixEnd_3278052 1683216286432313840174519 := by
  unfold tailWord_3278052
  simp only [CollatzResearch.WordTrace]
  refine ⟨59780189360092462777518205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79706919146789950370024273 59780189360092462777518205)
  ·
    refine ⟨22417571010034673541569327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59780189360092462777518205 22417571010034673541569327)
    ·
      refine ⟨33626356515052010312353991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22417571010034673541569327 33626356515052010312353991)
      ·
        refine ⟨50439534772578015468530987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33626356515052010312353991 50439534772578015468530987)
        ·
          refine ⟨75659302158867023202796481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50439534772578015468530987 75659302158867023202796481)
          ·
            refine ⟨56744476619150267402097361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75659302158867023202796481 56744476619150267402097361)
            ·
              refine ⟨42558357464362700551573021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56744476619150267402097361 42558357464362700551573021)
              ·
                refine ⟨15959384049136012706839883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42558357464362700551573021 15959384049136012706839883)
                ·
                  refine ⟨23939076073704019060259825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15959384049136012706839883 23939076073704019060259825)
                  ·
                    refine ⟨17954307055278014295194869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23939076073704019060259825 17954307055278014295194869)
                    ·
                      refine ⟨1683216286432313840174519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17954307055278014295194869 1683216286432313840174519)
                      ·
                        rfl

theorem cell23_3278052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_3278052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278052 prefixEnd_3278052 := by exact prefixLift 3278052
  have htrace : WordTrace (prefixWord ++ tailWord_3278052) baseStart_3278052 baseEnd_3278052 := by
    simpa [prefixWord, tailWord_3278052, baseEnd_3278052] using wordTrace_append hprefix tailTrace_3278052
  have hstable : (prefixWord ++ tailWord_3278052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278052).length < 2 ^ (prefixWord ++ tailWord_3278052).sum := by decide
  have hdescent : baseEnd_3278052 < baseStart_3278052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278106 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 3, 4]
def baseStart_3278106 : Nat := 118140960795 + 3278106 * 2 ^ 59
def prefixEnd_3278106 : Nat := 4983230072969 + 3 ^ 40 * 3278106 * 2
def baseEnd_3278106 : Nat := 561081338129218876299757

theorem tailTrace_3278106 : CollatzResearch.WordTrace tailWord_3278106 prefixEnd_3278106 561081338129218876299757 := by
  unfold tailWord_3278106
  simp only [CollatzResearch.WordTrace]
  refine ⟨29890587065497323194375543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79708232174659528518334781 29890587065497323194375543)
  ·
    refine ⟨44835880598245984791563315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29890587065497323194375543 44835880598245984791563315)
    ·
      refine ⟨67253820897368977187344973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44835880598245984791563315 67253820897368977187344973)
      ·
        refine ⟨25220182836513366445254365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67253820897368977187344973 25220182836513366445254365)
        ·
          refine ⟨9457568563692512416970387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25220182836513366445254365 9457568563692512416970387)
          ·
            refine ⟨14186352845538768625455581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9457568563692512416970387 14186352845538768625455581)
            ·
              refine ⟨5319882317077038234545843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14186352845538768625455581 5319882317077038234545843)
              ·
                refine ⟨7979823475615557351818765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5319882317077038234545843 7979823475615557351818765)
                ·
                  refine ⟨2992433803355834006932037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7979823475615557351818765 2992433803355834006932037)
                  ·
                    refine ⟨561081338129218876299757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2992433803355834006932037 561081338129218876299757)
                    ·
                      rfl

theorem cell23_3278106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_3278106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278106 prefixEnd_3278106 := by exact prefixLift 3278106
  have htrace : WordTrace (prefixWord ++ tailWord_3278106) baseStart_3278106 baseEnd_3278106 := by
    simpa [prefixWord, tailWord_3278106, baseEnd_3278106] using wordTrace_append hprefix tailTrace_3278106
  have hstable : (prefixWord ++ tailWord_3278106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278106).length < 2 ^ (prefixWord ++ tailWord_3278106).sum := by decide
  have hdescent : baseEnd_3278106 < baseStart_3278106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278139 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 7, 5, 2]
def baseStart_3278139 : Nat := 118140960795 + 3278139 * 2 ^ 59
def prefixEnd_3278139 : Nat := 4983230072969 + 3 ^ 40 * 3278139 * 2
def baseEnd_3278139 : Nat := 1683260959249254999786619

theorem tailTrace_3278139 : CollatzResearch.WordTrace tailWord_3278139 prefixEnd_3278139 1683260959249254999786619 := by
  unfold tailWord_3278139
  simp only [CollatzResearch.WordTrace]
  refine ⟨119563551870869739413453471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79709034580579826275635647 119563551870869739413453471)
  ·
    refine ⟨179345327806304609120180207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119563551870869739413453471 179345327806304609120180207)
    ·
      refine ⟨269017991709456913680270311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179345327806304609120180207 269017991709456913680270311)
      ·
        refine ⟨403526987564185370520405467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269017991709456913680270311 403526987564185370520405467)
        ·
          refine ⟨605290481346278055780608201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403526987564185370520405467 605290481346278055780608201)
          ·
            refine ⟨453967861009708541835456151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605290481346278055780608201 453967861009708541835456151)
            ·
              refine ⟨680951791514562812753184227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453967861009708541835456151 680951791514562812753184227)
              ·
                refine ⟨1021427687271844219129776341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680951791514562812753184227 1021427687271844219129776341)
                ·
                  refine ⟨23939711420433848885854133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1021427687271844219129776341 23939711420433848885854133)
                  ·
                    refine ⟨2244347945665673333048825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23939711420433848885854133 2244347945665673333048825)
                    ·
                      refine ⟨1683260959249254999786619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2244347945665673333048825 1683260959249254999786619)
                      ·
                        rfl

theorem cell23_3278139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 5, 2].length) (baseStart_3278139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278139 prefixEnd_3278139 := by exact prefixLift 3278139
  have htrace : WordTrace (prefixWord ++ tailWord_3278139) baseStart_3278139 baseEnd_3278139 := by
    simpa [prefixWord, tailWord_3278139, baseEnd_3278139] using wordTrace_append hprefix tailTrace_3278139
  have hstable : (prefixWord ++ tailWord_3278139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278139).length < 2 ^ (prefixWord ++ tailWord_3278139).sum := by decide
  have hdescent : baseEnd_3278139 < baseStart_3278139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278149 : List Nat := [1, 3, 1, 1, 1, 2, 1, 7, 1, 5]
def baseStart_3278149 : Nat := 118140960795 + 3278149 * 2 ^ 59
def prefixEnd_3278149 : Nat := 4983230072969 + 3 ^ 40 * 3278149 * 2
def baseEnd_3278149 : Nat := 561088698018599986887191

theorem tailTrace_3278149 : CollatzResearch.WordTrace tailWord_3278149 prefixEnd_3278149 561088698018599986887191 := by
  unfold tailWord_3278149
  simp only [CollatzResearch.WordTrace]
  refine ⟨119563916600833511121317501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79709277733889007414211667 119563916600833511121317501)
  ·
    refine ⟨44836468725312566670494063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119563916600833511121317501 44836468725312566670494063)
    ·
      refine ⟨67254703087968850005741095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44836468725312566670494063 67254703087968850005741095)
      ·
        refine ⟨100882054631953275008611643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67254703087968850005741095 100882054631953275008611643)
        ·
          refine ⟨151323081947929912512917465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100882054631953275008611643 151323081947929912512917465)
          ·
            refine ⟨113492311460947434384688099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151323081947929912512917465 113492311460947434384688099)
            ·
              refine ⟨170238467191421151577032149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113492311460947434384688099 170238467191421151577032149)
              ·
                refine ⟨3989964074798933240086691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 170238467191421151577032149 3989964074798933240086691)
                ·
                  refine ⟨5984946112198399860130037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3989964074798933240086691 5984946112198399860130037)
                  ·
                    refine ⟨561088698018599986887191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5984946112198399860130037 561088698018599986887191)
                    ·
                      rfl

theorem cell23_3278149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_3278149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278149 prefixEnd_3278149 := by exact prefixLift 3278149
  have htrace : WordTrace (prefixWord ++ tailWord_3278149) baseStart_3278149 baseEnd_3278149 := by
    simpa [prefixWord, tailWord_3278149, baseEnd_3278149] using wordTrace_append hprefix tailTrace_3278149
  have hstable : (prefixWord ++ tailWord_3278149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278149).length < 2 ^ (prefixWord ++ tailWord_3278149).sum := by decide
  have hdescent : baseEnd_3278149 < baseStart_3278149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278157 : List Nat := [1, 6, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_3278157 : Nat := 118140960795 + 3278157 * 2 ^ 59
def prefixEnd_3278157 : Nat := 4983230072969 + 3 ^ 40 * 3278157 * 2
def baseEnd_3278157 : Nat := 561090067300345309787179

theorem tailTrace_3278157 : CollatzResearch.WordTrace tailWord_3278157 prefixEnd_3278157 561090067300345309787179 := by
  unfold tailWord_3278157
  simp only [CollatzResearch.WordTrace]
  refine ⟨119564208384804528487608725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79709472256536352325072483 119564208384804528487608725)
  ·
    refine ⟨5604572268037712272856659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119564208384804528487608725 5604572268037712272856659)
    ·
      refine ⟨8406858402056568409284989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5604572268037712272856659 8406858402056568409284989)
      ·
        refine ⟨3152571900771213153481871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8406858402056568409284989 3152571900771213153481871)
        ·
          refine ⟨4728857851156819730222807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3152571900771213153481871 4728857851156819730222807)
          ·
            refine ⟨7093286776735229595334211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728857851156819730222807 7093286776735229595334211)
            ·
              refine ⟨10639930165102844393001317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7093286776735229595334211 10639930165102844393001317)
              ·
                refine ⟨1994986905956783323687747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10639930165102844393001317 1994986905956783323687747)
                ·
                  refine ⟨2992480358935174985531621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994986905956783323687747 2992480358935174985531621)
                  ·
                    refine ⟨561090067300345309787179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2992480358935174985531621 561090067300345309787179)
                    ·
                      rfl

theorem cell23_3278157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_3278157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278157 prefixEnd_3278157 := by exact prefixLift 3278157
  have htrace : WordTrace (prefixWord ++ tailWord_3278157) baseStart_3278157 baseEnd_3278157 := by
    simpa [prefixWord, tailWord_3278157, baseEnd_3278157] using wordTrace_append hprefix tailTrace_3278157
  have hstable : (prefixWord ++ tailWord_3278157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278157).length < 2 ^ (prefixWord ++ tailWord_3278157).sum := by decide
  have hdescent : baseEnd_3278157 < baseStart_3278157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278163 : List Nat := [1, 1, 1, 2, 1, 1, 7, 4, 1, 1, 3]
def baseStart_3278163 : Nat := 118140960795 + 3278163 * 2 ^ 59
def prefixEnd_3278163 : Nat := 4983230072969 + 3 ^ 40 * 3278163 * 2
def baseEnd_3278163 : Nat := 1683273282784962905886509

theorem tailTrace_3278163 : CollatzResearch.WordTrace tailWord_3278163 prefixEnd_3278163 1683273282784962905886509 := by
  unfold tailWord_3278163
  simp only [CollatzResearch.WordTrace]
  refine ⟨119564427222782791512327143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79709618148521861008218095 119564427222782791512327143)
  ·
    refine ⟨179346640834174187268490715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119564427222782791512327143 179346640834174187268490715)
    ·
      refine ⟨269019961251261280902736073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179346640834174187268490715 269019961251261280902736073)
      ·
        refine ⟨201764970938445960677052055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269019961251261280902736073 201764970938445960677052055)
        ·
          refine ⟨302647456407668941015578083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201764970938445960677052055 302647456407668941015578083)
          ·
            refine ⟨453971184611503411523367125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302647456407668941015578083 453971184611503411523367125)
            ·
              refine ⟨10639949639332111207578917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 453971184611503411523367125 10639949639332111207578917)
              ·
                refine ⟨1994990557374770851421047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10639949639332111207578917 1994990557374770851421047)
                ·
                  refine ⟨2992485836062156277131571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1994990557374770851421047 2992485836062156277131571)
                  ·
                    refine ⟨4488728754093234415697357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2992485836062156277131571 4488728754093234415697357)
                    ·
                      refine ⟨1683273282784962905886509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4488728754093234415697357 1683273282784962905886509)
                      ·
                        rfl

theorem cell23_3278163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 1, 1, 3].length) (baseStart_3278163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278163 prefixEnd_3278163 := by exact prefixLift 3278163
  have htrace : WordTrace (prefixWord ++ tailWord_3278163) baseStart_3278163 baseEnd_3278163 := by
    simpa [prefixWord, tailWord_3278163, baseEnd_3278163] using wordTrace_append hprefix tailTrace_3278163
  have hstable : (prefixWord ++ tailWord_3278163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278163).length < 2 ^ (prefixWord ++ tailWord_3278163).sum := by decide
  have hdescent : baseEnd_3278163 < baseStart_3278163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278169 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 3, 1, 4]
def baseStart_3278169 : Nat := 118140960795 + 3278169 * 2 ^ 59
def prefixEnd_3278169 : Nat := 4983230072969 + 3 ^ 40 * 3278169 * 2
def baseEnd_3278169 : Nat := 1683276363668889882411481

theorem tailTrace_3278169 : CollatzResearch.WordTrace tailWord_3278169 prefixEnd_3278169 1683276363668889882411481 := by
  unfold tailWord_3278169
  simp only [CollatzResearch.WordTrace]
  refine ⟨119564646060761054537045561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79709764040507369691363707 119564646060761054537045561)
  ·
    refine ⟨89673484545570790902784171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119564646060761054537045561 89673484545570790902784171)
    ·
      refine ⟨134510226818356186354176257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89673484545570790902784171 134510226818356186354176257)
      ·
        refine ⟨100882670113767139765632193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134510226818356186354176257 100882670113767139765632193)
        ·
          refine ⟨75662002585325354824224145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100882670113767139765632193 75662002585325354824224145)
          ·
            refine ⟨56746501938994016118168109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75662002585325354824224145 56746501938994016118168109)
            ·
              refine ⟨21279938227122756044313041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56746501938994016118168109 21279938227122756044313041)
              ·
                refine ⟨15959953670342067033234781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21279938227122756044313041 15959953670342067033234781)
                ·
                  refine ⟨5984982626378275137463043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15959953670342067033234781 5984982626378275137463043)
                  ·
                    refine ⟨8977473939567412706194565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5984982626378275137463043 8977473939567412706194565)
                    ·
                      refine ⟨1683276363668889882411481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8977473939567412706194565 1683276363668889882411481)
                      ·
                        rfl

theorem cell23_3278169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_3278169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278169 prefixEnd_3278169 := by exact prefixLift 3278169
  have htrace : WordTrace (prefixWord ++ tailWord_3278169) baseStart_3278169 baseEnd_3278169 := by
    simpa [prefixWord, tailWord_3278169, baseEnd_3278169] using wordTrace_append hprefix tailTrace_3278169
  have hstable : (prefixWord ++ tailWord_3278169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278169).length < 2 ^ (prefixWord ++ tailWord_3278169).sum := by decide
  have hdescent : baseEnd_3278169 < baseStart_3278169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278179 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 1, 6]
def baseStart_3278179 : Nat := 118140960795 + 3278179 * 2 ^ 59
def prefixEnd_3278179 : Nat := 4983230072969 + 3 ^ 40 * 3278179 * 2
def baseEnd_3278179 : Nat := 561093832825144947762145

theorem tailTrace_3278179 : CollatzResearch.WordTrace tailWord_3278179 prefixEnd_3278179 561093832825144947762145 := by
  unfold tailWord_3278179
  simp only [CollatzResearch.WordTrace]
  refine ⟨119565010790724826244909591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79710007193816550829939727 119565010790724826244909591)
  ·
    refine ⟨179347516186087239367364387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119565010790724826244909591 179347516186087239367364387)
    ·
      refine ⟨269021274279130859051046581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179347516186087239367364387 269021274279130859051046581)
      ·
        refine ⟨25220744463668518036035617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269021274279130859051046581 25220744463668518036035617)
        ·
          refine ⟨18915558347751388527026713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25220744463668518036035617 18915558347751388527026713)
          ·
            refine ⟨14186668760813541395270035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18915558347751388527026713 14186668760813541395270035)
            ·
              refine ⟨21280003141220312092905053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14186668760813541395270035 21280003141220312092905053)
              ·
                refine ⟨7980001177957617034839395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21280003141220312092905053 7980001177957617034839395)
                ·
                  refine ⟨11970001766936425552259093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7980001177957617034839395 11970001766936425552259093)
                  ·
                    refine ⟨561093832825144947762145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11970001766936425552259093 561093832825144947762145)
                    ·
                      rfl

theorem cell23_3278179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 6].length) (baseStart_3278179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278179 prefixEnd_3278179 := by exact prefixLift 3278179
  have htrace : WordTrace (prefixWord ++ tailWord_3278179) baseStart_3278179 baseEnd_3278179 := by
    simpa [prefixWord, tailWord_3278179, baseEnd_3278179] using wordTrace_append hprefix tailTrace_3278179
  have hstable : (prefixWord ++ tailWord_3278179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278179).length < 2 ^ (prefixWord ++ tailWord_3278179).sum := by decide
  have hdescent : baseEnd_3278179 < baseStart_3278179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278190 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_3278190 : Nat := 118140960795 + 3278190 * 2 ^ 59
def prefixEnd_3278190 : Nat := 4983230072969 + 3 ^ 40 * 3278190 * 2
def baseEnd_3278190 : Nat := 1683287146762634300248885

theorem tailTrace_3278190 : CollatzResearch.WordTrace tailWord_3278190 prefixEnd_3278190 1683287146762634300248885 := by
  unfold tailWord_3278190
  simp only [CollatzResearch.WordTrace]
  refine ⟨14945676499210621890445003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79710274662456650082373349 14945676499210621890445003)
  ·
    refine ⟨22418514748815932835667505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14945676499210621890445003 22418514748815932835667505)
    ·
      refine ⟨16813886061611949626750629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22418514748815932835667505 16813886061611949626750629)
      ·
        refine ⟨3152603636552240555015743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16813886061611949626750629 3152603636552240555015743)
        ·
          refine ⟨4728905454828360832523615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3152603636552240555015743 4728905454828360832523615)
          ·
            refine ⟨7093358182242541248785423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728905454828360832523615 7093358182242541248785423)
            ·
              refine ⟨10640037273363811873178135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7093358182242541248785423 10640037273363811873178135)
              ·
                refine ⟨15960055910045717809767203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10640037273363811873178135 15960055910045717809767203)
                ·
                  refine ⟨23940083865068576714650805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15960055910045717809767203 23940083865068576714650805)
                  ·
                    refine ⟨2244382862350179066998513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23940083865068576714650805 2244382862350179066998513)
                    ·
                      refine ⟨1683287146762634300248885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2244382862350179066998513 1683287146762634300248885)
                      ·
                        rfl

theorem cell23_3278190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_3278190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278190 prefixEnd_3278190 := by exact prefixLift 3278190
  have htrace : WordTrace (prefixWord ++ tailWord_3278190) baseStart_3278190 baseEnd_3278190 := by
    simpa [prefixWord, tailWord_3278190, baseEnd_3278190] using wordTrace_append hprefix tailTrace_3278190
  have hstable : (prefixWord ++ tailWord_3278190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278190).length < 2 ^ (prefixWord ++ tailWord_3278190).sum := by decide
  have hdescent : baseEnd_3278190 < baseStart_3278190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278197 : List Nat := [1, 3, 4, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_3278197 : Nat := 118140960795 + 3278197 * 2 ^ 59
def prefixEnd_3278197 : Nat := 4983230072969 + 3 ^ 40 * 3278197 * 2
def baseEnd_3278197 : Nat := 1683290741127215772861353

theorem tailTrace_3278197 : CollatzResearch.WordTrace tailWord_3278197 prefixEnd_3278197 1683290741127215772861353 := by
  unfold tailWord_3278197
  simp only [CollatzResearch.WordTrace]
  refine ⟨119565667304659615319064845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79710444869773076879376563 119565667304659615319064845)
  ·
    refine ⟨44837125239247355744649317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119565667304659615319064845 44837125239247355744649317)
    ·
      refine ⟨8406960982358879202121747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44837125239247355744649317 8406960982358879202121747)
      ·
        refine ⟨12610441473538318803182621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8406960982358879202121747 12610441473538318803182621)
        ·
          refine ⟨4728915552576869551193483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12610441473538318803182621 4728915552576869551193483)
          ·
            refine ⟨7093373328865304326790225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4728915552576869551193483 7093373328865304326790225)
            ·
              refine ⟨5320029996648978245092669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7093373328865304326790225 5320029996648978245092669)
              ·
                refine ⟨1995011248743366841909751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5320029996648978245092669 1995011248743366841909751)
                ·
                  refine ⟨2992516873115050262864627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995011248743366841909751 2992516873115050262864627)
                  ·
                    refine ⟨4488775309672575394296941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2992516873115050262864627 4488775309672575394296941)
                    ·
                      refine ⟨1683290741127215772861353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4488775309672575394296941 1683290741127215772861353)
                      ·
                        rfl

theorem cell23_3278197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_3278197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278197 prefixEnd_3278197 := by exact prefixLift 3278197
  have htrace : WordTrace (prefixWord ++ tailWord_3278197) baseStart_3278197 baseEnd_3278197 := by
    simpa [prefixWord, tailWord_3278197, baseEnd_3278197] using wordTrace_append hprefix tailTrace_3278197
  have hstable : (prefixWord ++ tailWord_3278197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278197).length < 2 ^ (prefixWord ++ tailWord_3278197).sum := by decide
  have hdescent : baseEnd_3278197 < baseStart_3278197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278199 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 4]
def baseStart_3278199 : Nat := 118140960795 + 3278199 * 2 ^ 59
def prefixEnd_3278199 : Nat := 4983230072969 + 3 ^ 40 * 3278199 * 2
def baseEnd_3278199 : Nat := 1683291768088524765036343

theorem tailTrace_3278199 : CollatzResearch.WordTrace tailWord_3278199 prefixEnd_3278199 1683291768088524765036343 := by
  unfold tailWord_3278199
  simp only [CollatzResearch.WordTrace]
  refine ⟨119565740250652369660637651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79710493500434913107091767 119565740250652369660637651)
  ·
    refine ⟨179348610375978554490956477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119565740250652369660637651 179348610375978554490956477)
    ·
      refine ⟨67255728890991957934108679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179348610375978554490956477 67255728890991957934108679)
      ·
        refine ⟨100883593336487936901163019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67255728890991957934108679 100883593336487936901163019)
        ·
          refine ⟨151325390004731905351744529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100883593336487936901163019 151325390004731905351744529)
          ·
            refine ⟨113494042503548929013808397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151325390004731905351744529 113494042503548929013808397)
            ·
              refine ⟨42560265938830848380178149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113494042503548929013808397 42560265938830848380178149)
              ·
                refine ⟨7980049863530784071283403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42560265938830848380178149 7980049863530784071283403)
                ·
                  refine ⟨11970074795296176106925105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7980049863530784071283403 11970074795296176106925105)
                  ·
                    refine ⟨8977556096472132080193829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11970074795296176106925105 8977556096472132080193829)
                    ·
                      refine ⟨1683291768088524765036343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8977556096472132080193829 1683291768088524765036343)
                      ·
                        rfl

theorem cell23_3278199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_3278199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278199 prefixEnd_3278199 := by exact prefixLift 3278199
  have htrace : WordTrace (prefixWord ++ tailWord_3278199) baseStart_3278199 baseEnd_3278199 := by
    simpa [prefixWord, tailWord_3278199, baseEnd_3278199] using wordTrace_append hprefix tailTrace_3278199
  have hstable : (prefixWord ++ tailWord_3278199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278199).length < 2 ^ (prefixWord ++ tailWord_3278199).sum := by decide
  have hdescent : baseEnd_3278199 < baseStart_3278199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278220 : List Nat := [2, 2, 1, 2, 1, 3, 1, 6, 1, 2, 2]
def baseStart_3278220 : Nat := 118140960795 + 3278220 * 2 ^ 59
def prefixEnd_3278220 : Nat := 4983230072969 + 3 ^ 40 * 3278220 * 2
def baseEnd_3278220 : Nat := 1683302551182269182873747

theorem tailTrace_3278220 : CollatzResearch.WordTrace tailWord_3278220 prefixEnd_3278220 1683302551182269182873747 := by
  unfold tailWord_3278220
  simp only [CollatzResearch.WordTrace]
  refine ⟨59783253091788145123576057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79711004122384193498101409 59783253091788145123576057)
  ·
    refine ⟨44837439818841108842682043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59783253091788145123576057 44837439818841108842682043)
    ·
      refine ⟨67256159728261663264023065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44837439818841108842682043 67256159728261663264023065)
      ·
        refine ⟨50442119796196247448017299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67256159728261663264023065 50442119796196247448017299)
        ·
          refine ⟨75663179694294371172025949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50442119796196247448017299 75663179694294371172025949)
          ·
            refine ⟨28373692385360389189509731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75663179694294371172025949 28373692385360389189509731)
            ·
              refine ⟨42560538578040583784264597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28373692385360389189509731 42560538578040583784264597)
              ·
                refine ⟨1995025245845652364887403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42560538578040583784264597 1995025245845652364887403)
                ·
                  refine ⟨2992537868768478547331105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995025245845652364887403 2992537868768478547331105)
                  ·
                    refine ⟨2244403401576358910498329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2992537868768478547331105 2244403401576358910498329)
                    ·
                      refine ⟨1683302551182269182873747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2244403401576358910498329 1683302551182269182873747)
                      ·
                        rfl

theorem cell23_3278220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_3278220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278220 prefixEnd_3278220 := by exact prefixLift 3278220
  have htrace : WordTrace (prefixWord ++ tailWord_3278220) baseStart_3278220 baseEnd_3278220 := by
    simpa [prefixWord, tailWord_3278220, baseEnd_3278220] using wordTrace_append hprefix tailTrace_3278220
  have hstable : (prefixWord ++ tailWord_3278220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278220).length < 2 ^ (prefixWord ++ tailWord_3278220).sum := by decide
  have hdescent : baseEnd_3278220 < baseStart_3278220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278263 : List Nat := [1, 1, 3, 1, 3, 2, 1, 5, 1, 3, 2]
def baseStart_3278263 : Nat := 118140960795 + 3278263 * 2 ^ 59
def prefixEnd_3278263 : Nat := 4983230072969 + 3 ^ 40 * 3278263 * 2
def baseEnd_3278263 : Nat := 1683324630850412514636049

theorem tailTrace_3278263 : CollatzResearch.WordTrace tailWord_3278263 prefixEnd_3278263 1683324630850412514636049 := by
  unfold tailWord_3278263
  simp only [CollatzResearch.WordTrace]
  refine ⟨119568074522420508590967443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79712049681613672393978295 119568074522420508590967443)
  ·
    refine ⟨179352111783630762886451165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119568074522420508590967443 179352111783630762886451165)
    ·
      refine ⟨67257041918861536082419187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179352111783630762886451165 67257041918861536082419187)
      ·
        refine ⟨100885562878292304123628781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67257041918861536082419187 100885562878292304123628781)
        ·
          refine ⟨37832086079359614046360793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100885562878292304123628781 37832086079359614046360793)
          ·
            refine ⟨28374064559519710534770595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37832086079359614046360793 28374064559519710534770595)
            ·
              refine ⟨42561096839279565802155893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28374064559519710534770595 42561096839279565802155893)
              ·
                refine ⟨3990102828682459293952115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42561096839279565802155893 3990102828682459293952115)
                ·
                  refine ⟨5985154243023688940928173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990102828682459293952115 5985154243023688940928173)
                  ·
                    refine ⟨2244432841133883352848065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5985154243023688940928173 2244432841133883352848065)
                    ·
                      refine ⟨1683324630850412514636049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2244432841133883352848065 1683324630850412514636049)
                      ·
                        rfl

theorem cell23_3278263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 3, 2].length) (baseStart_3278263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278263 prefixEnd_3278263 := by exact prefixLift 3278263
  have htrace : WordTrace (prefixWord ++ tailWord_3278263) baseStart_3278263 baseEnd_3278263 := by
    simpa [prefixWord, tailWord_3278263, baseEnd_3278263] using wordTrace_append hprefix tailTrace_3278263
  have hstable : (prefixWord ++ tailWord_3278263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278263).length < 2 ^ (prefixWord ++ tailWord_3278263).sum := by decide
  have hdescent : baseEnd_3278263 < baseStart_3278263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278279 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_3278279 : Nat := 118140960795 + 3278279 * 2 ^ 59
def prefixEnd_3278279 : Nat := 4983230072969 + 3 ^ 40 * 3278279 * 2
def baseEnd_3278279 : Nat := 1683332846540884452035975

theorem tailTrace_3278279 : CollatzResearch.WordTrace tailWord_3278279 prefixEnd_3278279 1683332846540884452035975 := by
  unfold tailWord_3278279
  simp only [CollatzResearch.WordTrace]
  refine ⟨119568658090362543323549891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79712438726908362215699927 119568658090362543323549891)
  ·
    refine ⟨179352987135543814985324837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119568658090362543323549891 179352987135543814985324837)
    ·
      refine ⟨33628685087914465309748407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179352987135543814985324837 33628685087914465309748407)
      ·
        refine ⟨50443027631871697964622611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33628685087914465309748407 50443027631871697964622611)
        ·
          refine ⟨75664541447807546946933917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50443027631871697964622611 75664541447807546946933917)
          ·
            refine ⟨28374203042927830105100219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75664541447807546946933917 28374203042927830105100219)
            ·
              refine ⟨42561304564391745157650329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28374203042927830105100219 42561304564391745157650329)
              ·
                refine ⟨31920978423293808868237747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42561304564391745157650329 31920978423293808868237747)
                ·
                  refine ⟨47881467634940713302356621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31920978423293808868237747 47881467634940713302356621)
                  ·
                    refine ⟨17955550363102767488383733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47881467634940713302356621 17955550363102767488383733)
                    ·
                      refine ⟨1683332846540884452035975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17955550363102767488383733 1683332846540884452035975)
                      ·
                        rfl

theorem cell23_3278279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_3278279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278279 prefixEnd_3278279 := by exact prefixLift 3278279
  have htrace : WordTrace (prefixWord ++ tailWord_3278279) baseStart_3278279 baseEnd_3278279 := by
    simpa [prefixWord, tailWord_3278279, baseEnd_3278279] using wordTrace_append hprefix tailTrace_3278279
  have hstable : (prefixWord ++ tailWord_3278279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278279).length < 2 ^ (prefixWord ++ tailWord_3278279).sum := by decide
  have hdescent : baseEnd_3278279 < baseStart_3278279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278293 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 1, 4, 2]
def baseStart_3278293 : Nat := 118140960795 + 3278293 * 2 ^ 59
def prefixEnd_3278293 : Nat := 4983230072969 + 3 ^ 40 * 3278293 * 2
def baseEnd_3278293 : Nat := 1683340035270047397260911

theorem tailTrace_3278293 : CollatzResearch.WordTrace tailWord_3278293 prefixEnd_3278293 1683340035270047397260911 := by
  unfold tailWord_3278293
  simp only [CollatzResearch.WordTrace]
  refine ⟨119569168712311823714559533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79712779141541215809706355 119569168712311823714559533)
  ·
    refine ⟨44838438267116933892959825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119569168712311823714559533 44838438267116933892959825)
    ·
      refine ⟨33628828700337700419719869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44838438267116933892959825 33628828700337700419719869)
      ·
        refine ⟨12610810762626637657394951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33628828700337700419719869 12610810762626637657394951)
        ·
          refine ⟨18916216143939956486092427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12610810762626637657394951 18916216143939956486092427)
          ·
            refine ⟨28374324215909934729138641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18916216143939956486092427 28374324215909934729138641)
            ·
              refine ⟨21280743161932451046853981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28374324215909934729138641 21280743161932451046853981)
              ·
                refine ⟨7980278685724669142570243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21280743161932451046853981 7980278685724669142570243)
                ·
                  refine ⟨11970418028587003713855365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7980278685724669142570243 11970418028587003713855365)
                  ·
                    refine ⟨2244453380360063196347881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11970418028587003713855365 2244453380360063196347881)
                    ·
                      refine ⟨1683340035270047397260911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2244453380360063196347881 1683340035270047397260911)
                      ·
                        rfl

theorem cell23_3278293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_3278293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278293 prefixEnd_3278293 := by exact prefixLift 3278293
  have htrace : WordTrace (prefixWord ++ tailWord_3278293) baseStart_3278293 baseEnd_3278293 := by
    simpa [prefixWord, tailWord_3278293, baseEnd_3278293] using wordTrace_append hprefix tailTrace_3278293
  have hstable : (prefixWord ++ tailWord_3278293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278293).length < 2 ^ (prefixWord ++ tailWord_3278293).sum := by decide
  have hdescent : baseEnd_3278293 < baseStart_3278293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278329 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 3, 7]
def baseStart_3278329 : Nat := 118140960795 + 3278329 * 2 ^ 59
def prefixEnd_3278329 : Nat := 4983230072969 + 3 ^ 40 * 3278329 * 2
def baseEnd_3278329 : Nat := 561119506857869752136915

theorem tailTrace_3278329 : CollatzResearch.WordTrace tailWord_3278329 prefixEnd_3278329 561119506857869752136915 := by
  unfold tailWord_3278329
  simp only [CollatzResearch.WordTrace]
  refine ⟨119570481740181401862870041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79713654493454267908580027 119570481740181401862870041)
  ·
    refine ⟨89677861305136051397152531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119570481740181401862870041 89677861305136051397152531)
    ·
      refine ⟨134516791957704077095728797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89677861305136051397152531 134516791957704077095728797)
      ·
        refine ⟨50443796984139028910898299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134516791957704077095728797 50443796984139028910898299)
        ·
          refine ⟨75665695476208543366347449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50443796984139028910898299 75665695476208543366347449)
          ·
            refine ⟨56749271607156407524760587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75665695476208543366347449 56749271607156407524760587)
            ·
              refine ⟨85123907410734611287140881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56749271607156407524760587 85123907410734611287140881)
              ·
                refine ⟨63842930558050958465355661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85123907410734611287140881 63842930558050958465355661)
                ·
                  refine ⟨23941098959269109424508373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63842930558050958465355661 23941098959269109424508373)
                  ·
                    refine ⟨561119506857869752136915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23941098959269109424508373 561119506857869752136915)
                    ·
                      rfl

theorem cell23_3278329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_3278329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278329 prefixEnd_3278329 := by exact prefixLift 3278329
  have htrace : WordTrace (prefixWord ++ tailWord_3278329) baseStart_3278329 baseEnd_3278329 := by
    simpa [prefixWord, tailWord_3278329, baseEnd_3278329] using wordTrace_append hprefix tailTrace_3278329
  have hstable : (prefixWord ++ tailWord_3278329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278329).length < 2 ^ (prefixWord ++ tailWord_3278329).sum := by decide
  have hdescent : baseEnd_3278329 < baseStart_3278329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278333 : List Nat := [1, 4, 1, 1, 1, 5, 1, 4, 5]
def baseStart_3278333 : Nat := 118140960795 + 3278333 * 2 ^ 59
def prefixEnd_3278333 : Nat := 4983230072969 + 3 ^ 40 * 3278333 * 2
def baseEnd_3278333 : Nat := 187040063832914137862303

theorem tailTrace_3278333 : CollatzResearch.WordTrace tailWord_3278333 prefixEnd_3278333 187040063832914137862303 := by
  unfold tailWord_3278333
  simp only [CollatzResearch.WordTrace]
  refine ⟨119570627632166910546015653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79713751754777940364010435 119570627632166910546015653)
  ·
    refine ⟨22419492681031295727377935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119570627632166910546015653 22419492681031295727377935)
    ·
      refine ⟨33629239021546943591066903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22419492681031295727377935 33629239021546943591066903)
      ·
        refine ⟨50443858532320415386600355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33629239021546943591066903 50443858532320415386600355)
        ·
          refine ⟨75665787798480623079900533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50443858532320415386600355 75665787798480623079900533)
          ·
            refine ⟨7093667606107558413740675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75665787798480623079900533 7093667606107558413740675)
            ·
              refine ⟨10640501409161337620611013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7093667606107558413740675 10640501409161337620611013)
              ·
                refine ⟨1995094014217750803864565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10640501409161337620611013 1995094014217750803864565)
                ·
                  refine ⟨187040063832914137862303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1995094014217750803864565 187040063832914137862303)
                  ·
                    rfl

theorem cell23_3278333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_3278333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278333 prefixEnd_3278333 := by exact prefixLift 3278333
  have htrace : WordTrace (prefixWord ++ tailWord_3278333) baseStart_3278333 baseEnd_3278333 := by
    simpa [prefixWord, tailWord_3278333, baseEnd_3278333] using wordTrace_append hprefix tailTrace_3278333
  have hstable : (prefixWord ++ tailWord_3278333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278333).length < 2 ^ (prefixWord ++ tailWord_3278333).sum := by decide
  have hdescent : baseEnd_3278333 < baseStart_3278333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278339 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 7]
def baseStart_3278339 : Nat := 118140960795 + 3278339 * 2 ^ 59
def prefixEnd_3278339 : Nat := 4983230072969 + 3 ^ 40 * 3278339 * 2
def baseEnd_3278339 : Nat := 1683363655380154217285699

theorem tailTrace_3278339 : CollatzResearch.WordTrace tailWord_3278339 prefixEnd_3278339 1683363655380154217285699 := by
  unfold tailWord_3278339
  simp only [CollatzResearch.WordTrace]
  refine ⟨119570846470145173570734071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79713897646763449047156047 119570846470145173570734071)
  ·
    refine ⟨179356269705217760356101107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119570846470145173570734071 179356269705217760356101107)
    ·
      refine ⟨269034404557826640534151661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179356269705217760356101107 269034404557826640534151661)
      ·
        refine ⟨100887901709184990200306873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269034404557826640534151661 100887901709184990200306873)
        ·
          refine ⟨75665926281888742650230155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100887901709184990200306873 75665926281888742650230155)
          ·
            refine ⟨113498889422833113975345233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75665926281888742650230155 113498889422833113975345233)
            ·
              refine ⟨85124167067124835481508925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113498889422833113975345233 85124167067124835481508925)
              ·
                refine ⟨31921562650171813305565847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85124167067124835481508925 31921562650171813305565847)
                ·
                  refine ⟨47882343975257719958348771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31921562650171813305565847 47882343975257719958348771)
                  ·
                    refine ⟨71823515962886579937523157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47882343975257719958348771 71823515962886579937523157)
                    ·
                      refine ⟨1683363655380154217285699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71823515962886579937523157 1683363655380154217285699)
                      ·
                        rfl

theorem cell23_3278339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_3278339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278339 prefixEnd_3278339 := by exact prefixLift 3278339
  have htrace : WordTrace (prefixWord ++ tailWord_3278339) baseStart_3278339 baseEnd_3278339 := by
    simpa [prefixWord, tailWord_3278339, baseEnd_3278339] using wordTrace_append hprefix tailTrace_3278339
  have hstable : (prefixWord ++ tailWord_3278339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278339).length < 2 ^ (prefixWord ++ tailWord_3278339).sum := by decide
  have hdescent : baseEnd_3278339 < baseStart_3278339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278343 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_3278343 : Nat := 118140960795 + 3278343 * 2 ^ 59
def prefixEnd_3278343 : Nat := 4983230072969 + 3 ^ 40 * 3278343 * 2
def baseEnd_3278343 : Nat := 1683365709302772201635681

theorem tailTrace_3278343 : CollatzResearch.WordTrace tailWord_3278343 prefixEnd_3278343 1683365709302772201635681 := by
  unfold tailWord_3278343
  simp only [CollatzResearch.WordTrace]
  refine ⟨119570992362130682253879683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79713994908087121502586455 119570992362130682253879683)
  ·
    refine ⟨179356488543196023380819525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119570992362130682253879683 179356488543196023380819525)
    ·
      refine ⟨33629341601849254383903661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179356488543196023380819525 33629341601849254383903661)
      ·
        refine ⟨12611003100693470393963873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33629341601849254383903661 12611003100693470393963873)
        ·
          refine ⟨9458252325520102795472905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12611003100693470393963873 9458252325520102795472905)
          ·
            refine ⟨7093689244140077096604679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9458252325520102795472905 7093689244140077096604679)
            ·
              refine ⟨10640533866210115644907019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7093689244140077096604679 10640533866210115644907019)
              ·
                refine ⟨15960800799315173467360529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10640533866210115644907019 15960800799315173467360529)
                ·
                  refine ⟨11970600599486380100520397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15960800799315173467360529 11970600599486380100520397)
                  ·
                    refine ⟨4488975224807392537695149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11970600599486380100520397 4488975224807392537695149)
                    ·
                      refine ⟨1683365709302772201635681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4488975224807392537695149 1683365709302772201635681)
                      ·
                        rfl

theorem cell23_3278343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_3278343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278343 prefixEnd_3278343 := by exact prefixLift 3278343
  have htrace : WordTrace (prefixWord ++ tailWord_3278343) baseStart_3278343 baseEnd_3278343 := by
    simpa [prefixWord, tailWord_3278343, baseEnd_3278343] using wordTrace_append hprefix tailTrace_3278343
  have hstable : (prefixWord ++ tailWord_3278343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278343).length < 2 ^ (prefixWord ++ tailWord_3278343).sum := by decide
  have hdescent : baseEnd_3278343 < baseStart_3278343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278393 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 3, 4]
def baseStart_3278393 : Nat := 118140960795 + 3278393 * 2 ^ 59
def prefixEnd_3278393 : Nat := 4983230072969 + 3 ^ 40 * 3278393 * 2
def baseEnd_3278393 : Nat := 561130461111832335336817

theorem tailTrace_3278393 : CollatzResearch.WordTrace tailWord_3278393 prefixEnd_3278393 561130461111832335336817 := by
  unfold tailWord_3278393
  simp only [CollatzResearch.WordTrace]
  refine ⟨119572816011949540793199833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79715210674633027195466555 119572816011949540793199833)
  ·
    refine ⟨89679612008962155594899875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119572816011949540793199833 89679612008962155594899875)
    ·
      refine ⟨134519418013443233392349813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89679612008962155594899875 134519418013443233392349813)
      ·
        refine ⟨12611195438760303130532795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134519418013443233392349813 12611195438760303130532795)
        ·
          refine ⟨18916793158140454695799193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12611195438760303130532795 18916793158140454695799193)
          ·
            refine ⟨14187594868605341021849395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18916793158140454695799193 14187594868605341021849395)
            ·
              refine ⟨21281392302908011532774093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14187594868605341021849395 21281392302908011532774093)
              ·
                refine ⟨7980522113590504324790285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21281392302908011532774093 7980522113590504324790285)
                ·
                  refine ⟨2992695792596439121796357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7980522113590504324790285 2992695792596439121796357)
                  ·
                    refine ⟨561130461111832335336817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2992695792596439121796357 561130461111832335336817)
                    ·
                      rfl

theorem cell23_3278393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 4].length) (baseStart_3278393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278393 prefixEnd_3278393 := by exact prefixLift 3278393
  have htrace : WordTrace (prefixWord ++ tailWord_3278393) baseStart_3278393 baseEnd_3278393 := by
    simpa [prefixWord, tailWord_3278393, baseEnd_3278393] using wordTrace_append hprefix tailTrace_3278393
  have hstable : (prefixWord ++ tailWord_3278393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278393).length < 2 ^ (prefixWord ++ tailWord_3278393).sum := by decide
  have hdescent : baseEnd_3278393 < baseStart_3278393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278416 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 3]
def baseStart_3278416 : Nat := 118140960795 + 3278416 * 2 ^ 59
def prefixEnd_3278416 : Nat := 4983230072969 + 3 ^ 40 * 3278416 * 2
def baseEnd_3278416 : Nat := 1683403193390550416022845

theorem tailTrace_3278416 : CollatzResearch.WordTrace tailWord_3278416 prefixEnd_3278416 1683403193390550416022845 := by
  unfold tailWord_3278416
  simp only [CollatzResearch.WordTrace]
  refine ⟨59786827445433107860643551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79715769927244143814191401 59786827445433107860643551)
  ·
    refine ⟨89680241168149661790965327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59786827445433107860643551 89680241168149661790965327)
    ·
      refine ⟨134520361752224492686447991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89680241168149661790965327 134520361752224492686447991)
      ·
        refine ⟨201780542628336739029671987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134520361752224492686447991 201780542628336739029671987)
        ·
          refine ⟨302670813942505108544507981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201780542628336739029671987 302670813942505108544507981)
          ·
            refine ⟨113501555228439415704190493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302670813942505108544507981 113501555228439415704190493)
            ·
              refine ⟨42563083210664780889071435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113501555228439415704190493 42563083210664780889071435)
              ·
                refine ⟨63844624815997171333607153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42563083210664780889071435 63844624815997171333607153)
                ·
                  refine ⟨47883468611997878500205365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63844624815997171333607153 47883468611997878500205365)
                  ·
                    refine ⟨4489075182374801109394253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47883468611997878500205365 4489075182374801109394253)
                    ·
                      refine ⟨1683403193390550416022845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4489075182374801109394253 1683403193390550416022845)
                      ·
                        rfl

theorem cell23_3278416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 3].length) (baseStart_3278416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278416 prefixEnd_3278416 := by exact prefixLift 3278416
  have htrace : WordTrace (prefixWord ++ tailWord_3278416) baseStart_3278416 baseEnd_3278416 := by
    simpa [prefixWord, tailWord_3278416, baseEnd_3278416] using wordTrace_append hprefix tailTrace_3278416
  have hstable : (prefixWord ++ tailWord_3278416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278416).length < 2 ^ (prefixWord ++ tailWord_3278416).sum := by decide
  have hdescent : baseEnd_3278416 < baseStart_3278416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278473 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 2, 6, 2]
def baseStart_3278473 : Nat := 118140960795 + 3278473 * 2 ^ 59
def prefixEnd_3278473 : Nat := 4983230072969 + 3 ^ 40 * 3278473 * 2
def baseEnd_3278473 : Nat := 1683432461787856693010083

theorem tailTrace_3278473 : CollatzResearch.WordTrace tailWord_3278473 prefixEnd_3278473 1683432461787856693010083 := by
  unfold tailWord_3278473
  simp only [CollatzResearch.WordTrace]
  refine ⟨119575733851659714456112073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79717155901106476304074715 119575733851659714456112073)
  ·
    refine ⟨89681800388744785842084055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119575733851659714456112073 89681800388744785842084055)
    ·
      refine ⟨134522700583117178763126083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89681800388744785842084055 134522700583117178763126083)
      ·
        refine ⟨201784050874675768144689125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134522700583117178763126083 201784050874675768144689125)
        ·
          refine ⟨37834509539001706527129211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201784050874675768144689125 37834509539001706527129211)
          ·
            refine ⟨56751764308502559790693817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37834509539001706527129211 56751764308502559790693817)
            ·
              refine ⟨42563823231376919843020363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56751764308502559790693817 42563823231376919843020363)
              ·
                refine ⟨63845734847065379764530545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42563823231376919843020363 63845734847065379764530545)
                ·
                  refine ⟨47884301135299034823397909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63845734847065379764530545 47884301135299034823397909)
                  ·
                    refine ⟨2244576615717142257346777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47884301135299034823397909 2244576615717142257346777)
                    ·
                      refine ⟨1683432461787856693010083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2244576615717142257346777 1683432461787856693010083)
                      ·
                        rfl

theorem cell23_3278473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 6, 2].length) (baseStart_3278473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278473 prefixEnd_3278473 := by exact prefixLift 3278473
  have htrace : WordTrace (prefixWord ++ tailWord_3278473) baseStart_3278473 baseEnd_3278473 := by
    simpa [prefixWord, tailWord_3278473, baseEnd_3278473] using wordTrace_append hprefix tailTrace_3278473
  have hstable : (prefixWord ++ tailWord_3278473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278473).length < 2 ^ (prefixWord ++ tailWord_3278473).sum := by decide
  have hdescent : baseEnd_3278473 < baseStart_3278473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278496 : List Nat := [2, 1, 1, 4, 3, 12]
def baseStart_3278496 : Nat := 118140960795 + 3278496 * 2 ^ 59
def prefixEnd_3278496 : Nat := 4983230072969 + 3 ^ 40 * 3278496 * 2
def baseEnd_3278496 : Nat := 6927754205114856391039

theorem tailTrace_3278496 : CollatzResearch.WordTrace tailWord_3278496 prefixEnd_3278496 6927754205114856391039 := by
  unfold tailWord_3278496
  simp only [CollatzResearch.WordTrace]
  refine ⟨59788286365288194692099671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79717715153717592922799561 59788286365288194692099671)
  ·
    refine ⟨89682429547932292038149507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59788286365288194692099671 89682429547932292038149507)
    ·
      refine ⟨134523644321898438057224261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89682429547932292038149507 134523644321898438057224261)
      ·
        refine ⟨25223183310355957135729549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134523644321898438057224261 25223183310355957135729549)
        ·
          refine ⟨9458693741383483925898581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25223183310355957135729549 9458693741383483925898581)
          ·
            refine ⟨6927754205114856391039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9458693741383483925898581 6927754205114856391039)
            ·
              rfl

theorem cell23_3278496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 12].length) (baseStart_3278496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278496 prefixEnd_3278496 := by exact prefixLift 3278496
  have htrace : WordTrace (prefixWord ++ tailWord_3278496) baseStart_3278496 baseEnd_3278496 := by
    simpa [prefixWord, tailWord_3278496, baseEnd_3278496] using wordTrace_append hprefix tailTrace_3278496
  have hstable : (prefixWord ++ tailWord_3278496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278496).length < 2 ^ (prefixWord ++ tailWord_3278496).sum := by decide
  have hdescent : baseEnd_3278496 < baseStart_3278496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278500 : List Nat := [2, 3, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_3278500 : Nat := 118140960795 + 3278500 * 2 ^ 59
def prefixEnd_3278500 : Nat := 4983230072969 + 3 ^ 40 * 3278500 * 2
def baseEnd_3278500 : Nat := 561148775255176029124153

theorem tailTrace_3278500 : CollatzResearch.WordTrace tailWord_3278500 prefixEnd_3278500 561148775255176029124153 := by
  unfold tailWord_3278500
  simp only [CollatzResearch.WordTrace]
  refine ⟨59788359311280949033672477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79717812415041265378229969 59788359311280949033672477)
  ·
    refine ⟨22420634741730355887627179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59788359311280949033672477 22420634741730355887627179)
    ·
      refine ⟨33630952112595533831440769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22420634741730355887627179 33630952112595533831440769)
      ·
        refine ⟨25223214084446650373580577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33630952112595533831440769 25223214084446650373580577)
        ·
          refine ⟨18917410563334987780185433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25223214084446650373580577 18917410563334987780185433)
          ·
            refine ⟨14188057922501240835139075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18917410563334987780185433 14188057922501240835139075)
            ·
              refine ⟨21282086883751861252708613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14188057922501240835139075 21282086883751861252708613)
              ·
                refine ⟨3990391290703473984882865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21282086883751861252708613 3990391290703473984882865)
                ·
                  refine ⟨2992793468027605488662149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3990391290703473984882865 2992793468027605488662149)
                  ·
                    refine ⟨561148775255176029124153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2992793468027605488662149 561148775255176029124153)
                    ·
                      rfl

theorem cell23_3278500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_3278500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278500 prefixEnd_3278500 := by exact prefixLift 3278500
  have htrace : WordTrace (prefixWord ++ tailWord_3278500) baseStart_3278500 baseEnd_3278500 := by
    simpa [prefixWord, tailWord_3278500, baseEnd_3278500] using wordTrace_append hprefix tailTrace_3278500
  have hstable : (prefixWord ++ tailWord_3278500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278500).length < 2 ^ (prefixWord ++ tailWord_3278500).sum := by decide
  have hdescent : baseEnd_3278500 < baseStart_3278500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278541 : List Nat := [1, 6, 2, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_3278541 : Nat := 118140960795 + 3278541 * 2 ^ 59
def prefixEnd_3278541 : Nat := 4983230072969 + 3 ^ 40 * 3278541 * 2
def baseEnd_3278541 : Nat := 1683467378472362426959771

theorem tailTrace_3278541 : CollatzResearch.WordTrace tailWord_3278541 prefixEnd_3278541 1683467378472362426959771 := by
  unfold tailWord_3278541
  simp only [CollatzResearch.WordTrace]
  refine ⟨119578214015413362069587477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79718809343608908046391651 119578214015413362069587477)
  ·
    refine ⟨5605228781972501347011913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 119578214015413362069587477 5605228781972501347011913)
    ·
      refine ⟨4203921586479376010258935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5605228781972501347011913 4203921586479376010258935)
      ·
        refine ⟨6305882379719064015388403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4203921586479376010258935 6305882379719064015388403)
        ·
          refine ⟨9458823569578596023082605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6305882379719064015388403 9458823569578596023082605)
          ·
            refine ⟨3547058838591973508655977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9458823569578596023082605 3547058838591973508655977)
            ·
              refine ⟨2660294128943980131491983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3547058838591973508655977 2660294128943980131491983)
              ·
                refine ⟨3990441193415970197237975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2660294128943980131491983 3990441193415970197237975)
                ·
                  refine ⟨5985661790123955295856963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990441193415970197237975 5985661790123955295856963)
                  ·
                    refine ⟨8978492685185932943785445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5985661790123955295856963 8978492685185932943785445)
                    ·
                      refine ⟨1683467378472362426959771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8978492685185932943785445 1683467378472362426959771)
                      ·
                        rfl

theorem cell23_3278541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_3278541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278541 prefixEnd_3278541 := by exact prefixLift 3278541
  have htrace : WordTrace (prefixWord ++ tailWord_3278541) baseStart_3278541 baseEnd_3278541 := by
    simpa [prefixWord, tailWord_3278541, baseEnd_3278541] using wordTrace_append hprefix tailTrace_3278541
  have hstable : (prefixWord ++ tailWord_3278541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278541).length < 2 ^ (prefixWord ++ tailWord_3278541).sum := by decide
  have hdescent : baseEnd_3278541 < baseStart_3278541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278574 : List Nat := [4, 1, 2, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_3278574 : Nat := 118140960795 + 3278574 * 2 ^ 59
def prefixEnd_3278574 : Nat := 4983230072969 + 3 ^ 40 * 3278574 * 2
def baseEnd_3278574 : Nat := 1683484323333960797847119

theorem tailTrace_3278574 : CollatzResearch.WordTrace tailWord_3278574 prefixEnd_3278574 1683484323333960797847119 := by
  unfold tailWord_3278574
  simp only [CollatzResearch.WordTrace]
  refine ⟨14947427203036726088192347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79719611749529205803692517 14947427203036726088192347)
  ·
    refine ⟨22421140804555089132288521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14947427203036726088192347 22421140804555089132288521)
    ·
      refine ⟨16815855603416316849216391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22421140804555089132288521 16815855603416316849216391)
      ·
        refine ⟨25223783405124475273824587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16815855603416316849216391 25223783405124475273824587)
        ·
          refine ⟨37835675107686712910736881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25223783405124475273824587 37835675107686712910736881)
          ·
            refine ⟨28376756330765034683052661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37835675107686712910736881 28376756330765034683052661)
            ·
              refine ⟨2660320906009222001536187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28376756330765034683052661 2660320906009222001536187)
              ·
                refine ⟨3990481359013833002304281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2660320906009222001536187 3990481359013833002304281)
                ·
                  refine ⟨2992861019260374751728211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3990481359013833002304281 2992861019260374751728211)
                  ·
                    refine ⟨4489291528890562127592317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2992861019260374751728211 4489291528890562127592317)
                    ·
                      refine ⟨1683484323333960797847119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4489291528890562127592317 1683484323333960797847119)
                      ·
                        rfl

theorem cell23_3278574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_3278574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278574 prefixEnd_3278574 := by exact prefixLift 3278574
  have htrace : WordTrace (prefixWord ++ tailWord_3278574) baseStart_3278574 baseEnd_3278574 := by
    simpa [prefixWord, tailWord_3278574, baseEnd_3278574] using wordTrace_append hprefix tailTrace_3278574
  have hstable : (prefixWord ++ tailWord_3278574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278574).length < 2 ^ (prefixWord ++ tailWord_3278574).sum := by decide
  have hdescent : baseEnd_3278574 < baseStart_3278574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278583 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 3]
def baseStart_3278583 : Nat := 118140960795 + 3278583 * 2 ^ 59
def prefixEnd_3278583 : Nat := 4983230072969 + 3 ^ 40 * 3278583 * 2
def baseEnd_3278583 : Nat := 1683488944659851262634577

theorem tailTrace_3278583 : CollatzResearch.WordTrace tailWord_3278583 prefixEnd_3278583 1683488944659851262634577 := by
  unfold tailWord_3278583
  simp only [CollatzResearch.WordTrace]
  refine ⟨119579745881261203242616403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79719830587507468828410935 119579745881261203242616403)
  ·
    refine ⟨179369618821891804863924605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119579745881261203242616403 179369618821891804863924605)
    ·
      refine ⟨67263607058209426823971727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179369618821891804863924605 67263607058209426823971727)
      ·
        refine ⟨100895410587314140235957591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67263607058209426823971727 100895410587314140235957591)
        ·
          refine ⟨151343115880971210353936387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100895410587314140235957591 151343115880971210353936387)
          ·
            refine ⟨227014673821456815530904581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151343115880971210353936387 227014673821456815530904581)
            ·
              refine ⟨42565251341523152912044609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227014673821456815530904581 42565251341523152912044609)
              ·
                refine ⟨31923938506142364684033457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42565251341523152912044609 31923938506142364684033457)
                ·
                  refine ⟨23942953879606773513025093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31923938506142364684033457 23942953879606773513025093)
                  ·
                    refine ⟨4489303852426270033692205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23942953879606773513025093 4489303852426270033692205)
                    ·
                      refine ⟨1683488944659851262634577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4489303852426270033692205 1683488944659851262634577)
                      ·
                        rfl

theorem cell23_3278583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_3278583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278583 prefixEnd_3278583 := by exact prefixLift 3278583
  have htrace : WordTrace (prefixWord ++ tailWord_3278583) baseStart_3278583 baseEnd_3278583 := by
    simpa [prefixWord, tailWord_3278583, baseEnd_3278583] using wordTrace_append hprefix tailTrace_3278583
  have hstable : (prefixWord ++ tailWord_3278583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278583).length < 2 ^ (prefixWord ++ tailWord_3278583).sum := by decide
  have hdescent : baseEnd_3278583 < baseStart_3278583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278593 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_3278593 : Nat := 118140960795 + 3278593 * 2 ^ 59
def prefixEnd_3278593 : Nat := 4983230072969 + 3 ^ 40 * 3278593 * 2
def baseEnd_3278593 : Nat := 1683494079466396223509531

theorem tailTrace_3278593 : CollatzResearch.WordTrace tailWord_3278593 prefixEnd_3278593 1683494079466396223509531 := by
  unfold tailWord_3278593
  simp only [CollatzResearch.WordTrace]
  refine ⟨119580110611224974950480433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79720073740816649966986955 119580110611224974950480433)
  ·
    refine ⟨89685082958418731212860325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119580110611224974950480433 89685082958418731212860325)
    ·
      refine ⟨16815953054703512102411311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89685082958418731212860325 16815953054703512102411311)
      ·
        refine ⟨25223929582055268153616967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16815953054703512102411311 25223929582055268153616967)
        ·
          refine ⟨37835894373082902230425451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25223929582055268153616967 37835894373082902230425451)
          ·
            refine ⟨56753841559624353345638177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37835894373082902230425451 56753841559624353345638177)
            ·
              refine ⟨42565381169718265009228633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56753841559624353345638177 42565381169718265009228633)
              ·
                refine ⟨31924035877288698756921475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42565381169718265009228633 31924035877288698756921475)
                ·
                  refine ⟨47886053815933048135382213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31924035877288698756921475 47886053815933048135382213)
                  ·
                    refine ⟨8978635090487446525384165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47886053815933048135382213 8978635090487446525384165)
                    ·
                      refine ⟨1683494079466396223509531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8978635090487446525384165 1683494079466396223509531)
                      ·
                        rfl

theorem cell23_3278593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_3278593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278593 prefixEnd_3278593 := by exact prefixLift 3278593
  have htrace : WordTrace (prefixWord ++ tailWord_3278593) baseStart_3278593 baseEnd_3278593 := by
    simpa [prefixWord, tailWord_3278593, baseEnd_3278593] using wordTrace_append hprefix tailTrace_3278593
  have hstable : (prefixWord ++ tailWord_3278593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278593).length < 2 ^ (prefixWord ++ tailWord_3278593).sum := by decide
  have hdescent : baseEnd_3278593 < baseStart_3278593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278598 : List Nat := [6, 2, 2, 1, 2, 1, 9]
def baseStart_3278598 : Nat := 118140960795 + 3278598 * 2 ^ 59
def prefixEnd_3278598 : Nat := 4983230072969 + 3 ^ 40 * 3278598 * 2
def baseEnd_3278598 : Nat := 20783909220613193875889

theorem tailTrace_3278598 : CollatzResearch.WordTrace tailWord_3278598 prefixEnd_3278598 20783909220613193875889 := by
  unfold tailWord_3278598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3736884155506464400137889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79720195317471240536274965 3736884155506464400137889)
  ·
    refine ⟨2802663116629848300103417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3736884155506464400137889 2802663116629848300103417)
    ·
      refine ⟨2101997337472386225077563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2802663116629848300103417 2101997337472386225077563)
      ·
        refine ⟨3152996006208579337616345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2101997337472386225077563 3152996006208579337616345)
        ·
          refine ⟨2364747004656434503212259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3152996006208579337616345 2364747004656434503212259)
          ·
            refine ⟨3547120506984651754818389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364747004656434503212259 3547120506984651754818389)
            ·
              refine ⟨20783909220613193875889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3547120506984651754818389 20783909220613193875889)
              ·
                rfl

theorem cell23_3278598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 9].length) (baseStart_3278598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278598 prefixEnd_3278598 := by exact prefixLift 3278598
  have htrace : WordTrace (prefixWord ++ tailWord_3278598) baseStart_3278598 baseEnd_3278598 := by
    simpa [prefixWord, tailWord_3278598, baseEnd_3278598] using wordTrace_append hprefix tailTrace_3278598
  have hstable : (prefixWord ++ tailWord_3278598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278598).length < 2 ^ (prefixWord ++ tailWord_3278598).sum := by decide
  have hdescent : baseEnd_3278598 < baseStart_3278598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278650 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 2, 5]
def baseStart_3278650 : Nat := 118140960795 + 3278650 * 2 ^ 59
def prefixEnd_3278650 : Nat := 4983230072969 + 3 ^ 40 * 3278650 * 2
def baseEnd_3278650 : Nat := 561174449287900833498923

theorem tailTrace_3278650 : CollatzResearch.WordTrace tailWord_3278650 prefixEnd_3278650 561174449287900833498923 := by
  unfold tailWord_3278650
  simp only [CollatzResearch.WordTrace]
  refine ⟨29895547393004618421326351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79721459714678982456870269 29895547393004618421326351)
  ·
    refine ⟨44843321089506927631989527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29895547393004618421326351 44843321089506927631989527)
    ·
      refine ⟨67264981634260391447984291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44843321089506927631989527 67264981634260391447984291)
      ·
        refine ⟨100897472451390587171976437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67264981634260391447984291 100897472451390587171976437)
        ·
          refine ⟨9459138042317867547372791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100897472451390587171976437 9459138042317867547372791)
          ·
            refine ⟨14188707063476801321059187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9459138042317867547372791 14188707063476801321059187)
            ·
              refine ⟨21283060595215201981588781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14188707063476801321059187 21283060595215201981588781)
              ·
                refine ⟨7981147723205700743095793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21283060595215201981588781 7981147723205700743095793)
                ·
                  refine ⟨5985860792404275557321845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7981147723205700743095793 5985860792404275557321845)
                  ·
                    refine ⟨561174449287900833498923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5985860792404275557321845 561174449287900833498923)
                    ·
                      rfl

theorem cell23_3278650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_3278650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278650 prefixEnd_3278650 := by exact prefixLift 3278650
  have htrace : WordTrace (prefixWord ++ tailWord_3278650) baseStart_3278650 baseEnd_3278650 := by
    simpa [prefixWord, tailWord_3278650, baseEnd_3278650] using wordTrace_append hprefix tailTrace_3278650
  have hstable : (prefixWord ++ tailWord_3278650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278650).length < 2 ^ (prefixWord ++ tailWord_3278650).sum := by decide
  have hdescent : baseEnd_3278650 < baseStart_3278650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278687 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 2, 4, 2]
def baseStart_3278687 : Nat := 118140960795 + 3278687 * 2 ^ 59
def prefixEnd_3278687 : Nat := 4983230072969 + 3 ^ 40 * 3278687 * 2
def baseEnd_3278687 : Nat := 1683542346647918855734099

theorem tailTrace_3278687 : CollatzResearch.WordTrace tailWord_3278687 prefixEnd_3278687 1683542346647918855734099 := by
  unfold tailWord_3278687
  simp only [CollatzResearch.WordTrace]
  refine ⟨119583539072884429004402315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79722359381922952669601543 119583539072884429004402315)
  ·
    refine ⟨179375308609326643506603473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119583539072884429004402315 179375308609326643506603473)
    ·
      refine ⟨134531481456994982629952605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179375308609326643506603473 134531481456994982629952605)
      ·
        refine ⟨50449305546373118486232227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134531481456994982629952605 50449305546373118486232227)
        ·
          refine ⟨75673958319559677729348341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50449305546373118486232227 75673958319559677729348341)
          ·
            refine ⟨7094433592458719787126407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75673958319559677729348341 7094433592458719787126407)
            ·
              refine ⟨10641650388688079680689611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7094433592458719787126407 10641650388688079680689611)
              ·
                refine ⟨15962475583032119521034417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10641650388688079680689611 15962475583032119521034417)
                ·
                  refine ⟨11971856687274089640775813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15962475583032119521034417 11971856687274089640775813)
                  ·
                    refine ⟨2244723128863891807645465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11971856687274089640775813 2244723128863891807645465)
                    ·
                      refine ⟨1683542346647918855734099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2244723128863891807645465 1683542346647918855734099)
                      ·
                        rfl

theorem cell23_3278687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_3278687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278687 prefixEnd_3278687 := by exact prefixLift 3278687
  have htrace : WordTrace (prefixWord ++ tailWord_3278687) baseStart_3278687 baseEnd_3278687 := by
    simpa [prefixWord, tailWord_3278687, baseEnd_3278687] using wordTrace_append hprefix tailTrace_3278687
  have hstable : (prefixWord ++ tailWord_3278687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278687).length < 2 ^ (prefixWord ++ tailWord_3278687).sum := by decide
  have hdescent : baseEnd_3278687 < baseStart_3278687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278693 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 10]
def baseStart_3278693 : Nat := 118140960795 + 3278693 * 2 ^ 59
def prefixEnd_3278693 : Nat := 4983230072969 + 3 ^ 40 * 3278693 * 2
def baseEnd_3278693 : Nat := 187060603059093981362119

theorem tailTrace_3278693 : CollatzResearch.WordTrace tailWord_3278693 prefixEnd_3278693 187060603059093981362119 := by
  unfold tailWord_3278693
  simp only [CollatzResearch.WordTrace]
  refine ⟨119583757910862692029120733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79722505273908461352747155 119583757910862692029120733)
  ·
    refine ⟨44843909216573509510920275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119583757910862692029120733 44843909216573509510920275)
    ·
      refine ⟨67265863824860264266380413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44843909216573509510920275 67265863824860264266380413)
      ·
        refine ⟨25224698934322599099892655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67265863824860264266380413 25224698934322599099892655)
        ·
          refine ⟨37837048401483898649838983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25224698934322599099892655 37837048401483898649838983)
          ·
            refine ⟨56755572602225847974758475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37837048401483898649838983 56755572602225847974758475)
            ·
              refine ⟨85133358903338771962137713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56755572602225847974758475 85133358903338771962137713)
              ·
                refine ⟨63850019177504078971603285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85133358903338771962137713 63850019177504078971603285)
                ·
                  refine ⟨187060603059093981362119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 63850019177504078971603285 187060603059093981362119)
                  ·
                    rfl

theorem cell23_3278693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_3278693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278693 prefixEnd_3278693 := by exact prefixLift 3278693
  have htrace : WordTrace (prefixWord ++ tailWord_3278693) baseStart_3278693 baseEnd_3278693 := by
    simpa [prefixWord, tailWord_3278693, baseEnd_3278693] using wordTrace_append hprefix tailTrace_3278693
  have hstable : (prefixWord ++ tailWord_3278693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278693).length < 2 ^ (prefixWord ++ tailWord_3278693).sum := by decide
  have hdescent : baseEnd_3278693 < baseStart_3278693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278737 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 3, 1, 3]
def baseStart_3278737 : Nat := 118140960795 + 3278737 * 2 ^ 59
def prefixEnd_3278737 : Nat := 4983230072969 + 3 ^ 40 * 3278737 * 2
def baseEnd_3278737 : Nat := 1683568020680643660108869

theorem tailTrace_3278737 : CollatzResearch.WordTrace tailWord_3278737 prefixEnd_3278737 1683568020680643660108869 := by
  unfold tailWord_3278737
  simp only [CollatzResearch.WordTrace]
  refine ⟨119585362722703287543722465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79723575148468858362481643 119585362722703287543722465)
  ·
    refine ⟨89689022042027465657791849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119585362722703287543722465 89689022042027465657791849)
    ·
      refine ⟨67266766531520599243343887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89689022042027465657791849 67266766531520599243343887)
      ·
        refine ⟨100900149797280898865015831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67266766531520599243343887 100900149797280898865015831)
        ·
          refine ⟨151350224695921348297523747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100900149797280898865015831 151350224695921348297523747)
          ·
            refine ⟨227025337043882022446285621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151350224695921348297523747 227025337043882022446285621)
            ·
              refine ⟨21283625347863939604339277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227025337043882022446285621 21283625347863939604339277)
              ·
                refine ⟨7981359505448977351627229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21283625347863939604339277 7981359505448977351627229)
                ·
                  refine ⟨2993009814543366506860211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7981359505448977351627229 2993009814543366506860211)
                  ·
                    refine ⟨4489514721815049760290317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2993009814543366506860211 4489514721815049760290317)
                    ·
                      refine ⟨1683568020680643660108869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4489514721815049760290317 1683568020680643660108869)
                      ·
                        rfl

theorem cell23_3278737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_3278737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278737 prefixEnd_3278737 := by exact prefixLift 3278737
  have htrace : WordTrace (prefixWord ++ tailWord_3278737) baseStart_3278737 baseEnd_3278737 := by
    simpa [prefixWord, tailWord_3278737, baseEnd_3278737] using wordTrace_append hprefix tailTrace_3278737
  have hstable : (prefixWord ++ tailWord_3278737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278737).length < 2 ^ (prefixWord ++ tailWord_3278737).sum := by decide
  have hdescent : baseEnd_3278737 < baseStart_3278737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278770 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_3278770 : Nat := 118140960795 + 3278770 * 2 ^ 59
def prefixEnd_3278770 : Nat := 4983230072969 + 3 ^ 40 * 3278770 * 2
def baseEnd_3278770 : Nat := 561194988514080676998739

theorem tailTrace_3278770 : CollatzResearch.WordTrace tailWord_3278770 prefixEnd_3278770 561194988514080676998739 := by
  unfold tailWord_3278770
  simp only [CollatzResearch.WordTrace]
  refine ⟨29896641582895933544918441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79724377554389156119782509 29896641582895933544918441)
  ·
    refine ⟨22422481187171950158688831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29896641582895933544918441 22422481187171950158688831)
    ·
      refine ⟨33633721780757925238033247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22422481187171950158688831 33633721780757925238033247)
      ·
        refine ⟨50450582671136887857049871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33633721780757925238033247 50450582671136887857049871)
        ·
          refine ⟨75675874006705331785574807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50450582671136887857049871 75675874006705331785574807)
          ·
            refine ⟨113513811010057997678362211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75675874006705331785574807 113513811010057997678362211)
            ·
              refine ⟨170270716515086996517543317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113513811010057997678362211 170270716515086996517543317)
              ·
                refine ⟨7981439836644702961759843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170270716515086996517543317 7981439836644702961759843)
                ·
                  refine ⟨11972159754967054442639765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7981439836644702961759843 11972159754967054442639765)
                  ·
                    refine ⟨561194988514080676998739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11972159754967054442639765 561194988514080676998739)
                    ·
                      rfl

theorem cell23_3278770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_3278770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278770 prefixEnd_3278770 := by exact prefixLift 3278770
  have htrace : WordTrace (prefixWord ++ tailWord_3278770) baseStart_3278770 baseEnd_3278770 := by
    simpa [prefixWord, tailWord_3278770, baseEnd_3278770] using wordTrace_append hprefix tailTrace_3278770
  have hstable : (prefixWord ++ tailWord_3278770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278770).length < 2 ^ (prefixWord ++ tailWord_3278770).sum := by decide
  have hdescent : baseEnd_3278770 < baseStart_3278770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278777 : List Nat := [1, 2, 1, 4, 2, 1, 1, 5, 1, 1, 4]
def baseStart_3278777 : Nat := 118140960795 + 3278777 * 2 ^ 59
def prefixEnd_3278777 : Nat := 4983230072969 + 3 ^ 40 * 3278777 * 2
def baseEnd_3278777 : Nat := 1683588559906823503608685

theorem tailTrace_3278777 : CollatzResearch.WordTrace tailWord_3278777 prefixEnd_3278777 1683588559906823503608685 := by
  unfold tailWord_3278777
  simp only [CollatzResearch.WordTrace]
  refine ⟨119586821642558374375178585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79724547761705582916785723 119586821642558374375178585)
  ·
    refine ⟨89690116231918780781383939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119586821642558374375178585 89690116231918780781383939)
    ·
      refine ⟨134535174347878171172075909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89690116231918780781383939 134535174347878171172075909)
      ·
        refine ⟨25225345190227157094764233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134535174347878171172075909 25225345190227157094764233)
        ·
          refine ⟨18919008892670367821073175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25225345190227157094764233 18919008892670367821073175)
          ·
            refine ⟨28378513339005551731609763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18919008892670367821073175 28378513339005551731609763)
            ·
              refine ⟨42567770008508327597414645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28378513339005551731609763 42567770008508327597414645)
              ·
                refine ⟨3990728438297655712257623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42567770008508327597414645 3990728438297655712257623)
                ·
                  refine ⟨5986092657446483568386435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3990728438297655712257623 5986092657446483568386435)
                  ·
                    refine ⟨8979138986169725352579653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5986092657446483568386435 8979138986169725352579653)
                    ·
                      refine ⟨1683588559906823503608685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8979138986169725352579653 1683588559906823503608685)
                      ·
                        rfl

theorem cell23_3278777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_3278777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278777 prefixEnd_3278777 := by exact prefixLift 3278777
  have htrace : WordTrace (prefixWord ++ tailWord_3278777) baseStart_3278777 baseEnd_3278777 := by
    simpa [prefixWord, tailWord_3278777, baseEnd_3278777] using wordTrace_append hprefix tailTrace_3278777
  have hstable : (prefixWord ++ tailWord_3278777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278777).length < 2 ^ (prefixWord ++ tailWord_3278777).sum := by decide
  have hdescent : baseEnd_3278777 < baseStart_3278777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278804 : List Nat := [2, 4, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_3278804 : Nat := 118140960795 + 3278804 * 2 ^ 59
def prefixEnd_3278804 : Nat := 4983230072969 + 3 ^ 40 * 3278804 * 2
def baseEnd_3278804 : Nat := 561200807961498299323687

theorem tailTrace_3278804 : CollatzResearch.WordTrace tailWord_3278804 prefixEnd_3278804 561200807961498299323687 := by
  unfold tailWord_3278804
  simp only [CollatzResearch.WordTrace]
  refine ⟨59793903206730278993205733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79725204275640371990940977 59793903206730278993205733)
  ·
    refine ⟨11211356851261927311226075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59793903206730278993205733 11211356851261927311226075)
    ·
      refine ⟨16817035276892890966839113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11211356851261927311226075 16817035276892890966839113)
      ·
        refine ⟨12612776457669668225129335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16817035276892890966839113 12612776457669668225129335)
        ·
          refine ⟨18919164686504502337694003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12612776457669668225129335 18919164686504502337694003)
          ·
            refine ⟨28378747029756753506541005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18919164686504502337694003 28378747029756753506541005)
            ·
              refine ⟨10642030136158782564952877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28378747029756753506541005 10642030136158782564952877)
              ·
                refine ⟨3990761301059543461857329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10642030136158782564952877 3990761301059543461857329)
                ·
                  refine ⟨2993070975794657596392997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3990761301059543461857329 2993070975794657596392997)
                  ·
                    refine ⟨561200807961498299323687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2993070975794657596392997 561200807961498299323687)
                    ·
                      rfl

theorem cell23_3278804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_3278804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278804 prefixEnd_3278804 := by exact prefixLift 3278804
  have htrace : WordTrace (prefixWord ++ tailWord_3278804) baseStart_3278804 baseEnd_3278804 := by
    simpa [prefixWord, tailWord_3278804, baseEnd_3278804] using wordTrace_append hprefix tailTrace_3278804
  have hstable : (prefixWord ++ tailWord_3278804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278804).length < 2 ^ (prefixWord ++ tailWord_3278804).sum := by decide
  have hdescent : baseEnd_3278804 < baseStart_3278804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278827 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 6, 1, 3]
def baseStart_3278827 : Nat := 118140960795 + 3278827 * 2 ^ 59
def prefixEnd_3278827 : Nat := 4983230072969 + 3 ^ 40 * 3278827 * 2
def baseEnd_3278827 : Nat := 1683614233939548307983455

theorem tailTrace_3278827 : CollatzResearch.WordTrace tailWord_3278827 prefixEnd_3278827 1683614233939548307983455 := by
  unfold tailWord_3278827
  simp only [CollatzResearch.WordTrace]
  refine ⟨119588645292377232914498735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79725763528251488609665823 119588645292377232914498735)
  ·
    refine ⟨179382967938565849371748103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119588645292377232914498735 179382967938565849371748103)
    ·
      refine ⟨269074451907848774057622155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179382967938565849371748103 269074451907848774057622155)
      ·
        refine ⟨403611677861773161086433233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269074451907848774057622155 403611677861773161086433233)
        ·
          refine ⟨302708758396329870814824925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403611677861773161086433233 302708758396329870814824925)
          ·
            refine ⟨113515784398623701555559347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302708758396329870814824925 113515784398623701555559347)
            ·
              refine ⟨170273676597935552333339021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113515784398623701555559347 170273676597935552333339021)
              ·
                refine ⟨63852628724225832125002133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170273676597935552333339021 63852628724225832125002133)
                ·
                  refine ⟨2993091971448085880859475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63852628724225832125002133 2993091971448085880859475)
                  ·
                    refine ⟨4489637957172128821289213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2993091971448085880859475 4489637957172128821289213)
                    ·
                      refine ⟨1683614233939548307983455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4489637957172128821289213 1683614233939548307983455)
                      ·
                        rfl

theorem cell23_3278827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 1, 3].length) (baseStart_3278827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278827 prefixEnd_3278827 := by exact prefixLift 3278827
  have htrace : WordTrace (prefixWord ++ tailWord_3278827) baseStart_3278827 baseEnd_3278827 := by
    simpa [prefixWord, tailWord_3278827, baseEnd_3278827] using wordTrace_append hprefix tailTrace_3278827
  have hstable : (prefixWord ++ tailWord_3278827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278827).length < 2 ^ (prefixWord ++ tailWord_3278827).sum := by decide
  have hdescent : baseEnd_3278827 < baseStart_3278827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278840 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_3278840 : Nat := 118140960795 + 3278840 * 2 ^ 59
def prefixEnd_3278840 : Nat := 4983230072969 + 3 ^ 40 * 3278840 * 2
def baseEnd_3278840 : Nat := 1683620909188056757120895

theorem tailTrace_3278840 : CollatzResearch.WordTrace tailWord_3278840 prefixEnd_3278840 1683620909188056757120895 := by
  unfold tailWord_3278840
  simp only [CollatzResearch.WordTrace]
  refine ⟨59794559720665068067360987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79726079627553424089814649 59794559720665068067360987)
  ·
    refine ⟨89691839580997602101041481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59794559720665068067360987 89691839580997602101041481)
    ·
      refine ⟨67268879685748201575781111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89691839580997602101041481 67268879685748201575781111)
      ·
        refine ⟨100903319528622302363671667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67268879685748201575781111 100903319528622302363671667)
        ·
          refine ⟨151354979292933453545507501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100903319528622302363671667 151354979292933453545507501)
          ·
            refine ⟨56758117234850045079565313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151354979292933453545507501 56758117234850045079565313)
            ·
              refine ⟨42568587926137533809673985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56758117234850045079565313 42568587926137533809673985)
              ·
                refine ⟨31926440944603150357255489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42568587926137533809673985 31926440944603150357255489)
                ·
                  refine ⟨23944830708452362767941617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31926440944603150357255489 23944830708452362767941617)
                  ·
                    refine ⟨17958623031339272075956213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23944830708452362767941617 17958623031339272075956213)
                    ·
                      refine ⟨1683620909188056757120895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17958623031339272075956213 1683620909188056757120895)
                      ·
                        rfl

theorem cell23_3278840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_3278840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278840 prefixEnd_3278840 := by exact prefixLift 3278840
  have htrace : WordTrace (prefixWord ++ tailWord_3278840) baseStart_3278840 baseEnd_3278840 := by
    simpa [prefixWord, tailWord_3278840, baseEnd_3278840] using wordTrace_append hprefix tailTrace_3278840
  have hstable : (prefixWord ++ tailWord_3278840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278840).length < 2 ^ (prefixWord ++ tailWord_3278840).sum := by decide
  have hdescent : baseEnd_3278840 < baseStart_3278840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278897 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_3278897 : Nat := 118140960795 + 3278897 * 2 ^ 59
def prefixEnd_3278897 : Nat := 4983230072969 + 3 ^ 40 * 3278897 * 2
def baseEnd_3278897 : Nat := 1683650177585363034108133

theorem tailTrace_3278897 : CollatzResearch.WordTrace tailWord_3278897 prefixEnd_3278897 1683650177585363034108133 := by
  unfold tailWord_3278897
  simp only [CollatzResearch.WordTrace]
  refine ⟨119591198402123634869546945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79727465601415756579697963 119591198402123634869546945)
  ·
    refine ⟨89693398801592726152160209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119591198402123634869546945 89693398801592726152160209)
    ·
      refine ⟨67270049101194544614120157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89693398801592726152160209 67270049101194544614120157)
      ·
        refine ⟨25226268412947954230295059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67270049101194544614120157 25226268412947954230295059)
        ·
          refine ⟨37839402619421931345442589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25226268412947954230295059 37839402619421931345442589)
          ·
            refine ⟨14189775982283224254540971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37839402619421931345442589 14189775982283224254540971)
            ·
              refine ⟨21284663973424836381811457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14189775982283224254540971 21284663973424836381811457)
              ·
                refine ⟨15963497980068627286358593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21284663973424836381811457 15963497980068627286358593)
                ·
                  refine ⟨11972623485051470464768945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15963497980068627286358593 11972623485051470464768945)
                  ·
                    refine ⟨8979467613788602848576709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11972623485051470464768945 8979467613788602848576709)
                    ·
                      refine ⟨1683650177585363034108133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8979467613788602848576709 1683650177585363034108133)
                      ·
                        rfl

theorem cell23_3278897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_3278897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278897 prefixEnd_3278897 := by exact prefixLift 3278897
  have htrace : WordTrace (prefixWord ++ tailWord_3278897) baseStart_3278897 baseEnd_3278897 := by
    simpa [prefixWord, tailWord_3278897, baseEnd_3278897] using wordTrace_append hprefix tailTrace_3278897
  have hstable : (prefixWord ++ tailWord_3278897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278897).length < 2 ^ (prefixWord ++ tailWord_3278897).sum := by decide
  have hdescent : baseEnd_3278897 < baseStart_3278897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3278937 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 2, 5]
def baseStart_3278937 : Nat := 118140960795 + 3278937 * 2 ^ 59
def prefixEnd_3278937 : Nat := 4983230072969 + 3 ^ 40 * 3278937 * 2
def baseEnd_3278937 : Nat := 561223572270514292535983

theorem tailTrace_3278937 : CollatzResearch.WordTrace tailWord_3278937 prefixEnd_3278937 561223572270514292535983 := by
  unfold tailWord_3278937
  simp only [CollatzResearch.WordTrace]
  refine ⟨119592657321978721701003065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79728438214652481134002043 119592657321978721701003065)
  ·
    refine ⟨89694492991484041275752299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119592657321978721701003065 89694492991484041275752299)
    ·
      refine ⟨134541739487226061913628449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89694492991484041275752299 134541739487226061913628449)
      ·
        refine ⟨100906304615419546435221337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134541739487226061913628449 100906304615419546435221337)
        ·
          refine ⟨75679728461564659826416003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100906304615419546435221337 75679728461564659826416003)
          ·
            refine ⟨113519592692346989739624005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75679728461564659826416003 113519592692346989739624005)
            ·
              refine ⟨21284923629815060576179501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113519592692346989739624005 21284923629815060576179501)
              ·
                refine ⟨7981846361180647716067313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21284923629815060576179501 7981846361180647716067313)
                ·
                  refine ⟨5986384770885485787050485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7981846361180647716067313 5986384770885485787050485)
                  ·
                    refine ⟨561223572270514292535983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5986384770885485787050485 561223572270514292535983)
                    ·
                      rfl

theorem cell23_3278937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 5].length) (baseStart_3278937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3278937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3278937 prefixEnd_3278937 := by exact prefixLift 3278937
  have htrace : WordTrace (prefixWord ++ tailWord_3278937) baseStart_3278937 baseEnd_3278937 := by
    simpa [prefixWord, tailWord_3278937, baseEnd_3278937] using wordTrace_append hprefix tailTrace_3278937
  have hstable : (prefixWord ++ tailWord_3278937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3278937).length < 2 ^ (prefixWord ++ tailWord_3278937).sum := by decide
  have hdescent : baseEnd_3278937 < baseStart_3278937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3278937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279037 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_3279037 : Nat := 118140960795 + 3279037 * 2 ^ 59
def prefixEnd_3279037 : Nat := 4983230072969 + 3 ^ 40 * 3279037 * 2
def baseEnd_3279037 : Nat := 1683722064876992486357489

theorem tailTrace_3279037 : CollatzResearch.WordTrace tailWord_3279037 prefixEnd_3279037 1683722064876992486357489 := by
  unfold tailWord_3279037
  simp only [CollatzResearch.WordTrace]
  refine ⟨119596304621616438779643365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79730869747744292519762243 119596304621616438779643365)
  ·
    refine ⟨22424307116553082271183131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119596304621616438779643365 22424307116553082271183131)
    ·
      refine ⟨33636460674829623406774697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22424307116553082271183131 33636460674829623406774697)
      ·
        refine ⟨25227345506122217555081023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33636460674829623406774697 25227345506122217555081023)
        ·
          refine ⟨37841018259183326332621535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25227345506122217555081023 37841018259183326332621535)
          ·
            refine ⟨56761527388774989498932303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37841018259183326332621535 56761527388774989498932303)
            ·
              refine ⟨85142291083162484248398455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56761527388774989498932303 85142291083162484248398455)
              ·
                refine ⟨127713436624743726372597683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85142291083162484248398455 127713436624743726372597683)
                ·
                  refine ⟨191570154937115589558896525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127713436624743726372597683 191570154937115589558896525)
                  ·
                    refine ⟨71838808101418346084586197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 191570154937115589558896525 71838808101418346084586197)
                    ·
                      refine ⟨1683722064876992486357489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71838808101418346084586197 1683722064876992486357489)
                      ·
                        rfl

theorem cell23_3279037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_3279037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279037 prefixEnd_3279037 := by exact prefixLift 3279037
  have htrace : WordTrace (prefixWord ++ tailWord_3279037) baseStart_3279037 baseEnd_3279037 := by
    simpa [prefixWord, tailWord_3279037, baseEnd_3279037] using wordTrace_append hprefix tailTrace_3279037
  have hstable : (prefixWord ++ tailWord_3279037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279037).length < 2 ^ (prefixWord ++ tailWord_3279037).sum := by decide
  have hdescent : baseEnd_3279037 < baseStart_3279037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279075 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3279075 : Nat := 118140960795 + 3279075 * 2 ^ 59
def prefixEnd_3279075 : Nat := 4983230072969 + 3 ^ 40 * 3279075 * 2
def baseEnd_3279075 : Nat := 1683741577141863337682315

theorem tailTrace_3279075 : CollatzResearch.WordTrace tailWord_3279075 prefixEnd_3279075 1683741577141863337682315 := by
  unfold tailWord_3279075
  simp only [CollatzResearch.WordTrace]
  refine ⟨119597690595478771269526679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79731793730319180846351119 119597690595478771269526679)
  ·
    refine ⟨179396535893218156904290019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119597690595478771269526679 179396535893218156904290019)
    ·
      refine ⟨269094803839827235356435029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179396535893218156904290019 269094803839827235356435029)
      ·
        refine ⟨3153454732497975414333223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 269094803839827235356435029 3153454732497975414333223)
        ·
          refine ⟨4730182098746963121499835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3153454732497975414333223 4730182098746963121499835)
          ·
            refine ⟨7095273148120444682249753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4730182098746963121499835 7095273148120444682249753)
            ·
              refine ⟨5321454861090333511687315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7095273148120444682249753 5321454861090333511687315)
              ·
                refine ⟨7982182291635500267530973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5321454861090333511687315 7982182291635500267530973)
                ·
                  refine ⟨2993318359363312600324115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7982182291635500267530973 2993318359363312600324115)
                  ·
                    refine ⟨4489977539044968900486173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2993318359363312600324115 4489977539044968900486173)
                    ·
                      refine ⟨1683741577141863337682315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4489977539044968900486173 1683741577141863337682315)
                      ·
                        rfl

theorem cell23_3279075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3279075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279075 prefixEnd_3279075 := by exact prefixLift 3279075
  have htrace : WordTrace (prefixWord ++ tailWord_3279075) baseStart_3279075 baseEnd_3279075 := by
    simpa [prefixWord, tailWord_3279075, baseEnd_3279075] using wordTrace_append hprefix tailTrace_3279075
  have hstable : (prefixWord ++ tailWord_3279075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279075).length < 2 ^ (prefixWord ++ tailWord_3279075).sum := by decide
  have hdescent : baseEnd_3279075 < baseStart_3279075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279081 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 7, 2, 2]
def baseStart_3279081 : Nat := 118140960795 + 3279081 * 2 ^ 59
def prefixEnd_3279081 : Nat := 4983230072969 + 3 ^ 40 * 3279081 * 2
def baseEnd_3279081 : Nat := 1683744658025790314207287

theorem tailTrace_3279081 : CollatzResearch.WordTrace tailWord_3279081 prefixEnd_3279081 1683744658025790314207287 := by
  unfold tailWord_3279081
  simp only [CollatzResearch.WordTrace]
  refine ⟨119597909433457034294245097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79731939622304689529496731 119597909433457034294245097)
  ·
    refine ⟨89698432075092775720683823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119597909433457034294245097 89698432075092775720683823)
    ·
      refine ⟨134547648112639163581025735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89698432075092775720683823 134547648112639163581025735)
      ·
        refine ⟨201821472168958745371538603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134547648112639163581025735 201821472168958745371538603)
        ·
          refine ⟨302732208253438118057307905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201821472168958745371538603 302732208253438118057307905)
          ·
            refine ⟨227049156190078588542980929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302732208253438118057307905 227049156190078588542980929)
            ·
              refine ⟨170286867142558941407235697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227049156190078588542980929 170286867142558941407235697)
              ·
                refine ⟨127715150356919206055426773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170286867142558941407235697 127715150356919206055426773)
                ·
                  refine ⟨2993323836490293891924065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 127715150356919206055426773 2993323836490293891924065)
                  ·
                    refine ⟨2244992877367720418943049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2993323836490293891924065 2244992877367720418943049)
                    ·
                      refine ⟨1683744658025790314207287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2244992877367720418943049 1683744658025790314207287)
                      ·
                        rfl

theorem cell23_3279081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 2, 2].length) (baseStart_3279081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279081 prefixEnd_3279081 := by exact prefixLift 3279081
  have htrace : WordTrace (prefixWord ++ tailWord_3279081) baseStart_3279081 baseEnd_3279081 := by
    simpa [prefixWord, tailWord_3279081, baseEnd_3279081] using wordTrace_append hprefix tailTrace_3279081
  have hstable : (prefixWord ++ tailWord_3279081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279081).length < 2 ^ (prefixWord ++ tailWord_3279081).sum := by decide
  have hdescent : baseEnd_3279081 < baseStart_3279081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279084 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 5]
def baseStart_3279084 : Nat := 118140960795 + 3279084 * 2 ^ 59
def prefixEnd_3279084 : Nat := 4983230072969 + 3 ^ 40 * 3279084 * 2
def baseEnd_3279084 : Nat := 1683746198467753802469773

theorem tailTrace_3279084 : CollatzResearch.WordTrace tailWord_3279084 prefixEnd_3279084 1683746198467753802469773 := by
  unfold tailWord_3279084
  simp only [CollatzResearch.WordTrace]
  refine ⟨59799009426223082903302153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79732012568297443871069537 59799009426223082903302153)
  ·
    refine ⟨44849257069667312177476615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59799009426223082903302153 44849257069667312177476615)
    ·
      refine ⟨67273885604500968266214923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44849257069667312177476615 67273885604500968266214923)
      ·
        refine ⟨100910828406751452399322385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67273885604500968266214923 100910828406751452399322385)
        ·
          refine ⟨75683121305063589299491789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100910828406751452399322385 75683121305063589299491789)
          ·
            refine ⟨28381170489398845987309421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75683121305063589299491789 28381170489398845987309421)
            ·
              refine ⟨10642938933524567245241033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28381170489398845987309421 10642938933524567245241033)
              ·
                refine ⟨7982204200143425433930775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10642938933524567245241033 7982204200143425433930775)
                ·
                  refine ⟨11973306300215138150896163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7982204200143425433930775 11973306300215138150896163)
                  ·
                    refine ⟨17959959450322707226344245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11973306300215138150896163 17959959450322707226344245)
                    ·
                      refine ⟨1683746198467753802469773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17959959450322707226344245 1683746198467753802469773)
                      ·
                        rfl

theorem cell23_3279084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_3279084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279084 prefixEnd_3279084 := by exact prefixLift 3279084
  have htrace : WordTrace (prefixWord ++ tailWord_3279084) baseStart_3279084 baseEnd_3279084 := by
    simpa [prefixWord, tailWord_3279084, baseEnd_3279084] using wordTrace_append hprefix tailTrace_3279084
  have hstable : (prefixWord ++ tailWord_3279084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279084).length < 2 ^ (prefixWord ++ tailWord_3279084).sum := by decide
  have hdescent : baseEnd_3279084 < baseStart_3279084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279098 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2]
def baseStart_3279098 : Nat := 118140960795 + 3279098 * 2 ^ 59
def prefixEnd_3279098 : Nat := 4983230072969 + 3 ^ 40 * 3279098 * 2
def baseEnd_3279098 : Nat := 1683753387196916747694709

theorem tailTrace_3279098 : CollatzResearch.WordTrace tailWord_3279098 prefixEnd_3279098 1683753387196916747694709 := by
  unfold tailWord_3279098
  simp only [CollatzResearch.WordTrace]
  refine ⟨29899632368598861549403487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79732352982930297465075965 29899632368598861549403487)
  ·
    refine ⟨44849448552898292324105231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29899632368598861549403487 44849448552898292324105231)
    ·
      refine ⟨67274172829347438486157847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44849448552898292324105231 67274172829347438486157847)
      ·
        refine ⟨100911259244021157729236771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67274172829347438486157847 100911259244021157729236771)
        ·
          refine ⟨151366888866031736593855157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100911259244021157729236771 151366888866031736593855157)
          ·
            refine ⟨14190645831190475305673921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151366888866031736593855157 14190645831190475305673921)
            ·
              refine ⟨10642984373392856479255441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14190645831190475305673921 10642984373392856479255441)
              ·
                refine ⟨7982238280044642359441581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10642984373392856479255441 7982238280044642359441581)
                ·
                  refine ⟨2993339355016740884790593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7982238280044642359441581 2993339355016740884790593)
                  ·
                    refine ⟨2245004516262555663592945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2993339355016740884790593 2245004516262555663592945)
                    ·
                      refine ⟨1683753387196916747694709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245004516262555663592945 1683753387196916747694709)
                      ·
                        rfl

theorem cell23_3279098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2].length) (baseStart_3279098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279098 prefixEnd_3279098 := by exact prefixLift 3279098
  have htrace : WordTrace (prefixWord ++ tailWord_3279098) baseStart_3279098 baseEnd_3279098 := by
    simpa [prefixWord, tailWord_3279098, baseEnd_3279098] using wordTrace_append hprefix tailTrace_3279098
  have hstable : (prefixWord ++ tailWord_3279098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279098).length < 2 ^ (prefixWord ++ tailWord_3279098).sum := by decide
  have hdescent : baseEnd_3279098 < baseStart_3279098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279104 : List Nat := [2, 1, 1, 2, 1, 1, 8, 7]
def baseStart_3279104 : Nat := 118140960795 + 3279104 * 2 ^ 59
def prefixEnd_3279104 : Nat := 4983230072969 + 3 ^ 40 * 3279104 * 2
def baseEnd_3279104 : Nat := 62361350669660878674803

theorem tailTrace_3279104 : CollatzResearch.WordTrace tailWord_3279104 prefixEnd_3279104 62361350669660878674803 := by
  unfold tailWord_3279104
  simp only [CollatzResearch.WordTrace]
  refine ⟨59799374156186854611166183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79732498874915806148221577 59799374156186854611166183)
  ·
    refine ⟨89699061234280281916749275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59799374156186854611166183 89699061234280281916749275)
    ·
      refine ⟨134548591851420422875123913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89699061234280281916749275 134548591851420422875123913)
      ·
        refine ⟨100911443888565317156342935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134548591851420422875123913 100911443888565317156342935)
        ·
          refine ⟨151367165832847975734514403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100911443888565317156342935 151367165832847975734514403)
          ·
            refine ⟨227050748749271963601771605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151367165832847975734514403 227050748749271963601771605)
            ·
              refine ⟨2660750961905530823458261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 227050748749271963601771605 2660750961905530823458261)
              ·
                refine ⟨62361350669660878674803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2660750961905530823458261 62361350669660878674803)
                ·
                  rfl

theorem cell23_3279104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 7].length) (baseStart_3279104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279104 prefixEnd_3279104 := by exact prefixLift 3279104
  have htrace : WordTrace (prefixWord ++ tailWord_3279104) baseStart_3279104 baseEnd_3279104 := by
    simpa [prefixWord, tailWord_3279104, baseEnd_3279104] using wordTrace_append hprefix tailTrace_3279104
  have hstable : (prefixWord ++ tailWord_3279104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279104).length < 2 ^ (prefixWord ++ tailWord_3279104).sum := by decide
  have hdescent : baseEnd_3279104 < baseStart_3279104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279131 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 4, 1, 3]
def baseStart_3279131 : Nat := 118140960795 + 3279131 * 2 ^ 59
def prefixEnd_3279131 : Nat := 4983230072969 + 3 ^ 40 * 3279131 * 2
def baseEnd_3279131 : Nat := 1683770332058515118582057

theorem tailTrace_3279131 : CollatzResearch.WordTrace tailWord_3279131 prefixEnd_3279131 1683770332058515118582057 := by
  unfold tailWord_3279131
  simp only [CollatzResearch.WordTrace]
  refine ⟨119599733083275892833565247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79733155388850595222376831 119599733083275892833565247)
  ·
    refine ⟨179399599624913839250347871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119599733083275892833565247 179399599624913839250347871)
    ·
      refine ⟨269099399437370758875521807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179399599624913839250347871 269099399437370758875521807)
      ·
        refine ⟨403649099156056138313282711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269099399437370758875521807 403649099156056138313282711)
        ·
          refine ⟨605473648734084207469924067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403649099156056138313282711 605473648734084207469924067)
          ·
            refine ⟨908210473101126311204886101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605473648734084207469924067 908210473101126311204886101)
            ·
              refine ⟨10643091481653823959432259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 908210473101126311204886101 10643091481653823959432259)
              ·
                refine ⟨15964637222480735939148389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10643091481653823959432259 15964637222480735939148389)
                ·
                  refine ⟨2993369479215137988590323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15964637222480735939148389 2993369479215137988590323)
                  ·
                    refine ⟨4490054218822706982885485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2993369479215137988590323 4490054218822706982885485)
                    ·
                      refine ⟨1683770332058515118582057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4490054218822706982885485 1683770332058515118582057)
                      ·
                        rfl

theorem cell23_3279131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 1, 3].length) (baseStart_3279131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279131 prefixEnd_3279131 := by exact prefixLift 3279131
  have htrace : WordTrace (prefixWord ++ tailWord_3279131) baseStart_3279131 baseEnd_3279131 := by
    simpa [prefixWord, tailWord_3279131, baseEnd_3279131] using wordTrace_append hprefix tailTrace_3279131
  have hstable : (prefixWord ++ tailWord_3279131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279131).length < 2 ^ (prefixWord ++ tailWord_3279131).sum := by decide
  have hdescent : baseEnd_3279131 < baseStart_3279131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279171 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 3, 4, 2]
def baseStart_3279171 : Nat := 118140960795 + 3279171 * 2 ^ 59
def prefixEnd_3279171 : Nat := 4983230072969 + 3 ^ 40 * 3279171 * 2
def baseEnd_3279171 : Nat := 1683790871284694962081873

theorem tailTrace_3279171 : CollatzResearch.WordTrace tailWord_3279171 prefixEnd_3279171 1683790871284694962081873 := by
  unfold tailWord_3279171
  simp only [CollatzResearch.WordTrace]
  refine ⟨119601192003130979665021367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79734128002087319776680911 119601192003130979665021367)
  ·
    refine ⟨179401788004696469497532051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119601192003130979665021367 179401788004696469497532051)
    ·
      refine ⟨269102682007044704246298077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179401788004696469497532051 269102682007044704246298077)
      ·
        refine ⟨100913505752641764092361779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269102682007044704246298077 100913505752641764092361779)
        ·
          refine ⟨151370258628962646138542669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100913505752641764092361779 151370258628962646138542669)
          ·
            refine ⟨56763846985860992301953501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151370258628962646138542669 56763846985860992301953501)
            ·
              refine ⟨21286442619697872113232563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56763846985860992301953501 21286442619697872113232563)
              ·
                refine ⟨31929663929546808169848845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21286442619697872113232563 31929663929546808169848845)
                ·
                  refine ⟨11973623973580053063693317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31929663929546808169848845 11973623973580053063693317)
                  ·
                    refine ⟨2245054495046259949442497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11973623973580053063693317 2245054495046259949442497)
                    ·
                      refine ⟨1683790871284694962081873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245054495046259949442497 1683790871284694962081873)
                      ·
                        rfl

theorem cell23_3279171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 4, 2].length) (baseStart_3279171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279171 prefixEnd_3279171 := by exact prefixLift 3279171
  have htrace : WordTrace (prefixWord ++ tailWord_3279171) baseStart_3279171 baseEnd_3279171 := by
    simpa [prefixWord, tailWord_3279171, baseEnd_3279171] using wordTrace_append hprefix tailTrace_3279171
  have hstable : (prefixWord ++ tailWord_3279171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279171).length < 2 ^ (prefixWord ++ tailWord_3279171).sum := by decide
  have hdescent : baseEnd_3279171 < baseStart_3279171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279175 : List Nat := [1, 1, 4, 1, 2, 2, 5, 1, 1, 3, 2]
def baseStart_3279175 : Nat := 118140960795 + 3279175 * 2 ^ 59
def prefixEnd_3279175 : Nat := 4983230072969 + 3 ^ 40 * 3279175 * 2
def baseEnd_3279175 : Nat := 1683792925207312946431855

theorem tailTrace_3279175 : CollatzResearch.WordTrace tailWord_3279175 prefixEnd_3279175 1683792925207312946431855 := by
  unfold tailWord_3279175
  simp only [CollatzResearch.WordTrace]
  refine ⟨119601337895116488348166979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79734225263410992232111319 119601337895116488348166979)
  ·
    refine ⟨179402006842674732522250469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119601337895116488348166979 179402006842674732522250469)
    ·
      refine ⟨33637876283001512347921963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179402006842674732522250469 33637876283001512347921963)
      ·
        refine ⟨50456814424502268521882945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33637876283001512347921963 50456814424502268521882945)
        ·
          refine ⟨37842610818376701391412209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50456814424502268521882945 37842610818376701391412209)
          ·
            refine ⟨28381958113782526043559157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37842610818376701391412209 28381958113782526043559157)
            ·
              refine ⟨2660808573167111816583671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28381958113782526043559157 2660808573167111816583671)
              ·
                refine ⟨3991212859750667724875507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2660808573167111816583671 3991212859750667724875507)
                ·
                  refine ⟨5986819289626001587313261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3991212859750667724875507 5986819289626001587313261)
                  ·
                    refine ⟨2245057233609750595242473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5986819289626001587313261 2245057233609750595242473)
                    ·
                      refine ⟨1683792925207312946431855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245057233609750595242473 1683792925207312946431855)
                      ·
                        rfl

theorem cell23_3279175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_3279175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279175 prefixEnd_3279175 := by exact prefixLift 3279175
  have htrace : WordTrace (prefixWord ++ tailWord_3279175) baseStart_3279175 baseEnd_3279175 := by
    simpa [prefixWord, tailWord_3279175, baseEnd_3279175] using wordTrace_append hprefix tailTrace_3279175
  have hstable : (prefixWord ++ tailWord_3279175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279175).length < 2 ^ (prefixWord ++ tailWord_3279175).sum := by decide
  have hdescent : baseEnd_3279175 < baseStart_3279175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279194 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 7]
def baseStart_3279194 : Nat := 118140960795 + 3279194 * 2 ^ 59
def prefixEnd_3279194 : Nat := 4983230072969 + 3 ^ 40 * 3279194 * 2
def baseEnd_3279194 : Nat := 187089186815527596899363

theorem tailTrace_3279194 : CollatzResearch.WordTrace tailWord_3279194 prefixEnd_3279194 187089186815527596899363 := by
  unfold tailWord_3279194
  simp only [CollatzResearch.WordTrace]
  refine ⟨29900507720511913648277159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79734687254698436395405757 29900507720511913648277159)
  ·
    refine ⟨44850761580767870472415739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29900507720511913648277159 44850761580767870472415739)
    ·
      refine ⟨67276142371151805708623609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44850761580767870472415739 67276142371151805708623609)
      ·
        refine ⟨50457106778363854281467707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67276142371151805708623609 50457106778363854281467707)
        ·
          refine ⟨75685660167545781422201561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50457106778363854281467707 75685660167545781422201561)
          ·
            refine ⟨56764245125659336066651171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75685660167545781422201561 56764245125659336066651171)
            ·
              refine ⟨85146367688489004099976757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56764245125659336066651171 85146367688489004099976757)
              ·
                refine ⟨7982471970795844134372821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85146367688489004099976757 7982471970795844134372821)
                ·
                  refine ⟨187089186815527596899363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7982471970795844134372821 187089186815527596899363)
                  ·
                    rfl

theorem cell23_3279194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_3279194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279194 prefixEnd_3279194 := by exact prefixLift 3279194
  have htrace : WordTrace (prefixWord ++ tailWord_3279194) baseStart_3279194 baseEnd_3279194 := by
    simpa [prefixWord, tailWord_3279194, baseEnd_3279194] using wordTrace_append hprefix tailTrace_3279194
  have hstable : (prefixWord ++ tailWord_3279194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279194).length < 2 ^ (prefixWord ++ tailWord_3279194).sum := by decide
  have hdescent : baseEnd_3279194 < baseStart_3279194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279205 : List Nat := [1, 3, 1, 3, 1, 3, 2, 3, 2, 2, 2]
def baseStart_3279205 : Nat := 118140960795 + 3279205 * 2 ^ 59
def prefixEnd_3279205 : Nat := 4983230072969 + 3 ^ 40 * 3279205 * 2
def baseEnd_3279205 : Nat := 1683808329626947829056717

theorem tailTrace_3279205 : CollatzResearch.WordTrace tailWord_3279205 prefixEnd_3279205 1683808329626947829056717 := by
  unfold tailWord_3279205
  simp only [CollatzResearch.WordTrace]
  refine ⟨119602432085007803471759069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79734954723338535647839379 119602432085007803471759069)
  ·
    refine ⟨44850912031877926301909651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119602432085007803471759069 44850912031877926301909651)
    ·
      refine ⟨67276368047816889452864477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44850912031877926301909651 67276368047816889452864477)
      ·
        refine ⟨25228638017931333544824179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67276368047816889452864477 25228638017931333544824179)
        ·
          refine ⟨37842957026897000317236269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25228638017931333544824179 37842957026897000317236269)
          ·
            refine ⟨14191108885086375118963601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37842957026897000317236269 14191108885086375118963601)
            ·
              refine ⟨10643331663814781339222701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14191108885086375118963601 10643331663814781339222701)
              ·
                refine ⟨3991249373930543002208513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10643331663814781339222701 3991249373930543002208513)
                ·
                  refine ⟨2993437030447907251656385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3991249373930543002208513 2993437030447907251656385)
                  ·
                    refine ⟨2245077772835930438742289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2993437030447907251656385 2245077772835930438742289)
                    ·
                      refine ⟨1683808329626947829056717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245077772835930438742289 1683808329626947829056717)
                      ·
                        rfl

theorem cell23_3279205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_3279205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279205 prefixEnd_3279205 := by exact prefixLift 3279205
  have htrace : WordTrace (prefixWord ++ tailWord_3279205) baseStart_3279205 baseEnd_3279205 := by
    simpa [prefixWord, tailWord_3279205, baseEnd_3279205] using wordTrace_append hprefix tailTrace_3279205
  have hstable : (prefixWord ++ tailWord_3279205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279205).length < 2 ^ (prefixWord ++ tailWord_3279205).sum := by decide
  have hdescent : baseEnd_3279205 < baseStart_3279205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279231 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 4, 5, 2]
def baseStart_3279231 : Nat := 118140960795 + 3279231 * 2 ^ 59
def prefixEnd_3279231 : Nat := 4983230072969 + 3 ^ 40 * 3279231 * 2
def baseEnd_3279231 : Nat := 1683821680123964727331597

theorem tailTrace_3279231 : CollatzResearch.WordTrace tailWord_3279231 prefixEnd_3279231 1683821680123964727331597 := by
  unfold tailWord_3279231
  simp only [CollatzResearch.WordTrace]
  refine ⟨119603380382913609912205547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79735586921942406608137031 119603380382913609912205547)
  ·
    refine ⟨179405070574370414868308321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119603380382913609912205547 179405070574370414868308321)
    ·
      refine ⟨134553802930777811151231241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179405070574370414868308321 134553802930777811151231241)
      ·
        refine ⟨100915352198083358363423431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134553802930777811151231241 100915352198083358363423431)
        ·
          refine ⟨151373028297125037545135147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100915352198083358363423431 151373028297125037545135147)
          ·
            refine ⟨227059542445687556317702721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151373028297125037545135147 227059542445687556317702721)
            ·
              refine ⟨170294656834265667238277041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227059542445687556317702721 170294656834265667238277041)
              ·
                refine ⟨127720992625699250428707781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170294656834265667238277041 127720992625699250428707781)
                ·
                  refine ⟨23947686117318609455382709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127720992625699250428707781 23947686117318609455382709)
                  ·
                    refine ⟨2245095573498619636442129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23947686117318609455382709 2245095573498619636442129)
                    ·
                      refine ⟨1683821680123964727331597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245095573498619636442129 1683821680123964727331597)
                      ·
                        rfl

theorem cell23_3279231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 5, 2].length) (baseStart_3279231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279231 prefixEnd_3279231 := by exact prefixLift 3279231
  have htrace : WordTrace (prefixWord ++ tailWord_3279231) baseStart_3279231 baseEnd_3279231 := by
    simpa [prefixWord, tailWord_3279231, baseEnd_3279231] using wordTrace_append hprefix tailTrace_3279231
  have hstable : (prefixWord ++ tailWord_3279231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279231).length < 2 ^ (prefixWord ++ tailWord_3279231).sum := by decide
  have hdescent : baseEnd_3279231 < baseStart_3279231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279328 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 5, 1, 3]
def baseStart_3279328 : Nat := 118140960795 + 3279328 * 2 ^ 59
def prefixEnd_3279328 : Nat := 4983230072969 + 3 ^ 40 * 3279328 * 2
def baseEnd_3279328 : Nat := 1683871487747450847818651

theorem tailTrace_3279328 : CollatzResearch.WordTrace tailWord_3279328 prefixEnd_3279328 1683871487747450847818651 := by
  unfold tailWord_3279328
  simp only [CollatzResearch.WordTrace]
  refine ⟨59803459131781097739243319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79737945509041463652324425 59803459131781097739243319)
  ·
    refine ⟨89705188697671646608864979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59803459131781097739243319 89705188697671646608864979)
    ·
      refine ⟨134557783046507469913297469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89705188697671646608864979 134557783046507469913297469)
      ·
        refine ⟨50459168642440301217486551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134557783046507469913297469 50459168642440301217486551)
        ·
          refine ⟨75688752963660451826229827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50459168642440301217486551 75688752963660451826229827)
          ·
            refine ⟨113533129445490677739344741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75688752963660451826229827 113533129445490677739344741)
            ·
              refine ⟨21287461771029502076127139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113533129445490677739344741 21287461771029502076127139)
              ·
                refine ⟨31931192656544253114190709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21287461771029502076127139 31931192656544253114190709)
                ·
                  refine ⟨2993549311551023729455379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31931192656544253114190709 2993549311551023729455379)
                  ·
                    refine ⟨4490323967326535594183069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2993549311551023729455379 4490323967326535594183069)
                    ·
                      refine ⟨1683871487747450847818651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4490323967326535594183069 1683871487747450847818651)
                      ·
                        rfl

theorem cell23_3279328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_3279328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279328 prefixEnd_3279328 := by exact prefixLift 3279328
  have htrace : WordTrace (prefixWord ++ tailWord_3279328) baseStart_3279328 baseEnd_3279328 := by
    simpa [prefixWord, tailWord_3279328, baseEnd_3279328] using wordTrace_append hprefix tailTrace_3279328
  have hstable : (prefixWord ++ tailWord_3279328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279328).length < 2 ^ (prefixWord ++ tailWord_3279328).sum := by decide
  have hdescent : baseEnd_3279328 < baseStart_3279328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279368 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 2, 6, 2]
def baseStart_3279368 : Nat := 118140960795 + 3279368 * 2 ^ 59
def prefixEnd_3279368 : Nat := 4983230072969 + 3 ^ 40 * 3279368 * 2
def baseEnd_3279368 : Nat := 1683892026973630691318467

theorem tailTrace_3279368 : CollatzResearch.WordTrace tailWord_3279368 prefixEnd_3279368 1683892026973630691318467 := by
  unfold tailWord_3279368
  simp only [CollatzResearch.WordTrace]
  refine ⟨59804188591708641154971379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79738918122278188206628505 59804188591708641154971379)
  ·
    refine ⟨89706282887562961732457069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59804188591708641154971379 89706282887562961732457069)
    ·
      refine ⟨33639856082836110649671401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89706282887562961732457069 33639856082836110649671401)
      ·
        refine ⟨25229892062127082987253551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33639856082836110649671401 25229892062127082987253551)
        ·
          refine ⟨37844838093190624480880327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25229892062127082987253551 37844838093190624480880327)
          ·
            refine ⟨56767257139785936721320491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37844838093190624480880327 56767257139785936721320491)
            ·
              refine ⟨85150885709678905081980737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56767257139785936721320491 85150885709678905081980737)
              ·
                refine ⟨63863164282259178811485553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85150885709678905081980737 63863164282259178811485553)
                ·
                  refine ⟨47897373211694384108614165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63863164282259178811485553 47897373211694384108614165)
                  ·
                    refine ⟨2245189369298174255091289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47897373211694384108614165 2245189369298174255091289)
                    ·
                      refine ⟨1683892026973630691318467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245189369298174255091289 1683892026973630691318467)
                      ·
                        rfl

theorem cell23_3279368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_3279368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279368 prefixEnd_3279368 := by exact prefixLift 3279368
  have htrace : WordTrace (prefixWord ++ tailWord_3279368) baseStart_3279368 baseEnd_3279368 := by
    simpa [prefixWord, tailWord_3279368, baseEnd_3279368] using wordTrace_append hprefix tailTrace_3279368
  have hstable : (prefixWord ++ tailWord_3279368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279368).length < 2 ^ (prefixWord ++ tailWord_3279368).sum := by decide
  have hdescent : baseEnd_3279368 < baseStart_3279368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279385 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 3, 2, 2]
def baseStart_3279385 : Nat := 118140960795 + 3279385 * 2 ^ 59
def prefixEnd_3279385 : Nat := 4983230072969 + 3 ^ 40 * 3279385 * 2
def baseEnd_3279385 : Nat := 1683900756144757124805889

theorem tailTrace_3279385 : CollatzResearch.WordTrace tailWord_3279385 prefixEnd_3279385 1683900756144757124805889 := by
  unfold tailWord_3279385
  simp only [CollatzResearch.WordTrace]
  refine ⟨119608997224355694213311609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79739331482903796142207739 119608997224355694213311609)
  ·
    refine ⟨89706747918266770659983707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119608997224355694213311609 89706747918266770659983707)
    ·
      refine ⟨134560121877400155989975561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89706747918266770659983707 134560121877400155989975561)
      ·
        refine ⟨100920091408050116992481671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134560121877400155989975561 100920091408050116992481671)
        ·
          refine ⟨151380137112075175488722507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100920091408050116992481671 151380137112075175488722507)
          ·
            refine ⟨227070205668112763233083761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151380137112075175488722507 227070205668112763233083761)
            ·
              refine ⟨170302654251084572424812821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227070205668112763233083761 170302654251084572424812821)
              ·
                refine ⟨7982936918019589332413101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170302654251084572424812821 7982936918019589332413101)
                ·
                  refine ⟨2993601344257345999654913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7982936918019589332413101 2993601344257345999654913)
                  ·
                    refine ⟨2245201008193009499741185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2993601344257345999654913 2245201008193009499741185)
                    ·
                      refine ⟨1683900756144757124805889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245201008193009499741185 1683900756144757124805889)
                      ·
                        rfl

theorem cell23_3279385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 2, 2].length) (baseStart_3279385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279385 prefixEnd_3279385 := by exact prefixLift 3279385
  have htrace : WordTrace (prefixWord ++ tailWord_3279385) baseStart_3279385 baseEnd_3279385 := by
    simpa [prefixWord, tailWord_3279385, baseEnd_3279385] using wordTrace_append hprefix tailTrace_3279385
  have hstable : (prefixWord ++ tailWord_3279385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279385).length < 2 ^ (prefixWord ++ tailWord_3279385).sum := by decide
  have hdescent : baseEnd_3279385 < baseStart_3279385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279396 : List Nat := [2, 3, 1, 5, 1, 1, 2, 3, 1, 1, 3]
def baseStart_3279396 : Nat := 118140960795 + 3279396 * 2 ^ 59
def prefixEnd_3279396 : Nat := 4983230072969 + 3 ^ 40 * 3279396 * 2
def baseEnd_3279396 : Nat := 1683906404431956581768339

theorem tailTrace_3279396 : CollatzResearch.WordTrace tailWord_3279396 prefixEnd_3279396 1683906404431956581768339 := by
  unfold tailWord_3279396
  simp only [CollatzResearch.WordTrace]
  refine ⟨59804699213657921545981021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79739598951543895394641361 59804699213657921545981021)
  ·
    refine ⟨22426762205121720579742883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59804699213657921545981021 22426762205121720579742883)
    ·
      refine ⟨33640143307682580869614325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22426762205121720579742883 33640143307682580869614325)
      ·
        refine ⟨3153763435095241956526343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33640143307682580869614325 3153763435095241956526343)
        ·
          refine ⟨4730645152642862934789515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3153763435095241956526343 4730645152642862934789515)
          ·
            refine ⟨7095967728964294402184273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4730645152642862934789515 7095967728964294402184273)
            ·
              refine ⟨5321975796723220801638205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7095967728964294402184273 5321975796723220801638205)
              ·
                refine ⟨1995740923771207800614327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5321975796723220801638205 1995740923771207800614327)
                ·
                  refine ⟨2993611385656811700921491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995740923771207800614327 2993611385656811700921491)
                  ·
                    refine ⟨4490417078485217551382237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2993611385656811700921491 4490417078485217551382237)
                    ·
                      refine ⟨1683906404431956581768339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4490417078485217551382237 1683906404431956581768339)
                      ·
                        rfl

theorem cell23_3279396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_3279396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279396 prefixEnd_3279396 := by exact prefixLift 3279396
  have htrace : WordTrace (prefixWord ++ tailWord_3279396) baseStart_3279396 baseEnd_3279396 := by
    simpa [prefixWord, tailWord_3279396, baseEnd_3279396] using wordTrace_append hprefix tailTrace_3279396
  have hstable : (prefixWord ++ tailWord_3279396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279396).length < 2 ^ (prefixWord ++ tailWord_3279396).sum := by decide
  have hdescent : baseEnd_3279396 < baseStart_3279396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279402 : List Nat := [3, 1, 4, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_3279402 : Nat := 118140960795 + 3279402 * 2 ^ 59
def prefixEnd_3279402 : Nat := 4983230072969 + 3 ^ 40 * 3279402 * 2
def baseEnd_3279402 : Nat := 1683909485315883558293311

theorem tailTrace_3279402 : CollatzResearch.WordTrace tailWord_3279402 prefixEnd_3279402 1683909485315883558293311 := by
  unfold tailWord_3279402
  simp only [CollatzResearch.WordTrace]
  refine ⟨29902404316323526529170115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79739744843529404077786973 29902404316323526529170115)
  ·
    refine ⟨44853606474485289793755173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29902404316323526529170115 44853606474485289793755173)
    ·
      refine ⟨8410051213965991836329095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44853606474485289793755173 8410051213965991836329095)
      ·
        refine ⟨12615076820948987754493643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8410051213965991836329095 12615076820948987754493643)
        ·
          refine ⟨18922615231423481631740465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12615076820948987754493643 18922615231423481631740465)
          ·
            refine ⟨14191961423567611223805349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18922615231423481631740465 14191961423567611223805349)
            ·
              refine ⟨2660992766918927104463503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14191961423567611223805349 2660992766918927104463503)
              ·
                refine ⟨3991489150378390656695255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2660992766918927104463503 3991489150378390656695255)
                ·
                  refine ⟨5987233725567585985042883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3991489150378390656695255 5987233725567585985042883)
                  ·
                    refine ⟨8980850588351378977564325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5987233725567585985042883 8980850588351378977564325)
                    ·
                      refine ⟨1683909485315883558293311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8980850588351378977564325 1683909485315883558293311)
                      ·
                        rfl

theorem cell23_3279402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_3279402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279402 prefixEnd_3279402 := by exact prefixLift 3279402
  have htrace : WordTrace (prefixWord ++ tailWord_3279402) baseStart_3279402 baseEnd_3279402 := by
    simpa [prefixWord, tailWord_3279402, baseEnd_3279402] using wordTrace_append hprefix tailTrace_3279402
  have hstable : (prefixWord ++ tailWord_3279402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279402).length < 2 ^ (prefixWord ++ tailWord_3279402).sum := by decide
  have hdescent : baseEnd_3279402 < baseStart_3279402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279422 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3279422 : Nat := 118140960795 + 3279422 * 2 ^ 59
def prefixEnd_3279422 : Nat := 4983230072969 + 3 ^ 40 * 3279422 * 2
def baseEnd_3279422 : Nat := 1683919754928973480043219

theorem tailTrace_3279422 : CollatzResearch.WordTrace tailWord_3279422 prefixEnd_3279422 1683919754928973480043219 := by
  unfold tailWord_3279422
  simp only [CollatzResearch.WordTrace]
  refine ⟨14951293340652706191551065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79740231150147766354939013 14951293340652706191551065)
  ·
    refine ⟨11213470005489529643663299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14951293340652706191551065 11213470005489529643663299)
    ·
      refine ⟨16820205008234294465494949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11213470005489529643663299 16820205008234294465494949)
      ·
        refine ⟨3153788439043930212280303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16820205008234294465494949 3153788439043930212280303)
        ·
          refine ⟨4730682658565895318420455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3153788439043930212280303 4730682658565895318420455)
          ·
            refine ⟨7096023987848842977630683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4730682658565895318420455 7096023987848842977630683)
            ·
              refine ⟨10644035981773264466446025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7096023987848842977630683 10644035981773264466446025)
              ·
                refine ⟨7983026986329948349834519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10644035981773264466446025 7983026986329948349834519)
                ·
                  refine ⟨11974540479494922524751779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7983026986329948349834519 11974540479494922524751779)
                  ·
                    refine ⟨17961810719242383787127669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11974540479494922524751779 17961810719242383787127669)
                    ·
                      refine ⟨1683919754928973480043219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17961810719242383787127669 1683919754928973480043219)
                      ·
                        rfl

theorem cell23_3279422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3279422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279422 prefixEnd_3279422 := by exact prefixLift 3279422
  have htrace : WordTrace (prefixWord ++ tailWord_3279422) baseStart_3279422 baseEnd_3279422 := by
    simpa [prefixWord, tailWord_3279422, baseEnd_3279422] using wordTrace_append hprefix tailTrace_3279422
  have hstable : (prefixWord ++ tailWord_3279422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279422).length < 2 ^ (prefixWord ++ tailWord_3279422).sum := by decide
  have hdescent : baseEnd_3279422 < baseStart_3279422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279435 : List Nat := [1, 1, 1, 1, 3, 1, 4, 5, 2, 1, 3]
def baseStart_3279435 : Nat := 118140960795 + 3279435 * 2 ^ 59
def prefixEnd_3279435 : Nat := 4983230072969 + 3 ^ 40 * 3279435 * 2
def baseEnd_3279435 : Nat := 1683926430177481929180659

theorem tailTrace_3279435 : CollatzResearch.WordTrace tailWord_3279435 prefixEnd_3279435 1683926430177481929180659 := by
  unfold tailWord_3279435
  simp only [CollatzResearch.WordTrace]
  refine ⟨119610820874174552752631759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79740547249449701835087839 119610820874174552752631759)
  ·
    refine ⟨179416231311261829128947639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119610820874174552752631759 179416231311261829128947639)
    ·
      refine ⟨269124346966892743693421459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179416231311261829128947639 269124346966892743693421459)
      ·
        refine ⟨403686520450339115540132189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269124346966892743693421459 403686520450339115540132189)
        ·
          refine ⟨151382445168877168327549571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 403686520450339115540132189 151382445168877168327549571)
          ·
            refine ⟨227073667753315752491324357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151382445168877168327549571 227073667753315752491324357)
            ·
              refine ⟨42576312703746703592123317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 227073667753315752491324357 42576312703746703592123317)
              ·
                refine ⟨3991529315976253461761561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42576312703746703592123317 3991529315976253461761561)
                ·
                  refine ⟨2993646986982190096321171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3991529315976253461761561 2993646986982190096321171)
                  ·
                    refine ⟨4490470480473285144481757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2993646986982190096321171 4490470480473285144481757)
                    ·
                      refine ⟨1683926430177481929180659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4490470480473285144481757 1683926430177481929180659)
                      ·
                        rfl

theorem cell23_3279435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 1, 3].length) (baseStart_3279435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279435 prefixEnd_3279435 := by exact prefixLift 3279435
  have htrace : WordTrace (prefixWord ++ tailWord_3279435) baseStart_3279435 baseEnd_3279435 := by
    simpa [prefixWord, tailWord_3279435, baseEnd_3279435] using wordTrace_append hprefix tailTrace_3279435
  have hstable : (prefixWord ++ tailWord_3279435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279435).length < 2 ^ (prefixWord ++ tailWord_3279435).sum := by decide
  have hdescent : baseEnd_3279435 < baseStart_3279435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279445 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 3, 3, 2]
def baseStart_3279445 : Nat := 118140960795 + 3279445 * 2 ^ 59
def prefixEnd_3279445 : Nat := 4983230072969 + 3 ^ 40 * 3279445 * 2
def baseEnd_3279445 : Nat := 1683931564984026890055613

theorem tailTrace_3279445 : CollatzResearch.WordTrace tailWord_3279445 prefixEnd_3279445 1683931564984026890055613 := by
  unfold tailWord_3279445
  simp only [CollatzResearch.WordTrace]
  refine ⟨119611185604138324460495789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79740790402758882973663859 119611185604138324460495789)
  ·
    refine ⟨44854194601551871672685921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119611185604138324460495789 44854194601551871672685921)
    ·
      refine ⟨33640645951163903754514441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44854194601551871672685921 33640645951163903754514441)
      ·
        refine ⟨25230484463372927815885831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33640645951163903754514441 25230484463372927815885831)
        ·
          refine ⟨37845726695059391723828747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25230484463372927815885831 37845726695059391723828747)
          ·
            refine ⟨56768590042589087585743121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37845726695059391723828747 56768590042589087585743121)
            ·
              refine ⟨42576442531941815689307341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56768590042589087585743121 42576442531941815689307341)
              ·
                refine ⟨15966165949478180883490253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42576442531941815689307341 15966165949478180883490253)
                ·
                  refine ⟨5987312231054317831308845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15966165949478180883490253 5987312231054317831308845)
                  ·
                    refine ⟨2245242086645369186740817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5987312231054317831308845 2245242086645369186740817)
                    ·
                      refine ⟨1683931564984026890055613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245242086645369186740817 1683931564984026890055613)
                      ·
                        rfl

theorem cell23_3279445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_3279445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279445 prefixEnd_3279445 := by exact prefixLift 3279445
  have htrace : WordTrace (prefixWord ++ tailWord_3279445) baseStart_3279445 baseEnd_3279445 := by
    simpa [prefixWord, tailWord_3279445, baseEnd_3279445] using wordTrace_append hprefix tailTrace_3279445
  have hstable : (prefixWord ++ tailWord_3279445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279445).length < 2 ^ (prefixWord ++ tailWord_3279445).sum := by decide
  have hdescent : baseEnd_3279445 < baseStart_3279445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279490 : List Nat := [3, 4, 3, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3279490 : Nat := 118140960795 + 3279490 * 2 ^ 59
def prefixEnd_3279490 : Nat := 4983230072969 + 3 ^ 40 * 3279490 * 2
def baseEnd_3279490 : Nat := 1683954671613479213992907

theorem tailTrace_3279490 : CollatzResearch.WordTrace tailWord_3279490 prefixEnd_3279490 1683954671613479213992907 := by
  unfold tailWord_3279490
  simp only [CollatzResearch.WordTrace]
  refine ⟨29903206722243824286470981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79741884592650198097255949 29903206722243824286470981)
  ·
    refine ⟨5606851260420717053713309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29903206722243824286470981 5606851260420717053713309)
    ·
      refine ⟨2102569222657768895142491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5606851260420717053713309 2102569222657768895142491)
      ·
        refine ⟨3153853833986653342713737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102569222657768895142491 3153853833986653342713737)
        ·
          refine ⟨2365390375489990007035303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3153853833986653342713737 2365390375489990007035303)
          ·
            refine ⟨3548085563234985010552955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2365390375489990007035303 3548085563234985010552955)
            ·
              refine ⟨5322128344852477515829433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3548085563234985010552955 5322128344852477515829433)
              ·
                refine ⟨3991596258639358136872075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5322128344852477515829433 3991596258639358136872075)
                ·
                  refine ⟨5987394387959037205308113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3991596258639358136872075 5987394387959037205308113)
                  ·
                    refine ⟨4490545790969277903981085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5987394387959037205308113 4490545790969277903981085)
                    ·
                      refine ⟨1683954671613479213992907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4490545790969277903981085 1683954671613479213992907)
                      ·
                        rfl

theorem cell23_3279490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3279490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279490 prefixEnd_3279490 := by exact prefixLift 3279490
  have htrace : WordTrace (prefixWord ++ tailWord_3279490) baseStart_3279490 baseEnd_3279490 := by
    simpa [prefixWord, tailWord_3279490, baseEnd_3279490] using wordTrace_append hprefix tailTrace_3279490
  have hstable : (prefixWord ++ tailWord_3279490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279490).length < 2 ^ (prefixWord ++ tailWord_3279490).sum := by decide
  have hdescent : baseEnd_3279490 < baseStart_3279490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279535 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 2, 5, 2]
def baseStart_3279535 : Nat := 118140960795 + 3279535 * 2 ^ 59
def prefixEnd_3279535 : Nat := 4983230072969 + 3 ^ 40 * 3279535 * 2
def baseEnd_3279535 : Nat := 1683977778242931537930199

theorem tailTrace_3279535 : CollatzResearch.WordTrace tailWord_3279535 prefixEnd_3279535 1683977778242931537930199 := by
  unfold tailWord_3279535
  simp only [CollatzResearch.WordTrace]
  refine ⟨119614468173812269831272059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79742978782541513220848039 119614468173812269831272059)
  ·
    refine ⟨179421702260718404746908089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119614468173812269831272059 179421702260718404746908089)
    ·
      refine ⟨134566276695538803560181067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179421702260718404746908089 134566276695538803560181067)
      ·
        refine ⟨201849415043308205340271601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134566276695538803560181067 201849415043308205340271601)
        ·
          refine ⟨151387061282481154005203701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201849415043308205340271601 151387061282481154005203701)
          ·
            refine ⟨14192536995232608187987847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151387061282481154005203701 14192536995232608187987847)
            ·
              refine ⟨21288805492848912281981771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14192536995232608187987847 21288805492848912281981771)
              ·
                refine ⟨31933208239273368422972657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21288805492848912281981771 31933208239273368422972657)
                ·
                  refine ⟨23949906179455026317229493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31933208239273368422972657 23949906179455026317229493)
                  ·
                    refine ⟨2245303704323908717240265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23949906179455026317229493 2245303704323908717240265)
                    ·
                      refine ⟨1683977778242931537930199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245303704323908717240265 1683977778242931537930199)
                      ·
                        rfl

theorem cell23_3279535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 5, 2].length) (baseStart_3279535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279535 prefixEnd_3279535 := by exact prefixLift 3279535
  have htrace : WordTrace (prefixWord ++ tailWord_3279535) baseStart_3279535 baseEnd_3279535 := by
    simpa [prefixWord, tailWord_3279535, baseEnd_3279535] using wordTrace_append hprefix tailTrace_3279535
  have hstable : (prefixWord ++ tailWord_3279535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279535).length < 2 ^ (prefixWord ++ tailWord_3279535).sum := by decide
  have hdescent : baseEnd_3279535 < baseStart_3279535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279562 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 2, 5]
def baseStart_3279562 : Nat := 118140960795 + 3279562 * 2 ^ 59
def prefixEnd_3279562 : Nat := 4983230072969 + 3 ^ 40 * 3279562 * 2
def baseEnd_3279562 : Nat := 561330547406867644097525

theorem tailTrace_3279562 : CollatzResearch.WordTrace tailWord_3279562 prefixEnd_3279562 561330547406867644097525 := by
  unfold tailWord_3279562
  simp only [CollatzResearch.WordTrace]
  refine ⟨29903863236178613360626235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79743635296476302295003293 29903863236178613360626235)
  ·
    refine ⟨44855794854267920040939353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29903863236178613360626235 44855794854267920040939353)
    ·
      refine ⟨33641846140700940030704515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44855794854267920040939353 33641846140700940030704515)
      ·
        refine ⟨50462769211051410046056773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33641846140700940030704515 50462769211051410046056773)
        ·
          refine ⟨9461769227072139383635645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50462769211051410046056773 9461769227072139383635645)
          ·
            refine ⟨3548163460152052268863367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9461769227072139383635645 3548163460152052268863367)
            ·
              refine ⟨5322245190228078403295051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3548163460152052268863367 5322245190228078403295051)
              ·
                refine ⟨7983367785342117604942577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5322245190228078403295051 7983367785342117604942577)
                ·
                  refine ⟨5987525839006588203706933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7983367785342117604942577 5987525839006588203706933)
                  ·
                    refine ⟨561330547406867644097525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5987525839006588203706933 561330547406867644097525)
                    ·
                      rfl

theorem cell23_3279562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_3279562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279562 prefixEnd_3279562 := by exact prefixLift 3279562
  have htrace : WordTrace (prefixWord ++ tailWord_3279562) baseStart_3279562 baseEnd_3279562 := by
    simpa [prefixWord, tailWord_3279562, baseEnd_3279562] using wordTrace_append hprefix tailTrace_3279562
  have hstable : (prefixWord ++ tailWord_3279562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279562).length < 2 ^ (prefixWord ++ tailWord_3279562).sum := by decide
  have hdescent : baseEnd_3279562 < baseStart_3279562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279578 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_3279578 : Nat := 118140960795 + 3279578 * 2 ^ 59
def prefixEnd_3279578 : Nat := 4983230072969 + 3 ^ 40 * 3279578 * 2
def baseEnd_3279578 : Nat := 1683999857911074869692501

theorem tailTrace_3279578 : CollatzResearch.WordTrace tailWord_3279578 prefixEnd_3279578 1683999857911074869692501 := by
  unfold tailWord_3279578
  simp only [CollatzResearch.WordTrace]
  refine ⟨29904009128164122043771847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79744024341770992116724925 29904009128164122043771847)
  ·
    refine ⟨44856013692246183065657771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29904009128164122043771847 44856013692246183065657771)
    ·
      refine ⟨67284020538369274598486657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44856013692246183065657771 67284020538369274598486657)
      ·
        refine ⟨50463015403776955948864993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67284020538369274598486657 50463015403776955948864993)
        ·
          refine ⟨37847261552832716961648745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50463015403776955948864993 37847261552832716961648745)
          ·
            refine ⟨28385446164624537721236559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37847261552832716961648745 28385446164624537721236559)
            ·
              refine ⟨42578169246936806581854839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28385446164624537721236559 42578169246936806581854839)
              ·
                refine ⟨63867253870405209872782259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42578169246936806581854839 63867253870405209872782259)
                ·
                  refine ⟨95800880805607814809173389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63867253870405209872782259 95800880805607814809173389)
                  ·
                    refine ⟨35925330302102930553440021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95800880805607814809173389 35925330302102930553440021)
                    ·
                      refine ⟨1683999857911074869692501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35925330302102930553440021 1683999857911074869692501)
                      ·
                        rfl

theorem cell23_3279578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_3279578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279578 prefixEnd_3279578 := by exact prefixLift 3279578
  have htrace : WordTrace (prefixWord ++ tailWord_3279578) baseStart_3279578 baseEnd_3279578 := by
    simpa [prefixWord, tailWord_3279578, baseEnd_3279578] using wordTrace_append hprefix tailTrace_3279578
  have hstable : (prefixWord ++ tailWord_3279578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279578).length < 2 ^ (prefixWord ++ tailWord_3279578).sum := by decide
  have hdescent : baseEnd_3279578 < baseStart_3279578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279608 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_3279608 : Nat := 118140960795 + 3279608 * 2 ^ 59
def prefixEnd_3279608 : Nat := 4983230072969 + 3 ^ 40 * 3279608 * 2
def baseEnd_3279608 : Nat := 1684015262330709752317363

theorem tailTrace_3279608 : CollatzResearch.WordTrace tailWord_3279608 prefixEnd_3279608 1684015262330709752317363 := by
  unfold tailWord_3279608
  simp only [CollatzResearch.WordTrace]
  refine ⟨59808565351273901649339739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79744753801698535532452985 59808565351273901649339739)
  ·
    refine ⟨89712848026910852474009609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59808565351273901649339739 89712848026910852474009609)
    ·
      refine ⟨67284636020183139355507207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89712848026910852474009609 67284636020183139355507207)
      ·
        refine ⟨100926954030274709033260811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67284636020183139355507207 100926954030274709033260811)
        ·
          refine ⟨151390431045412063549891217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100926954030274709033260811 151390431045412063549891217)
          ·
            refine ⟨113542823284059047662418413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151390431045412063549891217 113542823284059047662418413)
            ·
              refine ⟨42578558731522142873406905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113542823284059047662418413 42578558731522142873406905)
              ·
                refine ⟨31933919048641607155055179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42578558731522142873406905 31933919048641607155055179)
                ·
                  refine ⟨47900878572962410732582769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31933919048641607155055179 47900878572962410732582769)
                  ·
                    refine ⟨35925658929721808049437077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47900878572962410732582769 35925658929721808049437077)
                    ·
                      refine ⟨1684015262330709752317363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35925658929721808049437077 1684015262330709752317363)
                      ·
                        rfl

theorem cell23_3279608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_3279608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279608 prefixEnd_3279608 := by exact prefixLift 3279608
  have htrace : WordTrace (prefixWord ++ tailWord_3279608) baseStart_3279608 baseEnd_3279608 := by
    simpa [prefixWord, tailWord_3279608, baseEnd_3279608] using wordTrace_append hprefix tailTrace_3279608
  have hstable : (prefixWord ++ tailWord_3279608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279608).length < 2 ^ (prefixWord ++ tailWord_3279608).sum := by decide
  have hdescent : baseEnd_3279608 < baseStart_3279608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279635 : List Nat := [1, 1, 1, 2, 1, 3, 3, 5, 1, 5]
def baseStart_3279635 : Nat := 118140960795 + 3279635 * 2 ^ 59
def prefixEnd_3279635 : Nat := 4983230072969 + 3 ^ 40 * 3279635 * 2
def baseEnd_3279635 : Nat := 561343042102793715559913

theorem tailTrace_3279635 : CollatzResearch.WordTrace tailWord_3279635 prefixEnd_3279635 561343042102793715559913 := by
  unfold tailWord_3279635
  simp only [CollatzResearch.WordTrace]
  refine ⟨119618115473449986909912359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79745410315633324606608239 119618115473449986909912359)
  ·
    refine ⟨179427173210174980364868539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119618115473449986909912359 179427173210174980364868539)
    ·
      refine ⟨269140759815262470547302809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179427173210174980364868539 269140759815262470547302809)
      ·
        refine ⟨201855569861446852910477107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269140759815262470547302809 201855569861446852910477107)
        ·
          refine ⟨302783354792170279365715661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201855569861446852910477107 302783354792170279365715661)
          ·
            refine ⟨113543758047063854762143373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302783354792170279365715661 113543758047063854762143373)
            ·
              refine ⟨42578909267648945535803765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113543758047063854762143373 42578909267648945535803765)
              ·
                refine ⟨3991772743842088643981603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42578909267648945535803765 3991772743842088643981603)
                ·
                  refine ⟨5987659115763132965972405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3991772743842088643981603 5987659115763132965972405)
                  ·
                    refine ⟨561343042102793715559913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5987659115763132965972405 561343042102793715559913)
                    ·
                      rfl

theorem cell23_3279635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 5].length) (baseStart_3279635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279635 prefixEnd_3279635 := by exact prefixLift 3279635
  have htrace : WordTrace (prefixWord ++ tailWord_3279635) baseStart_3279635 baseEnd_3279635 := by
    simpa [prefixWord, tailWord_3279635, baseEnd_3279635] using wordTrace_append hprefix tailTrace_3279635
  have hstable : (prefixWord ++ tailWord_3279635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279635).length < 2 ^ (prefixWord ++ tailWord_3279635).sum := by decide
  have hdescent : baseEnd_3279635 < baseStart_3279635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279665 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 1, 6]
def baseStart_3279665 : Nat := 118140960795 + 3279665 * 2 ^ 59
def prefixEnd_3279665 : Nat := 4983230072969 + 3 ^ 40 * 3279665 * 2
def baseEnd_3279665 : Nat := 561348176909338676434867

theorem tailTrace_3279665 : CollatzResearch.WordTrace tailWord_3279665 prefixEnd_3279665 561348176909338676434867 := by
  unfold tailWord_3279665
  simp only [CollatzResearch.WordTrace]
  refine ⟨119619209663341302033504449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79746139775560868022336299 119619209663341302033504449)
  ·
    refine ⟨89714407247505976525128337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119619209663341302033504449 89714407247505976525128337)
    ·
      refine ⟨67285805435629482393846253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89714407247505976525128337 67285805435629482393846253)
      ·
        refine ⟨25232177038361055897692345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67285805435629482393846253 25232177038361055897692345)
        ·
          refine ⟨18924132778770791923269259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25232177038361055897692345 18924132778770791923269259)
          ·
            refine ⟨28386199168156187884903889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18924132778770791923269259 28386199168156187884903889)
            ·
              refine ⟨21289649376117140913677917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28386199168156187884903889 21289649376117140913677917)
              ·
                refine ⟨7983618516043927842629219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21289649376117140913677917 7983618516043927842629219)
                ·
                  refine ⟨11975427774065891763943829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7983618516043927842629219 11975427774065891763943829)
                  ·
                    refine ⟨561348176909338676434867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11975427774065891763943829 561348176909338676434867)
                    ·
                      rfl

theorem cell23_3279665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_3279665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279665 prefixEnd_3279665 := by exact prefixLift 3279665
  have htrace : WordTrace (prefixWord ++ tailWord_3279665) baseStart_3279665 baseEnd_3279665 := by
    simpa [prefixWord, tailWord_3279665, baseEnd_3279665] using wordTrace_append hprefix tailTrace_3279665
  have hstable : (prefixWord ++ tailWord_3279665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279665).length < 2 ^ (prefixWord ++ tailWord_3279665).sum := by decide
  have hdescent : baseEnd_3279665 < baseStart_3279665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279669 : List Nat := [1, 3, 3, 1, 3, 3, 1, 2, 1, 5]
def baseStart_3279669 : Nat := 118140960795 + 3279669 * 2 ^ 59
def prefixEnd_3279669 : Nat := 4983230072969 + 3 ^ 40 * 3279669 * 2
def baseEnd_3279669 : Nat := 561348861550211337884861

theorem tailTrace_3279669 : CollatzResearch.WordTrace tailWord_3279669 prefixEnd_3279669 561348861550211337884861 := by
  unfold tailWord_3279669
  simp only [CollatzResearch.WordTrace]
  refine ⟨119619355555326810716650061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79746237036884540477766707 119619355555326810716650061)
  ·
    refine ⟨44857258333247554018743773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119619355555326810716650061 44857258333247554018743773)
    ·
      refine ⟨16821471874967832757028915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44857258333247554018743773 16821471874967832757028915)
      ·
        refine ⟨25232207812451749135543373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16821471874967832757028915 25232207812451749135543373)
        ·
          refine ⟨9462077929669405925828765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25232207812451749135543373 9462077929669405925828765)
          ·
            refine ⟨3548279223626027222185787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9462077929669405925828765 3548279223626027222185787)
            ·
              refine ⟨5322418835439040833278681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3548279223626027222185787 5322418835439040833278681)
              ·
                refine ⟨3991814126579280624959011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5322418835439040833278681 3991814126579280624959011)
                ·
                  refine ⟨5987721189868920937438517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3991814126579280624959011 5987721189868920937438517)
                  ·
                    refine ⟨561348861550211337884861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5987721189868920937438517 561348861550211337884861)
                    ·
                      rfl

theorem cell23_3279669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_3279669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279669 prefixEnd_3279669 := by exact prefixLift 3279669
  have htrace : WordTrace (prefixWord ++ tailWord_3279669) baseStart_3279669 baseEnd_3279669 := by
    simpa [prefixWord, tailWord_3279669, baseEnd_3279669] using wordTrace_append hprefix tailTrace_3279669
  have hstable : (prefixWord ++ tailWord_3279669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279669).length < 2 ^ (prefixWord ++ tailWord_3279669).sum := by decide
  have hdescent : baseEnd_3279669 < baseStart_3279669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279689 : List Nat := [1, 2, 1, 1, 2, 6, 3, 1, 1, 1, 4]
def baseStart_3279689 : Nat := 118140960795 + 3279689 * 2 ^ 59
def prefixEnd_3279689 : Nat := 4983230072969 + 3 ^ 40 * 3279689 * 2
def baseEnd_3279689 : Nat := 1684056854263723935404491

theorem tailTrace_3279689 : CollatzResearch.WordTrace tailWord_3279689 prefixEnd_3279689 1684056854263723935404491 := by
  unfold tailWord_3279689
  simp only [CollatzResearch.WordTrace]
  refine ⟨119620085015254354132378121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79746723343502902754918747 119620085015254354132378121)
  ·
    refine ⟨89715063761440765599283591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119620085015254354132378121 89715063761440765599283591)
    ·
      refine ⟨134572595642161148398925387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89715063761440765599283591 134572595642161148398925387)
      ·
        refine ⟨201858893463241722598388081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134572595642161148398925387 201858893463241722598388081)
        ·
          refine ⟨151394170097431291948791061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201858893463241722598388081 151394170097431291948791061)
          ·
            refine ⟨7096601723317091810099581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 151394170097431291948791061 7096601723317091810099581)
            ·
              refine ⟨2661225646243909428787343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7096601723317091810099581 2661225646243909428787343)
              ·
                refine ⟨3991838469365864143181015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2661225646243909428787343 3991838469365864143181015)
                ·
                  refine ⟨5987757704048796214771523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3991838469365864143181015 5987757704048796214771523)
                  ·
                    refine ⟨8981636556073194322157285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5987757704048796214771523 8981636556073194322157285)
                    ·
                      refine ⟨1684056854263723935404491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8981636556073194322157285 1684056854263723935404491)
                      ·
                        rfl

theorem cell23_3279689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 1, 1, 4].length) (baseStart_3279689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279689 prefixEnd_3279689 := by exact prefixLift 3279689
  have htrace : WordTrace (prefixWord ++ tailWord_3279689) baseStart_3279689 baseEnd_3279689 := by
    simpa [prefixWord, tailWord_3279689, baseEnd_3279689] using wordTrace_append hprefix tailTrace_3279689
  have hstable : (prefixWord ++ tailWord_3279689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279689).length < 2 ^ (prefixWord ++ tailWord_3279689).sum := by decide
  have hdescent : baseEnd_3279689 < baseStart_3279689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279692 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 1, 1, 5]
def baseStart_3279692 : Nat := 118140960795 + 3279692 * 2 ^ 59
def prefixEnd_3279692 : Nat := 4983230072969 + 3 ^ 40 * 3279692 * 2
def baseEnd_3279692 : Nat := 1684058394705687423666977

theorem tailTrace_3279692 : CollatzResearch.WordTrace tailWord_3279692 prefixEnd_3279692 1684058394705687423666977 := by
  unfold tailWord_3279692
  simp only [CollatzResearch.WordTrace]
  refine ⟨59810097217121742822368665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79746796289495657096491553 59810097217121742822368665)
  ·
    refine ⟨44857572912841307116776499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59810097217121742822368665 44857572912841307116776499)
    ·
      refine ⟨67286359369261960675164749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44857572912841307116776499 67286359369261960675164749)
      ·
        refine ⟨25232384763473235253186781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67286359369261960675164749 25232384763473235253186781)
        ·
          refine ⟨9462144286302463219945043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25232384763473235253186781 9462144286302463219945043)
          ·
            refine ⟨14193216429453694829917565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9462144286302463219945043 14193216429453694829917565)
            ·
              refine ⟨5322456161045135561219087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14193216429453694829917565 5322456161045135561219087)
              ·
                refine ⟨7983684241567703341828631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5322456161045135561219087 7983684241567703341828631)
                ·
                  refine ⟨11975526362351555012742947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7983684241567703341828631 11975526362351555012742947)
                  ·
                    refine ⟨17963289543527332519114421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11975526362351555012742947 17963289543527332519114421)
                    ·
                      refine ⟨1684058394705687423666977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17963289543527332519114421 1684058394705687423666977)
                      ·
                        rfl

theorem cell23_3279692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_3279692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279692 prefixEnd_3279692 := by exact prefixLift 3279692
  have htrace : WordTrace (prefixWord ++ tailWord_3279692) baseStart_3279692 baseEnd_3279692 := by
    simpa [prefixWord, tailWord_3279692, baseEnd_3279692] using wordTrace_append hprefix tailTrace_3279692
  have hstable : (prefixWord ++ tailWord_3279692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279692).length < 2 ^ (prefixWord ++ tailWord_3279692).sum := by decide
  have hdescent : baseEnd_3279692 < baseStart_3279692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279700 : List Nat := [2, 4, 1, 1, 4, 2, 2, 2, 1, 1, 3]
def baseStart_3279700 : Nat := 118140960795 + 3279700 * 2 ^ 59
def prefixEnd_3279700 : Nat := 4983230072969 + 3 ^ 40 * 3279700 * 2
def baseEnd_3279700 : Nat := 1684062502550923392366941

theorem tailTrace_3279700 : CollatzResearch.WordTrace tailWord_3279700 prefixEnd_3279700 1684062502550923392366941 := by
  unfold tailWord_3279700
  simp only [CollatzResearch.WordTrace]
  refine ⟨59810243109107251505514277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79746990812143002007352369 59810243109107251505514277)
  ·
    refine ⟨11214420582957609657283927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59810243109107251505514277 11214420582957609657283927)
    ·
      refine ⟨16821630874436414485925891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11214420582957609657283927 16821630874436414485925891)
      ·
        refine ⟨25232446311654621728888837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16821630874436414485925891 25232446311654621728888837)
        ·
          refine ⟨4731083683435241574166657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25232446311654621728888837 4731083683435241574166657)
          ·
            refine ⟨3548312762576431180624993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4731083683435241574166657 3548312762576431180624993)
            ·
              refine ⟨2661234571932323385468745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3548312762576431180624993 2661234571932323385468745)
              ·
                refine ⟨1995925928949242539101559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2661234571932323385468745 1995925928949242539101559)
                ·
                  refine ⟨2993888893423863808652339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1995925928949242539101559 2993888893423863808652339)
                  ·
                    refine ⟨4490833340135795712978509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2993888893423863808652339 4490833340135795712978509)
                    ·
                      refine ⟨1684062502550923392366941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4490833340135795712978509 1684062502550923392366941)
                      ·
                        rfl

theorem cell23_3279700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_3279700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279700 prefixEnd_3279700 := by exact prefixLift 3279700
  have htrace : WordTrace (prefixWord ++ tailWord_3279700) baseStart_3279700 baseEnd_3279700 := by
    simpa [prefixWord, tailWord_3279700, baseEnd_3279700] using wordTrace_append hprefix tailTrace_3279700
  have hstable : (prefixWord ++ tailWord_3279700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279700).length < 2 ^ (prefixWord ++ tailWord_3279700).sum := by decide
  have hdescent : baseEnd_3279700 < baseStart_3279700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279725 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_3279725 : Nat := 118140960795 + 3279725 * 2 ^ 59
def prefixEnd_3279725 : Nat := 4983230072969 + 3 ^ 40 * 3279725 * 2
def baseEnd_3279725 : Nat := 561358446522428598184775

theorem tailTrace_3279725 : CollatzResearch.WordTrace tailWord_3279725 prefixEnd_3279725 561358446522428598184775 := by
  unfold tailWord_3279725
  simp only [CollatzResearch.WordTrace]
  refine ⟨119621398043123932280688629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79747598695415954853792419 119621398043123932280688629)
  ·
    refine ⟨11214506066542868651314559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119621398043123932280688629 11214506066542868651314559)
    ·
      refine ⟨16821759099814302976971839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11214506066542868651314559 16821759099814302976971839)
      ·
        refine ⟨25232638649721454465457759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16821759099814302976971839 25232638649721454465457759)
        ·
          refine ⟨37848957974582181698186639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25232638649721454465457759 37848957974582181698186639)
          ·
            refine ⟨56773436961873272547279959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37848957974582181698186639 56773436961873272547279959)
            ·
              refine ⟨85160155442809908820919939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56773436961873272547279959 85160155442809908820919939)
              ·
                refine ⟨127740233164214863231379909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85160155442809908820919939 127740233164214863231379909)
                ·
                  refine ⟨23951293718290286855883733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127740233164214863231379909 23951293718290286855883733)
                  ·
                    refine ⟨561358446522428598184775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23951293718290286855883733 561358446522428598184775)
                    ·
                      rfl

theorem cell23_3279725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_3279725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279725 prefixEnd_3279725 := by exact prefixLift 3279725
  have htrace : WordTrace (prefixWord ++ tailWord_3279725) baseStart_3279725 baseEnd_3279725 := by
    simpa [prefixWord, tailWord_3279725, baseEnd_3279725] using wordTrace_append hprefix tailTrace_3279725
  have hstable : (prefixWord ++ tailWord_3279725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279725).length < 2 ^ (prefixWord ++ tailWord_3279725).sum := by decide
  have hdescent : baseEnd_3279725 < baseStart_3279725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279755 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 2, 6]
def baseStart_3279755 : Nat := 118140960795 + 3279755 * 2 ^ 59
def prefixEnd_3279755 : Nat := 4983230072969 + 3 ^ 40 * 3279755 * 2
def baseEnd_3279755 : Nat := 561363581328973559059729

theorem tailTrace_3279755 : CollatzResearch.WordTrace tailWord_3279755 prefixEnd_3279755 561363581328973559059729 := by
  unfold tailWord_3279755
  simp only [CollatzResearch.WordTrace]
  refine ⟨119622492233015247404280719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79748328155343498269520479 119622492233015247404280719)
  ·
    refine ⟨179433738349522871106421079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119622492233015247404280719 179433738349522871106421079)
    ·
      refine ⟨269150607524284306659631619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179433738349522871106421079 269150607524284306659631619)
      ·
        refine ⟨403725911286426459989447429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269150607524284306659631619 403725911286426459989447429)
        ·
          refine ⟨75698608366204961248021393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 403725911286426459989447429 75698608366204961248021393)
          ·
            refine ⟨56773956274653720936016045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75698608366204961248021393 56773956274653720936016045)
            ·
              refine ⟨21290233602995145351006017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56773956274653720936016045 21290233602995145351006017)
              ·
                refine ⟨15967675202246359013254513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21290233602995145351006017 15967675202246359013254513)
                ·
                  refine ⟨11975756401684769259940885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15967675202246359013254513 11975756401684769259940885)
                  ·
                    refine ⟨561363581328973559059729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11975756401684769259940885 561363581328973559059729)
                    ·
                      rfl

theorem cell23_3279755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 6].length) (baseStart_3279755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279755 prefixEnd_3279755 := by exact prefixLift 3279755
  have htrace : WordTrace (prefixWord ++ tailWord_3279755) baseStart_3279755 baseEnd_3279755 := by
    simpa [prefixWord, tailWord_3279755, baseEnd_3279755] using wordTrace_append hprefix tailTrace_3279755
  have hstable : (prefixWord ++ tailWord_3279755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279755).length < 2 ^ (prefixWord ++ tailWord_3279755).sum := by decide
  have hdescent : baseEnd_3279755 < baseStart_3279755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279779 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 1, 4, 2]
def baseStart_3279779 : Nat := 118140960795 + 3279779 * 2 ^ 59
def prefixEnd_3279779 : Nat := 4983230072969 + 3 ^ 40 * 3279779 * 2
def baseEnd_3279779 : Nat := 1684103067522628583279077

theorem tailTrace_3279779 : CollatzResearch.WordTrace tailWord_3279779 prefixEnd_3279779 1684103067522628583279077 := by
  unfold tailWord_3279779
  simp only [CollatzResearch.WordTrace]
  refine ⟨119623367584928299503154391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79748911723285533002102927 119623367584928299503154391)
  ·
    refine ⟨179435051377392449254731587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119623367584928299503154391 179435051377392449254731587)
    ·
      refine ⟨269152577066088673882097381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179435051377392449254731587 269152577066088673882097381)
      ·
        refine ⟨50466108199891626352893259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269152577066088673882097381 50466108199891626352893259)
        ·
          refine ⟨75699162299837439529339889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50466108199891626352893259 75699162299837439529339889)
          ·
            refine ⟨56774371724878079647004917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75699162299837439529339889 56774371724878079647004917)
            ·
              refine ⟨5322597349207319966906711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56774371724878079647004917 5322597349207319966906711)
              ·
                refine ⟨7983896023810979950360067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5322597349207319966906711 7983896023810979950360067)
                ·
                  refine ⟨11975844035716469925540101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7983896023810979950360067 11975844035716469925540101)
                  ·
                    refine ⟨2245470756696838111038769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11975844035716469925540101 2245470756696838111038769)
                    ·
                      refine ⟨1684103067522628583279077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245470756696838111038769 1684103067522628583279077)
                      ·
                        rfl

theorem cell23_3279779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_3279779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279779 prefixEnd_3279779 := by exact prefixLift 3279779
  have htrace : WordTrace (prefixWord ++ tailWord_3279779) baseStart_3279779 baseEnd_3279779 := by
    simpa [prefixWord, tailWord_3279779, baseEnd_3279779] using wordTrace_append hprefix tailTrace_3279779
  have hstable : (prefixWord ++ tailWord_3279779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279779).length < 2 ^ (prefixWord ++ tailWord_3279779).sum := by decide
  have hdescent : baseEnd_3279779 < baseStart_3279779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279783 : List Nat := [1, 1, 6, 1, 3, 1, 2, 2, 1, 3, 2]
def baseStart_3279783 : Nat := 118140960795 + 3279783 * 2 ^ 59
def prefixEnd_3279783 : Nat := 4983230072969 + 3 ^ 40 * 3279783 * 2
def baseEnd_3279783 : Nat := 1684105121445246567629059

theorem tailTrace_3279783 : CollatzResearch.WordTrace tailWord_3279783 prefixEnd_3279783 1684105121445246567629059 := by
  unfold tailWord_3279783
  simp only [CollatzResearch.WordTrace]
  refine ⟨119623513476913808186300003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79749008984609205457533335 119623513476913808186300003)
  ·
    refine ⟨179435270215370712279450005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119623513476913808186300003 179435270215370712279450005)
    ·
      refine ⟨8411028291345502138099219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 179435270215370712279450005 8411028291345502138099219)
      ·
        refine ⟨12616542437018253207148829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8411028291345502138099219 12616542437018253207148829)
        ·
          refine ⟨4731203413881844952680811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12616542437018253207148829 4731203413881844952680811)
          ·
            refine ⟨7096805120822767429021217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4731203413881844952680811 7096805120822767429021217)
            ·
              refine ⟨5322603840617075571765913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7096805120822767429021217 5322603840617075571765913)
              ·
                refine ⟨3991952880462806678824435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5322603840617075571765913 3991952880462806678824435)
                ·
                  refine ⟨5987929320694210018236653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3991952880462806678824435 5987929320694210018236653)
                  ·
                    refine ⟨2245473495260328756838745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5987929320694210018236653 2245473495260328756838745)
                    ·
                      refine ⟨1684105121445246567629059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245473495260328756838745 1684105121445246567629059)
                      ·
                        rfl

theorem cell23_3279783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_3279783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279783 prefixEnd_3279783 := by exact prefixLift 3279783
  have htrace : WordTrace (prefixWord ++ tailWord_3279783) baseStart_3279783 baseEnd_3279783 := by
    simpa [prefixWord, tailWord_3279783, baseEnd_3279783] using wordTrace_append hprefix tailTrace_3279783
  have hstable : (prefixWord ++ tailWord_3279783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279783).length < 2 ^ (prefixWord ++ tailWord_3279783).sum := by decide
  have hdescent : baseEnd_3279783 < baseStart_3279783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279785 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 7]
def baseStart_3279785 : Nat := 118140960795 + 3279785 * 2 ^ 59
def prefixEnd_3279785 : Nat := 4983230072969 + 3 ^ 40 * 3279785 * 2
def baseEnd_3279785 : Nat := 187122905378506173311561

theorem tailTrace_3279785 : CollatzResearch.WordTrace tailWord_3279785 prefixEnd_3279785 187122905378506173311561 := by
  unfold tailWord_3279785
  simp only [CollatzResearch.WordTrace]
  refine ⟨119623586422906562527872809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79749057615271041685248539 119623586422906562527872809)
  ·
    refine ⟨89717689817179921895904607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119623586422906562527872809 89717689817179921895904607)
    ·
      refine ⟨134576534725769882843856911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89717689817179921895904607 134576534725769882843856911)
      ·
        refine ⟨201864802088654824265785367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134576534725769882843856911 201864802088654824265785367)
        ·
          refine ⟨302797203132982236398678051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201864802088654824265785367 302797203132982236398678051)
          ·
            refine ⟨454195804699473354598017077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302797203132982236398678051 454195804699473354598017077)
            ·
              refine ⟨42580856690575626993564101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 454195804699473354598017077 42580856690575626993564101)
              ·
                refine ⟨7983910629482930061293269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42580856690575626993564101 7983910629482930061293269)
                ·
                  refine ⟨187122905378506173311561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7983910629482930061293269 187122905378506173311561)
                  ·
                    rfl

theorem cell23_3279785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 7].length) (baseStart_3279785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279785 prefixEnd_3279785 := by exact prefixLift 3279785
  have htrace : WordTrace (prefixWord ++ tailWord_3279785) baseStart_3279785 baseEnd_3279785 := by
    simpa [prefixWord, tailWord_3279785, baseEnd_3279785] using wordTrace_append hprefix tailTrace_3279785
  have hstable : (prefixWord ++ tailWord_3279785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279785).length < 2 ^ (prefixWord ++ tailWord_3279785).sum := by decide
  have hdescent : baseEnd_3279785 < baseStart_3279785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279830 : List Nat := [5, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_3279830 : Nat := 118140960795 + 3279830 * 2 ^ 59
def prefixEnd_3279830 : Nat := 4983230072969 + 3 ^ 40 * 3279830 * 2
def baseEnd_3279830 : Nat := 1684129255036007883741343

theorem tailTrace_3279830 : CollatzResearch.WordTrace tailWord_3279830 prefixEnd_3279830 1684129255036007883741343 := by
  unfold tailWord_3279830
  simp only [CollatzResearch.WordTrace]
  refine ⟨7476576731733970950828809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79750151805162356808840629 7476576731733970950828809)
  ·
    refine ⟨5607432548800478213121607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7476576731733970950828809 5607432548800478213121607)
    ·
      refine ⟨8411148823200717319682411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5607432548800478213121607 8411148823200717319682411)
      ·
        refine ⟨12616723234801075979523617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8411148823200717319682411 12616723234801075979523617)
        ·
          refine ⟨9462542426100806984642713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12616723234801075979523617 9462542426100806984642713)
          ·
            refine ⟨7096906819575605238482035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9462542426100806984642713 7096906819575605238482035)
            ·
              refine ⟨10645360229363407857723053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7096906819575605238482035 10645360229363407857723053)
              ·
                refine ⟨3992010086011277946646145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10645360229363407857723053 3992010086011277946646145)
                ·
                  refine ⟨2994007564508458459984609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3992010086011277946646145 2994007564508458459984609)
                  ·
                    refine ⟨2245505673381343844988457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2994007564508458459984609 2245505673381343844988457)
                    ·
                      refine ⟨1684129255036007883741343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245505673381343844988457 1684129255036007883741343)
                      ·
                        rfl

theorem cell23_3279830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_3279830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279830 prefixEnd_3279830 := by exact prefixLift 3279830
  have htrace : WordTrace (prefixWord ++ tailWord_3279830) baseStart_3279830 baseEnd_3279830 := by
    simpa [prefixWord, tailWord_3279830, baseEnd_3279830] using wordTrace_append hprefix tailTrace_3279830
  have hstable : (prefixWord ++ tailWord_3279830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279830).length < 2 ^ (prefixWord ++ tailWord_3279830).sum := by decide
  have hdescent : baseEnd_3279830 < baseStart_3279830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279869 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 2, 4, 2]
def baseStart_3279869 : Nat := 118140960795 + 3279869 * 2 ^ 59
def prefixEnd_3279869 : Nat := 4983230072969 + 3 ^ 40 * 3279869 * 2
def baseEnd_3279869 : Nat := 1684149280781533231153663

theorem tailTrace_3279869 : CollatzResearch.WordTrace tailWord_3279869 prefixEnd_3279869 1684149280781533231153663 := by
  unfold tailWord_3279869
  simp only [CollatzResearch.WordTrace]
  refine ⟨119626650154602244873930661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79751100103068163249287107 119626650154602244873930661)
  ·
    refine ⟨22429996903987920913861999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119626650154602244873930661 22429996903987920913861999)
    ·
      refine ⟨33644995355981881370792999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22429996903987920913861999 33644995355981881370792999)
      ·
        refine ⟨50467493033972822056189499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33644995355981881370792999 50467493033972822056189499)
        ·
          refine ⟨75701239550959233084284249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50467493033972822056189499 75701239550959233084284249)
          ·
            refine ⟨56775929663219424813213187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75701239550959233084284249 56775929663219424813213187)
            ·
              refine ⟨85163894494829137219819781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56775929663219424813213187 85163894494829137219819781)
              ·
                refine ⟨15968230217780463228716209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85163894494829137219819781 15968230217780463228716209)
                ·
                  refine ⟨11976172663335347421537157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15968230217780463228716209 11976172663335347421537157)
                  ·
                    refine ⟨2245532374375377641538217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11976172663335347421537157 2245532374375377641538217)
                    ·
                      refine ⟨1684149280781533231153663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245532374375377641538217 1684149280781533231153663)
                      ·
                        rfl

theorem cell23_3279869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_3279869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279869 prefixEnd_3279869 := by exact prefixLift 3279869
  have htrace : WordTrace (prefixWord ++ tailWord_3279869) baseStart_3279869 baseEnd_3279869 := by
    simpa [prefixWord, tailWord_3279869, baseEnd_3279869] using wordTrace_append hprefix tailTrace_3279869
  have hstable : (prefixWord ++ tailWord_3279869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279869).length < 2 ^ (prefixWord ++ tailWord_3279869).sum := by decide
  have hdescent : baseEnd_3279869 < baseStart_3279869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279870 : List Nat := [4, 2, 2, 2, 2, 2, 2, 2, 5]
def baseStart_3279870 : Nat := 118140960795 + 3279870 * 2 ^ 59
def prefixEnd_3279870 : Nat := 4983230072969 + 3 ^ 40 * 3279870 * 2
def baseEnd_3279870 : Nat := 187127754918020858582351

theorem tailTrace_3279870 : CollatzResearch.WordTrace tailWord_3279870 prefixEnd_3279870 187127754918020858582351 := by
  unfold tailWord_3279870
  simp only [CollatzResearch.WordTrace]
  refine ⟨14953335828449827755589633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79751124418399081363144709 14953335828449827755589633)
  ·
    refine ⟨11215001871337370816692225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14953335828449827755589633 11215001871337370816692225)
    ·
      refine ⟨8411251403503028112519169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11215001871337370816692225 8411251403503028112519169)
      ·
        refine ⟨6308438552627271084389377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8411251403503028112519169 6308438552627271084389377)
        ·
          refine ⟨4731328914470453313292033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6308438552627271084389377 4731328914470453313292033)
          ·
            refine ⟨3548496685852839984969025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4731328914470453313292033 3548496685852839984969025)
            ·
              refine ⟨2661372514389629988726769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3548496685852839984969025 2661372514389629988726769)
              ·
                refine ⟨1996029385792222491545077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2661372514389629988726769 1996029385792222491545077)
                ·
                  refine ⟨187127754918020858582351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1996029385792222491545077 187127754918020858582351)
                  ·
                    rfl

theorem cell23_3279870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_3279870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279870 prefixEnd_3279870 := by exact prefixLift 3279870
  have htrace : WordTrace (prefixWord ++ tailWord_3279870) baseStart_3279870 baseEnd_3279870 := by
    simpa [prefixWord, tailWord_3279870, baseEnd_3279870] using wordTrace_append hprefix tailTrace_3279870
  have hstable : (prefixWord ++ tailWord_3279870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279870).length < 2 ^ (prefixWord ++ tailWord_3279870).sum := by decide
  have hdescent : baseEnd_3279870 < baseStart_3279870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279879 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 3, 4]
def baseStart_3279879 : Nat := 118140960795 + 3279879 * 2 ^ 59
def prefixEnd_3279879 : Nat := 4983230072969 + 3 ^ 40 * 3279879 * 2
def baseEnd_3279879 : Nat := 561384805196026064009539

theorem tailTrace_3279879 : CollatzResearch.WordTrace tailWord_3279879 prefixEnd_3279879 561384805196026064009539 := by
  unfold tailWord_3279879
  simp only [CollatzResearch.WordTrace]
  refine ⟨119627014884566016581794691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79751343256377344387863127 119627014884566016581794691)
  ·
    refine ⟨179440522326849024872692037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119627014884566016581794691 179440522326849024872692037)
    ·
      refine ⟨33645097936284192163629757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179440522326849024872692037 33645097936284192163629757)
      ·
        refine ⟨12616911726106572061361159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33645097936284192163629757 12616911726106572061361159)
        ·
          refine ⟨18925367589159858092041739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12616911726106572061361159 18925367589159858092041739)
          ·
            refine ⟨28388051383739787138062609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18925367589159858092041739 28388051383739787138062609)
            ·
              refine ⟨21291038537804840353546957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28388051383739787138062609 21291038537804840353546957)
              ·
                refine ⟨7984139451676815132580109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21291038537804840353546957 7984139451676815132580109)
                ·
                  refine ⟨2994052294378805674717541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7984139451676815132580109 2994052294378805674717541)
                  ·
                    refine ⟨561384805196026064009539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2994052294378805674717541 561384805196026064009539)
                    ·
                      rfl

theorem cell23_3279879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_3279879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279879 prefixEnd_3279879 := by exact prefixLift 3279879
  have htrace : WordTrace (prefixWord ++ tailWord_3279879) baseStart_3279879 baseEnd_3279879 := by
    simpa [prefixWord, tailWord_3279879, baseEnd_3279879] using wordTrace_append hprefix tailTrace_3279879
  have hstable : (prefixWord ++ tailWord_3279879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279879).length < 2 ^ (prefixWord ++ tailWord_3279879).sum := by decide
  have hdescent : baseEnd_3279879 < baseStart_3279879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279886 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2]
def baseStart_3279886 : Nat := 118140960795 + 3279886 * 2 ^ 59
def prefixEnd_3279886 : Nat := 4983230072969 + 3 ^ 40 * 3279886 * 2
def baseEnd_3279886 : Nat := 1684158009952659664641085

theorem tailTrace_3279886 : CollatzResearch.WordTrace tailWord_3279886 prefixEnd_3279886 1684158009952659664641085 := by
  unfold tailWord_3279886
  simp only [CollatzResearch.WordTrace]
  refine ⟨14953408774442582097162439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79751513463693771184866341 14953408774442582097162439)
  ·
    refine ⟨22430113161663873145743659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14953408774442582097162439 22430113161663873145743659)
    ·
      refine ⟨33645169742495809718615489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22430113161663873145743659 33645169742495809718615489)
      ·
        refine ⟨25233877306871857288961617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33645169742495809718615489 25233877306871857288961617)
        ·
          refine ⟨18925407980153892966721213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25233877306871857288961617 18925407980153892966721213)
          ·
            refine ⟨7097027992557709862520455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18925407980153892966721213 7097027992557709862520455)
            ·
              refine ⟨10645541988836564793780683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7097027992557709862520455 10645541988836564793780683)
              ·
                refine ⟨15968312983254847190671025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10645541988836564793780683 15968312983254847190671025)
                ·
                  refine ⟨11976234737441135393003269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15968312983254847190671025 11976234737441135393003269)
                  ·
                    refine ⟨2245544013270212886188113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11976234737441135393003269 2245544013270212886188113)
                    ·
                      refine ⟨1684158009952659664641085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245544013270212886188113 1684158009952659664641085)
                      ·
                        rfl

theorem cell23_3279886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_3279886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279886 prefixEnd_3279886 := by exact prefixLift 3279886
  have htrace : WordTrace (prefixWord ++ tailWord_3279886) baseStart_3279886 baseEnd_3279886 := by
    simpa [prefixWord, tailWord_3279886, baseEnd_3279886] using wordTrace_append hprefix tailTrace_3279886
  have hstable : (prefixWord ++ tailWord_3279886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279886).length < 2 ^ (prefixWord ++ tailWord_3279886).sum := by decide
  have hdescent : baseEnd_3279886 < baseStart_3279886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279906 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_3279906 : Nat := 118140960795 + 3279906 * 2 ^ 59
def prefixEnd_3279906 : Nat := 4983230072969 + 3 ^ 40 * 3279906 * 2
def baseEnd_3279906 : Nat := 1684168279565749586390993

theorem tailTrace_3279906 : CollatzResearch.WordTrace tailWord_3279906 prefixEnd_3279906 1684168279565749586390993 := by
  unfold tailWord_3279906
  simp only [CollatzResearch.WordTrace]
  refine ⟨29906999913867050048256893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79751999770312133462018381 29906999913867050048256893)
  ·
    refine ⟨11215124967700143768096335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29906999913867050048256893 11215124967700143768096335)
    ·
      refine ⟨16822687451550215652144503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11215124967700143768096335 16822687451550215652144503)
      ·
        refine ⟨25234031177325323478216755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16822687451550215652144503 25234031177325323478216755)
        ·
          refine ⟨37851046765987985217325133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25234031177325323478216755 37851046765987985217325133)
          ·
            refine ⟨14194142537245494456496925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37851046765987985217325133 14194142537245494456496925)
            ·
              refine ⟨5322803451467060421186347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14194142537245494456496925 5322803451467060421186347)
              ·
                refine ⟨7984205177200590631779521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5322803451467060421186347 7984205177200590631779521)
                ·
                  refine ⟨5988153882900442973834641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7984205177200590631779521 5988153882900442973834641)
                  ·
                    refine ⟨4491115412175332230375981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5988153882900442973834641 4491115412175332230375981)
                    ·
                      refine ⟨1684168279565749586390993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4491115412175332230375981 1684168279565749586390993)
                      ·
                        rfl

theorem cell23_3279906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_3279906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279906 prefixEnd_3279906 := by exact prefixLift 3279906
  have htrace : WordTrace (prefixWord ++ tailWord_3279906) baseStart_3279906 baseEnd_3279906 := by
    simpa [prefixWord, tailWord_3279906, baseEnd_3279906] using wordTrace_append hprefix tailTrace_3279906
  have hstable : (prefixWord ++ tailWord_3279906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279906).length < 2 ^ (prefixWord ++ tailWord_3279906).sum := by decide
  have hdescent : baseEnd_3279906 < baseStart_3279906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279926 : List Nat := [5, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_3279926 : Nat := 118140960795 + 3279926 * 2 ^ 59
def prefixEnd_3279926 : Nat := 4983230072969 + 3 ^ 40 * 3279926 * 2
def baseEnd_3279926 : Nat := 187130949908759945348989

theorem tailTrace_3279926 : CollatzResearch.WordTrace tailWord_3279926 prefixEnd_3279926 187130949908759945348989 := by
  unfold tailWord_3279926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7476795569712233975547227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79752486076930495739170421 7476795569712233975547227)
  ·
    refine ⟨11215193354568350963320841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7476795569712233975547227 11215193354568350963320841)
    ·
      refine ⟨8411395015926263222490631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11215193354568350963320841 8411395015926263222490631)
      ·
        refine ⟨12617092523889394833735947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8411395015926263222490631 12617092523889394833735947)
        ·
          refine ⟨18925638785834092250603921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12617092523889394833735947 18925638785834092250603921)
          ·
            refine ⟨14194229089375569187952941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18925638785834092250603921 14194229089375569187952941)
            ·
              refine ⟨5322835908515838445482353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14194229089375569187952941 5322835908515838445482353)
              ·
                refine ⟨3992126931386878834111765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5322835908515838445482353 3992126931386878834111765)
                ·
                  refine ⟨187130949908759945348989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3992126931386878834111765 187130949908759945348989)
                  ·
                    rfl

theorem cell23_3279926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_3279926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279926 prefixEnd_3279926 := by exact prefixLift 3279926
  have htrace : WordTrace (prefixWord ++ tailWord_3279926) baseStart_3279926 baseEnd_3279926 := by
    simpa [prefixWord, tailWord_3279926, baseEnd_3279926] using wordTrace_append hprefix tailTrace_3279926
  have hstable : (prefixWord ++ tailWord_3279926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279926).length < 2 ^ (prefixWord ++ tailWord_3279926).sum := by decide
  have hdescent : baseEnd_3279926 < baseStart_3279926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279936 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 3, 1, 3]
def baseStart_3279936 : Nat := 118140960795 + 3279936 * 2 ^ 59
def prefixEnd_3279936 : Nat := 4983230072969 + 3 ^ 40 * 3279936 * 2
def baseEnd_3279936 : Nat := 1684183683985384469015855

theorem tailTrace_3279936 : CollatzResearch.WordTrace tailWord_3279936 prefixEnd_3279936 1684183683985384469015855 := by
  unfold tailWord_3279936
  simp only [CollatzResearch.WordTrace]
  refine ⟨59814546922679757658309831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79752729230239676877746441 59814546922679757658309831)
  ·
    refine ⟨89721820384019636487464747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59814546922679757658309831 89721820384019636487464747)
    ·
      refine ⟨134582730576029454731197121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89721820384019636487464747 134582730576029454731197121)
      ·
        refine ⟨100937047932022091048397841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134582730576029454731197121 100937047932022091048397841)
        ·
          refine ⟨75702785949016568286298381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100937047932022091048397841 75702785949016568286298381)
          ·
            refine ⟨28388544730881213107361893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75702785949016568286298381 28388544730881213107361893)
            ·
              refine ⟨5322852137040227457630355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28388544730881213107361893 5322852137040227457630355)
              ·
                refine ⟨7984278205560341186445533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5322852137040227457630355 7984278205560341186445533)
                ·
                  refine ⟨2994104327085127944917075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7984278205560341186445533 2994104327085127944917075)
                  ·
                    refine ⟨4491156490627691917375613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2994104327085127944917075 4491156490627691917375613)
                    ·
                      refine ⟨1684183683985384469015855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4491156490627691917375613 1684183683985384469015855)
                      ·
                        rfl

theorem cell23_3279936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_3279936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279936 prefixEnd_3279936 := by exact prefixLift 3279936
  have htrace : WordTrace (prefixWord ++ tailWord_3279936) baseStart_3279936 baseEnd_3279936 := by
    simpa [prefixWord, tailWord_3279936, baseEnd_3279936] using wordTrace_append hprefix tailTrace_3279936
  have hstable : (prefixWord ++ tailWord_3279936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279936).length < 2 ^ (prefixWord ++ tailWord_3279936).sum := by decide
  have hdescent : baseEnd_3279936 < baseStart_3279936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279959 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 1, 8, 2]
def baseStart_3279959 : Nat := 118140960795 + 3279959 * 2 ^ 59
def prefixEnd_3279959 : Nat := 4983230072969 + 3 ^ 40 * 3279959 * 2
def baseEnd_3279959 : Nat := 1684195494040437879028249

theorem tailTrace_3279959 : CollatzResearch.WordTrace tailWord_3279959 prefixEnd_3279959 1684195494040437879028249 := by
  unfold tailWord_3279959
  simp only [CollatzResearch.WordTrace]
  refine ⟨119629932724276190244706931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79753288482850793496471287 119629932724276190244706931)
  ·
    refine ⟨179444899086414285367060397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119629932724276190244706931 179444899086414285367060397)
    ·
      refine ⟨67291837157405357012647649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179444899086414285367060397 67291837157405357012647649)
      ·
        refine ⟨50468877868054017759485737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67291837157405357012647649 50468877868054017759485737)
        ·
          refine ⟨37851658401040513319614303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50468877868054017759485737 37851658401040513319614303)
          ·
            refine ⟨56777487601560769979421455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37851658401040513319614303 56777487601560769979421455)
            ·
              refine ⟨85166231402341154969132183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56777487601560769979421455 85166231402341154969132183)
              ·
                refine ⟨127749347103511732453698275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85166231402341154969132183 127749347103511732453698275)
                ·
                  refine ⟨191624020655267598680547413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127749347103511732453698275 191624020655267598680547413)
                  ·
                    refine ⟨2245593992053917172037665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 191624020655267598680547413 2245593992053917172037665)
                    ·
                      refine ⟨1684195494040437879028249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2245593992053917172037665 1684195494040437879028249)
                      ·
                        rfl

theorem cell23_3279959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_3279959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279959 prefixEnd_3279959 := by exact prefixLift 3279959
  have htrace : WordTrace (prefixWord ++ tailWord_3279959) baseStart_3279959 baseEnd_3279959 := by
    simpa [prefixWord, tailWord_3279959, baseEnd_3279959] using wordTrace_append hprefix tailTrace_3279959
  have hstable : (prefixWord ++ tailWord_3279959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279959).length < 2 ^ (prefixWord ++ tailWord_3279959).sum := by decide
  have hdescent : baseEnd_3279959 < baseStart_3279959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279969 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 4, 4]
def baseStart_3279969 : Nat := 118140960795 + 3279969 * 2 ^ 59
def prefixEnd_3279969 : Nat := 4983230072969 + 3 ^ 40 * 3279969 * 2
def baseEnd_3279969 : Nat := 561400209615660946634401

theorem tailTrace_3279969 : CollatzResearch.WordTrace tailWord_3279969 prefixEnd_3279969 561400209615660946634401 := by
  unfold tailWord_3279969
  simp only [CollatzResearch.WordTrace]
  refine ⟨119630297454239961952570961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79753531636159974635047307 119630297454239961952570961)
  ·
    refine ⟨89722723090679971464428221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119630297454239961952570961 89722723090679971464428221)
    ·
      refine ⟨33646021159004989299160583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89722723090679971464428221 33646021159004989299160583)
      ·
        refine ⟨50469031738507483948740875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33646021159004989299160583 50469031738507483948740875)
        ·
          refine ⟨75703547607761225923111313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50469031738507483948740875 75703547607761225923111313)
          ·
            refine ⟨56777660705820919442333485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75703547607761225923111313 56777660705820919442333485)
            ·
              refine ⟨21291622764682844790875057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56777660705820919442333485 21291622764682844790875057)
              ·
                refine ⟨15968717073512133593156293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21291622764682844790875057 15968717073512133593156293)
                ·
                  refine ⟨2994134451283525048716805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15968717073512133593156293 2994134451283525048716805)
                  ·
                    refine ⟨561400209615660946634401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2994134451283525048716805 561400209615660946634401)
                    ·
                      rfl

theorem cell23_3279969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_3279969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279969 prefixEnd_3279969 := by exact prefixLift 3279969
  have htrace : WordTrace (prefixWord ++ tailWord_3279969) baseStart_3279969 baseEnd_3279969 := by
    simpa [prefixWord, tailWord_3279969, baseEnd_3279969] using wordTrace_append hprefix tailTrace_3279969
  have hstable : (prefixWord ++ tailWord_3279969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279969).length < 2 ^ (prefixWord ++ tailWord_3279969).sum := by decide
  have hdescent : baseEnd_3279969 < baseStart_3279969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3279986 : List Nat := [3, 2, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_3279986 : Nat := 118140960795 + 3279986 * 2 ^ 59
def prefixEnd_3279986 : Nat := 4983230072969 + 3 ^ 40 * 3279986 * 2
def baseEnd_3279986 : Nat := 561403119339369757796875

theorem tailTrace_3279986 : CollatzResearch.WordTrace tailWord_3279986 prefixEnd_3279986 561403119339369757796875 := by
  unfold tailWord_3279986
  simp only [CollatzResearch.WordTrace]
  refine ⟨29907729373794593463984953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79753944996785582570626541 29907729373794593463984953)
  ·
    refine ⟨22430797030345945097988715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29907729373794593463984953 22430797030345945097988715)
    ·
      refine ⟨33646195545518917646983073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22430797030345945097988715 33646195545518917646983073)
      ·
        refine ⟨25234646659139188235237305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33646195545518917646983073 25234646659139188235237305)
        ·
          refine ⟨18925984994354391176427979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25234646659139188235237305 18925984994354391176427979)
          ·
            refine ⟨28388977491531586764641969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18925984994354391176427979 28388977491531586764641969)
            ·
              refine ⟨21291733118648690073481477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28388977491531586764641969 21291733118648690073481477)
              ·
                refine ⟨3992199959746629388777777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21291733118648690073481477 3992199959746629388777777)
                ·
                  refine ⟨2994149969809972041583333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3992199959746629388777777 2994149969809972041583333)
                  ·
                    refine ⟨561403119339369757796875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2994149969809972041583333 561403119339369757796875)
                    ·
                      rfl

theorem cell23_3279986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_3279986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3279986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3279986 prefixEnd_3279986 := by exact prefixLift 3279986
  have htrace : WordTrace (prefixWord ++ tailWord_3279986) baseStart_3279986 baseEnd_3279986 := by
    simpa [prefixWord, tailWord_3279986, baseEnd_3279986] using wordTrace_append hprefix tailTrace_3279986
  have hstable : (prefixWord ++ tailWord_3279986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3279986).length < 2 ^ (prefixWord ++ tailWord_3279986).sum := by decide
  have hdescent : baseEnd_3279986 < baseStart_3279986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3279986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3280026 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3280026 : Nat := 118140960795 + 3280026 * 2 ^ 59
def prefixEnd_3280026 : Nat := 4983230072969 + 3 ^ 40 * 3280026 * 2
def baseEnd_3280026 : Nat := 1684229897244289116890441

theorem tailTrace_3280026 : CollatzResearch.WordTrace tailWord_3280026 prefixEnd_3280026 1684229897244289116890441 := by
  unfold tailWord_3280026
  simp only [CollatzResearch.WordTrace]
  refine ⟨29908094103758365171848983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79754917610022307124930621 29908094103758365171848983)
  ·
    refine ⟨44862141155637547757773475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29908094103758365171848983 44862141155637547757773475)
    ·
      refine ⟨67293211733456321636660213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44862141155637547757773475 67293211733456321636660213)
      ·
        refine ⟨6308738600011530153436895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67293211733456321636660213 6308738600011530153436895)
        ·
          refine ⟨9463107900017295230155343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6308738600011530153436895 9463107900017295230155343)
          ·
            refine ⟨14194661850025942845233015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9463107900017295230155343 14194661850025942845233015)
            ·
              refine ⟨21291992775038914267849523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14194661850025942845233015 21291992775038914267849523)
              ·
                refine ⟨31937989162558371401774285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21291992775038914267849523 31937989162558371401774285)
                ·
                  refine ⟨11976745935959389275665357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31937989162558371401774285 11976745935959389275665357)
                  ·
                    refine ⟨4491279725984770978374509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11976745935959389275665357 4491279725984770978374509)
                    ·
                      refine ⟨1684229897244289116890441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4491279725984770978374509 1684229897244289116890441)
                      ·
                        rfl

theorem cell23_3280026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3280026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3280026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3280026 prefixEnd_3280026 := by exact prefixLift 3280026
  have htrace : WordTrace (prefixWord ++ tailWord_3280026) baseStart_3280026 baseEnd_3280026 := by
    simpa [prefixWord, tailWord_3280026, baseEnd_3280026] using wordTrace_append hprefix tailTrace_3280026
  have hstable : (prefixWord ++ tailWord_3280026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3280026).length < 2 ^ (prefixWord ++ tailWord_3280026).sum := by decide
  have hdescent : baseEnd_3280026 < baseStart_3280026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3280026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
