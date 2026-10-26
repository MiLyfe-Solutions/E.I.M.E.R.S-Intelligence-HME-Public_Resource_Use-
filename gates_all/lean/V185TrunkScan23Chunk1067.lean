import V185TrunkScan23Chunk1066

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6316176 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 4]
def baseStart_6316176 : Nat := 118140960795 + 6316176 * 2 ^ 59
def prefixEnd_6316176 : Nat := 4983230072969 + 3 ^ 40 * 6316176 * 2
def baseEnd_6316176 : Nat := 3243234186392585166052441

theorem tailTrace_6316176 : CollatzResearch.WordTrace tailWord_6316176 prefixEnd_6316176 3243234186392585166052441 := by
  unfold tailWord_6316176
  simp only [CollatzResearch.WordTrace]
  refine ⟨115184932182790271912432191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153579909577053695883242921 115184932182790271912432191)
  ·
    refine ⟨172777398274185407868648287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115184932182790271912432191 172777398274185407868648287)
    ·
      refine ⟨259166097411278111802972431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172777398274185407868648287 259166097411278111802972431)
      ·
        refine ⟨388749146116917167704458647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259166097411278111802972431 388749146116917167704458647)
        ·
          refine ⟨583123719175375751556687971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388749146116917167704458647 583123719175375751556687971)
          ·
            refine ⟨874685578763063627335031957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583123719175375751556687971 874685578763063627335031957)
            ·
              refine ⟨41000886504518607531329623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 874685578763063627335031957 41000886504518607531329623)
              ·
                refine ⟨61501329756777911296994435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41000886504518607531329623 61501329756777911296994435)
                ·
                  refine ⟨92251994635166866945491653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61501329756777911296994435 92251994635166866945491653)
                  ·
                    refine ⟨17297248994093787552279685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92251994635166866945491653 17297248994093787552279685)
                    ·
                      refine ⟨3243234186392585166052441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17297248994093787552279685 3243234186392585166052441)
                      ·
                        rfl

theorem cell23_6316176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_6316176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316176 prefixEnd_6316176 := by exact prefixLift 6316176
  have htrace : WordTrace (prefixWord ++ tailWord_6316176) baseStart_6316176 baseEnd_6316176 := by
    simpa [prefixWord, tailWord_6316176, baseEnd_6316176] using wordTrace_append hprefix tailTrace_6316176
  have hstable : (prefixWord ++ tailWord_6316176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316176).length < 2 ^ (prefixWord ++ tailWord_6316176).sum := by decide
  have hdescent : baseEnd_6316176 < baseStart_6316176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316184 : List Nat := [2, 1, 2, 4, 3, 2, 1, 2, 1, 3, 2]
def baseStart_6316184 : Nat := 118140960795 + 6316184 * 2 ^ 59
def prefixEnd_6316184 : Nat := 4983230072969 + 3 ^ 40 * 6316184 * 2
def baseEnd_6316184 : Nat := 3243238294237821134752405

theorem tailTrace_6316184 : CollatzResearch.WordTrace tailWord_6316184 prefixEnd_6316184 3243238294237821134752405 := by
  unfold tailWord_6316184
  simp only [CollatzResearch.WordTrace]
  refine ⟨115185078074775780595577803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153580104099701040794103737 115185078074775780595577803)
  ·
    refine ⟨172777617112163670893366705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115185078074775780595577803 172777617112163670893366705)
    ·
      refine ⟨129583212834122753170025029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172777617112163670893366705 129583212834122753170025029)
      ·
        refine ⟨24296852406398016219379693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129583212834122753170025029 24296852406398016219379693)
        ·
          refine ⟨9111319652399256082267385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24296852406398016219379693 9111319652399256082267385)
          ·
            refine ⟨6833489739299442061700539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9111319652399256082267385 6833489739299442061700539)
            ·
              refine ⟨10250234608949163092550809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6833489739299442061700539 10250234608949163092550809)
              ·
                refine ⟨7687675956711872319413107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10250234608949163092550809 7687675956711872319413107)
                ·
                  refine ⟨11531513935067808479119661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7687675956711872319413107 11531513935067808479119661)
                  ·
                    refine ⟨4324317725650428179669873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11531513935067808479119661 4324317725650428179669873)
                    ·
                      refine ⟨3243238294237821134752405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4324317725650428179669873 3243238294237821134752405)
                      ·
                        rfl

theorem cell23_6316184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_6316184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316184 prefixEnd_6316184 := by exact prefixLift 6316184
  have htrace : WordTrace (prefixWord ++ tailWord_6316184) baseStart_6316184 baseEnd_6316184 := by
    simpa [prefixWord, tailWord_6316184, baseEnd_6316184] using wordTrace_append hprefix tailTrace_6316184
  have hstable : (prefixWord ++ tailWord_6316184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316184).length < 2 ^ (prefixWord ++ tailWord_6316184).sum := by decide
  have hdescent : baseEnd_6316184 < baseStart_6316184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316360 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 2, 6, 2]
def baseStart_6316360 : Nat := 118140960795 + 6316360 * 2 ^ 59
def prefixEnd_6316360 : Nat := 4983230072969 + 3 ^ 40 * 6316360 * 2
def baseEnd_6316360 : Nat := 3243328666833012446151595

theorem tailTrace_6316360 : CollatzResearch.WordTrace tailWord_6316360 prefixEnd_6316360 3243328666833012446151595 := by
  unfold tailWord_6316360
  simp only [CollatzResearch.WordTrace]
  refine ⟨115188287698456971624781267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153584383597942628833041689 115188287698456971624781267)
  ·
    refine ⟨172782431547685457437171901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115188287698456971624781267 172782431547685457437171901)
    ·
      refine ⟨64793411830382046538939463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172782431547685457437171901 64793411830382046538939463)
      ·
        refine ⟨97190117745573069808409195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64793411830382046538939463 97190117745573069808409195)
        ·
          refine ⟨145785176618359604712613793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97190117745573069808409195 145785176618359604712613793)
          ·
            refine ⟨109338882463769703534460345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145785176618359604712613793 109338882463769703534460345)
            ·
              refine ⟨82004161847827277650845259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109338882463769703534460345 82004161847827277650845259)
              ·
                refine ⟨123006242771740916476267889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82004161847827277650845259 123006242771740916476267889)
                ·
                  refine ⟨92254682078805687357200917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123006242771740916476267889 92254682078805687357200917)
                  ·
                    refine ⟨4324438222444016594868793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92254682078805687357200917 4324438222444016594868793)
                    ·
                      refine ⟨3243328666833012446151595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4324438222444016594868793 3243328666833012446151595)
                      ·
                        rfl

theorem cell23_6316360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_6316360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316360 prefixEnd_6316360 := by exact prefixLift 6316360
  have htrace : WordTrace (prefixWord ++ tailWord_6316360) baseStart_6316360 baseEnd_6316360 := by
    simpa [prefixWord, tailWord_6316360, baseEnd_6316360] using wordTrace_append hprefix tailTrace_6316360
  have hstable : (prefixWord ++ tailWord_6316360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316360).length < 2 ^ (prefixWord ++ tailWord_6316360).sum := by decide
  have hdescent : baseEnd_6316360 < baseStart_6316360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316370 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_6316370 : Nat := 118140960795 + 6316370 * 2 ^ 59
def prefixEnd_6316370 : Nat := 4983230072969 + 3 ^ 40 * 6316370 * 2
def baseEnd_6316370 : Nat := 1081111267213185802342183

theorem tailTrace_6316370 : CollatzResearch.WordTrace tailWord_6316370 prefixEnd_6316370 1081111267213185802342183 := by
  unfold tailWord_6316370
  simp only [CollatzResearch.WordTrace]
  refine ⟨57594235031719428739356641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153584626751251809971617709 57594235031719428739356641)
  ·
    refine ⟨43195676273789571554517481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57594235031719428739356641 43195676273789571554517481)
    ·
      refine ⟨32396757205342178665888111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43195676273789571554517481 32396757205342178665888111)
      ·
        refine ⟨48595135808013267998832167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32396757205342178665888111 48595135808013267998832167)
        ·
          refine ⟨72892703712019901998248251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48595135808013267998832167 72892703712019901998248251)
          ·
            refine ⟨109339055568029852997372377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72892703712019901998248251 109339055568029852997372377)
            ·
              refine ⟨82004291676022389748029283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109339055568029852997372377 82004291676022389748029283)
              ·
                refine ⟨123006437514033584622043925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82004291676022389748029283 123006437514033584622043925)
                ·
                  refine ⟨5765926758470324279158309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123006437514033584622043925 5765926758470324279158309)
                  ·
                    refine ⟨1081111267213185802342183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5765926758470324279158309 1081111267213185802342183)
                    ·
                      rfl

theorem cell23_6316370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_6316370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316370 prefixEnd_6316370 := by exact prefixLift 6316370
  have htrace : WordTrace (prefixWord ++ tailWord_6316370) baseStart_6316370 baseEnd_6316370 := by
    simpa [prefixWord, tailWord_6316370, baseEnd_6316370] using wordTrace_append hprefix tailTrace_6316370
  have hstable : (prefixWord ++ tailWord_6316370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316370).length < 2 ^ (prefixWord ++ tailWord_6316370).sum := by decide
  have hdescent : baseEnd_6316370 < baseStart_6316370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316387 : List Nat := [1, 1, 1, 5, 2, 1, 4, 2, 2, 4]
def baseStart_6316387 : Nat := 118140960795 + 6316387 * 2 ^ 59
def prefixEnd_6316387 : Nat := 4983230072969 + 3 ^ 40 * 6316387 * 2
def baseEnd_6316387 : Nat := 1081114176936894613504657

theorem tailTrace_6316387 : CollatzResearch.WordTrace tailWord_6316387 prefixEnd_6316387 1081114176936894613504657 := by
  unfold tailWord_6316387
  simp only [CollatzResearch.WordTrace]
  refine ⟨230377560167816126860795415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153585040111877417907196943 230377560167816126860795415)
  ·
    refine ⟨345566340251724190291193123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230377560167816126860795415 345566340251724190291193123)
    ·
      refine ⟨518349510377586285436789685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345566340251724190291193123 518349510377586285436789685)
      ·
        refine ⟨48595266597898714259699033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 518349510377586285436789685 48595266597898714259699033)
        ·
          refine ⟨36446449948424035694774275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48595266597898714259699033 36446449948424035694774275)
          ·
            refine ⟨54669674922636053542161413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36446449948424035694774275 54669674922636053542161413)
            ·
              refine ⟨10250564047994260039155265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54669674922636053542161413 10250564047994260039155265)
              ·
                refine ⟨7687923035995695029366449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10250564047994260039155265 7687923035995695029366449)
                ·
                  refine ⟨5765942276996771272024837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7687923035995695029366449 5765942276996771272024837)
                  ·
                    refine ⟨1081114176936894613504657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5765942276996771272024837 1081114176936894613504657)
                    ·
                      rfl

theorem cell23_6316387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 4].length) (baseStart_6316387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316387 prefixEnd_6316387 := by exact prefixLift 6316387
  have htrace : WordTrace (prefixWord ++ tailWord_6316387) baseStart_6316387 baseEnd_6316387 := by
    simpa [prefixWord, tailWord_6316387, baseEnd_6316387] using wordTrace_append hprefix tailTrace_6316387
  have hstable : (prefixWord ++ tailWord_6316387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316387).length < 2 ^ (prefixWord ++ tailWord_6316387).sum := by decide
  have hdescent : baseEnd_6316387 < baseStart_6316387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316400 : List Nat := [2, 1, 1, 1, 4, 5, 1, 8]
def baseStart_6316400 : Nat := 118140960795 + 6316400 * 2 ^ 59
def prefixEnd_6316400 : Nat := 4983230072969 + 3 ^ 40 * 6316400 * 2
def baseEnd_6316400 : Nat := 120124044668858973690793

theorem tailTrace_6316400 : CollatzResearch.WordTrace tailWord_6316400 prefixEnd_6316400 120124044668858973690793 := by
  unfold tailWord_6316400
  simp only [CollatzResearch.WordTrace]
  refine ⟨115189017158384515040509327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153585356211179353387345769 115189017158384515040509327)
  ·
    refine ⟨172783525737576772560763991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115189017158384515040509327 172783525737576772560763991)
    ·
      refine ⟨259175288606365158841145987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172783525737576772560763991 259175288606365158841145987)
      ·
        refine ⟨388762932909547738261718981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259175288606365158841145987 388762932909547738261718981)
        ·
          refine ⟨72893049920540200924072309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 388762932909547738261718981 72893049920540200924072309)
          ·
            refine ⟨6833723430050643836631779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72893049920540200924072309 6833723430050643836631779)
            ·
              refine ⟨10250585145075965754947669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6833723430050643836631779 10250585145075965754947669)
              ·
                refine ⟨120124044668858973690793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10250585145075965754947669 120124044668858973690793)
                ·
                  rfl

theorem cell23_6316400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 8].length) (baseStart_6316400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316400 prefixEnd_6316400 := by exact prefixLift 6316400
  have htrace : WordTrace (prefixWord ++ tailWord_6316400) baseStart_6316400 baseEnd_6316400 := by
    simpa [prefixWord, tailWord_6316400, baseEnd_6316400] using wordTrace_append hprefix tailTrace_6316400
  have hstable : (prefixWord ++ tailWord_6316400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316400).length < 2 ^ (prefixWord ++ tailWord_6316400).sum := by decide
  have hdescent : baseEnd_6316400 < baseStart_6316400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316417 : List Nat := [1, 2, 4, 3, 1, 2, 3, 7]
def baseStart_6316417 : Nat := 118140960795 + 6316417 * 2 ^ 59
def prefixEnd_6316417 : Nat := 4983230072969 + 3 ^ 40 * 6316417 * 2
def baseEnd_6316417 : Nat := 120124367971493286042179

theorem tailTrace_6316417 : CollatzResearch.WordTrace tailWord_6316417 prefixEnd_6316417 120124367971493286042179 := by
  unfold tailWord_6316417
  simp only [CollatzResearch.WordTrace]
  refine ⟨230378654357707441984387505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153585769571804961322925003 230378654357707441984387505)
  ·
    refine ⟨172783990768280581488290629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230378654357707441984387505 172783990768280581488290629)
    ·
      refine ⟨32396998269052609029054493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172783990768280581488290629 32396998269052609029054493)
      ·
        refine ⟨12148874350894728385895435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32396998269052609029054493 12148874350894728385895435)
        ·
          refine ⟨18223311526342092578843153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12148874350894728385895435 18223311526342092578843153)
          ·
            refine ⟨13667483644756569434132365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18223311526342092578843153 13667483644756569434132365)
            ·
              refine ⟨5125306366783713537799637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13667483644756569434132365 5125306366783713537799637)
              ·
                refine ⟨120124367971493286042179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5125306366783713537799637 120124367971493286042179)
                ·
                  rfl

theorem cell23_6316417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 7].length) (baseStart_6316417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316417 prefixEnd_6316417 := by exact prefixLift 6316417
  have htrace : WordTrace (prefixWord ++ tailWord_6316417) baseStart_6316417 baseEnd_6316417 := by
    simpa [prefixWord, tailWord_6316417, baseEnd_6316417] using wordTrace_append hprefix tailTrace_6316417
  have hstable : (prefixWord ++ tailWord_6316417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316417).length < 2 ^ (prefixWord ++ tailWord_6316417).sum := by decide
  have hdescent : baseEnd_6316417 < baseStart_6316417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316438 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_6316438 : Nat := 118140960795 + 6316438 * 2 ^ 59
def prefixEnd_6316438 : Nat := 4983230072969 + 3 ^ 40 * 6316438 * 2
def baseEnd_6316438 : Nat := 1081122906108021046992079

theorem tailTrace_6316438 : CollatzResearch.WordTrace tailWord_6316438 prefixEnd_6316438 1081122906108021046992079 := by
  unfold tailWord_6316438
  simp only [CollatzResearch.WordTrace]
  refine ⟨14398713768164460160681373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153586280193754241713934645 14398713768164460160681373)
  ·
    refine ⟨5399517663061672560255515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14398713768164460160681373 5399517663061672560255515)
    ·
      refine ⟨8099276494592508840383273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5399517663061672560255515 8099276494592508840383273)
      ·
        refine ⟨6074457370944381630287455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8099276494592508840383273 6074457370944381630287455)
        ·
          refine ⟨9111686056416572445431183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6074457370944381630287455 9111686056416572445431183)
          ·
            refine ⟨13667529084624858668146775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9111686056416572445431183 13667529084624858668146775)
            ·
              refine ⟨20501293626937288002220163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13667529084624858668146775 20501293626937288002220163)
              ·
                refine ⟨30751940440405932003330245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20501293626937288002220163 30751940440405932003330245)
                ·
                  refine ⟨5765988832576112250624421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30751940440405932003330245 5765988832576112250624421)
                  ·
                    refine ⟨1081122906108021046992079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5765988832576112250624421 1081122906108021046992079)
                    ·
                      rfl

theorem cell23_6316438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_6316438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316438 prefixEnd_6316438 := by exact prefixLift 6316438
  have htrace : WordTrace (prefixWord ++ tailWord_6316438) baseStart_6316438 baseEnd_6316438 := by
    simpa [prefixWord, tailWord_6316438, baseEnd_6316438] using wordTrace_append hprefix tailTrace_6316438
  have hstable : (prefixWord ++ tailWord_6316438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316438).length < 2 ^ (prefixWord ++ tailWord_6316438).sum := by decide
  have hdescent : baseEnd_6316438 < baseStart_6316438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316458 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_6316458 : Nat := 118140960795 + 6316458 * 2 ^ 59
def prefixEnd_6316458 : Nat := 4983230072969 + 3 ^ 40 * 6316458 * 2
def baseEnd_6316458 : Nat := 3243378987937153062726145

theorem tailTrace_6316458 : CollatzResearch.WordTrace tailWord_6316458 prefixEnd_6316458 3243378987937153062726145 := by
  unfold tailWord_6316458
  simp only [CollatzResearch.WordTrace]
  refine ⟨57595037437639726496657507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153586766500372603991086685 57595037437639726496657507)
  ·
    refine ⟨86392556156459589744986261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57595037437639726496657507 86392556156459589744986261)
    ·
      refine ⟨4049651069834043269296231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86392556156459589744986261 4049651069834043269296231)
      ·
        refine ⟨6074476604751064903944347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4049651069834043269296231 6074476604751064903944347)
        ·
          refine ⟨9111714907126597355916521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6074476604751064903944347 9111714907126597355916521)
          ·
            refine ⟨6833786180344948016937391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9111714907126597355916521 6833786180344948016937391)
            ·
              refine ⟨10250679270517422025406087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6833786180344948016937391 10250679270517422025406087)
              ·
                refine ⟨15376018905776133038109131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10250679270517422025406087 15376018905776133038109131)
                ·
                  refine ⟨23064028358664199557163697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15376018905776133038109131 23064028358664199557163697)
                  ·
                    refine ⟨17298021268998149667872773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23064028358664199557163697 17298021268998149667872773)
                    ·
                      refine ⟨3243378987937153062726145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17298021268998149667872773 3243378987937153062726145)
                      ·
                        rfl

theorem cell23_6316458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_6316458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316458 prefixEnd_6316458 := by exact prefixLift 6316458
  have htrace : WordTrace (prefixWord ++ tailWord_6316458) baseStart_6316458 baseEnd_6316458 := by
    simpa [prefixWord, tailWord_6316458, baseEnd_6316458] using wordTrace_append hprefix tailTrace_6316458
  have hstable : (prefixWord ++ tailWord_6316458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316458).length < 2 ^ (prefixWord ++ tailWord_6316458).sum := by decide
  have hdescent : baseEnd_6316458 < baseStart_6316458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316461 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_6316461 : Nat := 118140960795 + 6316461 * 2 ^ 59
def prefixEnd_6316461 : Nat := 4983230072969 + 3 ^ 40 * 6316461 * 2
def baseEnd_6316461 : Nat := 3243380528379116550988631

theorem tailTrace_6316461 : CollatzResearch.WordTrace tailWord_6316461 prefixEnd_6316461 3243380528379116550988631 := by
  unfold tailWord_6316461
  simp only [CollatzResearch.WordTrace]
  refine ⟨230380259169548037498989237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153586839446365358332659491 230380259169548037498989237)
  ·
    refine ⟨21598149297145128515530241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 230380259169548037498989237 21598149297145128515530241)
    ·
      refine ⟨16198611972858846386647681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21598149297145128515530241 16198611972858846386647681)
      ·
        refine ⟨12148958979644134789985761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16198611972858846386647681 12148958979644134789985761)
        ·
          refine ⟨9111719234733101092489321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12148958979644134789985761 9111719234733101092489321)
          ·
            refine ⟨6833789426049825819366991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9111719234733101092489321 6833789426049825819366991)
            ·
              refine ⟨10250684139074738729050487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6833789426049825819366991 10250684139074738729050487)
              ·
                refine ⟨15376026208612108093575731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10250684139074738729050487 15376026208612108093575731)
                ·
                  refine ⟨23064039312918162140363597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15376026208612108093575731 23064039312918162140363597)
                  ·
                    refine ⟨8649014742344310802636349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23064039312918162140363597 8649014742344310802636349)
                    ·
                      refine ⟨3243380528379116550988631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8649014742344310802636349 3243380528379116550988631)
                      ·
                        rfl

theorem cell23_6316461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_6316461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316461 prefixEnd_6316461 := by exact prefixLift 6316461
  have htrace : WordTrace (prefixWord ++ tailWord_6316461) baseStart_6316461 baseEnd_6316461 := by
    simpa [prefixWord, tailWord_6316461, baseEnd_6316461] using wordTrace_append hprefix tailTrace_6316461
  have hstable : (prefixWord ++ tailWord_6316461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316461).length < 2 ^ (prefixWord ++ tailWord_6316461).sum := by decide
  have hdescent : baseEnd_6316461 < baseStart_6316461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316468 : List Nat := [2, 5, 2, 2, 2, 1, 2, 7]
def baseStart_6316468 : Nat := 118140960795 + 6316468 * 2 ^ 59
def prefixEnd_6316468 : Nat := 4983230072969 + 3 ^ 40 * 6316468 * 2
def baseEnd_6316468 : Nat := 120125337879396223096337

theorem tailTrace_6316468 : CollatzResearch.WordTrace tailWord_6316468 prefixEnd_6316468 120125337879396223096337 := by
  unfold tailWord_6316468
  simp only [CollatzResearch.WordTrace]
  refine ⟨115190257240261338847247029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153587009653681785129662705 115190257240261338847247029)
  ·
    refine ⟨10799086616274500516929409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115190257240261338847247029 10799086616274500516929409)
    ·
      refine ⟨8099314962205875387697057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10799086616274500516929409 8099314962205875387697057)
      ·
        refine ⟨6074486221654406540772793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8099314962205875387697057 6074486221654406540772793)
        ·
          refine ⟨4555864666240804905579595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6074486221654406540772793 4555864666240804905579595)
          ·
            refine ⟨6833796999361207358369393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4555864666240804905579595 6833796999361207358369393)
            ·
              refine ⟨5125347749520905518777045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6833796999361207358369393 5125347749520905518777045)
              ·
                refine ⟨120125337879396223096337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5125347749520905518777045 120125337879396223096337)
                ·
                  rfl

theorem cell23_6316468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 7].length) (baseStart_6316468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316468 prefixEnd_6316468 := by exact prefixLift 6316468
  have htrace : WordTrace (prefixWord ++ tailWord_6316468) baseStart_6316468 baseEnd_6316468 := by
    simpa [prefixWord, tailWord_6316468, baseEnd_6316468] using wordTrace_append hprefix tailTrace_6316468
  have hstable : (prefixWord ++ tailWord_6316468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316468).length < 2 ^ (prefixWord ++ tailWord_6316468).sum := by decide
  have hdescent : baseEnd_6316468 < baseStart_6316468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316564 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_6316564 : Nat := 118140960795 + 6316564 * 2 ^ 59
def prefixEnd_6316564 : Nat := 4983230072969 + 3 ^ 40 * 6316564 * 2
def baseEnd_6316564 : Nat := 3243433416886529648000657

theorem tailTrace_6316564 : CollatzResearch.WordTrace tailWord_6316564 prefixEnd_6316564 3243433416886529648000657 := by
  unfold tailWord_6316564
  simp only [CollatzResearch.WordTrace]
  refine ⟨115192007944087443044994373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153589343925449924059992497 115192007944087443044994373)
  ·
    refine ⟨21598501489516395570936445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115192007944087443044994373 21598501489516395570936445)
    ·
      refine ⟨8099438058568648339101167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21598501489516395570936445 8099438058568648339101167)
      ·
        refine ⟨12149157087852972508651751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8099438058568648339101167 12149157087852972508651751)
        ·
          refine ⟨18223735631779458762977627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12149157087852972508651751 18223735631779458762977627)
          ·
            refine ⟨27335603447669188144466441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18223735631779458762977627 27335603447669188144466441)
            ·
              refine ⟨20501702585751891108349831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27335603447669188144466441 20501702585751891108349831)
              ·
                refine ⟨30752553878627836662524747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20501702585751891108349831 30752553878627836662524747)
                ·
                  refine ⟨46128830817941754993787121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30752553878627836662524747 46128830817941754993787121)
                  ·
                    refine ⟨34596623113456316245340341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46128830817941754993787121 34596623113456316245340341)
                    ·
                      refine ⟨3243433416886529648000657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34596623113456316245340341 3243433416886529648000657)
                      ·
                        rfl

theorem cell23_6316564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_6316564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316564 prefixEnd_6316564 := by exact prefixLift 6316564
  have htrace : WordTrace (prefixWord ++ tailWord_6316564) baseStart_6316564 baseEnd_6316564 := by
    simpa [prefixWord, tailWord_6316564, baseEnd_6316564] using wordTrace_append hprefix tailTrace_6316564
  have hstable : (prefixWord ++ tailWord_6316564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316564).length < 2 ^ (prefixWord ++ tailWord_6316564).sum := by decide
  have hdescent : baseEnd_6316564 < baseStart_6316564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316577 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_6316577 : Nat := 118140960795 + 6316577 * 2 ^ 59
def prefixEnd_6316577 : Nat := 4983230072969 + 3 ^ 40 * 6316577 * 2
def baseEnd_6316577 : Nat := 3243440092135038097138097

theorem tailTrace_6316577 : CollatzResearch.WordTrace tailWord_6316577 prefixEnd_6316577 3243440092135038097138097 := by
  unfold tailWord_6316577
  simp only [CollatzResearch.WordTrace]
  refine ⟨230384490037127789310211985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153589660024751859540141323 230384490037127789310211985)
  ·
    refine ⟨172788367527845841982658989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230384490037127789310211985 172788367527845841982658989)
    ·
      refine ⟨64795637822942190743497121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172788367527845841982658989 64795637822942190743497121)
      ·
        refine ⟨48596728367206643057622841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64795637822942190743497121 48596728367206643057622841)
        ·
          refine ⟨36447546275404982293217131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48596728367206643057622841 36447546275404982293217131)
          ·
            refine ⟨54671319413107473439825697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36447546275404982293217131 54671319413107473439825697)
            ·
              refine ⟨41003489559830605079869273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54671319413107473439825697 41003489559830605079869273)
              ·
                refine ⟨30752617169872953809901955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41003489559830605079869273 30752617169872953809901955)
                ·
                  refine ⟨46128925754809430714852933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30752617169872953809901955 46128925754809430714852933)
                  ·
                    refine ⟨8649173579026768259034925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46128925754809430714852933 8649173579026768259034925)
                    ·
                      refine ⟨3243440092135038097138097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8649173579026768259034925 3243440092135038097138097)
                      ·
                        rfl

theorem cell23_6316577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_6316577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316577 prefixEnd_6316577 := by exact prefixLift 6316577
  have htrace : WordTrace (prefixWord ++ tailWord_6316577) baseStart_6316577 baseEnd_6316577 := by
    simpa [prefixWord, tailWord_6316577, baseEnd_6316577] using wordTrace_append hprefix tailTrace_6316577
  have hstable : (prefixWord ++ tailWord_6316577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316577).length < 2 ^ (prefixWord ++ tailWord_6316577).sum := by decide
  have hdescent : baseEnd_6316577 < baseStart_6316577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316584 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 5, 4]
def baseStart_6316584 : Nat := 118140960795 + 6316584 * 2 ^ 59
def prefixEnd_6316584 : Nat := 4983230072969 + 3 ^ 40 * 6316584 * 2
def baseEnd_6316584 : Nat := 1081147895499873189916855

theorem tailTrace_6316584 : CollatzResearch.WordTrace tailWord_6316584 prefixEnd_6316584 1081147895499873189916855 := by
  unfold tailWord_6316584
  simp only [CollatzResearch.WordTrace]
  refine ⟨115192372674051214752858403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153589830232068286337144537 115192372674051214752858403)
  ·
    refine ⟨172788559011076822129287605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115192372674051214752858403 172788559011076822129287605)
    ·
      refine ⟨16198927407288452074620713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172788559011076822129287605 16198927407288452074620713)
      ·
        refine ⟨12149195555466339055965535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16198927407288452074620713 12149195555466339055965535)
        ·
          refine ⟨18223793333199508583948303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12149195555466339055965535 18223793333199508583948303)
          ·
            refine ⟨27335689999799262875922455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18223793333199508583948303 27335689999799262875922455)
            ·
              refine ⟨41003534999698894313883683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27335689999799262875922455 41003534999698894313883683)
              ·
                refine ⟨61505302499548341470825525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41003534999698894313883683 61505302499548341470825525)
                ·
                  refine ⟨5766122109332657012889893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61505302499548341470825525 5766122109332657012889893)
                  ·
                    refine ⟨1081147895499873189916855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5766122109332657012889893 1081147895499873189916855)
                    ·
                      rfl

theorem cell23_6316584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_6316584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316584 prefixEnd_6316584 := by exact prefixLift 6316584
  have htrace : WordTrace (prefixWord ++ tailWord_6316584) baseStart_6316584 baseEnd_6316584 := by
    simpa [prefixWord, tailWord_6316584, baseEnd_6316584] using wordTrace_append hprefix tailTrace_6316584
  have hstable : (prefixWord ++ tailWord_6316584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316584).length < 2 ^ (prefixWord ++ tailWord_6316584).sum := by decide
  have hdescent : baseEnd_6316584 < baseStart_6316584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316594 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_6316594 : Nat := 118140960795 + 6316594 * 2 ^ 59
def prefixEnd_6316594 : Nat := 4983230072969 + 3 ^ 40 * 6316594 * 2
def baseEnd_6316594 : Nat := 3243448821306164530625519

theorem tailTrace_6316594 : CollatzResearch.WordTrace tailWord_6316594 prefixEnd_6316594 3243448821306164530625519 := by
  unfold tailWord_6316594
  simp only [CollatzResearch.WordTrace]
  refine ⟨57596277519516550303395209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153590073385377467475720557 57596277519516550303395209)
  ·
    refine ⟨43197208139637412727546407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57596277519516550303395209 43197208139637412727546407)
    ·
      refine ⟨64795812209456119091319611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43197208139637412727546407 64795812209456119091319611)
      ·
        refine ⟨97193718314184178636979417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64795812209456119091319611 97193718314184178636979417)
        ·
          refine ⟨72895288735638133977734563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97193718314184178636979417 72895288735638133977734563)
          ·
            refine ⟨109342933103457200966601845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72895288735638133977734563 109342933103457200966601845)
            ·
              refine ⟨10250899978449112590618923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109342933103457200966601845 10250899978449112590618923)
              ·
                refine ⟨15376349967673668885928385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10250899978449112590618923 15376349967673668885928385)
                ·
                  refine ⟨11532262475755251664446289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15376349967673668885928385 11532262475755251664446289)
                  ·
                    refine ⟨8649196856816438748334717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11532262475755251664446289 8649196856816438748334717)
                    ·
                      refine ⟨3243448821306164530625519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8649196856816438748334717 3243448821306164530625519)
                      ·
                        rfl

theorem cell23_6316594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_6316594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316594 prefixEnd_6316594 := by exact prefixLift 6316594
  have htrace : WordTrace (prefixWord ++ tailWord_6316594) baseStart_6316594 baseEnd_6316594 := by
    simpa [prefixWord, tailWord_6316594, baseEnd_6316594] using wordTrace_append hprefix tailTrace_6316594
  have hstable : (prefixWord ++ tailWord_6316594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316594).length < 2 ^ (prefixWord ++ tailWord_6316594).sum := by decide
  have hdescent : baseEnd_6316594 < baseStart_6316594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316601 : List Nat := [1, 2, 1, 5, 1, 1, 4, 3, 1, 4]
def baseStart_6316601 : Nat := 118140960795 + 6316601 * 2 ^ 59
def prefixEnd_6316601 : Nat := 4983230072969 + 3 ^ 40 * 6316601 * 2
def baseEnd_6316601 : Nat := 1081150805223582001079329

theorem tailTrace_6316601 : CollatzResearch.WordTrace tailWord_6316601 prefixEnd_6316601 1081150805223582001079329 := by
  unfold tailWord_6316601
  simp only [CollatzResearch.WordTrace]
  refine ⟨230385365389040841409085657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153590243592693894272723771 230385365389040841409085657)
  ·
    refine ⟨172789024041780631056814243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230385365389040841409085657 172789024041780631056814243)
    ·
      refine ⟨259183536062670946585221365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172789024041780631056814243 259183536062670946585221365)
      ·
        refine ⟨24298456505875401242364503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 259183536062670946585221365 24298456505875401242364503)
        ·
          refine ⟨36447684758813101863546755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24298456505875401242364503 36447684758813101863546755)
          ·
            refine ⟨54671527138219652795320133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36447684758813101863546755 54671527138219652795320133)
            ·
              refine ⟨10250911338416184899122525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54671527138219652795320133 10250911338416184899122525)
              ·
                refine ⟨3844091751906069337170947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10250911338416184899122525 3844091751906069337170947)
                ·
                  refine ⟨5766137627859104005756421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3844091751906069337170947 5766137627859104005756421)
                  ·
                    refine ⟨1081150805223582001079329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5766137627859104005756421 1081150805223582001079329)
                    ·
                      rfl

theorem cell23_6316601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 1, 4].length) (baseStart_6316601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316601 prefixEnd_6316601 := by exact prefixLift 6316601
  have htrace : WordTrace (prefixWord ++ tailWord_6316601) baseStart_6316601 baseEnd_6316601 := by
    simpa [prefixWord, tailWord_6316601, baseEnd_6316601] using wordTrace_append hprefix tailTrace_6316601
  have hstable : (prefixWord ++ tailWord_6316601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316601).length < 2 ^ (prefixWord ++ tailWord_6316601).sum := by decide
  have hdescent : baseEnd_6316601 < baseStart_6316601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316644 : List Nat := [2, 3, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_6316644 : Nat := 118140960795 + 6316644 * 2 ^ 59
def prefixEnd_6316644 : Nat := 4983230072969 + 3 ^ 40 * 6316644 * 2
def baseEnd_6316644 : Nat := 1081158165112963111666763

theorem tailTrace_6316644 : CollatzResearch.WordTrace tailWord_6316644 prefixEnd_6316644 1081158165112963111666763 := by
  unfold tailWord_6316644
  simp only [CollatzResearch.WordTrace]
  refine ⟨115193466863942529876450493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153591289151923373168600657 115193466863942529876450493)
  ·
    refine ⟨43197550073978448703668935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115193466863942529876450493 43197550073978448703668935)
    ·
      refine ⟨64796325110967673055503403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43197550073978448703668935 64796325110967673055503403)
      ·
        refine ⟨97194487666451509583255105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64796325110967673055503403 97194487666451509583255105)
        ·
          refine ⟨72895865749838632187441329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97194487666451509583255105 72895865749838632187441329)
          ·
            refine ⟨54671899312378974140580997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72895865749838632187441329 54671899312378974140580997)
            ·
              refine ⟨10250981121071057651358937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54671899312378974140580997 10250981121071057651358937)
              ·
                refine ⟨7688235840803293238519203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10250981121071057651358937 7688235840803293238519203)
                ·
                  refine ⟨11532353761204939857778805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7688235840803293238519203 11532353761204939857778805)
                  ·
                    refine ⟨1081158165112963111666763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11532353761204939857778805 1081158165112963111666763)
                    ·
                      rfl

theorem cell23_6316644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_6316644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316644 prefixEnd_6316644 := by exact prefixLift 6316644
  have htrace : WordTrace (prefixWord ++ tailWord_6316644) baseStart_6316644 baseEnd_6316644 := by
    simpa [prefixWord, tailWord_6316644, baseEnd_6316644] using wordTrace_append hprefix tailTrace_6316644
  have hstable : (prefixWord ++ tailWord_6316644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316644).length < 2 ^ (prefixWord ++ tailWord_6316644).sum := by decide
  have hdescent : baseEnd_6316644 < baseStart_6316644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316677 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_6316677 : Nat := 118140960795 + 6316677 * 2 ^ 59
def prefixEnd_6316677 : Nat := 4983230072969 + 3 ^ 40 * 6316677 * 2
def baseEnd_6316677 : Nat := 3243491440200487705887637

theorem tailTrace_6316677 : CollatzResearch.WordTrace tailWord_6316677 prefixEnd_6316677 3243491440200487705887637 := by
  unfold tailWord_6316677
  simp only [CollatzResearch.WordTrace]
  refine ⟨230388137336765506388852285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153592091557843670925901523 230388137336765506388852285)
  ·
    refine ⟨86395551501287064895819607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230388137336765506388852285 86395551501287064895819607)
    ·
      refine ⟨129593327251930597343729411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86395551501287064895819607 129593327251930597343729411)
      ·
        refine ⟨194389990877895896015594117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129593327251930597343729411 194389990877895896015594117)
        ·
          refine ⟨36448123289605480502923897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194389990877895896015594117 36448123289605480502923897)
          ·
            refine ⟨27336092467204110377192923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36448123289605480502923897 27336092467204110377192923)
            ·
              refine ⟨41004138700806165565789385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27336092467204110377192923 41004138700806165565789385)
              ·
                refine ⟨30753104025604624174342039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41004138700806165565789385 30753104025604624174342039)
                ·
                  refine ⟨46129656038406936261513059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30753104025604624174342039 46129656038406936261513059)
                  ·
                    refine ⟨69194484057610404392269589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46129656038406936261513059 69194484057610404392269589)
                    ·
                      refine ⟨3243491440200487705887637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69194484057610404392269589 3243491440200487705887637)
                      ·
                        rfl

theorem cell23_6316677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_6316677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316677 prefixEnd_6316677 := by exact prefixLift 6316677
  have htrace : WordTrace (prefixWord ++ tailWord_6316677) baseStart_6316677 baseEnd_6316677 := by
    simpa [prefixWord, tailWord_6316677, baseEnd_6316677] using wordTrace_append hprefix tailTrace_6316677
  have hstable : (prefixWord ++ tailWord_6316677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316677).length < 2 ^ (prefixWord ++ tailWord_6316677).sum := by decide
  have hdescent : baseEnd_6316677 < baseStart_6316677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316701 : List Nat := [1, 4, 2, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_6316701 : Nat := 118140960795 + 6316701 * 2 ^ 59
def prefixEnd_6316701 : Nat := 4983230072969 + 3 ^ 40 * 6316701 * 2
def baseEnd_6316701 : Nat := 3243503763736195611987527

theorem tailTrace_6316701 : CollatzResearch.WordTrace tailWord_6316701 prefixEnd_6316701 3243503763736195611987527 := by
  unfold tailWord_6316701
  simp only [CollatzResearch.WordTrace]
  refine ⟨230389012688678558487725957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153592675125785705658483971 230389012688678558487725957)
  ·
    refine ⟨43197939879127229716448617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230389012688678558487725957 43197939879127229716448617)
    ·
      refine ⟨32398454909345422287336463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43197939879127229716448617 32398454909345422287336463)
      ·
        refine ⟨48597682364018133431004695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32398454909345422287336463 48597682364018133431004695)
        ·
          refine ⟨72896523546027200146507043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48597682364018133431004695 72896523546027200146507043)
          ·
            refine ⟨109344785319040800219760565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72896523546027200146507043 109344785319040800219760565)
            ·
              refine ⟨10251073623660075020602553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109344785319040800219760565 10251073623660075020602553)
              ·
                refine ⟨7688305217745056265451915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10251073623660075020602553 7688305217745056265451915)
                ·
                  refine ⟨11532457826617584398177873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7688305217745056265451915 11532457826617584398177873)
                  ·
                    refine ⟨8649343369963188298633405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11532457826617584398177873 8649343369963188298633405)
                    ·
                      refine ⟨3243503763736195611987527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8649343369963188298633405 3243503763736195611987527)
                      ·
                        rfl

theorem cell23_6316701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_6316701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316701 prefixEnd_6316701 := by exact prefixLift 6316701
  have htrace : WordTrace (prefixWord ++ tailWord_6316701) baseStart_6316701 baseEnd_6316701 := by
    simpa [prefixWord, tailWord_6316701, baseEnd_6316701] using wordTrace_append hprefix tailTrace_6316701
  have hstable : (prefixWord ++ tailWord_6316701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316701).length < 2 ^ (prefixWord ++ tailWord_6316701).sum := by decide
  have hdescent : baseEnd_6316701 < baseStart_6316701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316718 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_6316718 : Nat := 118140960795 + 6316718 * 2 ^ 59
def prefixEnd_6316718 : Nat := 4983230072969 + 3 ^ 40 * 6316718 * 2
def baseEnd_6316718 : Nat := 3243512492907322045474949

theorem tailTrace_6316718 : CollatzResearch.WordTrace tailWord_6316718 prefixEnd_6316718 3243512492907322045474949 := by
  unfold tailWord_6316718
  simp only [CollatzResearch.WordTrace]
  refine ⟨28798704091202121298886851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153593088486411313594063205 28798704091202121298886851)
  ·
    refine ⟨43198056136803181948330277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28798704091202121298886851 43198056136803181948330277)
    ·
      refine ⟨8099635525650596615311927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43198056136803181948330277 8099635525650596615311927)
      ·
        refine ⟨12149453288475894922967891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8099635525650596615311927 12149453288475894922967891)
        ·
          refine ⟨18224179932713842384451837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12149453288475894922967891 18224179932713842384451837)
          ·
            refine ⟨6834067474767690894169439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18224179932713842384451837 6834067474767690894169439)
            ·
              refine ⟨10251101212151536341254159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6834067474767690894169439 10251101212151536341254159)
              ·
                refine ⟨15376651818227304511881239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10251101212151536341254159 15376651818227304511881239)
                ·
                  refine ⟨23064977727340956767821859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15376651818227304511881239 23064977727340956767821859)
                  ·
                    refine ⟨34597466591011435151732789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23064977727340956767821859 34597466591011435151732789)
                    ·
                      refine ⟨3243512492907322045474949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34597466591011435151732789 3243512492907322045474949)
                      ·
                        rfl

theorem cell23_6316718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_6316718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316718 prefixEnd_6316718 := by exact prefixLift 6316718
  have htrace : WordTrace (prefixWord ++ tailWord_6316718) baseStart_6316718 baseEnd_6316718 := by
    simpa [prefixWord, tailWord_6316718, baseEnd_6316718] using wordTrace_append hprefix tailTrace_6316718
  have hstable : (prefixWord ++ tailWord_6316718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316718).length < 2 ^ (prefixWord ++ tailWord_6316718).sum := by decide
  have hdescent : baseEnd_6316718 < baseStart_6316718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316726 : List Nat := [5, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_6316726 : Nat := 118140960795 + 6316726 * 2 ^ 59
def prefixEnd_6316726 : Nat := 4983230072969 + 3 ^ 40 * 6316726 * 2
def baseEnd_6316726 : Nat := 3243516600752558014174913

theorem tailTrace_6316726 : CollatzResearch.WordTrace tailWord_6316726 prefixEnd_6316726 3243516600752558014174913 := by
  unfold tailWord_6316726
  simp only [CollatzResearch.WordTrace]
  refine ⟨14399370282099249234836627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153593283009058658504924021 14399370282099249234836627)
  ·
    refine ⟨21599055423148873852254941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14399370282099249234836627 21599055423148873852254941)
    ·
      refine ⟨8099645783680827694595603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21599055423148873852254941 8099645783680827694595603)
      ·
        refine ⟨12149468675521241541893405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8099645783680827694595603 12149468675521241541893405)
        ·
          refine ⟨4556050753320465578210027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12149468675521241541893405 4556050753320465578210027)
          ·
            refine ⟨6834076129980698367315041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556050753320465578210027 6834076129980698367315041)
            ·
              refine ⟨5125557097485523775486281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6834076129980698367315041 5125557097485523775486281)
              ·
                refine ⟨3844167823114142831614711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5125557097485523775486281 3844167823114142831614711)
                ·
                  refine ⟨5766251734671214247422067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3844167823114142831614711 5766251734671214247422067)
                  ·
                    refine ⟨8649377602006821371133101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5766251734671214247422067 8649377602006821371133101)
                    ·
                      refine ⟨3243516600752558014174913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8649377602006821371133101 3243516600752558014174913)
                      ·
                        rfl

theorem cell23_6316726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_6316726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316726 prefixEnd_6316726 := by exact prefixLift 6316726
  have htrace : WordTrace (prefixWord ++ tailWord_6316726) baseStart_6316726 baseEnd_6316726 := by
    simpa [prefixWord, tailWord_6316726, baseEnd_6316726] using wordTrace_append hprefix tailTrace_6316726
  have hstable : (prefixWord ++ tailWord_6316726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316726).length < 2 ^ (prefixWord ++ tailWord_6316726).sum := by decide
  have hdescent : baseEnd_6316726 < baseStart_6316726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316748 : List Nat := [2, 2, 1, 5, 1, 1, 2, 3, 2, 1, 3]
def baseStart_6316748 : Nat := 118140960795 + 6316748 * 2 ^ 59
def prefixEnd_6316748 : Nat := 4983230072969 + 3 ^ 40 * 6316748 * 2
def baseEnd_6316748 : Nat := 3243527897326956928099811

theorem tailTrace_6316748 : CollatzResearch.WordTrace tailWord_6316748 prefixEnd_6316748 3243527897326956928099811 := by
  unfold tailWord_6316748
  simp only [CollatzResearch.WordTrace]
  refine ⟨115195363459754142757343449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153593817946338857009791265 115195363459754142757343449)
  ·
    refine ⟨86396522594815607068007587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115195363459754142757343449 86396522594815607068007587)
    ·
      refine ⟨129594783892223410602011381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86396522594815607068007587 129594783892223410602011381)
      ·
        refine ⟨12149510989895944743938567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129594783892223410602011381 12149510989895944743938567)
        ·
          refine ⟨18224266484843917115907851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12149510989895944743938567 18224266484843917115907851)
          ·
            refine ⟨27336399727265875673861777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18224266484843917115907851 27336399727265875673861777)
            ·
              refine ⟨20502299795449406755396333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27336399727265875673861777 20502299795449406755396333)
              ·
                refine ⟨7688362423293527533273625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20502299795449406755396333 7688362423293527533273625)
                ·
                  refine ⟨5766271817470145649955219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7688362423293527533273625 5766271817470145649955219)
                  ·
                    refine ⟨8649407726205218474932829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5766271817470145649955219 8649407726205218474932829)
                    ·
                      refine ⟨3243527897326956928099811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8649407726205218474932829 3243527897326956928099811)
                      ·
                        rfl

theorem cell23_6316748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_6316748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316748 prefixEnd_6316748 := by exact prefixLift 6316748
  have htrace : WordTrace (prefixWord ++ tailWord_6316748) baseStart_6316748 baseEnd_6316748 := by
    simpa [prefixWord, tailWord_6316748, baseEnd_6316748] using wordTrace_append hprefix tailTrace_6316748
  have hstable : (prefixWord ++ tailWord_6316748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316748).length < 2 ^ (prefixWord ++ tailWord_6316748).sum := by decide
  have hdescent : baseEnd_6316748 < baseStart_6316748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316824 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 2, 5]
def baseStart_6316824 : Nat := 118140960795 + 6316824 * 2 ^ 59
def prefixEnd_6316824 : Nat := 4983230072969 + 3 ^ 40 * 6316824 * 2
def baseEnd_6316824 : Nat := 1081188973952232876916487

theorem tailTrace_6316824 : CollatzResearch.WordTrace tailWord_6316824 prefixEnd_6316824 1081188973952232876916487 := by
  unfold tailWord_6316824
  simp only [CollatzResearch.WordTrace]
  refine ⟨115196749433616475247226763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153595665911488633662969017 115196749433616475247226763)
  ·
    refine ⟨172795124150424712870840145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115196749433616475247226763 172795124150424712870840145)
    ·
      refine ⟨129596343112818534653130109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172795124150424712870840145 129596343112818534653130109)
      ·
        refine ⟨48598628667306950494923791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129596343112818534653130109 48598628667306950494923791)
        ·
          refine ⟨72897943000960425742385687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48598628667306950494923791 72897943000960425742385687)
          ·
            refine ⟨109346914501440638613578531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72897943000960425742385687 109346914501440638613578531)
            ·
              refine ⟨164020371752160957920367797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109346914501440638613578531 164020371752160957920367797)
              ·
                refine ⟨15376909851765089805034481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164020371752160957920367797 15376909851765089805034481)
                ·
                  refine ⟨11532682388823817353775861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15376909851765089805034481 11532682388823817353775861)
                  ·
                    refine ⟨1081188973952232876916487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11532682388823817353775861 1081188973952232876916487)
                    ·
                      rfl

theorem cell23_6316824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_6316824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316824 prefixEnd_6316824 := by exact prefixLift 6316824
  have htrace : WordTrace (prefixWord ++ tailWord_6316824) baseStart_6316824 baseEnd_6316824 := by
    simpa [prefixWord, tailWord_6316824, baseEnd_6316824] using wordTrace_append hprefix tailTrace_6316824
  have hstable : (prefixWord ++ tailWord_6316824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316824).length < 2 ^ (prefixWord ++ tailWord_6316824).sum := by decide
  have hdescent : baseEnd_6316824 < baseStart_6316824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316828 : List Nat := [2, 2, 3, 1, 1, 5, 1, 3, 5]
def baseStart_6316828 : Nat := 118140960795 + 6316828 * 2 ^ 59
def prefixEnd_6316828 : Nat := 4983230072969 + 3 ^ 40 * 6316828 * 2
def baseEnd_6316828 : Nat := 360396552864368512788827

theorem tailTrace_6316828 : CollatzResearch.WordTrace tailWord_6316828 prefixEnd_6316828 360396552864368512788827 := by
  unfold tailWord_6316828
  simp only [CollatzResearch.WordTrace]
  refine ⟨115196822379609229588799569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153595763172812306118399425 115196822379609229588799569)
  ·
    refine ⟨86397616784706922191599677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115196822379609229588799569 86397616784706922191599677)
    ·
      refine ⟨32399106294265095821849879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86397616784706922191599677 32399106294265095821849879)
      ·
        refine ⟨48598659441397643732774819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32399106294265095821849879 48598659441397643732774819)
        ·
          refine ⟨72897989162096465599162229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48598659441397643732774819 72897989162096465599162229)
          ·
            refine ⟨6834186483946543649921459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72897989162096465599162229 6834186483946543649921459)
            ·
              refine ⟨10251279725919815474882189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6834186483946543649921459 10251279725919815474882189)
              ·
                refine ⟨3844229897219930803080821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10251279725919815474882189 3844229897219930803080821)
                ·
                  refine ⟨360396552864368512788827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3844229897219930803080821 360396552864368512788827)
                  ·
                    rfl

theorem cell23_6316828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 5].length) (baseStart_6316828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316828 prefixEnd_6316828 := by exact prefixLift 6316828
  have htrace : WordTrace (prefixWord ++ tailWord_6316828) baseStart_6316828 baseEnd_6316828 := by
    simpa [prefixWord, tailWord_6316828, baseEnd_6316828] using wordTrace_append hprefix tailTrace_6316828
  have hstable : (prefixWord ++ tailWord_6316828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316828).length < 2 ^ (prefixWord ++ tailWord_6316828).sum := by decide
  have hdescent : baseEnd_6316828 < baseStart_6316828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316845 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 7]
def baseStart_6316845 : Nat := 118140960795 + 6316845 * 2 ^ 59
def prefixEnd_6316845 : Nat := 4983230072969 + 3 ^ 40 * 6316845 * 2
def baseEnd_6316845 : Nat := 360397522772271449842985

theorem tailTrace_6316845 : CollatzResearch.WordTrace tailWord_6316845 prefixEnd_6316845 360397522772271449842985 := by
  unfold tailWord_6316845
  simp only [CollatzResearch.WordTrace]
  refine ⟨230394264800156871080967989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153596176533437914053978659 230394264800156871080967989)
  ·
    refine ⟨21599462325014706663840749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 230394264800156871080967989 21599462325014706663840749)
    ·
      refine ⟨8099798371880514998940281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21599462325014706663840749 8099798371880514998940281)
      ·
        refine ⟨6074848778910386249205211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8099798371880514998940281 6074848778910386249205211)
        ·
          refine ⟨9112273168365579373807817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6074848778910386249205211 9112273168365579373807817)
          ·
            refine ⟨6834204876274184530355863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9112273168365579373807817 6834204876274184530355863)
            ·
              refine ⟨10251307314411276795533795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6834204876274184530355863 10251307314411276795533795)
              ·
                refine ⟨15376960971616915193300693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10251307314411276795533795 15376960971616915193300693)
                ·
                  refine ⟨360397522772271449842985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15376960971616915193300693 360397522772271449842985)
                  ·
                    rfl

theorem cell23_6316845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_6316845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316845 prefixEnd_6316845 := by exact prefixLift 6316845
  have htrace : WordTrace (prefixWord ++ tailWord_6316845) baseStart_6316845 baseEnd_6316845 := by
    simpa [prefixWord, tailWord_6316845, baseEnd_6316845] using wordTrace_append hprefix tailTrace_6316845
  have hstable : (prefixWord ++ tailWord_6316845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316845).length < 2 ^ (prefixWord ++ tailWord_6316845).sum := by decide
  have hdescent : baseEnd_6316845 < baseStart_6316845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316864 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 3]
def baseStart_6316864 : Nat := 118140960795 + 6316864 * 2 ^ 59
def prefixEnd_6316864 : Nat := 4983230072969 + 3 ^ 40 * 6316864 * 2
def baseEnd_6316864 : Nat := 3243587461082878474249277

theorem tailTrace_6316864 : CollatzResearch.WordTrace tailWord_6316864 prefixEnd_6316864 3243587461082878474249277 := by
  unfold tailWord_6316864
  simp only [CollatzResearch.WordTrace]
  refine ⟨115197478893544018662954823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153596638524725358217273097 115197478893544018662954823)
  ·
    refine ⟨172796218340316027994432235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115197478893544018662954823 172796218340316027994432235)
    ·
      refine ⟨259194327510474041991648353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172796218340316027994432235 259194327510474041991648353)
      ·
        refine ⟨194395745632855531493736265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259194327510474041991648353 194395745632855531493736265)
        ·
          refine ⟨145796809224641648620302199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194395745632855531493736265 145796809224641648620302199)
          ·
            refine ⟨218695213836962472930453299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145796809224641648620302199 218695213836962472930453299)
            ·
              refine ⟨328042820755443709395679949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218695213836962472930453299 328042820755443709395679949)
              ·
                refine ⟨123016057783291391023379981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328042820755443709395679949 123016057783291391023379981)
                ·
                  refine ⟨46131021668734271633767493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123016057783291391023379981 46131021668734271633767493)
                  ·
                    refine ⟨8649566562887675931331405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46131021668734271633767493 8649566562887675931331405)
                    ·
                      refine ⟨3243587461082878474249277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8649566562887675931331405 3243587461082878474249277)
                      ·
                        rfl

theorem cell23_6316864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_6316864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316864 prefixEnd_6316864 := by exact prefixLift 6316864
  have htrace : WordTrace (prefixWord ++ tailWord_6316864) baseStart_6316864 baseEnd_6316864 := by
    simpa [prefixWord, tailWord_6316864, baseEnd_6316864] using wordTrace_append hprefix tailTrace_6316864
  have hstable : (prefixWord ++ tailWord_6316864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316864).length < 2 ^ (prefixWord ++ tailWord_6316864).sum := by decide
  have hdescent : baseEnd_6316864 < baseStart_6316864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316911 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 7, 1, 3]
def baseStart_6316911 : Nat := 118140960795 + 6316911 * 2 ^ 59
def prefixEnd_6316911 : Nat := 4983230072969 + 3 ^ 40 * 6316911 * 2
def baseEnd_6316911 : Nat := 3243611594673639790361561

theorem tailTrace_6316911 : CollatzResearch.WordTrace tailWord_6316911 prefixEnd_6316911 3243611594673639790361561 := by
  unfold tailWord_6316911
  simp only [CollatzResearch.WordTrace]
  refine ⟨230396672017917764352870587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153597781345278509568580391 230396672017917764352870587)
  ·
    refine ⟨345595008026876646529305881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230396672017917764352870587 345595008026876646529305881)
    ·
      refine ⟨259196256020157484896979411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345595008026876646529305881 259196256020157484896979411)
      ·
        refine ⟨388794384030236227345469117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259196256020157484896979411 388794384030236227345469117)
        ·
          refine ⟨145797894011338585254550919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388794384030236227345469117 145797894011338585254550919)
          ·
            refine ⟨218696841017007877881826379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145797894011338585254550919 218696841017007877881826379)
            ·
              refine ⟨328045261525511816822739569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218696841017007877881826379 328045261525511816822739569)
              ·
                refine ⟨246033946144133862617054677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328045261525511816822739569 246033946144133862617054677)
                ·
                  refine ⟨5766420612753137405087219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 246033946144133862617054677 5766420612753137405087219)
                  ·
                    refine ⟨8649630919129706107630829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5766420612753137405087219 8649630919129706107630829)
                    ·
                      refine ⟨3243611594673639790361561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8649630919129706107630829 3243611594673639790361561)
                      ·
                        rfl

theorem cell23_6316911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 1, 3].length) (baseStart_6316911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316911 prefixEnd_6316911 := by exact prefixLift 6316911
  have htrace : WordTrace (prefixWord ++ tailWord_6316911) baseStart_6316911 baseEnd_6316911 := by
    simpa [prefixWord, tailWord_6316911, baseEnd_6316911] using wordTrace_append hprefix tailTrace_6316911
  have hstable : (prefixWord ++ tailWord_6316911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316911).length < 2 ^ (prefixWord ++ tailWord_6316911).sum := by decide
  have hdescent : baseEnd_6316911 < baseStart_6316911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316918 : List Nat := [5, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_6316918 : Nat := 118140960795 + 6316918 * 2 ^ 59
def prefixEnd_6316918 : Nat := 4983230072969 + 3 ^ 40 * 6316918 * 2
def baseEnd_6316918 : Nat := 360401687670913473663781

theorem tailTrace_6316918 : CollatzResearch.WordTrace tailWord_6316918 prefixEnd_6316918 360401687670913473663781 := by
  unfold tailWord_6316918
  simp only [CollatzResearch.WordTrace]
  refine ⟨14399807958055775284273463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153597951552594936365583605 14399807958055775284273463)
  ·
    refine ⟨21599711937083662926410195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14399807958055775284273463 21599711937083662926410195)
    ·
      refine ⟨32399567905625494389615293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21599711937083662926410195 32399567905625494389615293)
      ·
        refine ⟨12149837964609560396105735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32399567905625494389615293 12149837964609560396105735)
        ·
          refine ⟨18224756946914340594158603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12149837964609560396105735 18224756946914340594158603)
          ·
            refine ⟨27337135420371510891237905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18224756946914340594158603 27337135420371510891237905)
            ·
              refine ⟨20502851565278633168428429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27337135420371510891237905 20502851565278633168428429)
              ·
                refine ⟨7688569336979487438160661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20502851565278633168428429 7688569336979487438160661)
                ·
                  refine ⟨360401687670913473663781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7688569336979487438160661 360401687670913473663781)
                  ·
                    rfl

theorem cell23_6316918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_6316918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316918 prefixEnd_6316918 := by exact prefixLift 6316918
  have htrace : WordTrace (prefixWord ++ tailWord_6316918) baseStart_6316918 baseEnd_6316918 := by
    simpa [prefixWord, tailWord_6316918, baseEnd_6316918] using wordTrace_append hprefix tailTrace_6316918
  have hstable : (prefixWord ++ tailWord_6316918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316918).length < 2 ^ (prefixWord ++ tailWord_6316918).sum := by decide
  have hdescent : baseEnd_6316918 < baseStart_6316918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316931 : List Nat := [1, 1, 1, 3, 4, 1, 2, 4, 1, 5]
def baseStart_6316931 : Nat := 118140960795 + 6316931 * 2 ^ 59
def prefixEnd_6316931 : Nat := 4983230072969 + 3 ^ 40 * 6316931 * 2
def baseEnd_6316931 : Nat := 1081207288095576570703823

theorem tailTrace_6316931 : CollatzResearch.WordTrace tailWord_6316931 prefixEnd_6316931 1081207288095576570703823 := by
  unfold tailWord_6316931
  simp only [CollatzResearch.WordTrace]
  refine ⟨230397401477845307768598647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153598267651896871845732431 230397401477845307768598647)
  ·
    refine ⟨345596102216767961652897971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230397401477845307768598647 345596102216767961652897971)
    ·
      refine ⟨518394153325151942479346957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345596102216767961652897971 518394153325151942479346957)
      ·
        refine ⟨194397807496931978429755109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 518394153325151942479346957 194397807496931978429755109)
        ·
          refine ⟨36449588905674745955579083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194397807496931978429755109 36449588905674745955579083)
          ·
            refine ⟨54674383358512118933368625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36449588905674745955579083 54674383358512118933368625)
            ·
              refine ⟨41005787518884089200026469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54674383358512118933368625 41005787518884089200026469)
              ·
                refine ⟨7688585159790766725004963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41005787518884089200026469 7688585159790766725004963)
                ·
                  refine ⟨11532877739686150087507445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7688585159790766725004963 11532877739686150087507445)
                  ·
                    refine ⟨1081207288095576570703823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11532877739686150087507445 1081207288095576570703823)
                    ·
                      rfl

theorem cell23_6316931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 5].length) (baseStart_6316931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316931 prefixEnd_6316931 := by exact prefixLift 6316931
  have htrace : WordTrace (prefixWord ++ tailWord_6316931) baseStart_6316931 baseEnd_6316931 := by
    simpa [prefixWord, tailWord_6316931, baseEnd_6316931] using wordTrace_append hprefix tailTrace_6316931
  have hstable : (prefixWord ++ tailWord_6316931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316931).length < 2 ^ (prefixWord ++ tailWord_6316931).sum := by decide
  have hdescent : baseEnd_6316931 < baseStart_6316931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316948 : List Nat := [2, 4, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_6316948 : Nat := 118140960795 + 6316948 * 2 ^ 59
def prefixEnd_6316948 : Nat := 4983230072969 + 3 ^ 40 * 6316948 * 2
def baseEnd_6316948 : Nat := 1081210197819285381866297

theorem tailTrace_6316948 : CollatzResearch.WordTrace tailWord_6316948 prefixEnd_6316948 1081210197819285381866297 := by
  unfold tailWord_6316948
  simp only [CollatzResearch.WordTrace]
  refine ⟨115199010759391859835983749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153598681012522479781311665 115199010759391859835983749)
  ·
    refine ⟨21599814517385973719246953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115199010759391859835983749 21599814517385973719246953)
    ·
      refine ⟨16199860888039480289435215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21599814517385973719246953 16199860888039480289435215)
      ·
        refine ⟨24299791332059220434152823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16199860888039480289435215 24299791332059220434152823)
        ·
          refine ⟨36449686998088830651229235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24299791332059220434152823 36449686998088830651229235)
          ·
            refine ⟨54674530497133245976843853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36449686998088830651229235 54674530497133245976843853)
            ·
              refine ⟨20502948936424967241316445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54674530497133245976843853 20502948936424967241316445)
              ·
                refine ⟨7688605851159362715493667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20502948936424967241316445 7688605851159362715493667)
                ·
                  refine ⟨11532908776739044073240501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7688605851159362715493667 11532908776739044073240501)
                  ·
                    refine ⟨1081210197819285381866297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11532908776739044073240501 1081210197819285381866297)
                    ·
                      rfl

theorem cell23_6316948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_6316948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316948 prefixEnd_6316948 := by exact prefixLift 6316948
  have htrace : WordTrace (prefixWord ++ tailWord_6316948) baseStart_6316948 baseEnd_6316948 := by
    simpa [prefixWord, tailWord_6316948, baseEnd_6316948] using wordTrace_append hprefix tailTrace_6316948
  have hstable : (prefixWord ++ tailWord_6316948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316948).length < 2 ^ (prefixWord ++ tailWord_6316948).sum := by decide
  have hdescent : baseEnd_6316948 < baseStart_6316948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316962 : List Nat := [3, 3, 1, 2, 2, 1, 2, 4, 1, 1, 3]
def baseStart_6316962 : Nat := 118140960795 + 6316962 * 2 ^ 59
def prefixEnd_6316962 : Nat := 4983230072969 + 3 ^ 40 * 6316962 * 2
def baseEnd_6316962 : Nat := 3243637782187019090823827

theorem tailTrace_6316962 : CollatzResearch.WordTrace tailWord_6316962 prefixEnd_6316962 3243637782187019090823827 := by
  unfold tailWord_6316962
  simp only [CollatzResearch.WordTrace]
  refine ⟨57599633035183250015744285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153599021427155333375318093 57599633035183250015744285)
  ·
    refine ⟨21599862388193718755904107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57599633035183250015744285 21599862388193718755904107)
    ·
      refine ⟨32399793582290578133856161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21599862388193718755904107 32399793582290578133856161)
      ·
        refine ⟨24299845186717933600392121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32399793582290578133856161 24299845186717933600392121)
        ·
          refine ⟨18224883890038450200294091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24299845186717933600392121 18224883890038450200294091)
          ·
            refine ⟨27337325835057675300441137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18224883890038450200294091 27337325835057675300441137)
            ·
              refine ⟨20502994376293256475330853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27337325835057675300441137 20502994376293256475330853)
              ·
                refine ⟨3844311445554985589124535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20502994376293256475330853 3844311445554985589124535)
                ·
                  refine ⟨5766467168332478383686803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3844311445554985589124535 5766467168332478383686803)
                  ·
                    refine ⟨8649700752498717575530205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5766467168332478383686803 8649700752498717575530205)
                    ·
                      refine ⟨3243637782187019090823827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8649700752498717575530205 3243637782187019090823827)
                      ·
                        rfl

theorem cell23_6316962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_6316962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316962 prefixEnd_6316962 := by exact prefixLift 6316962
  have htrace : WordTrace (prefixWord ++ tailWord_6316962) baseStart_6316962 baseEnd_6316962 := by
    simpa [prefixWord, tailWord_6316962, baseEnd_6316962] using wordTrace_append hprefix tailTrace_6316962
  have hstable : (prefixWord ++ tailWord_6316962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316962).length < 2 ^ (prefixWord ++ tailWord_6316962).sum := by decide
  have hdescent : baseEnd_6316962 < baseStart_6316962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316981 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_6316981 : Nat := 118140960795 + 6316981 * 2 ^ 59
def prefixEnd_6316981 : Nat := 4983230072969 + 3 ^ 40 * 6316981 * 2
def baseEnd_6316981 : Nat := 3243647538319454516486239

theorem tailTrace_6316981 : CollatzResearch.WordTrace tailWord_6316981 prefixEnd_6316981 3243647538319454516486239 := by
  unfold tailWord_6316981
  simp only [CollatzResearch.WordTrace]
  refine ⟨230399225127664166307918797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153599483418442777538612531 230399225127664166307918797)
  ·
    refine ⟨86399709422874062365469549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230399225127664166307918797 86399709422874062365469549)
    ·
      refine ⟨32399891033577773387051081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86399709422874062365469549 32399891033577773387051081)
      ·
        refine ⟨24299918275183330040288311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32399891033577773387051081 24299918275183330040288311)
        ·
          refine ⟨36449877412774995060432467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24299918275183330040288311 36449877412774995060432467)
          ·
            refine ⟨54674816119162492590648701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36449877412774995060432467 54674816119162492590648701)
            ·
              refine ⟨20503056044685934721493263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54674816119162492590648701 20503056044685934721493263)
              ·
                refine ⟨30754584067028902082239895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20503056044685934721493263 30754584067028902082239895)
                ·
                  refine ⟨46131876100543353123359843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30754584067028902082239895 46131876100543353123359843)
                  ·
                    refine ⟨69197814150815029685039765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46131876100543353123359843 69197814150815029685039765)
                    ·
                      refine ⟨3243647538319454516486239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69197814150815029685039765 3243647538319454516486239)
                      ·
                        rfl

theorem cell23_6316981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_6316981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316981 prefixEnd_6316981 := by exact prefixLift 6316981
  have htrace : WordTrace (prefixWord ++ tailWord_6316981) baseStart_6316981 baseEnd_6316981 := by
    simpa [prefixWord, tailWord_6316981, baseEnd_6316981] using wordTrace_append hprefix tailTrace_6316981
  have hstable : (prefixWord ++ tailWord_6316981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316981).length < 2 ^ (prefixWord ++ tailWord_6316981).sum := by decide
  have hdescent : baseEnd_6316981 < baseStart_6316981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316985 : List Nat := [1, 2, 1, 4, 2, 2, 2, 2, 3, 2, 2]
def baseStart_6316985 : Nat := 118140960795 + 6316985 * 2 ^ 59
def prefixEnd_6316985 : Nat := 4983230072969 + 3 ^ 40 * 6316985 * 2
def baseEnd_6316985 : Nat := 3243649592242072500836221

theorem tailTrace_6316985 : CollatzResearch.WordTrace tailWord_6316985 prefixEnd_6316985 3243649592242072500836221 := by
  unfold tailWord_6316985
  simp only [CollatzResearch.WordTrace]
  refine ⟨230399371019649674991064409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153599580679766449994042939 230399371019649674991064409)
  ·
    refine ⟨172799528264737256243298307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230399371019649674991064409 172799528264737256243298307)
    ·
      refine ⟨259199292397105884364947461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172799528264737256243298307 259199292397105884364947461)
      ·
        refine ⟨48599867324457353318427649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259199292397105884364947461 48599867324457353318427649)
        ·
          refine ⟨36449900493343014988820737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48599867324457353318427649 36449900493343014988820737)
          ·
            refine ⟨27337425370007261241615553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36449900493343014988820737 27337425370007261241615553)
            ·
              refine ⟨20503069027505445931211665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27337425370007261241615553 20503069027505445931211665)
              ·
                refine ⟨15377301770629084448408749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20503069027505445931211665 15377301770629084448408749)
                ·
                  refine ⟨5766488163985906668153281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15377301770629084448408749 5766488163985906668153281)
                  ·
                    refine ⟨4324866122989430001114961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5766488163985906668153281 4324866122989430001114961)
                    ·
                      refine ⟨3243649592242072500836221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4324866122989430001114961 3243649592242072500836221)
                      ·
                        rfl

theorem cell23_6316985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_6316985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316985 prefixEnd_6316985 := by exact prefixLift 6316985
  have htrace : WordTrace (prefixWord ++ tailWord_6316985) baseStart_6316985 baseEnd_6316985 := by
    simpa [prefixWord, tailWord_6316985, baseEnd_6316985] using wordTrace_append hprefix tailTrace_6316985
  have hstable : (prefixWord ++ tailWord_6316985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316985).length < 2 ^ (prefixWord ++ tailWord_6316985).sum := by decide
  have hdescent : baseEnd_6316985 < baseStart_6316985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6316996 : List Nat := [2, 3, 3, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_6316996 : Nat := 118140960795 + 6316996 * 2 ^ 59
def prefixEnd_6316996 : Nat := 4983230072969 + 3 ^ 40 * 6316996 * 2
def baseEnd_6316996 : Nat := 3243655240529271957798671

theorem tailTrace_6316996 : CollatzResearch.WordTrace tailWord_6316996 prefixEnd_6316996 3243655240529271957798671 := by
  unfold tailWord_6316996
  simp only [CollatzResearch.WordTrace]
  refine ⟨115199886111304911934857421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153599848148406549246476561 115199886111304911934857421)
  ·
    refine ⟨43199957291739341975571533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115199886111304911934857421 43199957291739341975571533)
    ·
      refine ⟨16199983984402253240839325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43199957291739341975571533 16199983984402253240839325)
      ·
        refine ⟨6074993994150844965314747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16199983984402253240839325 6074993994150844965314747)
        ·
          refine ⟨9112490991226267447972121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6074993994150844965314747 9112490991226267447972121)
          ·
            refine ⟨6834368243419700585979091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9112490991226267447972121 6834368243419700585979091)
            ·
              refine ⟨10251552365129550878968637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6834368243419700585979091 10251552365129550878968637)
              ·
                refine ⟨3844332136923581579613239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10251552365129550878968637 3844332136923581579613239)
                ·
                  refine ⟨5766498205385372369419859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3844332136923581579613239 5766498205385372369419859)
                  ·
                    refine ⟨8649747308078058554129789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5766498205385372369419859 8649747308078058554129789)
                    ·
                      refine ⟨3243655240529271957798671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8649747308078058554129789 3243655240529271957798671)
                      ·
                        rfl

theorem cell23_6316996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_6316996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6316996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6316996 prefixEnd_6316996 := by exact prefixLift 6316996
  have htrace : WordTrace (prefixWord ++ tailWord_6316996) baseStart_6316996 baseEnd_6316996 := by
    simpa [prefixWord, tailWord_6316996, baseEnd_6316996] using wordTrace_append hprefix tailTrace_6316996
  have hstable : (prefixWord ++ tailWord_6316996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6316996).length < 2 ^ (prefixWord ++ tailWord_6316996).sum := by decide
  have hdescent : baseEnd_6316996 < baseStart_6316996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6316996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317029 : List Nat := [1, 3, 1, 6, 1, 2, 2, 1, 2, 4]
def baseStart_6317029 : Nat := 118140960795 + 6317029 * 2 ^ 59
def prefixEnd_6317029 : Nat := 4983230072969 + 3 ^ 40 * 6317029 * 2
def baseEnd_6317029 : Nat := 1081224061796956776228673

theorem tailTrace_6317029 : CollatzResearch.WordTrace tailWord_6317029 prefixEnd_6317029 1081224061796956776228673 := by
  unfold tailWord_6317029
  simp only [CollatzResearch.WordTrace]
  refine ⟨230400975831490270505666141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153600650554326847003777427 230400975831490270505666141)
  ·
    refine ⟨86400365936808851439624803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230400975831490270505666141 86400365936808851439624803)
    ·
      refine ⟨129600548905213277159437205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86400365936808851439624803 129600548905213277159437205)
      ·
        refine ⟨6075025729931872366848619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 129600548905213277159437205 6075025729931872366848619)
        ·
          refine ⟨9112538594897808550272929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6075025729931872366848619 9112538594897808550272929)
          ·
            refine ⟨6834403946173356412704697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9112538594897808550272929 6834403946173356412704697)
            ·
              refine ⟨5125802959630017309528523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6834403946173356412704697 5125802959630017309528523)
              ·
                refine ⟨7688704439445025964292785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5125802959630017309528523 7688704439445025964292785)
                ·
                  refine ⟨5766528329583769473219589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7688704439445025964292785 5766528329583769473219589)
                  ·
                    refine ⟨1081224061796956776228673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5766528329583769473219589 1081224061796956776228673)
                    ·
                      rfl

theorem cell23_6317029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_6317029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317029 prefixEnd_6317029 := by exact prefixLift 6317029
  have htrace : WordTrace (prefixWord ++ tailWord_6317029) baseStart_6317029 baseEnd_6317029 := by
    simpa [prefixWord, tailWord_6317029, baseEnd_6317029] using wordTrace_append hprefix tailTrace_6317029
  have hstable : (prefixWord ++ tailWord_6317029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317029).length < 2 ^ (prefixWord ++ tailWord_6317029).sum := by decide
  have hdescent : baseEnd_6317029 < baseStart_6317029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317061 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_6317061 : Nat := 118140960795 + 6317061 * 2 ^ 59
def prefixEnd_6317061 : Nat := 4983230072969 + 3 ^ 40 * 6317061 * 2
def baseEnd_6317061 : Nat := 3243688616771814203485871

theorem tailTrace_6317061 : CollatzResearch.WordTrace tailWord_6317061 prefixEnd_6317061 3243688616771814203485871 := by
  unfold tailWord_6317061
  simp only [CollatzResearch.WordTrace]
  refine ⟨230402142967374339970831037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153601428644916226647220691 230402142967374339970831037)
  ·
    refine ⟨86400803612765377489061639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230402142967374339970831037 86400803612765377489061639)
    ·
      refine ⟨129601205419148066233592459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86400803612765377489061639 129601205419148066233592459)
      ·
        refine ⟨194401808128722099350388689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129601205419148066233592459 194401808128722099350388689)
        ·
          refine ⟨145801356096541574512791517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194401808128722099350388689 145801356096541574512791517)
          ·
            refine ⟨54675508536203090442296819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145801356096541574512791517 54675508536203090442296819)
            ·
              refine ⟨82013262804304635663445229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54675508536203090442296819 82013262804304635663445229)
              ·
                refine ⟨30754973551614238373791961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82013262804304635663445229 30754973551614238373791961)
                ·
                  refine ⟨23066230163710678780343971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30754973551614238373791961 23066230163710678780343971)
                  ·
                    refine ⟨34599345245566018170515957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23066230163710678780343971 34599345245566018170515957)
                    ·
                      refine ⟨3243688616771814203485871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34599345245566018170515957 3243688616771814203485871)
                      ·
                        rfl

theorem cell23_6317061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_6317061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317061 prefixEnd_6317061 := by exact prefixLift 6317061
  have htrace : WordTrace (prefixWord ++ tailWord_6317061) baseStart_6317061 baseEnd_6317061 := by
    simpa [prefixWord, tailWord_6317061, baseEnd_6317061] using wordTrace_append hprefix tailTrace_6317061
  have hstable : (prefixWord ++ tailWord_6317061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317061).length < 2 ^ (prefixWord ++ tailWord_6317061).sum := by decide
  have hdescent : baseEnd_6317061 < baseStart_6317061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317092 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 1, 4, 2]
def baseStart_6317092 : Nat := 118140960795 + 6317092 * 2 ^ 59
def prefixEnd_6317092 : Nat := 4983230072969 + 3 ^ 40 * 6317092 * 2
def baseEnd_6317092 : Nat := 3243704534672103582198229

theorem tailTrace_6317092 : CollatzResearch.WordTrace tailWord_6317092 prefixEnd_6317092 3243704534672103582198229 := by
  unfold tailWord_6317092
  simp only [CollatzResearch.WordTrace]
  refine ⟨115201636815131016132604765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153602182420174688176806353 115201636815131016132604765)
  ·
    refine ⟨43200613805674131049726787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115201636815131016132604765 43200613805674131049726787)
    ·
      refine ⟨64800920708511196574590181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43200613805674131049726787 64800920708511196574590181)
      ·
        refine ⟨12150172632845849357735659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64800920708511196574590181 12150172632845849357735659)
        ·
          refine ⟨18225258949268774036603489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12150172632845849357735659 18225258949268774036603489)
          ·
            refine ⟨13668944211951580527452617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18225258949268774036603489 13668944211951580527452617)
            ·
              refine ⟨10251708158963685395589463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13668944211951580527452617 10251708158963685395589463)
              ·
                refine ⟨15377562238445528093384195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10251708158963685395589463 15377562238445528093384195)
                ·
                  refine ⟨23066343357668292140076293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15377562238445528093384195 23066343357668292140076293)
                  ·
                    refine ⟨4324939379562804776264305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23066343357668292140076293 4324939379562804776264305)
                    ·
                      refine ⟨3243704534672103582198229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4324939379562804776264305 3243704534672103582198229)
                      ·
                        rfl

theorem cell23_6317092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_6317092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317092 prefixEnd_6317092 := by exact prefixLift 6317092
  have htrace : WordTrace (prefixWord ++ tailWord_6317092) baseStart_6317092 baseEnd_6317092 := by
    simpa [prefixWord, tailWord_6317092, baseEnd_6317092] using wordTrace_append hprefix tailTrace_6317092
  have hstable : (prefixWord ++ tailWord_6317092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317092).length < 2 ^ (prefixWord ++ tailWord_6317092).sum := by decide
  have hdescent : baseEnd_6317092 < baseStart_6317092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317126 : List Nat := [6, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_6317126 : Nat := 118140960795 + 6317126 * 2 ^ 59
def prefixEnd_6317126 : Nat := 4983230072969 + 3 ^ 40 * 6317126 * 2
def baseEnd_6317126 : Nat := 3243721993014356449173073

theorem tailTrace_6317126 : CollatzResearch.WordTrace tailWord_6317126 prefixEnd_6317126 3243721993014356449173073 := by
  unfold tailWord_6317126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7200141053504339252248351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153603009141425904047964821 7200141053504339252248351)
  ·
    refine ⟨10800211580256508878372527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7200141053504339252248351 10800211580256508878372527)
    ·
      refine ⟨16200317370384763317558791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10800211580256508878372527 16200317370384763317558791)
      ·
        refine ⟨24300476055577144976338187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16200317370384763317558791 24300476055577144976338187)
        ·
          refine ⟨36450714083365717464507281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24300476055577144976338187 36450714083365717464507281)
          ·
            refine ⟨27338035562524288098380461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36450714083365717464507281 27338035562524288098380461)
            ·
              refine ⟨10251763335946608036892673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27338035562524288098380461 10251763335946608036892673)
              ·
                refine ⟨7688822501959956027669505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10251763335946608036892673 7688822501959956027669505)
                ·
                  refine ⟨5766616876469967020752129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7688822501959956027669505 5766616876469967020752129)
                  ·
                    refine ⟨4324962657352475265564097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5766616876469967020752129 4324962657352475265564097)
                    ·
                      refine ⟨3243721993014356449173073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4324962657352475265564097 3243721993014356449173073)
                      ·
                        rfl

theorem cell23_6317126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_6317126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317126 prefixEnd_6317126 := by exact prefixLift 6317126
  have htrace : WordTrace (prefixWord ++ tailWord_6317126) baseStart_6317126 baseEnd_6317126 := by
    simpa [prefixWord, tailWord_6317126, baseEnd_6317126] using wordTrace_append hprefix tailTrace_6317126
  have hstable : (prefixWord ++ tailWord_6317126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317126).length < 2 ^ (prefixWord ++ tailWord_6317126).sum := by decide
  have hdescent : baseEnd_6317126 < baseStart_6317126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317131 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 4]
def baseStart_6317131 : Nat := 118140960795 + 6317131 * 2 ^ 59
def prefixEnd_6317131 : Nat := 4983230072969 + 3 ^ 40 * 6317131 * 2
def baseEnd_6317131 : Nat := 3243724560417628929610549

theorem tailTrace_6317131 : CollatzResearch.WordTrace tailWord_6317131 prefixEnd_6317131 3243724560417628929610549 := by
  unfold tailWord_6317131
  simp only [CollatzResearch.WordTrace]
  refine ⟨230404696077120741925879247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153603130718080494617252831 230404696077120741925879247)
  ·
    refine ⟨345607044115681112888818871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230404696077120741925879247 345607044115681112888818871)
    ·
      refine ⟨518410566173521669333228307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345607044115681112888818871 518410566173521669333228307)
      ·
        refine ⟨777615849260282503999842461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518410566173521669333228307 777615849260282503999842461)
        ·
          refine ⟨291605943472605938999940923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 777615849260282503999842461 291605943472605938999940923)
          ·
            refine ⟨437408915208908908499911385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291605943472605938999940923 437408915208908908499911385)
            ·
              refine ⟨328056686406681681374933539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437408915208908908499911385 328056686406681681374933539)
              ·
                refine ⟨492085029610022522062400309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328056686406681681374933539 492085029610022522062400309)
                ·
                  refine ⟨46132971525939611443350029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 492085029610022522062400309 46132971525939611443350029)
                  ·
                    refine ⟨17299864322227354291256261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46132971525939611443350029 17299864322227354291256261)
                    ·
                      refine ⟨3243724560417628929610549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17299864322227354291256261 3243724560417628929610549)
                      ·
                        rfl

theorem cell23_6317131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 4].length) (baseStart_6317131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317131 prefixEnd_6317131 := by exact prefixLift 6317131
  have htrace : WordTrace (prefixWord ++ tailWord_6317131) baseStart_6317131 baseEnd_6317131 := by
    simpa [prefixWord, tailWord_6317131, baseEnd_6317131] using wordTrace_append hprefix tailTrace_6317131
  have hstable : (prefixWord ++ tailWord_6317131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317131).length < 2 ^ (prefixWord ++ tailWord_6317131).sum := by decide
  have hdescent : baseEnd_6317131 < baseStart_6317131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317148 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_6317148 : Nat := 118140960795 + 6317148 * 2 ^ 59
def prefixEnd_6317148 : Nat := 4983230072969 + 3 ^ 40 * 6317148 * 2
def baseEnd_6317148 : Nat := 3243733289588755363097971

theorem tailTrace_6317148 : CollatzResearch.WordTrace tailWord_6317148 prefixEnd_6317148 3243733289588755363097971 := by
  unfold tailWord_6317148
  simp only [CollatzResearch.WordTrace]
  refine ⟨115202658059029576914624049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153603544078706102552832065 115202658059029576914624049)
  ·
    refine ⟨86401993544272182685968037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115202658059029576914624049 86401993544272182685968037)
    ·
      refine ⟨16200373789551034253619007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86401993544272182685968037 16200373789551034253619007)
      ·
        refine ⟨24300560684326551380428511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16200373789551034253619007 24300560684326551380428511)
        ·
          refine ⟨36450841026489827070642767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24300560684326551380428511 36450841026489827070642767)
          ·
            refine ⟨54676261539734740605964151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36450841026489827070642767 54676261539734740605964151)
            ·
              refine ⟨82014392309602110908946227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54676261539734740605964151 82014392309602110908946227)
              ·
                refine ⟨123021588464403166363419341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82014392309602110908946227 123021588464403166363419341)
                ·
                  refine ⟨46133095674151187386282253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123021588464403166363419341 46133095674151187386282253)
                  ·
                    refine ⟨17299910877806695269855845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46133095674151187386282253 17299910877806695269855845)
                    ·
                      refine ⟨3243733289588755363097971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17299910877806695269855845 3243733289588755363097971)
                      ·
                        rfl

theorem cell23_6317148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_6317148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317148 prefixEnd_6317148 := by exact prefixLift 6317148
  have htrace : WordTrace (prefixWord ++ tailWord_6317148) baseStart_6317148 baseEnd_6317148 := by
    simpa [prefixWord, tailWord_6317148, baseEnd_6317148] using wordTrace_append hprefix tailTrace_6317148
  have hstable : (prefixWord ++ tailWord_6317148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317148).length < 2 ^ (prefixWord ++ tailWord_6317148).sum := by decide
  have hdescent : baseEnd_6317148 < baseStart_6317148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317168 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 3]
def baseStart_6317168 : Nat := 118140960795 + 6317168 * 2 ^ 59
def prefixEnd_6317168 : Nat := 4983230072969 + 3 ^ 40 * 6317168 * 2
def baseEnd_6317168 : Nat := 3243743559201845284847879

theorem tailTrace_6317168 : CollatzResearch.WordTrace tailWord_6317168 prefixEnd_6317168 3243743559201845284847879 := by
  unfold tailWord_6317168
  simp only [CollatzResearch.WordTrace]
  refine ⟨115203022788993348622488079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153604030385324464829984105 115203022788993348622488079)
  ·
    refine ⟨172804534183490022933732119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115203022788993348622488079 172804534183490022933732119)
    ·
      refine ⟨259206801275235034400598179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172804534183490022933732119 259206801275235034400598179)
      ·
        refine ⟨388810201912852551600897269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259206801275235034400598179 388810201912852551600897269)
        ·
          refine ⟨36450956429329926712584119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 388810201912852551600897269 36450956429329926712584119)
          ·
            refine ⟨54676434643994890068876179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36450956429329926712584119 54676434643994890068876179)
            ·
              refine ⟨82014651965992335103314269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54676434643994890068876179 82014651965992335103314269)
              ·
                refine ⟨30755494487247125663742851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82014651965992335103314269 30755494487247125663742851)
                ·
                  refine ⟨46133241730870688495614277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30755494487247125663742851 46133241730870688495614277)
                  ·
                    refine ⟨8649982824538254092927677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46133241730870688495614277 8649982824538254092927677)
                    ·
                      refine ⟨3243743559201845284847879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8649982824538254092927677 3243743559201845284847879)
                      ·
                        rfl

theorem cell23_6317168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 3].length) (baseStart_6317168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317168 prefixEnd_6317168 := by exact prefixLift 6317168
  have htrace : WordTrace (prefixWord ++ tailWord_6317168) baseStart_6317168 baseEnd_6317168 := by
    simpa [prefixWord, tailWord_6317168, baseEnd_6317168] using wordTrace_append hprefix tailTrace_6317168
  have hstable : (prefixWord ++ tailWord_6317168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317168).length < 2 ^ (prefixWord ++ tailWord_6317168).sum := by decide
  have hdescent : baseEnd_6317168 < baseStart_6317168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317185 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_6317185 : Nat := 118140960795 + 6317185 * 2 ^ 59
def prefixEnd_6317185 : Nat := 4983230072969 + 3 ^ 40 * 6317185 * 2
def baseEnd_6317185 : Nat := 3243752288372971718335301

theorem tailTrace_6317185 : CollatzResearch.WordTrace tailWord_6317185 prefixEnd_6317185 3243752288372971718335301 := by
  unfold tailWord_6317185
  simp only [CollatzResearch.WordTrace]
  refine ⟨230406665618925109148345009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153604443745950072765563339 230406665618925109148345009)
  ·
    refine ⟨172804999214193831861258757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230406665618925109148345009 172804999214193831861258757)
    ·
      refine ⟨32400937352661343473986017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172804999214193831861258757 32400937352661343473986017)
      ·
        refine ⟨24300703014496007605489513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32400937352661343473986017 24300703014496007605489513)
        ·
          refine ⟨18225527260872005704117135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24300703014496007605489513 18225527260872005704117135)
          ·
            refine ⟨27338290891308008556175703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18225527260872005704117135 27338290891308008556175703)
            ·
              refine ⟨41007436336962012834263555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27338290891308008556175703 41007436336962012834263555)
              ·
                refine ⟨61511154505443019251395333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41007436336962012834263555 61511154505443019251395333)
                ·
                  refine ⟨11533341469770566109636625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61511154505443019251395333 11533341469770566109636625)
                  ·
                    refine ⟨8650006102327924582227469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11533341469770566109636625 8650006102327924582227469)
                    ·
                      refine ⟨3243752288372971718335301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8650006102327924582227469 3243752288372971718335301)
                      ·
                        rfl

theorem cell23_6317185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_6317185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317185 prefixEnd_6317185 := by exact prefixLift 6317185
  have htrace : WordTrace (prefixWord ++ tailWord_6317185) baseStart_6317185 baseEnd_6317185 := by
    simpa [prefixWord, tailWord_6317185, baseEnd_6317185] using wordTrace_append hprefix tailTrace_6317185
  have hstable : (prefixWord ++ tailWord_6317185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317185).length < 2 ^ (prefixWord ++ tailWord_6317185).sum := by decide
  have hdescent : baseEnd_6317185 < baseStart_6317185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317188 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 8]
def baseStart_6317188 : Nat := 118140960795 + 6317188 * 2 ^ 59
def prefixEnd_6317188 : Nat := 4983230072969 + 3 ^ 40 * 6317188 * 2
def baseEnd_6317188 : Nat := 360417092090548356288643

theorem tailTrace_6317188 : CollatzResearch.WordTrace tailWord_6317188 prefixEnd_6317188 360417092090548356288643 := by
  unfold tailWord_6317188
  simp only [CollatzResearch.WordTrace]
  refine ⟨115203387518957120330352109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153604516691942827107136145 115203387518957120330352109)
  ·
    refine ⟨43201270319608920123882041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115203387518957120330352109 43201270319608920123882041)
    ·
      refine ⟨32400952739706690092911531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43201270319608920123882041 32400952739706690092911531)
      ·
        refine ⟨48601429109560035139367297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32400952739706690092911531 48601429109560035139367297)
        ·
          refine ⟨36451071832170026354525473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48601429109560035139367297 36451071832170026354525473)
          ·
            refine ⟨27338303874127519765894105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36451071832170026354525473 27338303874127519765894105)
            ·
              refine ⟨20503727905595639824420579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27338303874127519765894105 20503727905595639824420579)
              ·
                refine ⟨30755591858393459736630869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20503727905595639824420579 30755591858393459736630869)
                ·
                  refine ⟨360417092090548356288643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30755591858393459736630869 360417092090548356288643)
                  ·
                    rfl

theorem cell23_6317188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_6317188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317188 prefixEnd_6317188 := by exact prefixLift 6317188
  have htrace : WordTrace (prefixWord ++ tailWord_6317188) baseStart_6317188 baseEnd_6317188 := by
    simpa [prefixWord, tailWord_6317188, baseEnd_6317188] using wordTrace_append hprefix tailTrace_6317188
  have hstable : (prefixWord ++ tailWord_6317188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317188).length < 2 ^ (prefixWord ++ tailWord_6317188).sum := by decide
  have hdescent : baseEnd_6317188 < baseStart_6317188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317292 : List Nat := [2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 3]
def baseStart_6317292 : Nat := 118140960795 + 6317292 * 2 ^ 59
def prefixEnd_6317292 : Nat := 4983230072969 + 3 ^ 40 * 6317292 * 2
def baseEnd_6317292 : Nat := 3243807230803002799697309

theorem tailTrace_6317292 : CollatzResearch.WordTrace tailWord_6317292 prefixEnd_6317292 3243807230803002799697309 := by
  unfold tailWord_6317292
  simp only [CollatzResearch.WordTrace]
  refine ⟨115205284114768733211245065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153607045486358310948326753 115205284114768733211245065)
  ·
    refine ⟨86403963086076549908433799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115205284114768733211245065 86403963086076549908433799)
    ·
      refine ⟨129605944629114824862650699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86403963086076549908433799 129605944629114824862650699)
      ·
        refine ⟨194408916943672237293976049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129605944629114824862650699 194408916943672237293976049)
        ·
          refine ⟨145806687707754177970482037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194408916943672237293976049 145806687707754177970482037)
          ·
            refine ⟨13669376972601954184732691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145806687707754177970482037 13669376972601954184732691)
            ·
              refine ⟨20504065458902931277099037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13669376972601954184732691 20504065458902931277099037)
              ·
                refine ⟨7689024547088599228912139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20504065458902931277099037 7689024547088599228912139)
                ·
                  refine ⟨11533536820632898843368209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7689024547088599228912139 11533536820632898843368209)
                  ·
                    refine ⟨8650152615474674132526157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11533536820632898843368209 8650152615474674132526157)
                    ·
                      refine ⟨3243807230803002799697309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8650152615474674132526157 3243807230803002799697309)
                      ·
                        rfl

theorem cell23_6317292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_6317292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317292 prefixEnd_6317292 := by exact prefixLift 6317292
  have htrace : WordTrace (prefixWord ++ tailWord_6317292) baseStart_6317292 baseEnd_6317292 := by
    simpa [prefixWord, tailWord_6317292, baseEnd_6317292] using wordTrace_append hprefix tailTrace_6317292
  have hstable : (prefixWord ++ tailWord_6317292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317292).length < 2 ^ (prefixWord ++ tailWord_6317292).sum := by decide
  have hdescent : baseEnd_6317292 < baseStart_6317292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317328 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 4]
def baseStart_6317328 : Nat := 118140960795 + 6317328 * 2 ^ 59
def prefixEnd_6317328 : Nat := 4983230072969 + 3 ^ 40 * 6317328 * 2
def baseEnd_6317328 : Nat := 3243825716106564658847143

theorem tailTrace_6317328 : CollatzResearch.WordTrace tailWord_6317328 prefixEnd_6317328 3243825716106564658847143 := by
  unfold tailWord_6317328
  simp only [CollatzResearch.WordTrace]
  refine ⟨115205940628703522285400319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153607920838271363047200425 115205940628703522285400319)
  ·
    refine ⟨172808910943055283428100479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115205940628703522285400319 172808910943055283428100479)
    ·
      refine ⟨259213366414582925142150719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172808910943055283428100479 259213366414582925142150719)
      ·
        refine ⟨388820049621874387713226079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259213366414582925142150719 388820049621874387713226079)
        ·
          refine ⟨583230074432811581569839119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388820049621874387713226079 583230074432811581569839119)
          ·
            refine ⟨874845111649217372354758679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583230074432811581569839119 874845111649217372354758679)
            ·
              refine ⟨1312267667473826058532138019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874845111649217372354758679 1312267667473826058532138019)
              ·
                refine ⟨1968401501210739087798207029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312267667473826058532138019 1968401501210739087798207029)
                ·
                  refine ⟨184537640738506789481081909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1968401501210739087798207029 184537640738506789481081909)
                  ·
                    refine ⟨17300403819235011513851429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 184537640738506789481081909 17300403819235011513851429)
                    ·
                      refine ⟨3243825716106564658847143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17300403819235011513851429 3243825716106564658847143)
                      ·
                        rfl

theorem cell23_6317328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_6317328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317328 prefixEnd_6317328 := by exact prefixLift 6317328
  have htrace : WordTrace (prefixWord ++ tailWord_6317328) baseStart_6317328 baseEnd_6317328 := by
    simpa [prefixWord, tailWord_6317328, baseEnd_6317328] using wordTrace_append hprefix tailTrace_6317328
  have hstable : (prefixWord ++ tailWord_6317328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317328).length < 2 ^ (prefixWord ++ tailWord_6317328).sum := by decide
  have hdescent : baseEnd_6317328 < baseStart_6317328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317349 : List Nat := [1, 3, 1, 2, 4, 1, 2, 3, 1, 3, 2]
def baseStart_6317349 : Nat := 118140960795 + 6317349 * 2 ^ 59
def prefixEnd_6317349 : Nat := 4983230072969 + 3 ^ 40 * 6317349 * 2
def baseEnd_6317349 : Nat := 3243836499200309076684547

theorem tailTrace_6317349 : CollatzResearch.WordTrace tailWord_6317349 prefixEnd_6317349 3243836499200309076684547 := by
  unfold tailWord_6317349
  simp only [CollatzResearch.WordTrace]
  refine ⟨230412647190330965157315101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153608431460220643438210067 230412647190330965157315101)
  ·
    refine ⟨86404742696374111933993163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230412647190330965157315101 86404742696374111933993163)
    ·
      refine ⟨129607114044561167900989745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86404742696374111933993163 129607114044561167900989745)
      ·
        refine ⟨97205335533420875925742309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129607114044561167900989745 97205335533420875925742309)
        ·
          refine ⟨18226000412516414236076683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97205335533420875925742309 18226000412516414236076683)
          ·
            refine ⟨27339000618774621354115025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18226000412516414236076683 27339000618774621354115025)
            ·
              refine ⟨20504250464080966015586269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27339000618774621354115025 20504250464080966015586269)
              ·
                refine ⟨7689093924030362255844851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20504250464080966015586269 7689093924030362255844851)
                ·
                  refine ⟨11533640886045543383767277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7689093924030362255844851 11533640886045543383767277)
                  ·
                    refine ⟨4325115332267078768912729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11533640886045543383767277 4325115332267078768912729)
                    ·
                      refine ⟨3243836499200309076684547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325115332267078768912729 3243836499200309076684547)
                      ·
                        rfl

theorem cell23_6317349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_6317349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317349 prefixEnd_6317349 := by exact prefixLift 6317349
  have htrace : WordTrace (prefixWord ++ tailWord_6317349) baseStart_6317349 baseEnd_6317349 := by
    simpa [prefixWord, tailWord_6317349, baseEnd_6317349] using wordTrace_append hprefix tailTrace_6317349
  have hstable : (prefixWord ++ tailWord_6317349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317349).length < 2 ^ (prefixWord ++ tailWord_6317349).sum := by decide
  have hdescent : baseEnd_6317349 < baseStart_6317349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317425 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_6317425 : Nat := 118140960795 + 6317425 * 2 ^ 59
def prefixEnd_6317425 : Nat := 4983230072969 + 3 ^ 40 * 6317425 * 2
def baseEnd_6317425 : Nat := 3243875523730050779334197

theorem tailTrace_6317425 : CollatzResearch.WordTrace tailWord_6317425 prefixEnd_6317425 3243875523730050779334197 := by
  unfold tailWord_6317425
  simp only [CollatzResearch.WordTrace]
  refine ⟨230415419138055630137081729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153610279425370420091387819 230415419138055630137081729)
  ·
    refine ⟨172811564353541722602811297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230415419138055630137081729 172811564353541722602811297)
    ·
      refine ⟨129608673265156291952108473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172811564353541722602811297 129608673265156291952108473)
      ·
        refine ⟨97206504948867218964081355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129608673265156291952108473 97206504948867218964081355)
        ·
          refine ⟨145809757423300828446122033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97206504948867218964081355 145809757423300828446122033)
          ·
            refine ⟨109357318067475621334591525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145809757423300828446122033 109357318067475621334591525)
            ·
              refine ⟨20504497137651679000235911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109357318067475621334591525 20504497137651679000235911)
              ·
                refine ⟨30756745706477518500353867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20504497137651679000235911 30756745706477518500353867)
                ·
                  refine ⟨46135118559716277750530801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30756745706477518500353867 46135118559716277750530801)
                  ·
                    refine ⟨34601338919787208312898101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46135118559716277750530801 34601338919787208312898101)
                    ·
                      refine ⟨3243875523730050779334197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34601338919787208312898101 3243875523730050779334197)
                      ·
                        rfl

theorem cell23_6317425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_6317425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317425 prefixEnd_6317425 := by exact prefixLift 6317425
  have htrace : WordTrace (prefixWord ++ tailWord_6317425) baseStart_6317425 baseEnd_6317425 := by
    simpa [prefixWord, tailWord_6317425, baseEnd_6317425] using wordTrace_append hprefix tailTrace_6317425
  have hstable : (prefixWord ++ tailWord_6317425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317425).length < 2 ^ (prefixWord ++ tailWord_6317425).sum := by decide
  have hdescent : baseEnd_6317425 < baseStart_6317425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317429 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_6317429 : Nat := 118140960795 + 6317429 * 2 ^ 59
def prefixEnd_6317429 : Nat := 4983230072969 + 3 ^ 40 * 6317429 * 2
def baseEnd_6317429 : Nat := 3243877577652668763684179

theorem tailTrace_6317429 : CollatzResearch.WordTrace tailWord_6317429 prefixEnd_6317429 3243877577652668763684179 := by
  unfold tailWord_6317429
  simp only [CollatzResearch.WordTrace]
  refine ⟨230415565030041138820227341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153610376686694092546818227 230415565030041138820227341)
  ·
    refine ⟨86405836886265427057585253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230415565030041138820227341 86405836886265427057585253)
    ·
      refine ⟨16201094416174767573297235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86405836886265427057585253 16201094416174767573297235)
      ·
        refine ⟨24301641624262151359945853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16201094416174767573297235 24301641624262151359945853)
        ·
          refine ⟨9113115609098306759979695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24301641624262151359945853 9113115609098306759979695)
          ·
            refine ⟨13669673413647460139969543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9113115609098306759979695 13669673413647460139969543)
            ·
              refine ⟨20504510120471190209954315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13669673413647460139969543 20504510120471190209954315)
              ·
                refine ⟨30756765180706785314931473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20504510120471190209954315 30756765180706785314931473)
                ·
                  refine ⟨23067573885530088986198605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30756765180706785314931473 23067573885530088986198605)
                  ·
                    refine ⟨8650340207073783369824477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23067573885530088986198605 8650340207073783369824477)
                    ·
                      refine ⟨3243877577652668763684179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8650340207073783369824477 3243877577652668763684179)
                      ·
                        rfl

theorem cell23_6317429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_6317429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317429 prefixEnd_6317429 := by exact prefixLift 6317429
  have htrace : WordTrace (prefixWord ++ tailWord_6317429) baseStart_6317429 baseEnd_6317429 := by
    simpa [prefixWord, tailWord_6317429, baseEnd_6317429] using wordTrace_append hprefix tailTrace_6317429
  have hstable : (prefixWord ++ tailWord_6317429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317429).length < 2 ^ (prefixWord ++ tailWord_6317429).sum := by decide
  have hdescent : baseEnd_6317429 < baseStart_6317429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317435 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 4]
def baseStart_6317435 : Nat := 118140960795 + 6317435 * 2 ^ 59
def prefixEnd_6317435 : Nat := 4983230072969 + 3 ^ 40 * 6317435 * 2
def baseEnd_6317435 : Nat := 3243880658536595740209151

theorem tailTrace_6317435 : CollatzResearch.WordTrace tailWord_6317435 prefixEnd_6317435 3243880658536595740209151 := by
  unfold tailWord_6317435
  simp only [CollatzResearch.WordTrace]
  refine ⟨230415783868019401844945759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153610522578679601229963839 230415783868019401844945759)
  ·
    refine ⟨345623675802029102767418639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230415783868019401844945759 345623675802029102767418639)
    ·
      refine ⟨518435513703043654151127959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345623675802029102767418639 518435513703043654151127959)
      ·
        refine ⟨777653270554565481226691939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518435513703043654151127959 777653270554565481226691939)
        ·
          refine ⟨1166479905831848221840037909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777653270554565481226691939 1166479905831848221840037909)
          ·
            refine ⟨54678745585867885398751777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1166479905831848221840037909 54678745585867885398751777)
            ·
              refine ⟨41009059189400914049063833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54678745585867885398751777 41009059189400914049063833)
              ·
                refine ⟨30756794392050685536797875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41009059189400914049063833 30756794392050685536797875)
                ·
                  refine ⟨46135191588076028305196813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30756794392050685536797875 46135191588076028305196813)
                  ·
                    refine ⟨17300696845528510614448805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46135191588076028305196813 17300696845528510614448805)
                    ·
                      refine ⟨3243880658536595740209151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17300696845528510614448805 3243880658536595740209151)
                      ·
                        rfl

theorem cell23_6317435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 4].length) (baseStart_6317435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317435 prefixEnd_6317435 := by exact prefixLift 6317435
  have htrace : WordTrace (prefixWord ++ tailWord_6317435) baseStart_6317435 baseEnd_6317435 := by
    simpa [prefixWord, tailWord_6317435, baseEnd_6317435] using wordTrace_append hprefix tailTrace_6317435
  have hstable : (prefixWord ++ tailWord_6317435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317435).length < 2 ^ (prefixWord ++ tailWord_6317435).sum := by decide
  have hdescent : baseEnd_6317435 < baseStart_6317435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317449 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 2, 5]
def baseStart_6317449 : Nat := 118140960795 + 6317449 * 2 ^ 59
def prefixEnd_6317449 : Nat := 4983230072969 + 3 ^ 40 * 6317449 * 2
def baseEnd_6317449 : Nat := 1081295949088586228478029

theorem tailTrace_6317449 : CollatzResearch.WordTrace tailWord_6317449 prefixEnd_6317449 1081295949088586228478029 := by
  unfold tailWord_6317449
  simp only [CollatzResearch.WordTrace]
  refine ⟨230416294489968682235955401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153610862993312454823970267 230416294489968682235955401)
  ·
    refine ⟨172812220867476511676966551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230416294489968682235955401 172812220867476511676966551)
    ·
      refine ⟨259218331301214767515449827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172812220867476511676966551 259218331301214767515449827)
      ·
        refine ⟨388827496951822151273174741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259218331301214767515449827 388827496951822151273174741)
        ·
          refine ⟨9113144459808331670465033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 388827496951822151273174741 9113144459808331670465033)
          ·
            refine ⟨6834858344856248752848775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9113144459808331670465033 6834858344856248752848775)
            ·
              refine ⟨10252287517284373129273163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6834858344856248752848775 10252287517284373129273163)
              ·
                refine ⟨15378431275926559693909745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10252287517284373129273163 15378431275926559693909745)
                ·
                  refine ⟨11533823456944919770432309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15378431275926559693909745 11533823456944919770432309)
                  ·
                    refine ⟨1081295949088586228478029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11533823456944919770432309 1081295949088586228478029)
                    ·
                      rfl

theorem cell23_6317449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 5].length) (baseStart_6317449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317449 prefixEnd_6317449 := by exact prefixLift 6317449
  have htrace : WordTrace (prefixWord ++ tailWord_6317449) baseStart_6317449 baseEnd_6317449 := by
    simpa [prefixWord, tailWord_6317449, baseEnd_6317449] using wordTrace_append hprefix tailTrace_6317449
  have hstable : (prefixWord ++ tailWord_6317449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317449).length < 2 ^ (prefixWord ++ tailWord_6317449).sum := by decide
  have hdescent : baseEnd_6317449 < baseStart_6317449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317452 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 1, 6, 2]
def baseStart_6317452 : Nat := 118140960795 + 6317452 * 2 ^ 59
def prefixEnd_6317452 : Nat := 4983230072969 + 3 ^ 40 * 6317452 * 2
def baseEnd_6317452 : Nat := 3243889387707722173696573

theorem tailTrace_6317452 : CollatzResearch.WordTrace tailWord_6317452 prefixEnd_6317452 3243889387707722173696573 := by
  unfold tailWord_6317452
  simp only [CollatzResearch.WordTrace]
  refine ⟨115208201954478906874157305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153610935939305209165543073 115208201954478906874157305)
  ·
    refine ⟨86406151465859180155617979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115208201954478906874157305 86406151465859180155617979)
    ·
      refine ⟨129609227198788770233426969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86406151465859180155617979 129609227198788770233426969)
      ·
        refine ⟨97206920399091577675070227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129609227198788770233426969 97206920399091577675070227)
        ·
          refine ⟨145810380598637366512605341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97206920399091577675070227 145810380598637366512605341)
          ·
            refine ⟨54678892724489012442227003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145810380598637366512605341 54678892724489012442227003)
            ·
              refine ⟨82018339086733518663340505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54678892724489012442227003 82018339086733518663340505)
              ·
                refine ⟨61513754315050138997505379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82018339086733518663340505 61513754315050138997505379)
                ·
                  refine ⟨92270631472575208496258069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61513754315050138997505379 92270631472575208496258069)
                  ·
                    refine ⟨4325185850276962898262097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92270631472575208496258069 4325185850276962898262097)
                    ·
                      refine ⟨3243889387707722173696573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325185850276962898262097 3243889387707722173696573)
                      ·
                        rfl

theorem cell23_6317452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_6317452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317452 prefixEnd_6317452 := by exact prefixLift 6317452
  have htrace : WordTrace (prefixWord ++ tailWord_6317452) baseStart_6317452 baseEnd_6317452 := by
    simpa [prefixWord, tailWord_6317452, baseEnd_6317452] using wordTrace_append hprefix tailTrace_6317452
  have hstable : (prefixWord ++ tailWord_6317452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317452).length < 2 ^ (prefixWord ++ tailWord_6317452).sum := by decide
  have hdescent : baseEnd_6317452 < baseStart_6317452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317465 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 6]
def baseStart_6317465 : Nat := 118140960795 + 6317465 * 2 ^ 59
def prefixEnd_6317465 : Nat := 4983230072969 + 3 ^ 40 * 6317465 * 2
def baseEnd_6317465 : Nat := 3243896062956230622834013

theorem tailTrace_6317465 : CollatzResearch.WordTrace tailWord_6317465 prefixEnd_6317465 3243896062956230622834013 := by
  unfold tailWord_6317465
  simp only [CollatzResearch.WordTrace]
  refine ⟨230416878057910716968537849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153611252038607144645691899 230416878057910716968537849)
  ·
    refine ⟨172812658543433037726403387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230416878057910716968537849 172812658543433037726403387)
    ·
      refine ⟨259218987815149556589605081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172812658543433037726403387 259218987815149556589605081)
      ·
        refine ⟨194414240861362167442203811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259218987815149556589605081 194414240861362167442203811)
        ·
          refine ⟨291621361292043251163305717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194414240861362167442203811 291621361292043251163305717)
          ·
            refine ⟨27339502621129054796559911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 291621361292043251163305717 27339502621129054796559911)
            ·
              refine ⟨41009253931693582194839867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27339502621129054796559911 41009253931693582194839867)
              ·
                refine ⟨61513880897540373292259801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41009253931693582194839867 61513880897540373292259801)
                ·
                  refine ⟨46135410673155279969194851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61513880897540373292259801 46135410673155279969194851)
                  ·
                    refine ⟨69203116009732919953792277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46135410673155279969194851 69203116009732919953792277)
                    ·
                      refine ⟨3243896062956230622834013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69203116009732919953792277 3243896062956230622834013)
                      ·
                        rfl

theorem cell23_6317465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_6317465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317465 prefixEnd_6317465 := by exact prefixLift 6317465
  have htrace : WordTrace (prefixWord ++ tailWord_6317465) baseStart_6317465 baseEnd_6317465 := by
    simpa [prefixWord, tailWord_6317465, baseEnd_6317465] using wordTrace_append hprefix tailTrace_6317465
  have hstable : (prefixWord ++ tailWord_6317465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317465).length < 2 ^ (prefixWord ++ tailWord_6317465).sum := by decide
  have hdescent : baseEnd_6317465 < baseStart_6317465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317469 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_6317469 : Nat := 118140960795 + 6317469 * 2 ^ 59
def prefixEnd_6317469 : Nat := 4983230072969 + 3 ^ 40 * 6317469 * 2
def baseEnd_6317469 : Nat := 3243898116878848607183995

theorem tailTrace_6317469 : CollatzResearch.WordTrace tailWord_6317469 prefixEnd_6317469 3243898116878848607183995 := by
  unfold tailWord_6317469
  simp only [CollatzResearch.WordTrace]
  refine ⟨230417023949896225651683461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153611349299930817101122307 230417023949896225651683461)
  ·
    refine ⟨43203191990605542309690649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230417023949896225651683461 43203191990605542309690649)
    ·
      refine ⟨32402393992954156732267987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43203191990605542309690649 32402393992954156732267987)
      ·
        refine ⟨48603590989431235098401981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32402393992954156732267987 48603590989431235098401981)
        ·
          refine ⟨18226346621036713161900743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48603590989431235098401981 18226346621036713161900743)
          ·
            refine ⟨27339519931555069742851115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18226346621036713161900743 27339519931555069742851115)
            ·
              refine ⟨41009279897332604614276673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27339519931555069742851115 41009279897332604614276673)
              ·
                refine ⟨30756959922999453460707505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41009279897332604614276673 30756959922999453460707505)
                ·
                  refine ⟨23067719942249590095530629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30756959922999453460707505 23067719942249590095530629)
                  ·
                    refine ⟨4325197489171798142911993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23067719942249590095530629 4325197489171798142911993)
                    ·
                      refine ⟨3243898116878848607183995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325197489171798142911993 3243898116878848607183995)
                      ·
                        rfl

theorem cell23_6317469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_6317469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317469 prefixEnd_6317469 := by exact prefixLift 6317469
  have htrace : WordTrace (prefixWord ++ tailWord_6317469) baseStart_6317469 baseEnd_6317469 := by
    simpa [prefixWord, tailWord_6317469, baseEnd_6317469] using wordTrace_append hprefix tailTrace_6317469
  have hstable : (prefixWord ++ tailWord_6317469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317469).length < 2 ^ (prefixWord ++ tailWord_6317469).sum := by decide
  have hdescent : baseEnd_6317469 < baseStart_6317469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317472 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 3]
def baseStart_6317472 : Nat := 118140960795 + 6317472 * 2 ^ 59
def prefixEnd_6317472 : Nat := 4983230072969 + 3 ^ 40 * 6317472 * 2
def baseEnd_6317472 : Nat := 3243899657320812095446481

theorem tailTrace_6317472 : CollatzResearch.WordTrace tailWord_6317472 prefixEnd_6317472 3243899657320812095446481 := by
  unfold tailWord_6317472
  simp only [CollatzResearch.WordTrace]
  refine ⟨115208566684442678582021335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153611422245923571442695113 115208566684442678582021335)
  ·
    refine ⟨172812850026664017873032003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115208566684442678582021335 172812850026664017873032003)
    ·
      refine ⟨259219275039996026809548005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172812850026664017873032003 259219275039996026809548005)
      ·
        refine ⟨48603614069999255026790251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259219275039996026809548005 48603614069999255026790251)
        ·
          refine ⟨72905421104998882540185377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48603614069999255026790251 72905421104998882540185377)
          ·
            refine ⟨54679065828749161905139033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72905421104998882540185377 54679065828749161905139033)
            ·
              refine ⟨41009299371561871428854275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54679065828749161905139033 41009299371561871428854275)
              ·
                refine ⟨61513949057342807143281413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41009299371561871428854275 61513949057342807143281413)
                ·
                  refine ⟨11533865448251776339365265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61513949057342807143281413 11533865448251776339365265)
                  ·
                    refine ⟨8650399086188832254523949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11533865448251776339365265 8650399086188832254523949)
                    ·
                      refine ⟨3243899657320812095446481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8650399086188832254523949 3243899657320812095446481)
                      ·
                        rfl

theorem cell23_6317472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_6317472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317472 prefixEnd_6317472 := by exact prefixLift 6317472
  have htrace : WordTrace (prefixWord ++ tailWord_6317472) baseStart_6317472 baseEnd_6317472 := by
    simpa [prefixWord, tailWord_6317472, baseEnd_6317472] using wordTrace_append hprefix tailTrace_6317472
  have hstable : (prefixWord ++ tailWord_6317472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317472).length < 2 ^ (prefixWord ++ tailWord_6317472).sum := by decide
  have hdescent : baseEnd_6317472 < baseStart_6317472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317475 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 8]
def baseStart_6317475 : Nat := 118140960795 + 6317475 * 2 ^ 59
def prefixEnd_6317475 : Nat := 4983230072969 + 3 ^ 40 * 6317475 * 2
def baseEnd_6317475 : Nat := 360433466418086175967663

theorem tailTrace_6317475 : CollatzResearch.WordTrace tailWord_6317475 prefixEnd_6317475 360433466418086175967663 := by
  unfold tailWord_6317475
  simp only [CollatzResearch.WordTrace]
  refine ⟨230417242787874488676401879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153611495191916325784267919 230417242787874488676401879)
  ·
    refine ⟨345625864181811733014602819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230417242787874488676401879 345625864181811733014602819)
    ·
      refine ⟨518438796272717599521904229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345625864181811733014602819 518438796272717599521904229)
      ·
        refine ⟨97207274301134549910357043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 518438796272717599521904229 97207274301134549910357043)
        ·
          refine ⟨145810911451701824865535565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97207274301134549910357043 145810911451701824865535565)
          ·
            refine ⟨54679091794388184324575837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145810911451701824865535565 54679091794388184324575837)
            ·
              refine ⟨20504659422895569121715939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54679091794388184324575837 20504659422895569121715939)
              ·
                refine ⟨30756989134343353682573909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20504659422895569121715939 30756989134343353682573909)
                ·
                  refine ⟨360433466418086175967663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30756989134343353682573909 360433466418086175967663)
                  ·
                    rfl

theorem cell23_6317475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 8].length) (baseStart_6317475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317475 prefixEnd_6317475 := by exact prefixLift 6317475
  have htrace : WordTrace (prefixWord ++ tailWord_6317475) baseStart_6317475 baseEnd_6317475 := by
    simpa [prefixWord, tailWord_6317475, baseEnd_6317475] using wordTrace_append hprefix tailTrace_6317475
  have hstable : (prefixWord ++ tailWord_6317475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317475).length < 2 ^ (prefixWord ++ tailWord_6317475).sum := by decide
  have hdescent : baseEnd_6317475 < baseStart_6317475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317479 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 3, 4]
def baseStart_6317479 : Nat := 118140960795 + 6317479 * 2 ^ 59
def prefixEnd_6317479 : Nat := 4983230072969 + 3 ^ 40 * 6317479 * 2
def baseEnd_6317479 : Nat := 1081301083895131189352983

theorem tailTrace_6317479 : CollatzResearch.WordTrace tailWord_6317479 prefixEnd_6317479 1081301083895131189352983 := by
  unfold tailWord_6317479
  simp only [CollatzResearch.WordTrace]
  refine ⟨230417388679859997359547491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153611592453239998239698327 230417388679859997359547491)
  ·
    refine ⟨345626083019789996039321237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230417388679859997359547491 345626083019789996039321237)
    ·
      refine ⟨16201222641552656064343183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 345626083019789996039321237 16201222641552656064343183)
      ·
        refine ⟨24301833962328984096514775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16201222641552656064343183 24301833962328984096514775)
        ·
          refine ⟨36452750943493476144772163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24301833962328984096514775 36452750943493476144772163)
          ·
            refine ⟨54679126415240214217158245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36452750943493476144772163 54679126415240214217158245)
            ·
              refine ⟨10252336202857540165717171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54679126415240214217158245 10252336202857540165717171)
              ·
                refine ⟨15378504304286310248575757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10252336202857540165717171 15378504304286310248575757)
                ·
                  refine ⟨5766939114107366343215909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15378504304286310248575757 5766939114107366343215909)
                  ·
                    refine ⟨1081301083895131189352983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5766939114107366343215909 1081301083895131189352983)
                    ·
                      rfl

theorem cell23_6317479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_6317479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317479 prefixEnd_6317479 := by exact prefixLift 6317479
  have htrace : WordTrace (prefixWord ++ tailWord_6317479) baseStart_6317479 baseEnd_6317479 := by
    simpa [prefixWord, tailWord_6317479, baseEnd_6317479] using wordTrace_append hprefix tailTrace_6317479
  have hstable : (prefixWord ++ tailWord_6317479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317479).length < 2 ^ (prefixWord ++ tailWord_6317479).sum := by decide
  have hdescent : baseEnd_6317479 < baseStart_6317479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317495 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_6317495 : Nat := 118140960795 + 6317495 * 2 ^ 59
def prefixEnd_6317495 : Nat := 4983230072969 + 3 ^ 40 * 6317495 * 2
def baseEnd_6317495 : Nat := 3243911467375865505458875

theorem tailTrace_6317495 : CollatzResearch.WordTrace tailWord_6317495 prefixEnd_6317495 3243911467375865505458875 := by
  unfold tailWord_6317495
  simp only [CollatzResearch.WordTrace]
  refine ⟨230417972247802032092129939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153611981498534688061419959 230417972247802032092129939)
  ·
    refine ⟨345626958371703048138194909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230417972247802032092129939 345626958371703048138194909)
    ·
      refine ⟨129610109389388643051823091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345626958371703048138194909 129610109389388643051823091)
      ·
        refine ⟨194415164084082964577734637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129610109389388643051823091 194415164084082964577734637)
        ·
          refine ⟨72905686531531111716650489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194415164084082964577734637 72905686531531111716650489)
          ·
            refine ⟨54679264898648333787487867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72905686531531111716650489 54679264898648333787487867)
            ·
              refine ⟨82018897347972500681231801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54679264898648333787487867 82018897347972500681231801)
              ·
                refine ⟨61514173010979375510923851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82018897347972500681231801 61514173010979375510923851)
                ·
                  refine ⟨92271259516469063266385777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61514173010979375510923851 92271259516469063266385777)
                  ·
                    refine ⟨69203444637351797449789333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92271259516469063266385777 69203444637351797449789333)
                    ·
                      refine ⟨3243911467375865505458875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69203444637351797449789333 3243911467375865505458875)
                      ·
                        rfl

theorem cell23_6317495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_6317495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317495 prefixEnd_6317495 := by exact prefixLift 6317495
  have htrace : WordTrace (prefixWord ++ tailWord_6317495) baseStart_6317495 baseEnd_6317495 := by
    simpa [prefixWord, tailWord_6317495, baseEnd_6317495] using wordTrace_append hprefix tailTrace_6317495
  have hstable : (prefixWord ++ tailWord_6317495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317495).length < 2 ^ (prefixWord ++ tailWord_6317495).sum := by decide
  have hdescent : baseEnd_6317495 < baseStart_6317495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317502 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_6317502 : Nat := 118140960795 + 6317502 * 2 ^ 59
def prefixEnd_6317502 : Nat := 4983230072969 + 3 ^ 40 * 6317502 * 2
def baseEnd_6317502 : Nat := 3243915061740446978071343

theorem tailTrace_6317502 : CollatzResearch.WordTrace tailWord_6317502 prefixEnd_6317502 3243915061740446978071343 := by
  unfold tailWord_6317502
  simp only [CollatzResearch.WordTrace]
  refine ⟨28802278444847084035954345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153612151705851114858423173 28802278444847084035954345)
  ·
    refine ⟨21601708833635313026965759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28802278444847084035954345 21601708833635313026965759)
    ·
      refine ⟨32402563250452969540448639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21601708833635313026965759 32402563250452969540448639)
      ·
        refine ⟨48603844875679454310672959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32402563250452969540448639 48603844875679454310672959)
        ·
          refine ⟨72905767313519181466009439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48603844875679454310672959 72905767313519181466009439)
          ·
            refine ⟨109358650970278772199014159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72905767313519181466009439 109358650970278772199014159)
            ·
              refine ⟨164037976455418158298521239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109358650970278772199014159 164037976455418158298521239)
              ·
                refine ⟨246056964683127237447781859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164037976455418158298521239 246056964683127237447781859)
                ·
                  refine ⟨369085447024690856171672789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246056964683127237447781859 369085447024690856171672789)
                  ·
                    refine ⟨8650440164641191941523581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 369085447024690856171672789 8650440164641191941523581)
                    ·
                      refine ⟨3243915061740446978071343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8650440164641191941523581 3243915061740446978071343)
                      ·
                        rfl

theorem cell23_6317502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_6317502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317502 prefixEnd_6317502 := by exact prefixLift 6317502
  have htrace : WordTrace (prefixWord ++ tailWord_6317502) baseStart_6317502 baseEnd_6317502 := by
    simpa [prefixWord, tailWord_6317502, baseEnd_6317502] using wordTrace_append hprefix tailTrace_6317502
  have hstable : (prefixWord ++ tailWord_6317502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317502).length < 2 ^ (prefixWord ++ tailWord_6317502).sum := by decide
  have hdescent : baseEnd_6317502 < baseStart_6317502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317529 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 4, 3, 2]
def baseStart_6317529 : Nat := 118140960795 + 6317529 * 2 ^ 59
def prefixEnd_6317529 : Nat := 4983230072969 + 3 ^ 40 * 6317529 * 2
def baseEnd_6317529 : Nat := 3243928925718118372433719

theorem tailTrace_6317529 : CollatzResearch.WordTrace tailWord_6317529 prefixEnd_6317529 3243928925718118372433719 := by
  unfold tailWord_6317529
  simp only [CollatzResearch.WordTrace]
  refine ⟨230419212329678855898867641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153612808219785903932578427 230419212329678855898867641)
  ·
    refine ⟨172814409247259141924150731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230419212329678855898867641 172814409247259141924150731)
    ·
      refine ⟨259221613870888712886226097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172814409247259141924150731 259221613870888712886226097)
      ·
        refine ⟨194416210403166534664669573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259221613870888712886226097 194416210403166534664669573)
        ·
          refine ⟨36453039450593725249625545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194416210403166534664669573 36453039450593725249625545)
          ·
            refine ⟨27339779587945293937219159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36453039450593725249625545 27339779587945293937219159)
            ·
              refine ⟨41009669381917940905828739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27339779587945293937219159 41009669381917940905828739)
              ·
                refine ⟨61514504072876911358743109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41009669381917940905828739 61514504072876911358743109)
                ·
                  refine ⟨11533969513664420879764333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61514504072876911358743109 11533969513664420879764333)
                  ·
                    refine ⟨4325238567624157829911625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11533969513664420879764333 4325238567624157829911625)
                    ·
                      refine ⟨3243928925718118372433719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325238567624157829911625 3243928925718118372433719)
                      ·
                        rfl

theorem cell23_6317529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 3, 2].length) (baseStart_6317529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317529 prefixEnd_6317529 := by exact prefixLift 6317529
  have htrace : WordTrace (prefixWord ++ tailWord_6317529) baseStart_6317529 baseEnd_6317529 := by
    simpa [prefixWord, tailWord_6317529, baseEnd_6317529] using wordTrace_append hprefix tailTrace_6317529
  have hstable : (prefixWord ++ tailWord_6317529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317529).length < 2 ^ (prefixWord ++ tailWord_6317529).sum := by decide
  have hdescent : baseEnd_6317529 < baseStart_6317529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317545 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 2, 5, 5]
def baseStart_6317545 : Nat := 118140960795 + 6317545 * 2 ^ 59
def prefixEnd_6317545 : Nat := 4983230072969 + 3 ^ 40 * 6317545 * 2
def baseEnd_6317545 : Nat := 3243937141408590309833645

theorem tailTrace_6317545 : CollatzResearch.WordTrace tailWord_6317545 prefixEnd_6317545 3243937141408590309833645 := by
  unfold tailWord_6317545
  simp only [CollatzResearch.WordTrace]
  refine ⟨230419795897620890631450089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153613197265080593754300059 230419795897620890631450089)
  ·
    refine ⟨172814846923215667973587567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230419795897620890631450089 172814846923215667973587567)
    ·
      refine ⟨259222270384823501960381351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172814846923215667973587567 259222270384823501960381351)
      ·
        refine ⟨388833405577235252940572027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259222270384823501960381351 388833405577235252940572027)
        ·
          refine ⟨583250108365852879410858041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388833405577235252940572027 583250108365852879410858041)
          ·
            refine ⟨437437581274389659558143531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 583250108365852879410858041 437437581274389659558143531)
            ·
              refine ⟨656156371911584489337215297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437437581274389659558143531 656156371911584489337215297)
              ·
                refine ⟨492117278933688367002911473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 656156371911584489337215297 492117278933688367002911473)
                ·
                  refine ⟨369087959200266275252183605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492117278933688367002911473 369087959200266275252183605)
                  ·
                    refine ⟨34601996175024963304892213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 369087959200266275252183605 34601996175024963304892213)
                    ·
                      refine ⟨3243937141408590309833645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34601996175024963304892213 3243937141408590309833645)
                      ·
                        rfl

theorem cell23_6317545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_6317545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317545 prefixEnd_6317545 := by exact prefixLift 6317545
  have htrace : WordTrace (prefixWord ++ tailWord_6317545) baseStart_6317545 baseEnd_6317545 := by
    simpa [prefixWord, tailWord_6317545, baseEnd_6317545] using wordTrace_append hprefix tailTrace_6317545
  have hstable : (prefixWord ++ tailWord_6317545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317545).length < 2 ^ (prefixWord ++ tailWord_6317545).sum := by decide
  have hdescent : baseEnd_6317545 < baseStart_6317545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317569 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 1, 6]
def baseStart_6317569 : Nat := 118140960795 + 6317569 * 2 ^ 59
def prefixEnd_6317569 : Nat := 4983230072969 + 3 ^ 40 * 6317569 * 2
def baseEnd_6317569 : Nat := 1081316488314766071977845

theorem tailTrace_6317569 : CollatzResearch.WordTrace tailWord_6317569 prefixEnd_6317569 1081316488314766071977845 := by
  unfold tailWord_6317569
  simp only [CollatzResearch.WordTrace]
  refine ⟨230420671249533942730323761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153613780833022628486882507 230420671249533942730323761)
  ·
    refine ⟨172815503437150457047742821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230420671249533942730323761 172815503437150457047742821)
    ·
      refine ⟨32402906894465710696451779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172815503437150457047742821 32402906894465710696451779)
      ·
        refine ⟨48604360341698566044677669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32402906894465710696451779 48604360341698566044677669)
        ·
          refine ⟨9113317564068481133377063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48604360341698566044677669 9113317564068481133377063)
          ·
            refine ⟨13669976346102721700065595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9113317564068481133377063 13669976346102721700065595)
            ·
              refine ⟨20504964519154082550098393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13669976346102721700065595 20504964519154082550098393)
              ·
                refine ⟨15378723389365561912573795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20504964519154082550098393 15378723389365561912573795)
                ·
                  refine ⟨23068085084048342868860693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15378723389365561912573795 23068085084048342868860693)
                  ·
                    refine ⟨1081316488314766071977845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23068085084048342868860693 1081316488314766071977845)
                    ·
                      rfl

theorem cell23_6317569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_6317569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317569 prefixEnd_6317569 := by exact prefixLift 6317569
  have htrace : WordTrace (prefixWord ++ tailWord_6317569) baseStart_6317569 baseEnd_6317569 := by
    simpa [prefixWord, tailWord_6317569, baseEnd_6317569] using wordTrace_append hprefix tailTrace_6317569
  have hstable : (prefixWord ++ tailWord_6317569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317569).length < 2 ^ (prefixWord ++ tailWord_6317569).sum := by decide
  have hdescent : baseEnd_6317569 < baseStart_6317569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317582 : List Nat := [4, 1, 1, 2, 4, 11]
def baseStart_6317582 : Nat := 118140960795 + 6317582 * 2 ^ 59
def prefixEnd_6317582 : Nat := 4983230072969 + 3 ^ 40 * 6317582 * 2
def baseEnd_6317582 : Nat := 13349613745649410144325

theorem tailTrace_6317582 : CollatzResearch.WordTrace tailWord_6317582 prefixEnd_6317582 13349613745649410144325 := by
  unfold tailWord_6317582
  simp only [CollatzResearch.WordTrace]
  refine ⟨28802643174810855743818375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153614096932324563967031333 28802643174810855743818375)
  ·
    refine ⟨43203964762216283615727563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28802643174810855743818375 43203964762216283615727563)
    ·
      refine ⟨64805947143324425423591345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43203964762216283615727563 64805947143324425423591345)
      ·
        refine ⟨48604460357493319067693509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64805947143324425423591345 48604460357493319067693509)
        ·
          refine ⟨9113336317029997325192533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48604460357493319067693509 9113336317029997325192533)
          ·
            refine ⟨13349613745649410144325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9113336317029997325192533 13349613745649410144325)
            ·
              rfl

theorem cell23_6317582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 11].length) (baseStart_6317582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317582 prefixEnd_6317582 := by exact prefixLift 6317582
  have htrace : WordTrace (prefixWord ++ tailWord_6317582) baseStart_6317582 baseEnd_6317582 := by
    simpa [prefixWord, tailWord_6317582, baseEnd_6317582] using wordTrace_append hprefix tailTrace_6317582
  have hstable : (prefixWord ++ tailWord_6317582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317582).length < 2 ^ (prefixWord ++ tailWord_6317582).sum := by decide
  have hdescent : baseEnd_6317582 < baseStart_6317582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317602 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_6317602 : Nat := 118140960795 + 6317602 * 2 ^ 59
def prefixEnd_6317602 : Nat := 4983230072969 + 3 ^ 40 * 6317602 * 2
def baseEnd_6317602 : Nat := 3243966409805896586820883

theorem tailTrace_6317602 : CollatzResearch.WordTrace tailWord_6317602 prefixEnd_6317602 3243966409805896586820883 := by
  unfold tailWord_6317602
  simp only [CollatzResearch.WordTrace]
  refine ⟨57605468714603597341568765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153614583238942926244183373 57605468714603597341568765)
  ·
    refine ⟨21602050767976349003088287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57605468714603597341568765 21602050767976349003088287)
    ·
      refine ⟨32403076151964523504632431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21602050767976349003088287 32403076151964523504632431)
      ·
        refine ⟨48604614227946785256948647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32403076151964523504632431 48604614227946785256948647)
        ·
          refine ⟨72906921341920177885422971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48604614227946785256948647 72906921341920177885422971)
          ·
            refine ⟨109360382012880266828134457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72906921341920177885422971 109360382012880266828134457)
            ·
              refine ⟨82020286509660200121100843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109360382012880266828134457 82020286509660200121100843)
              ·
                refine ⟨123030429764490300181651265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82020286509660200121100843 123030429764490300181651265)
                ·
                  refine ⟨92272822323367725136238449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123030429764490300181651265 92272822323367725136238449)
                  ·
                    refine ⟨69204616742525793852178837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92272822323367725136238449 69204616742525793852178837)
                    ·
                      refine ⟨3243966409805896586820883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69204616742525793852178837 3243966409805896586820883)
                      ·
                        rfl

theorem cell23_6317602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_6317602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317602 prefixEnd_6317602 := by exact prefixLift 6317602
  have htrace : WordTrace (prefixWord ++ tailWord_6317602) baseStart_6317602 baseEnd_6317602 := by
    simpa [prefixWord, tailWord_6317602, baseEnd_6317602] using wordTrace_append hprefix tailTrace_6317602
  have hstable : (prefixWord ++ tailWord_6317602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317602).length < 2 ^ (prefixWord ++ tailWord_6317602).sum := by decide
  have hdescent : baseEnd_6317602 < baseStart_6317602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317642 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 4, 6]
def baseStart_6317642 : Nat := 118140960795 + 6317642 * 2 ^ 59
def prefixEnd_6317642 : Nat := 4983230072969 + 3 ^ 40 * 6317642 * 2
def baseEnd_6317642 : Nat := 1081328983010692143440233

theorem tailTrace_6317642 : CollatzResearch.WordTrace tailWord_6317642 prefixEnd_6317642 1081328983010692143440233 := by
  unfold tailWord_6317642
  simp only [CollatzResearch.WordTrace]
  refine ⟨57605833444567369049432795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153615555852179650798487453 57605833444567369049432795)
  ·
    refine ⟨86408750166851053574149193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57605833444567369049432795 86408750166851053574149193)
    ·
      refine ⟨64806562625138290180611895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86408750166851053574149193 64806562625138290180611895)
      ·
        refine ⟨97209843937707435270917843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64806562625138290180611895 97209843937707435270917843)
        ·
          refine ⟨145814765906561152906376765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97209843937707435270917843 145814765906561152906376765)
          ·
            refine ⟨54680537214960432339891287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145814765906561152906376765 54680537214960432339891287)
            ·
              refine ⟨82020805822440648509836931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54680537214960432339891287 82020805822440648509836931)
              ·
                refine ⟨123031208733660972764755397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82020805822440648509836931 123031208733660972764755397)
                ·
                  refine ⟨23068351637561432393391637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123031208733660972764755397 23068351637561432393391637)
                  ·
                    refine ⟨1081328983010692143440233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23068351637561432393391637 1081328983010692143440233)
                    ·
                      rfl

theorem cell23_6317642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_6317642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317642 prefixEnd_6317642 := by exact prefixLift 6317642
  have htrace : WordTrace (prefixWord ++ tailWord_6317642) baseStart_6317642 baseEnd_6317642 := by
    simpa [prefixWord, tailWord_6317642, baseEnd_6317642] using wordTrace_append hprefix tailTrace_6317642
  have hstable : (prefixWord ++ tailWord_6317642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317642).length < 2 ^ (prefixWord ++ tailWord_6317642).sum := by decide
  have hdescent : baseEnd_6317642 < baseStart_6317642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317660 : List Nat := [2, 2, 4, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_6317660 : Nat := 118140960795 + 6317660 * 2 ^ 59
def prefixEnd_6317660 : Nat := 4983230072969 + 3 ^ 40 * 6317660 * 2
def baseEnd_6317660 : Nat := 3243996191683857359895617

theorem tailTrace_6317660 : CollatzResearch.WordTrace tailWord_6317660 prefixEnd_6317660 3243996191683857359895617 := by
  unfold tailWord_6317660
  simp only [CollatzResearch.WordTrace]
  refine ⟨115211995146102132635943217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153615993528136176847924289 115211995146102132635943217)
  ·
    refine ⟨86408996359576599476957413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115211995146102132635943217 86408996359576599476957413)
    ·
      refine ⟨16201686817420612401929515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86408996359576599476957413 16201686817420612401929515)
      ·
        refine ⟨24302530226130918602894273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16201686817420612401929515 24302530226130918602894273)
        ·
          refine ⟨18226897669598188952170705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24302530226130918602894273 18226897669598188952170705)
          ·
            refine ⟨13670173252198641714128029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18226897669598188952170705 13670173252198641714128029)
            ·
              refine ⟨5126314969574490642798011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13670173252198641714128029 5126314969574490642798011)
              ·
                refine ⟨7689472454361735964197017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5126314969574490642798011 7689472454361735964197017)
                ·
                  refine ⟨5767104340771301973147763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7689472454361735964197017 5767104340771301973147763)
                  ·
                    refine ⟨8650656511156952959721645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5767104340771301973147763 8650656511156952959721645)
                    ·
                      refine ⟨3243996191683857359895617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8650656511156952959721645 3243996191683857359895617)
                      ·
                        rfl

theorem cell23_6317660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_6317660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317660 prefixEnd_6317660 := by exact prefixLift 6317660
  have htrace : WordTrace (prefixWord ++ tailWord_6317660) baseStart_6317660 baseEnd_6317660 := by
    simpa [prefixWord, tailWord_6317660, baseEnd_6317660] using wordTrace_append hprefix tailTrace_6317660
  have hstable : (prefixWord ++ tailWord_6317660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317660).length < 2 ^ (prefixWord ++ tailWord_6317660).sum := by decide
  have hdescent : baseEnd_6317660 < baseStart_6317660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317686 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_6317686 : Nat := 118140960795 + 6317686 * 2 ^ 59
def prefixEnd_6317686 : Nat := 4983230072969 + 3 ^ 40 * 6317686 * 2
def baseEnd_6317686 : Nat := 3244009542180874258170497

theorem tailTrace_6317686 : CollatzResearch.WordTrace tailWord_6317686 prefixEnd_6317686 3244009542180874258170497 := by
  unfold tailWord_6317686
  simp only [CollatzResearch.WordTrace]
  refine ⟨14401558661881879482020807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153616625726740047808221941 14401558661881879482020807)
  ·
    refine ⟨21602337992822819223031211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14401558661881879482020807 21602337992822819223031211)
    ·
      refine ⟨32403506989234228834546817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21602337992822819223031211 32403506989234228834546817)
      ·
        refine ⟨24302630241925671625910113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32403506989234228834546817 24302630241925671625910113)
        ·
          refine ⟨18226972681444253719432585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24302630241925671625910113 18226972681444253719432585)
          ·
            refine ⟨13670229511083190289574439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18226972681444253719432585 13670229511083190289574439)
            ·
              refine ⟨20505344266624785434361659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13670229511083190289574439 20505344266624785434361659)
              ·
                refine ⟨30758016399937178151542489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20505344266624785434361659 30758016399937178151542489)
                ·
                  refine ⟨23068512299952883613656867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30758016399937178151542489 23068512299952883613656867)
                  ·
                    refine ⟨34602768449929325420485301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23068512299952883613656867 34602768449929325420485301)
                    ·
                      refine ⟨3244009542180874258170497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34602768449929325420485301 3244009542180874258170497)
                      ·
                        rfl

theorem cell23_6317686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_6317686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317686 prefixEnd_6317686 := by exact prefixLift 6317686
  have htrace : WordTrace (prefixWord ++ tailWord_6317686) baseStart_6317686 baseEnd_6317686 := by
    simpa [prefixWord, tailWord_6317686, baseEnd_6317686] using wordTrace_append hprefix tailTrace_6317686
  have hstable : (prefixWord ++ tailWord_6317686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317686).length < 2 ^ (prefixWord ++ tailWord_6317686).sum := by decide
  have hdescent : baseEnd_6317686 < baseStart_6317686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317706 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 7]
def baseStart_6317706 : Nat := 118140960795 + 6317706 * 2 ^ 59
def prefixEnd_6317706 : Nat := 4983230072969 + 3 ^ 40 * 6317706 * 2
def baseEnd_6317706 : Nat := 360446645754884908880045

theorem tailTrace_6317706 : CollatzResearch.WordTrace tailWord_6317706 prefixEnd_6317706 360446645754884908880045 := by
  unfold tailWord_6317706
  simp only [CollatzResearch.WordTrace]
  refine ⟨57606417012509403782015243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153617112033358410085373981 57606417012509403782015243)
  ·
    refine ⟨86409625518764105673022865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57606417012509403782015243 86409625518764105673022865)
    ·
      refine ⟨64807219139073079254767149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86409625518764105673022865 64807219139073079254767149)
      ·
        refine ⟨24302707177152404720537681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64807219139073079254767149 24302707177152404720537681)
        ·
          refine ⟨18227030382864303540403261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24302707177152404720537681 18227030382864303540403261)
          ·
            refine ⟨6835136393574113827651223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18227030382864303540403261 6835136393574113827651223)
            ·
              refine ⟨10252704590361170741476835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6835136393574113827651223 10252704590361170741476835)
              ·
                refine ⟨15379056885541756112215253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10252704590361170741476835 15379056885541756112215253)
                ·
                  refine ⟨360446645754884908880045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15379056885541756112215253 360446645754884908880045)
                  ·
                    rfl

theorem cell23_6317706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 7].length) (baseStart_6317706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317706 prefixEnd_6317706 := by exact prefixLift 6317706
  have htrace : WordTrace (prefixWord ++ tailWord_6317706) baseStart_6317706 baseEnd_6317706 := by
    simpa [prefixWord, tailWord_6317706, baseEnd_6317706] using wordTrace_append hprefix tailTrace_6317706
  have hstable : (prefixWord ++ tailWord_6317706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317706).length < 2 ^ (prefixWord ++ tailWord_6317706).sum := by decide
  have hdescent : baseEnd_6317706 < baseStart_6317706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317756 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_6317756 : Nat := 118140960795 + 6317756 * 2 ^ 59
def prefixEnd_6317756 : Nat := 4983230072969 + 3 ^ 40 * 6317756 * 2
def baseEnd_6317756 : Nat := 3244045485826688984295175

theorem tailTrace_6317756 : CollatzResearch.WordTrace tailWord_6317756 prefixEnd_6317756 3244045485826688984295175 := by
  unfold tailWord_6317756
  simp only [CollatzResearch.WordTrace]
  refine ⟨115213745849928236833690561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153618327799904315778254081 115213745849928236833690561)
  ·
    refine ⟨86410309387446177625267921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115213745849928236833690561 86410309387446177625267921)
    ·
      refine ⟨64807732040584633218950941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86410309387446177625267921 64807732040584633218950941)
      ·
        refine ⟨24302899515219237457106603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64807732040584633218950941 24302899515219237457106603)
        ·
          refine ⟨36454349272828856185659905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24302899515219237457106603 36454349272828856185659905)
          ·
            refine ⟨27340761954621642139244929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36454349272828856185659905 27340761954621642139244929)
            ·
              refine ⟨20505571465966231604433697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27340761954621642139244929 20505571465966231604433697)
              ·
                refine ⟨15379178599474673703325273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20505571465966231604433697 15379178599474673703325273)
                ·
                  refine ⟨11534383949606005277493955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15379178599474673703325273 11534383949606005277493955)
                  ·
                    refine ⟨17301575924409007916240933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11534383949606005277493955 17301575924409007916240933)
                    ·
                      refine ⟨3244045485826688984295175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17301575924409007916240933 3244045485826688984295175)
                      ·
                        rfl

theorem cell23_6317756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_6317756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317756 prefixEnd_6317756 := by exact prefixLift 6317756
  have htrace : WordTrace (prefixWord ++ tailWord_6317756) baseStart_6317756 baseEnd_6317756 := by
    simpa [prefixWord, tailWord_6317756, baseEnd_6317756] using wordTrace_append hprefix tailTrace_6317756
  have hstable : (prefixWord ++ tailWord_6317756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317756).length < 2 ^ (prefixWord ++ tailWord_6317756).sum := by decide
  have hdescent : baseEnd_6317756 < baseStart_6317756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317800 : List Nat := [2, 1, 4, 1, 3, 2, 2, 3, 1, 4]
def baseStart_6317800 : Nat := 118140960795 + 6317800 * 2 ^ 59
def prefixEnd_6317800 : Nat := 4983230072969 + 3 ^ 40 * 6317800 * 2
def baseEnd_6317800 : Nat := 1081356026325162270714991

theorem tailTrace_6317800 : CollatzResearch.WordTrace tailWord_6317800 prefixEnd_6317800 1081356026325162270714991 := by
  unfold tailWord_6317800
  simp only [CollatzResearch.WordTrace]
  refine ⟨115214548255848534590991427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153619397674464712787988569 115214548255848534590991427)
  ·
    refine ⟨172821822383772801886487141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115214548255848534590991427 172821822383772801886487141)
    ·
      refine ⟨32404091696957400353716339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172821822383772801886487141 32404091696957400353716339)
      ·
        refine ⟨48606137545436100530574509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32404091696957400353716339 48606137545436100530574509)
        ·
          refine ⟨18227301579538537698965441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48606137545436100530574509 18227301579538537698965441)
          ·
            refine ⟨13670476184653903274224081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18227301579538537698965441 13670476184653903274224081)
            ·
              refine ⟨10252857138490427455668061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13670476184653903274224081 10252857138490427455668061)
              ·
                refine ⟨3844821426933910295875523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10252857138490427455668061 3844821426933910295875523)
                ·
                  refine ⟨5767232140400865443813285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3844821426933910295875523 5767232140400865443813285)
                  ·
                    refine ⟨1081356026325162270714991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5767232140400865443813285 1081356026325162270714991)
                    ·
                      rfl

theorem cell23_6317800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_6317800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317800 prefixEnd_6317800 := by exact prefixLift 6317800
  have htrace : WordTrace (prefixWord ++ tailWord_6317800) baseStart_6317800 baseEnd_6317800 := by
    simpa [prefixWord, tailWord_6317800, baseEnd_6317800] using wordTrace_append hprefix tailTrace_6317800
  have hstable : (prefixWord ++ tailWord_6317800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317800).length < 2 ^ (prefixWord ++ tailWord_6317800).sum := by decide
  have hdescent : baseEnd_6317800 < baseStart_6317800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317839 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 1, 6]
def baseStart_6317839 : Nat := 118140960795 + 6317839 * 2 ^ 59
def prefixEnd_6317839 : Nat := 4983230072969 + 3 ^ 40 * 6317839 * 2
def baseEnd_6317839 : Nat := 1081362701573670719852431

theorem tailTrace_6317839 : CollatzResearch.WordTrace tailWord_6317839 prefixEnd_6317839 1081362701573670719852431 := by
  unfold tailWord_6317839
  simp only [CollatzResearch.WordTrace]
  refine ⟨230430518958555778842652571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153620345972370519228435047 230430518958555778842652571)
  ·
    refine ⟨345645778437833668263978857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230430518958555778842652571 345645778437833668263978857)
    ·
      refine ⟨259234333828375251197984143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345645778437833668263978857 259234333828375251197984143)
      ·
        refine ⟨388851500742562876796976215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259234333828375251197984143 388851500742562876796976215)
        ·
          refine ⟨583277251113844315195464323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388851500742562876796976215 583277251113844315195464323)
          ·
            refine ⟨874915876670766472793196485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583277251113844315195464323 874915876670766472793196485)
            ·
              refine ⟨164046726875768713648724341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 874915876670766472793196485 164046726875768713648724341)
              ·
                refine ⟨15379380644603316904567907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164046726875768713648724341 15379380644603316904567907)
                ·
                  refine ⟨23069070966904975356851861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15379380644603316904567907 23069070966904975356851861)
                  ·
                    refine ⟨1081362701573670719852431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23069070966904975356851861 1081362701573670719852431)
                    ·
                      rfl

theorem cell23_6317839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 6].length) (baseStart_6317839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317839 prefixEnd_6317839 := by exact prefixLift 6317839
  have htrace : WordTrace (prefixWord ++ tailWord_6317839) baseStart_6317839 baseEnd_6317839 := by
    simpa [prefixWord, tailWord_6317839, baseEnd_6317839] using wordTrace_append hprefix tailTrace_6317839
  have hstable : (prefixWord ++ tailWord_6317839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317839).length < 2 ^ (prefixWord ++ tailWord_6317839).sum := by decide
  have hdescent : baseEnd_6317839 < baseStart_6317839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317856 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 6, 4]
def baseStart_6317856 : Nat := 118140960795 + 6317856 * 2 ^ 59
def prefixEnd_6317856 : Nat := 4983230072969 + 3 ^ 40 * 6317856 * 2
def baseEnd_6317856 : Nat := 1081365611297379531014905

theorem tailTrace_6317856 : CollatzResearch.WordTrace tailWord_6317856 prefixEnd_6317856 1081365611297379531014905 := by
  unfold tailWord_6317856
  simp only [CollatzResearch.WordTrace]
  refine ⟨115215569499747095373010711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153620759332996127164014281 115215569499747095373010711)
  ·
    refine ⟨172823354249620643059516067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115215569499747095373010711 172823354249620643059516067)
    ·
      refine ⟨259235031374430964589274101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172823354249620643059516067 259235031374430964589274101)
      ·
        refine ⟨24303284191352902930244447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 259235031374430964589274101 24303284191352902930244447)
        ·
          refine ⟨36454926287029354395366671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24303284191352902930244447 36454926287029354395366671)
          ·
            refine ⟨54682389430544031593050007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36454926287029354395366671 54682389430544031593050007)
            ·
              refine ⟨82023584145816047389575011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54682389430544031593050007 82023584145816047389575011)
              ·
                refine ⟨123035376218724071084362517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82023584145816047389575011 123035376218724071084362517)
                ·
                  refine ⟨5767283260252690832079493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 123035376218724071084362517 5767283260252690832079493)
                  ·
                    refine ⟨1081365611297379531014905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5767283260252690832079493 1081365611297379531014905)
                    ·
                      rfl

theorem cell23_6317856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 6, 4].length) (baseStart_6317856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317856 prefixEnd_6317856 := by exact prefixLift 6317856
  have htrace : WordTrace (prefixWord ++ tailWord_6317856) baseStart_6317856 baseEnd_6317856 := by
    simpa [prefixWord, tailWord_6317856, baseEnd_6317856] using wordTrace_append hprefix tailTrace_6317856
  have hstable : (prefixWord ++ tailWord_6317856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317856).length < 2 ^ (prefixWord ++ tailWord_6317856).sum := by decide
  have hdescent : baseEnd_6317856 < baseStart_6317856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317857 : List Nat := [1, 2, 3, 2, 1, 5, 1, 3, 1, 1, 3]
def baseStart_6317857 : Nat := 118140960795 + 6317857 * 2 ^ 59
def prefixEnd_6317857 : Nat := 4983230072969 + 3 ^ 40 * 6317857 * 2
def baseEnd_6317857 : Nat := 3244097347372793089132211

theorem tailTrace_6317857 : CollatzResearch.WordTrace tailWord_6317857 prefixEnd_6317857 3244097347372793089132211 := by
  unfold tailWord_6317857
  simp only [CollatzResearch.WordTrace]
  refine ⟨230431175472490567916807825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153620783648327045277871883 230431175472490567916807825)
  ·
    refine ⟨172823381604367925937605869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230431175472490567916807825 172823381604367925937605869)
    ·
      refine ⟨64808768101637972226602201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172823381604367925937605869 64808768101637972226602201)
      ·
        refine ⟨48606576076228479169951651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64808768101637972226602201 48606576076228479169951651)
        ·
          refine ⟨72909864114342718754927477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48606576076228479169951651 72909864114342718754927477)
          ·
            refine ⟨6835299760719629883274451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72909864114342718754927477 6835299760719629883274451)
            ·
              refine ⟨10252949641079444824911677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6835299760719629883274451 10252949641079444824911677)
              ·
                refine ⟨3844856115404791809341879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10252949641079444824911677 3844856115404791809341879)
                ·
                  refine ⟨5767284173107187714012819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3844856115404791809341879 5767284173107187714012819)
                  ·
                    refine ⟨8650926259660781571019229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5767284173107187714012819 8650926259660781571019229)
                    ·
                      refine ⟨3244097347372793089132211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8650926259660781571019229 3244097347372793089132211)
                      ·
                        rfl

theorem cell23_6317857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_6317857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317857 prefixEnd_6317857 := by exact prefixLift 6317857
  have htrace : WordTrace (prefixWord ++ tailWord_6317857) baseStart_6317857 baseEnd_6317857 := by
    simpa [prefixWord, tailWord_6317857, baseEnd_6317857] using wordTrace_append hprefix tailTrace_6317857
  have hstable : (prefixWord ++ tailWord_6317857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317857).length < 2 ^ (prefixWord ++ tailWord_6317857).sum := by decide
  have hdescent : baseEnd_6317857 < baseStart_6317857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317880 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 3, 2, 2]
def baseStart_6317880 : Nat := 118140960795 + 6317880 * 2 ^ 59
def prefixEnd_6317880 : Nat := 4983230072969 + 3 ^ 40 * 6317880 * 2
def baseEnd_6317880 : Nat := 3244109157427846499144605

theorem tailTrace_6317880 : CollatzResearch.WordTrace tailWord_6317880 prefixEnd_6317880 3244109157427846499144605 := by
  unfold tailWord_6317880
  simp only [CollatzResearch.WordTrace]
  refine ⟨115216007175703621422447547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153621342900938161896596729 115216007175703621422447547)
  ·
    refine ⟨172824010763555432133671321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115216007175703621422447547 172824010763555432133671321)
    ·
      refine ⟨129618008072666574100253491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172824010763555432133671321 129618008072666574100253491)
      ·
        refine ⟨194427012108999861150380237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129618008072666574100253491 194427012108999861150380237)
        ·
          refine ⟨72910129540874947931392589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194427012108999861150380237 72910129540874947931392589)
          ·
            refine ⟨27341298577828105474272221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72910129540874947931392589 27341298577828105474272221)
            ·
              refine ⟨10252986966685539552852083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27341298577828105474272221 10252986966685539552852083)
              ·
                refine ⟨15379480450028309329278125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10252986966685539552852083 15379480450028309329278125)
                ·
                  refine ⟨5767305168760615998479297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15379480450028309329278125 5767305168760615998479297)
                  ·
                    refine ⟨4325478876570461998859473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5767305168760615998479297 4325478876570461998859473)
                    ·
                      refine ⟨3244109157427846499144605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325478876570461998859473 3244109157427846499144605)
                      ·
                        rfl

theorem cell23_6317880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 3, 2, 2].length) (baseStart_6317880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317880 prefixEnd_6317880 := by exact prefixLift 6317880
  have htrace : WordTrace (prefixWord ++ tailWord_6317880) baseStart_6317880 baseEnd_6317880 := by
    simpa [prefixWord, tailWord_6317880, baseEnd_6317880] using wordTrace_append hprefix tailTrace_6317880
  have hstable : (prefixWord ++ tailWord_6317880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317880).length < 2 ^ (prefixWord ++ tailWord_6317880).sum := by decide
  have hdescent : baseEnd_6317880 < baseStart_6317880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317886 : List Nat := [4, 2, 1, 2, 2, 1, 1, 10]
def baseStart_6317886 : Nat := 118140960795 + 6317886 * 2 ^ 59
def prefixEnd_6317886 : Nat := 4983230072969 + 3 ^ 40 * 6317886 * 2
def baseEnd_6317886 : Nat := 120152305122658276876651

theorem tailTrace_6317886 : CollatzResearch.WordTrace tailWord_6317886 prefixEnd_6317886 120152305122658276876651 := by
  unfold tailWord_6317886
  simp only [CollatzResearch.WordTrace]
  refine ⟨28804029148673188233701689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153621488792923670579742341 28804029148673188233701689)
  ·
    refine ⟨21603021861504891175276267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28804029148673188233701689 21603021861504891175276267)
    ·
      refine ⟨32404532792257336762914401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21603021861504891175276267 32404532792257336762914401)
      ·
        refine ⟨24303399594193002572185801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32404532792257336762914401 24303399594193002572185801)
        ·
          refine ⟨18227549695644751929139351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24303399594193002572185801 18227549695644751929139351)
          ·
            refine ⟨27341324543467127893709027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18227549695644751929139351 27341324543467127893709027)
            ·
              refine ⟨41011986815200691840563541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27341324543467127893709027 41011986815200691840563541)
              ·
                refine ⟨120152305122658276876651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41011986815200691840563541 120152305122658276876651)
                ·
                  rfl

theorem cell23_6317886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_6317886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317886 prefixEnd_6317886 := by exact prefixLift 6317886
  have htrace : WordTrace (prefixWord ++ tailWord_6317886) baseStart_6317886 baseEnd_6317886 := by
    simpa [prefixWord, tailWord_6317886, baseEnd_6317886] using wordTrace_append hprefix tailTrace_6317886
  have hstable : (prefixWord ++ tailWord_6317886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317886).length < 2 ^ (prefixWord ++ tailWord_6317886).sum := by decide
  have hdescent : baseEnd_6317886 < baseStart_6317886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317929 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 3, 8]
def baseStart_6317929 : Nat := 118140960795 + 6317929 * 2 ^ 59
def prefixEnd_6317929 : Nat := 4983230072969 + 3 ^ 40 * 6317929 * 2
def baseEnd_6317929 : Nat := 1081378105993305602477293

theorem tailTrace_6317929 : CollatzResearch.WordTrace tailWord_6317929 prefixEnd_6317929 1081378105993305602477293 := by
  unfold tailWord_6317929
  simp only [CollatzResearch.WordTrace]
  refine ⟨230433801528229724213428841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153622534352153149475619227 230433801528229724213428841)
  ·
    refine ⟨172825351146172293160071631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230433801528229724213428841 172825351146172293160071631)
    ·
      refine ⟨259238026719258439740107447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172825351146172293160071631 259238026719258439740107447)
      ·
        refine ⟨388857040078887659610161171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259238026719258439740107447 388857040078887659610161171)
        ·
          refine ⟨583285560118331489415241757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388857040078887659610161171 583285560118331489415241757)
          ·
            refine ⟨218732085044374308530715659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 583285560118331489415241757 218732085044374308530715659)
            ·
              refine ⟨328098127566561462796073489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218732085044374308530715659 328098127566561462796073489)
              ·
                refine ⟨246073595674921097097055117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328098127566561462796073489 246073595674921097097055117)
                ·
                  refine ⟨92277598378095411411395669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246073595674921097097055117 92277598378095411411395669)
                  ·
                    refine ⟨1081378105993305602477293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92277598378095411411395669 1081378105993305602477293)
                    ·
                      rfl

theorem cell23_6317929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_6317929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317929 prefixEnd_6317929 := by exact prefixLift 6317929
  have htrace : WordTrace (prefixWord ++ tailWord_6317929) baseStart_6317929 baseEnd_6317929 := by
    simpa [prefixWord, tailWord_6317929, baseEnd_6317929] using wordTrace_append hprefix tailTrace_6317929
  have hstable : (prefixWord ++ tailWord_6317929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317929).length < 2 ^ (prefixWord ++ tailWord_6317929).sum := by decide
  have hdescent : baseEnd_6317929 < baseStart_6317929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317956 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_6317956 : Nat := 118140960795 + 6317956 * 2 ^ 59
def prefixEnd_6317956 : Nat := 4983230072969 + 3 ^ 40 * 6317956 * 2
def baseEnd_6317956 : Nat := 3244148181957588201794255

theorem tailTrace_6317956 : CollatzResearch.WordTrace tailWord_6317956 prefixEnd_6317956 3244148181957588201794255 := by
  unfold tailWord_6317956
  simp only [CollatzResearch.WordTrace]
  refine ⟨115217393149565953912330861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153623190866087938549774481 115217393149565953912330861)
  ·
    refine ⟨43206522431087232717124073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115217393149565953912330861 43206522431087232717124073)
    ·
      refine ⟨32404891823315424537843055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43206522431087232717124073 32404891823315424537843055)
      ·
        refine ⟨48607337734973136806764583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32404891823315424537843055 48607337734973136806764583)
        ·
          refine ⟨72911006602459705210146875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48607337734973136806764583 72911006602459705210146875)
          ·
            refine ⟨109366509903689557815220313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72911006602459705210146875 109366509903689557815220313)
            ·
              refine ⟨82024882427767168361415235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109366509903689557815220313 82024882427767168361415235)
              ·
                refine ⟨123037323641650752542122853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82024882427767168361415235 123037323641650752542122853)
                ·
                  refine ⟨23069498182809516101648035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123037323641650752542122853 23069498182809516101648035)
                  ·
                    refine ⟨34604247274214274152472053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23069498182809516101648035 34604247274214274152472053)
                    ·
                      refine ⟨3244148181957588201794255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34604247274214274152472053 3244148181957588201794255)
                      ·
                        rfl

theorem cell23_6317956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_6317956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317956 prefixEnd_6317956 := by exact prefixLift 6317956
  have htrace : WordTrace (prefixWord ++ tailWord_6317956) baseStart_6317956 baseEnd_6317956 := by
    simpa [prefixWord, tailWord_6317956, baseEnd_6317956] using wordTrace_append hprefix tailTrace_6317956
  have hstable : (prefixWord ++ tailWord_6317956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317956).length < 2 ^ (prefixWord ++ tailWord_6317956).sum := by decide
  have hdescent : baseEnd_6317956 < baseStart_6317956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6317998 : List Nat := [4, 1, 5, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_6317998 : Nat := 118140960795 + 6317998 * 2 ^ 59
def prefixEnd_6317998 : Nat := 4983230072969 + 3 ^ 40 * 6317998 * 2
def baseEnd_6317998 : Nat := 3244169748145077037469063

theorem tailTrace_6317998 : CollatzResearch.WordTrace tailWord_6317998 prefixEnd_6317998 3244169748145077037469063 := by
  unfold tailWord_6317998
  simp only [CollatzResearch.WordTrace]
  refine ⟨28804539770622468624711331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153624212109986499331793765 28804539770622468624711331)
  ·
    refine ⟨43206809655933702937066997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28804539770622468624711331 43206809655933702937066997)
    ·
      refine ⟨4050638405243784650350031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43206809655933702937066997 4050638405243784650350031)
      ·
        refine ⟨6075957607865676975525047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4050638405243784650350031 6075957607865676975525047)
        ·
          refine ⟨9113936411798515463287571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6075957607865676975525047 9113936411798515463287571)
          ·
            refine ⟨13670904617697773194931357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9113936411798515463287571 13670904617697773194931357)
            ·
              refine ⟨5126589231636664948099259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13670904617697773194931357 5126589231636664948099259)
              ·
                refine ⟨7689883847454997422148889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5126589231636664948099259 7689883847454997422148889)
                ·
                  refine ⟨5767412885591248066611667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7689883847454997422148889 5767412885591248066611667)
                  ·
                    refine ⟨8651119328386872099917501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5767412885591248066611667 8651119328386872099917501)
                    ·
                      refine ⟨3244169748145077037469063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8651119328386872099917501 3244169748145077037469063)
                      ·
                        rfl

theorem cell23_6317998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_6317998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6317998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6317998 prefixEnd_6317998 := by exact prefixLift 6317998
  have htrace : WordTrace (prefixWord ++ tailWord_6317998) baseStart_6317998 baseEnd_6317998 := by
    simpa [prefixWord, tailWord_6317998, baseEnd_6317998] using wordTrace_append hprefix tailTrace_6317998
  have hstable : (prefixWord ++ tailWord_6317998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6317998).length < 2 ^ (prefixWord ++ tailWord_6317998).sum := by decide
  have hdescent : baseEnd_6317998 < baseStart_6317998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6317998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318044 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 7]
def baseStart_6318044 : Nat := 118140960795 + 6318044 * 2 ^ 59
def prefixEnd_6318044 : Nat := 4983230072969 + 3 ^ 40 * 6318044 * 2
def baseEnd_6318044 : Nat := 360465929806131539721539

theorem tailTrace_6318044 : CollatzResearch.WordTrace tailWord_6318044 prefixEnd_6318044 360465929806131539721539 := by
  unfold tailWord_6318044
  simp only [CollatzResearch.WordTrace]
  refine ⟨115218997961406549426932593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153625330615208732569243457 115218997961406549426932593)
  ·
    refine ⟨86414248471054912070199445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115218997961406549426932593 86414248471054912070199445)
    ·
      refine ⟨4050667897080699003290599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86414248471054912070199445 4050667897080699003290599)
      ·
        refine ⟨6076001845621048504935899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4050667897080699003290599 6076001845621048504935899)
        ·
          refine ⟨9114002768431572757403849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076001845621048504935899 9114002768431572757403849)
          ·
            refine ⟨6835502076323679568052887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9114002768431572757403849 6835502076323679568052887)
            ·
              refine ⟨10253253114485519352079331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6835502076323679568052887 10253253114485519352079331)
              ·
                refine ⟨15379879671728279028118997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10253253114485519352079331 15379879671728279028118997)
                ·
                  refine ⟨360465929806131539721539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15379879671728279028118997 360465929806131539721539)
                  ·
                    rfl

theorem cell23_6318044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 7].length) (baseStart_6318044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318044 prefixEnd_6318044 := by exact prefixLift 6318044
  have htrace : WordTrace (prefixWord ++ tailWord_6318044) baseStart_6318044 baseEnd_6318044 := by
    simpa [prefixWord, tailWord_6318044, baseEnd_6318044] using wordTrace_append hprefix tailTrace_6318044
  have hstable : (prefixWord ++ tailWord_6318044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318044).length < 2 ^ (prefixWord ++ tailWord_6318044).sum := by decide
  have hdescent : baseEnd_6318044 < baseStart_6318044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318063 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 3]
def baseStart_6318063 : Nat := 118140960795 + 6318063 * 2 ^ 59
def prefixEnd_6318063 : Nat := 4983230072969 + 3 ^ 40 * 6318063 * 2
def baseEnd_6318063 : Nat := 3244203124387619283156263

theorem tailTrace_6318063 : CollatzResearch.WordTrace tailWord_6318063 prefixEnd_6318063 3244203124387619283156263 := by
  unfold tailWord_6318063
  simp only [CollatzResearch.WordTrace]
  refine ⟨230438688909744265098806843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153625792606496176732537895 230438688909744265098806843)
  ·
    refine ⟨345658033364616397648210265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230438688909744265098806843 345658033364616397648210265)
    ·
      refine ⟨259243525023462298236157699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345658033364616397648210265 259243525023462298236157699)
      ·
        refine ⟨388865287535193447354236549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259243525023462298236157699 388865287535193447354236549)
        ·
          refine ⟨72912241412848771378919353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 388865287535193447354236549 72912241412848771378919353)
          ·
            refine ⟨54684181059636578534189515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72912241412848771378919353 54684181059636578534189515)
            ·
              refine ⟨82026271589454867801284273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54684181059636578534189515 82026271589454867801284273)
              ·
                refine ⟨61519703692091150850963205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82026271589454867801284273 61519703692091150850963205)
                ·
                  refine ⟨11534944442267090784555601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61519703692091150850963205 11534944442267090784555601)
                  ·
                    refine ⟨8651208331700318088416701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11534944442267090784555601 8651208331700318088416701)
                    ·
                      refine ⟨3244203124387619283156263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8651208331700318088416701 3244203124387619283156263)
                      ·
                        rfl

theorem cell23_6318063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 2, 3].length) (baseStart_6318063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318063 prefixEnd_6318063 := by exact prefixLift 6318063
  have htrace : WordTrace (prefixWord ++ tailWord_6318063) baseStart_6318063 baseEnd_6318063 := by
    simpa [prefixWord, tailWord_6318063, baseEnd_6318063] using wordTrace_append hprefix tailTrace_6318063
  have hstable : (prefixWord ++ tailWord_6318063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318063).length < 2 ^ (prefixWord ++ tailWord_6318063).sum := by decide
  have hdescent : baseEnd_6318063 < baseStart_6318063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318137 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 1, 5, 2]
def baseStart_6318137 : Nat := 118140960795 + 6318137 * 2 ^ 59
def prefixEnd_6318137 : Nat := 4983230072969 + 3 ^ 40 * 6318137 * 2
def baseEnd_6318137 : Nat := 3244241121956051993630923

theorem tailTrace_6318137 : CollatzResearch.WordTrace tailWord_6318137 prefixEnd_6318137 3244241121956051993630923 := by
  unfold tailWord_6318137
  simp only [CollatzResearch.WordTrace]
  refine ⟨230441387911476175737000665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153627591940984117158000443 230441387911476175737000665)
  ·
    refine ⟨172831040933607131802750499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230441387911476175737000665 172831040933607131802750499)
    ·
      refine ⟨259246561400410697704125749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172831040933607131802750499 259246561400410697704125749)
      ·
        refine ⟨24304365131288502909761789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 259246561400410697704125749 24304365131288502909761789)
        ·
          refine ⟨9114136924233188591160671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24304365131288502909761789 9114136924233188591160671)
          ·
            refine ⟨13671205386349782886741007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9114136924233188591160671 13671205386349782886741007)
            ·
              refine ⟨20506808079524674330111511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13671205386349782886741007 20506808079524674330111511)
              ·
                refine ⟨30760212119287011495167267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20506808079524674330111511 30760212119287011495167267)
                ·
                  refine ⟨46140318178930517242750901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30760212119287011495167267 46140318178930517242750901)
                  ·
                    refine ⟨4325654829274735991507897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46140318178930517242750901 4325654829274735991507897)
                    ·
                      refine ⟨3244241121956051993630923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325654829274735991507897 3244241121956051993630923)
                      ·
                        rfl

theorem cell23_6318137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_6318137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318137 prefixEnd_6318137 := by exact prefixLift 6318137
  have htrace : WordTrace (prefixWord ++ tailWord_6318137) baseStart_6318137 baseEnd_6318137 := by
    simpa [prefixWord, tailWord_6318137, baseEnd_6318137] using wordTrace_append hprefix tailTrace_6318137
  have hstable : (prefixWord ++ tailWord_6318137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318137).length < 2 ^ (prefixWord ++ tailWord_6318137).sum := by decide
  have hdescent : baseEnd_6318137 < baseStart_6318137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318143 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 1, 6]
def baseStart_6318143 : Nat := 118140960795 + 6318143 * 2 ^ 59
def prefixEnd_6318143 : Nat := 4983230072969 + 3 ^ 40 * 6318143 * 2
def baseEnd_6318143 : Nat := 1081414734279992990051965

theorem tailTrace_6318143 : CollatzResearch.WordTrace tailWord_6318143 prefixEnd_6318143 1081414734279992990051965 := by
  unfold tailWord_6318143
  simp only [CollatzResearch.WordTrace]
  refine ⟨230441606749454438761719083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153627737832969625841146055 230441606749454438761719083)
  ·
    refine ⟨345662410124181658142578625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230441606749454438761719083 345662410124181658142578625)
    ·
      refine ⟨259246807593136243606933969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345662410124181658142578625 259246807593136243606933969)
      ·
        refine ⟨194435105694852182705200477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259246807593136243606933969 194435105694852182705200477)
        ·
          refine ⟨72913164635569568514450179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194435105694852182705200477 72913164635569568514450179)
          ·
            refine ⟨109369746953354352771675269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72913164635569568514450179 109369746953354352771675269)
            ·
              refine ⟨20506827553753941144689113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109369746953354352771675269 20506827553753941144689113)
              ·
                refine ⟨15380120665315455858516835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20506827553753941144689113 15380120665315455858516835)
                ·
                  refine ⟨23070180997973183787775253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15380120665315455858516835 23070180997973183787775253)
                  ·
                    refine ⟨1081414734279992990051965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23070180997973183787775253 1081414734279992990051965)
                    ·
                      rfl

theorem cell23_6318143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 6].length) (baseStart_6318143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318143 prefixEnd_6318143 := by exact prefixLift 6318143
  have htrace : WordTrace (prefixWord ++ tailWord_6318143) baseStart_6318143 baseEnd_6318143 := by
    simpa [prefixWord, tailWord_6318143, baseEnd_6318143] using wordTrace_append hprefix tailTrace_6318143
  have hstable : (prefixWord ++ tailWord_6318143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318143).length < 2 ^ (prefixWord ++ tailWord_6318143).sum := by decide
  have hdescent : baseEnd_6318143 < baseStart_6318143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318144 : List Nat := [2, 1, 1, 2, 2, 5, 2, 3, 1, 1, 3]
def baseStart_6318144 : Nat := 118140960795 + 6318144 * 2 ^ 59
def prefixEnd_6318144 : Nat := 4983230072969 + 3 ^ 40 * 6318144 * 2
def baseEnd_6318144 : Nat := 3244244716320633466243391

theorem tailTrace_6318144 : CollatzResearch.WordTrace tailWord_6318144 prefixEnd_6318144 3244244716320633466243391 := by
  unfold tailWord_6318144
  simp only [CollatzResearch.WordTrace]
  refine ⟨115220821611225407966252743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153627762148300543955003657 115220821611225407966252743)
  ·
    refine ⟨172831232416838111949379115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115220821611225407966252743 172831232416838111949379115)
    ·
      refine ⟨259246848625257167924068673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172831232416838111949379115 259246848625257167924068673)
      ·
        refine ⟨194435136468942875943051505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259246848625257167924068673 194435136468942875943051505)
        ·
          refine ⟨145826352351707156957288629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194435136468942875943051505 145826352351707156957288629)
          ·
            refine ⟨13671220532972545964745809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145826352351707156957288629 13671220532972545964745809)
            ·
              refine ⟨10253415399729409473559357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13671220532972545964745809 10253415399729409473559357)
              ·
                refine ⟨3845030774898528552584759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10253415399729409473559357 3845030774898528552584759)
                ·
                  refine ⟨5767546162347792828877139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845030774898528552584759 5767546162347792828877139)
                  ·
                    refine ⟨8651319243521689243315709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5767546162347792828877139 8651319243521689243315709)
                    ·
                      refine ⟨3244244716320633466243391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8651319243521689243315709 3244244716320633466243391)
                      ·
                        rfl

theorem cell23_6318144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 1, 1, 3].length) (baseStart_6318144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318144 prefixEnd_6318144 := by exact prefixLift 6318144
  have htrace : WordTrace (prefixWord ++ tailWord_6318144) baseStart_6318144 baseEnd_6318144 := by
    simpa [prefixWord, tailWord_6318144, baseEnd_6318144] using wordTrace_append hprefix tailTrace_6318144
  have hstable : (prefixWord ++ tailWord_6318144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318144).length < 2 ^ (prefixWord ++ tailWord_6318144).sum := by decide
  have hdescent : baseEnd_6318144 < baseStart_6318144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318153 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 1, 1, 5]
def baseStart_6318153 : Nat := 118140960795 + 6318153 * 2 ^ 59
def prefixEnd_6318153 : Nat := 4983230072969 + 3 ^ 40 * 6318153 * 2
def baseEnd_6318153 : Nat := 3244249337646523931030849

theorem tailTrace_6318153 : CollatzResearch.WordTrace tailWord_6318153 prefixEnd_6318153 3244249337646523931030849 := by
  unfold tailWord_6318153
  simp only [CollatzResearch.WordTrace]
  refine ⟨230441971479418210469583113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153627980986278806979722075 230441971479418210469583113)
  ·
    refine ⟨172831478609563657852187335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230441971479418210469583113 172831478609563657852187335)
    ·
      refine ⟨259247217914345486778281003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172831478609563657852187335 259247217914345486778281003)
      ·
        refine ⟨388870826871518230167421505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259247217914345486778281003 388870826871518230167421505)
        ·
          refine ⟨291653120153638672625566129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388870826871518230167421505 291653120153638672625566129)
          ·
            refine ⟨218739840115229004469174597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291653120153638672625566129 218739840115229004469174597)
            ·
              refine ⟨41013720021605438337970237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218739840115229004469174597 41013720021605438337970237)
              ·
                refine ⟨15380145008102039376738839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41013720021605438337970237 15380145008102039376738839)
                ·
                  refine ⟨23070217512153059065108259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15380145008102039376738839 23070217512153059065108259)
                  ·
                    refine ⟨34605326268229588597662389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23070217512153059065108259 34605326268229588597662389)
                    ·
                      refine ⟨3244249337646523931030849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34605326268229588597662389 3244249337646523931030849)
                      ·
                        rfl

theorem cell23_6318153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_6318153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318153 prefixEnd_6318153 := by exact prefixLift 6318153
  have htrace : WordTrace (prefixWord ++ tailWord_6318153) baseStart_6318153 baseEnd_6318153 := by
    simpa [prefixWord, tailWord_6318153, baseEnd_6318153] using wordTrace_append hprefix tailTrace_6318153
  have hstable : (prefixWord ++ tailWord_6318153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318153).length < 2 ^ (prefixWord ++ tailWord_6318153).sum := by decide
  have hdescent : baseEnd_6318153 < baseStart_6318153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318167 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 3, 2, 2]
def baseStart_6318167 : Nat := 118140960795 + 6318167 * 2 ^ 59
def prefixEnd_6318167 : Nat := 4983230072969 + 3 ^ 40 * 6318167 * 2
def baseEnd_6318167 : Nat := 3244256526375686876255785

theorem tailTrace_6318167 : CollatzResearch.WordTrace tailWord_6318167 prefixEnd_6318167 3244256526375686876255785 := by
  unfold tailWord_6318167
  simp only [CollatzResearch.WordTrace]
  refine ⟨230442482101367490860592755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153628321400911660573728503 230442482101367490860592755)
  ·
    refine ⟨345663723152051236290889133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230442482101367490860592755 345663723152051236290889133)
    ·
      refine ⟨129623896182019213609083425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345663723152051236290889133 129623896182019213609083425)
      ·
        refine ⟨97217922136514410206812569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129623896182019213609083425 97217922136514410206812569)
        ·
          refine ⟨72913441602385807655109427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97217922136514410206812569 72913441602385807655109427)
          ·
            refine ⟨109370162403578711482664141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72913441602385807655109427 109370162403578711482664141)
            ·
              refine ⟨41013810901342016805999053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109370162403578711482664141 41013810901342016805999053)
              ·
                refine ⟨15380179088003256302249645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41013810901342016805999053 15380179088003256302249645)
                ·
                  refine ⟨5767567158001221113343617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15380179088003256302249645 5767567158001221113343617)
                  ·
                    refine ⟨4325675368500915835007713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5767567158001221113343617 4325675368500915835007713)
                    ·
                      refine ⟨3244256526375686876255785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325675368500915835007713 3244256526375686876255785)
                      ·
                        rfl

theorem cell23_6318167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_6318167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318167 prefixEnd_6318167 := by exact prefixLift 6318167
  have htrace : WordTrace (prefixWord ++ tailWord_6318167) baseStart_6318167 baseEnd_6318167 := by
    simpa [prefixWord, tailWord_6318167, baseEnd_6318167] using wordTrace_append hprefix tailTrace_6318167
  have hstable : (prefixWord ++ tailWord_6318167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318167).length < 2 ^ (prefixWord ++ tailWord_6318167).sum := by decide
  have hdescent : baseEnd_6318167 < baseStart_6318167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318180 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_6318180 : Nat := 118140960795 + 6318180 * 2 ^ 59
def prefixEnd_6318180 : Nat := 4983230072969 + 3 ^ 40 * 6318180 * 2
def baseEnd_6318180 : Nat := 3244263201624195325393225

theorem tailTrace_6318180 : CollatzResearch.WordTrace tailWord_6318180 prefixEnd_6318180 3244263201624195325393225 := by
  unfold tailWord_6318180
  simp only [CollatzResearch.WordTrace]
  refine ⟨115221478125160197040407997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153628637500213596053877329 115221478125160197040407997)
  ·
    refine ⟨43208054296935073890152999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115221478125160197040407997 43208054296935073890152999)
    ·
      refine ⟨64812081445402610835229499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43208054296935073890152999 64812081445402610835229499)
      ·
        refine ⟨97218122168103916252844249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64812081445402610835229499 97218122168103916252844249)
        ·
          refine ⟨72913591626077937189633187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97218122168103916252844249 72913591626077937189633187)
          ·
            refine ⟨109370387439116905784449781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72913591626077937189633187 109370387439116905784449781)
            ·
              refine ⟨10253473822417209917292167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109370387439116905784449781 10253473822417209917292167)
              ·
                refine ⟨15380210733625814875938251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10253473822417209917292167 15380210733625814875938251)
                ·
                  refine ⟨23070316100438722313907377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15380210733625814875938251 23070316100438722313907377)
                  ·
                    refine ⟨17302737075329041735430533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23070316100438722313907377 17302737075329041735430533)
                    ·
                      refine ⟨3244263201624195325393225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17302737075329041735430533 3244263201624195325393225)
                      ·
                        rfl

theorem cell23_6318180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_6318180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318180 prefixEnd_6318180 := by exact prefixLift 6318180
  have htrace : WordTrace (prefixWord ++ tailWord_6318180) baseStart_6318180 baseEnd_6318180 := by
    simpa [prefixWord, tailWord_6318180, baseEnd_6318180] using wordTrace_append hprefix tailTrace_6318180
  have hstable : (prefixWord ++ tailWord_6318180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318180).length < 2 ^ (prefixWord ++ tailWord_6318180).sum := by decide
  have hdescent : baseEnd_6318180 < baseStart_6318180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318201 : List Nat := [1, 2, 1, 3, 4, 1, 3, 3, 1, 2, 2]
def baseStart_6318201 : Nat := 118140960795 + 6318201 * 2 ^ 59
def prefixEnd_6318201 : Nat := 4983230072969 + 3 ^ 40 * 6318201 * 2
def baseEnd_6318201 : Nat := 3244273984717939743230629

theorem tailTrace_6318201 : CollatzResearch.WordTrace tailWord_6318201 prefixEnd_6318201 3244273984717939743230629 := by
  unfold tailWord_6318201
  simp only [CollatzResearch.WordTrace]
  refine ⟨230443722183244314667330457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153629148122162876444886971 230443722183244314667330457)
  ·
    refine ⟨172832791637433236000497843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230443722183244314667330457 172832791637433236000497843)
    ·
      refine ⟨259249187456149854000746765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172832791637433236000497843 259249187456149854000746765)
      ·
        refine ⟨97218445296056195250280037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259249187456149854000746765 97218445296056195250280037)
        ·
          refine ⟨18228458493010536609427507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97218445296056195250280037 18228458493010536609427507)
          ·
            refine ⟨27342687739515804914141261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18228458493010536609427507 27342687739515804914141261)
            ·
              refine ⟨10253507902318426842802973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27342687739515804914141261 10253507902318426842802973)
              ·
                refine ⟨3845065463369410066051115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10253507902318426842802973 3845065463369410066051115)
                ·
                  refine ⟨5767598195054115099076673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845065463369410066051115 5767598195054115099076673)
                  ·
                    refine ⟨4325698646290586324307505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5767598195054115099076673 4325698646290586324307505)
                    ·
                      refine ⟨3244273984717939743230629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325698646290586324307505 3244273984717939743230629)
                      ·
                        rfl

theorem cell23_6318201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_6318201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318201 prefixEnd_6318201 := by exact prefixLift 6318201
  have htrace : WordTrace (prefixWord ++ tailWord_6318201) baseStart_6318201 baseEnd_6318201 := by
    simpa [prefixWord, tailWord_6318201, baseEnd_6318201] using wordTrace_append hprefix tailTrace_6318201
  have hstable : (prefixWord ++ tailWord_6318201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318201).length < 2 ^ (prefixWord ++ tailWord_6318201).sum := by decide
  have hdescent : baseEnd_6318201 < baseStart_6318201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318217 : List Nat := [1, 2, 1, 1, 4, 2, 2, 4, 2, 1, 3]
def baseStart_6318217 : Nat := 118140960795 + 6318217 * 2 ^ 59
def prefixEnd_6318217 : Nat := 4983230072969 + 3 ^ 40 * 6318217 * 2
def baseEnd_6318217 : Nat := 3244282200408411680630555

theorem tailTrace_6318217 : CollatzResearch.WordTrace tailWord_6318217 prefixEnd_6318217 3244282200408411680630555 := by
  unfold tailWord_6318217
  simp only [CollatzResearch.WordTrace]
  refine ⟨230444305751186349399912905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153629537167457566266608603 230444305751186349399912905)
  ·
    refine ⟨172833229313389762049934679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230444305751186349399912905 172833229313389762049934679)
    ·
      refine ⟨259249843970084643074902019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172833229313389762049934679 259249843970084643074902019)
      ·
        refine ⟨388874765955126964612353029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259249843970084643074902019 388874765955126964612353029)
        ·
          refine ⟨72914018616586305864816193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 388874765955126964612353029 72914018616586305864816193)
          ·
            refine ⟨54685513962439729398612145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72914018616586305864816193 54685513962439729398612145)
            ·
              refine ⟨41014135471829797048959109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54685513962439729398612145 41014135471829797048959109)
              ·
                refine ⟨7690150400968086946679833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41014135471829797048959109 7690150400968086946679833)
                ·
                  refine ⟨5767612800726065210009875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7690150400968086946679833 5767612800726065210009875)
                  ·
                    refine ⟨8651419201089097815014813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5767612800726065210009875 8651419201089097815014813)
                    ·
                      refine ⟨3244282200408411680630555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8651419201089097815014813 3244282200408411680630555)
                      ·
                        rfl

theorem cell23_6318217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 1, 3].length) (baseStart_6318217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318217 prefixEnd_6318217 := by exact prefixLift 6318217
  have htrace : WordTrace (prefixWord ++ tailWord_6318217) baseStart_6318217 baseEnd_6318217 := by
    simpa [prefixWord, tailWord_6318217, baseEnd_6318217] using wordTrace_append hprefix tailTrace_6318217
  have hstable : (prefixWord ++ tailWord_6318217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318217).length < 2 ^ (prefixWord ++ tailWord_6318217).sum := by decide
  have hdescent : baseEnd_6318217 < baseStart_6318217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318218 : List Nat := [3, 1, 2, 3, 1, 3, 3, 2, 1, 2, 2]
def baseStart_6318218 : Nat := 118140960795 + 6318218 * 2 ^ 59
def prefixEnd_6318218 : Nat := 4983230072969 + 3 ^ 40 * 6318218 * 2
def baseEnd_6318218 : Nat := 3244282713889066176718051

theorem tailTrace_6318218 : CollatzResearch.WordTrace tailWord_6318218 prefixEnd_6318218 3244282713889066176718051 := by
  unfold tailWord_6318218
  simp only [CollatzResearch.WordTrace]
  refine ⟨57611085556045681642674827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153629561482788484380466205 57611085556045681642674827)
  ·
    refine ⟨86416628334068522464012241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57611085556045681642674827 86416628334068522464012241)
    ·
      refine ⟨64812471250551391848009181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86416628334068522464012241 64812471250551391848009181)
      ·
        refine ⟨24304676718956771943003443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64812471250551391848009181 24304676718956771943003443)
        ·
          refine ⟨36457015078435157914505165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24304676718956771943003443 36457015078435157914505165)
          ·
            refine ⟨13671380654413184217939437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36457015078435157914505165 13671380654413184217939437)
            ·
              refine ⟨5126767745404944081727289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13671380654413184217939437 5126767745404944081727289)
              ·
                refine ⟨3845075809053708061295467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5126767745404944081727289 3845075809053708061295467)
                ·
                  refine ⟨5767613713580562091943201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845075809053708061295467 5767613713580562091943201)
                  ·
                    refine ⟨4325710285185421568957401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5767613713580562091943201 4325710285185421568957401)
                    ·
                      refine ⟨3244282713889066176718051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325710285185421568957401 3244282713889066176718051)
                      ·
                        rfl

theorem cell23_6318218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_6318218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318218 prefixEnd_6318218 := by exact prefixLift 6318218
  have htrace : WordTrace (prefixWord ++ tailWord_6318218) baseStart_6318218 baseEnd_6318218 := by
    simpa [prefixWord, tailWord_6318218, baseEnd_6318218] using wordTrace_append hprefix tailTrace_6318218
  have hstable : (prefixWord ++ tailWord_6318218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318218).length < 2 ^ (prefixWord ++ tailWord_6318218).sum := by decide
  have hdescent : baseEnd_6318218 < baseStart_6318218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318228 : List Nat := [2, 4, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_6318228 : Nat := 118140960795 + 6318228 * 2 ^ 59
def prefixEnd_6318228 : Nat := 4983230072969 + 3 ^ 40 * 6318228 * 2
def baseEnd_6318228 : Nat := 1081429282898537045864335

theorem tailTrace_6318228 : CollatzResearch.WordTrace tailWord_6318228 prefixEnd_6318228 1081429282898537045864335 := by
  unfold tailWord_6318228
  simp only [CollatzResearch.WordTrace]
  refine ⟨115222353477073249139281669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153629804636097665519042225 115222353477073249139281669)
  ·
    refine ⟨21604191276951234213615313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115222353477073249139281669 21604191276951234213615313)
    ·
      refine ⟨16203143457713425660211485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21604191276951234213615313 16203143457713425660211485)
      ·
        refine ⟨6076178796642534622579307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16203143457713425660211485 6076178796642534622579307)
        ·
          refine ⟨9114268194963801933868961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076178796642534622579307 9114268194963801933868961)
          ·
            refine ⟨6835701146222851450401721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9114268194963801933868961 6835701146222851450401721)
            ·
              refine ⟨5126775859667138587801291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6835701146222851450401721 5126775859667138587801291)
              ·
                refine ⟨7690163789500707881701937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5126775859667138587801291 7690163789500707881701937)
                ·
                  refine ⟨5767622842125530911276453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7690163789500707881701937 5767622842125530911276453)
                  ·
                    refine ⟨1081429282898537045864335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5767622842125530911276453 1081429282898537045864335)
                    ·
                      rfl

theorem cell23_6318228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_6318228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318228 prefixEnd_6318228 := by exact prefixLift 6318228
  have htrace : WordTrace (prefixWord ++ tailWord_6318228) baseStart_6318228 baseEnd_6318228 := by
    simpa [prefixWord, tailWord_6318228, baseEnd_6318228] using wordTrace_append hprefix tailTrace_6318228
  have hstable : (prefixWord ++ tailWord_6318228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318228).length < 2 ^ (prefixWord ++ tailWord_6318228).sum := by decide
  have hdescent : baseEnd_6318228 < baseStart_6318228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318233 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 2, 6]
def baseStart_6318233 : Nat := 118140960795 + 6318233 * 2 ^ 59
def prefixEnd_6318233 : Nat := 4983230072969 + 3 ^ 40 * 6318233 * 2
def baseEnd_6318233 : Nat := 1081430138699627872676827

theorem tailTrace_6318233 : CollatzResearch.WordTrace tailWord_6318233 prefixEnd_6318233 1081430138699627872676827 := by
  unfold tailWord_6318233
  simp only [CollatzResearch.WordTrace]
  refine ⟨230444889319128384132495353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153629926212752256088330235 230444889319128384132495353)
  ·
    refine ⟨172833666989346288099371515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230444889319128384132495353 172833666989346288099371515)
    ·
      refine ⟨259250500484019432149057273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172833666989346288099371515 259250500484019432149057273)
      ·
        refine ⟨194437875363014574111792955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259250500484019432149057273 194437875363014574111792955)
        ·
          refine ⟨291656813044521861167689433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194437875363014574111792955 291656813044521861167689433)
          ·
            refine ⟨218742609783391395875767075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291656813044521861167689433 218742609783391395875767075)
            ·
              refine ⟨328113914675087093813650613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218742609783391395875767075 328113914675087093813650613)
              ·
                refine ⟨30760679500789415045029745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 328113914675087093813650613 30760679500789415045029745)
                ·
                  refine ⟨23070509625592061283772309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30760679500789415045029745 23070509625592061283772309)
                  ·
                    refine ⟨1081430138699627872676827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23070509625592061283772309 1081430138699627872676827)
                    ·
                      rfl

theorem cell23_6318233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 6].length) (baseStart_6318233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318233 prefixEnd_6318233 := by exact prefixLift 6318233
  have htrace : WordTrace (prefixWord ++ tailWord_6318233) baseStart_6318233 baseEnd_6318233 := by
    simpa [prefixWord, tailWord_6318233, baseEnd_6318233] using wordTrace_append hprefix tailTrace_6318233
  have hstable : (prefixWord ++ tailWord_6318233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318233).length < 2 ^ (prefixWord ++ tailWord_6318233).sum := by decide
  have hdescent : baseEnd_6318233 < baseStart_6318233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318238 : List Nat := [4, 3, 1, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_6318238 : Nat := 118140960795 + 6318238 * 2 ^ 59
def prefixEnd_6318238 : Nat := 4983230072969 + 3 ^ 40 * 6318238 * 2
def baseEnd_6318238 : Nat := 3244292983502156098467959

theorem tailTrace_6318238 : CollatzResearch.WordTrace tailWord_6318238 prefixEnd_6318238 3244292983502156098467959 := by
  unfold tailWord_6318238
  simp only [CollatzResearch.WordTrace]
  refine ⟨28805633960513783748303421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153630047789406846657618245 28805633960513783748303421)
  ·
    refine ⟨10802112735192668905613783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28805633960513783748303421 10802112735192668905613783)
    ·
      refine ⟨16203169102789003358420675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10802112735192668905613783 16203169102789003358420675)
      ·
        refine ⟨24304753654183505037631013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16203169102789003358420675 24304753654183505037631013)
        ·
          refine ⟨4557141310159407194555815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24304753654183505037631013 4557141310159407194555815)
          ·
            refine ⟨6835711965239110791833723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4557141310159407194555815 6835711965239110791833723)
            ·
              refine ⟨10253567947858666187750585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6835711965239110791833723 10253567947858666187750585)
              ·
                refine ⟨7690175960893999640812939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10253567947858666187750585 7690175960893999640812939)
                ·
                  refine ⟨11535263941340999461219409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7690175960893999640812939 11535263941340999461219409)
                  ·
                    refine ⟨8651447956005749595914557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11535263941340999461219409 8651447956005749595914557)
                    ·
                      refine ⟨3244292983502156098467959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8651447956005749595914557 3244292983502156098467959)
                      ·
                        rfl

theorem cell23_6318238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_6318238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318238 prefixEnd_6318238 := by exact prefixLift 6318238
  have htrace : WordTrace (prefixWord ++ tailWord_6318238) baseStart_6318238 baseEnd_6318238 := by
    simpa [prefixWord, tailWord_6318238, baseEnd_6318238] using wordTrace_append hprefix tailTrace_6318238
  have hstable : (prefixWord ++ tailWord_6318238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318238).length < 2 ^ (prefixWord ++ tailWord_6318238).sum := by decide
  have hdescent : baseEnd_6318238 < baseStart_6318238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318244 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 3, 3, 2]
def baseStart_6318244 : Nat := 118140960795 + 6318244 * 2 ^ 59
def prefixEnd_6318244 : Nat := 4983230072969 + 3 ^ 40 * 6318244 * 2
def baseEnd_6318244 : Nat := 3244296064386083074992931

theorem tailTrace_6318244 : CollatzResearch.WordTrace tailWord_6318244 prefixEnd_6318244 3244296064386083074992931 := by
  unfold tailWord_6318244
  simp only [CollatzResearch.WordTrace]
  refine ⟨115222645261044266505572893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153630193681392355340763857 115222645261044266505572893)
  ·
    refine ⟨43208491972891599939589835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115222645261044266505572893 43208491972891599939589835)
    ·
      refine ⟨64812737959337399909384753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43208491972891599939589835 64812737959337399909384753)
      ·
        refine ⟨48609553469503049932038565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64812737959337399909384753 48609553469503049932038565)
        ·
          refine ⟨9114291275531821862257231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48609553469503049932038565 9114291275531821862257231)
          ·
            refine ⟨13671436913297732793385847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9114291275531821862257231 13671436913297732793385847)
            ·
              refine ⟨20507155369946599190078771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13671436913297732793385847 20507155369946599190078771)
              ·
                refine ⟨30760733054919898785118157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20507155369946599190078771 30760733054919898785118157)
                ·
                  refine ⟨11535274895594962044419309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30760733054919898785118157 11535274895594962044419309)
                  ·
                    refine ⟨4325728085848110766657241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11535274895594962044419309 4325728085848110766657241)
                    ·
                      refine ⟨3244296064386083074992931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325728085848110766657241 3244296064386083074992931)
                      ·
                        rfl

theorem cell23_6318244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_6318244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318244 prefixEnd_6318244 := by exact prefixLift 6318244
  have htrace : WordTrace (prefixWord ++ tailWord_6318244) baseStart_6318244 baseEnd_6318244 := by
    simpa [prefixWord, tailWord_6318244, baseEnd_6318244] using wordTrace_append hprefix tailTrace_6318244
  have hstable : (prefixWord ++ tailWord_6318244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318244).length < 2 ^ (prefixWord ++ tailWord_6318244).sum := by decide
  have hdescent : baseEnd_6318244 < baseStart_6318244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318274 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_6318274 : Nat := 118140960795 + 6318274 * 2 ^ 59
def prefixEnd_6318274 : Nat := 4983230072969 + 3 ^ 40 * 6318274 * 2
def baseEnd_6318274 : Nat := 3244311468805717957617793

theorem tailTrace_6318274 : CollatzResearch.WordTrace tailWord_6318274 prefixEnd_6318274 3244311468805717957617793 := by
  unfold tailWord_6318274
  simp only [CollatzResearch.WordTrace]
  refine ⟨57611596177994962033684469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153630923141319898756491917 57611596177994962033684469)
  ·
    refine ⟨5401087141687027690657919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57611596177994962033684469 5401087141687027690657919)
    ·
      refine ⟨8101630712530541535986879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5401087141687027690657919 8101630712530541535986879)
      ·
        refine ⟨12152446068795812303980319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8101630712530541535986879 12152446068795812303980319)
        ·
          refine ⟨18228669103193718455970479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12152446068795812303980319 18228669103193718455970479)
          ·
            refine ⟨27343003654790577683955719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18228669103193718455970479 27343003654790577683955719)
            ·
              refine ⟨41014505482185866525933579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27343003654790577683955719 41014505482185866525933579)
              ·
                refine ⟨61521758223278799788900369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41014505482185866525933579 61521758223278799788900369)
                ·
                  refine ⟨46141318667459099841675277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61521758223278799788900369 46141318667459099841675277)
                  ·
                    refine ⟨17302994500297162440628229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46141318667459099841675277 17302994500297162440628229)
                    ·
                      refine ⟨3244311468805717957617793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17302994500297162440628229 3244311468805717957617793)
                      ·
                        rfl

theorem cell23_6318274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_6318274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318274 prefixEnd_6318274 := by exact prefixLift 6318274
  have htrace : WordTrace (prefixWord ++ tailWord_6318274) baseStart_6318274 baseEnd_6318274 := by
    simpa [prefixWord, tailWord_6318274, baseEnd_6318274] using wordTrace_append hprefix tailTrace_6318274
  have hstable : (prefixWord ++ tailWord_6318274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318274).length < 2 ^ (prefixWord ++ tailWord_6318274).sum := by decide
  have hdescent : baseEnd_6318274 < baseStart_6318274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318347 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 2, 4, 2]
def baseStart_6318347 : Nat := 118140960795 + 6318347 * 2 ^ 59
def prefixEnd_6318347 : Nat := 4983230072969 + 3 ^ 40 * 6318347 * 2
def baseEnd_6318347 : Nat := 3244348952893496172004957

theorem tailTrace_6318347 : CollatzResearch.WordTrace tailWord_6318347 prefixEnd_6318347 3244348952893496172004957 := by
  unfold tailWord_6318347
  simp only [CollatzResearch.WordTrace]
  refine ⟨230449047240715381602145295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153632698160476921068096863 230449047240715381602145295)
  ·
    refine ⟨345673570861073072403217943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230449047240715381602145295 345673570861073072403217943)
    ·
      refine ⟨518510356291609608604826915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345673570861073072403217943 518510356291609608604826915)
      ·
        refine ⟨777765534437414412907240373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518510356291609608604826915 777765534437414412907240373)
        ·
          refine ⟨72915518853507601210053785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 777765534437414412907240373 72915518853507601210053785)
          ·
            refine ⟨54686639140130700907540339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72915518853507601210053785 54686639140130700907540339)
            ·
              refine ⟨82029958710196051361310509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54686639140130700907540339 82029958710196051361310509)
              ·
                refine ⟨30761234516323519260491441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82029958710196051361310509 30761234516323519260491441)
                ·
                  refine ⟨23070925887242639445368581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30761234516323519260491441 23070925887242639445368581)
                  ·
                    refine ⟨4325798603857994896006609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23070925887242639445368581 4325798603857994896006609)
                    ·
                      refine ⟨3244348952893496172004957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325798603857994896006609 3244348952893496172004957)
                      ·
                        rfl

theorem cell23_6318347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 4, 2].length) (baseStart_6318347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318347 prefixEnd_6318347 := by exact prefixLift 6318347
  have htrace : WordTrace (prefixWord ++ tailWord_6318347) baseStart_6318347 baseEnd_6318347 := by
    simpa [prefixWord, tailWord_6318347, baseEnd_6318347] using wordTrace_append hprefix tailTrace_6318347
  have hstable : (prefixWord ++ tailWord_6318347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318347).length < 2 ^ (prefixWord ++ tailWord_6318347).sum := by decide
  have hdescent : baseEnd_6318347 < baseStart_6318347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318357 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 3, 4]
def baseStart_6318357 : Nat := 118140960795 + 6318357 * 2 ^ 59
def prefixEnd_6318357 : Nat := 4983230072969 + 3 ^ 40 * 6318357 * 2
def baseEnd_6318357 : Nat := 1081451362566680377626637

theorem tailTrace_6318357 : CollatzResearch.WordTrace tailWord_6318357 prefixEnd_6318357 1081451362566680377626637 := by
  unfold tailWord_6318357
  simp only [CollatzResearch.WordTrace]
  refine ⟨230449411970679153310009325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153632941313786102206672883 230449411970679153310009325)
  ·
    refine ⟨86418529489004682491253497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230449411970679153310009325 86418529489004682491253497)
    ·
      refine ⟨64813897116753511868440123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86418529489004682491253497 64813897116753511868440123)
      ·
        refine ⟨97220845675130267802660185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64813897116753511868440123 97220845675130267802660185)
        ·
          refine ⟨72915634256347700851995139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97220845675130267802660185 72915634256347700851995139)
          ·
            refine ⟨109373451384521551277992709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72915634256347700851995139 109373451384521551277992709)
            ·
              refine ⟨20507522134597790864623633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109373451384521551277992709 20507522134597790864623633)
              ·
                refine ⟨15380641600948343148467725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20507522134597790864623633 15380641600948343148467725)
                ·
                  refine ⟨5767740600355628680675397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15380641600948343148467725 5767740600355628680675397)
                  ·
                    refine ⟨1081451362566680377626637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5767740600355628680675397 1081451362566680377626637)
                    ·
                      rfl

theorem cell23_6318357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_6318357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318357 prefixEnd_6318357 := by exact prefixLift 6318357
  have htrace : WordTrace (prefixWord ++ tailWord_6318357) baseStart_6318357 baseEnd_6318357 := by
    simpa [prefixWord, tailWord_6318357, baseEnd_6318357] using wordTrace_append hprefix tailTrace_6318357
  have hstable : (prefixWord ++ tailWord_6318357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318357).length < 2 ^ (prefixWord ++ tailWord_6318357).sum := by decide
  have hdescent : baseEnd_6318357 < baseStart_6318357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318360 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_6318360 : Nat := 118140960795 + 6318360 * 2 ^ 59
def prefixEnd_6318360 : Nat := 4983230072969 + 3 ^ 40 * 6318360 * 2
def baseEnd_6318360 : Nat := 3244355628142004621142397

theorem tailTrace_6318360 : CollatzResearch.WordTrace tailWord_6318360 prefixEnd_6318360 3244355628142004621142397 := by
  unfold tailWord_6318360
  simp only [CollatzResearch.WordTrace]
  refine ⟨115224760694834142411184267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153633014259778856548245689 115224760694834142411184267)
  ·
    refine ⟨172837141042251213616776401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115224760694834142411184267 172837141042251213616776401)
    ·
      refine ⟨129627855781688410212582301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172837141042251213616776401 129627855781688410212582301)
      ·
        refine ⟨48610445918133153829718363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129627855781688410212582301 48610445918133153829718363)
        ·
          refine ⟨72915668877199730744577545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48610445918133153829718363 72915668877199730744577545)
          ·
            refine ⟨54686751657899798058433159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72915668877199730744577545 54686751657899798058433159)
            ·
              refine ⟨82030127486849697087649739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54686751657899798058433159 82030127486849697087649739)
              ·
                refine ⟨123045191230274545631474609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82030127486849697087649739 123045191230274545631474609)
                ·
                  refine ⟨92283893422705909223605957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123045191230274545631474609 92283893422705909223605957)
                  ·
                    refine ⟨17303230016757357979426117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92283893422705909223605957 17303230016757357979426117)
                    ·
                      refine ⟨3244355628142004621142397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17303230016757357979426117 3244355628142004621142397)
                      ·
                        rfl

theorem cell23_6318360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_6318360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318360 prefixEnd_6318360 := by exact prefixLift 6318360
  have htrace : WordTrace (prefixWord ++ tailWord_6318360) baseStart_6318360 baseEnd_6318360 := by
    simpa [prefixWord, tailWord_6318360, baseEnd_6318360] using wordTrace_append hprefix tailTrace_6318360
  have hstable : (prefixWord ++ tailWord_6318360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318360).length < 2 ^ (prefixWord ++ tailWord_6318360).sum := by decide
  have hdescent : baseEnd_6318360 < baseStart_6318360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318367 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 3]
def baseStart_6318367 : Nat := 118140960795 + 6318367 * 2 ^ 59
def prefixEnd_6318367 : Nat := 4983230072969 + 3 ^ 40 * 6318367 * 2
def baseEnd_6318367 : Nat := 3244359222506586093754865

theorem tailTrace_6318367 : CollatzResearch.WordTrace tailWord_6318367 prefixEnd_6318367 3244359222506586093754865 := by
  unfold tailWord_6318367
  simp only [CollatzResearch.WordTrace]
  refine ⟨230449776700642925017873355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153633184467095283345248903 230449776700642925017873355)
  ·
    refine ⟨345674665050964387526810033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230449776700642925017873355 345674665050964387526810033)
    ·
      refine ⟨259255998788223290645107525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345674665050964387526810033 259255998788223290645107525)
      ·
        refine ⟨48610499772791866995957661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259255998788223290645107525 48610499772791866995957661)
        ·
          refine ⟨18228937414796950123484123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48610499772791866995957661 18228937414796950123484123)
          ·
            refine ⟨27343406122195425185226185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18228937414796950123484123 27343406122195425185226185)
            ·
              refine ⟨20507554591646568888919639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27343406122195425185226185 20507554591646568888919639)
              ·
                refine ⟨30761331887469853333379459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20507554591646568888919639 30761331887469853333379459)
                ·
                  refine ⟨46141997831204780000069189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30761331887469853333379459 46141997831204780000069189)
                  ·
                    refine ⟨8651624593350896250012973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46141997831204780000069189 8651624593350896250012973)
                    ·
                      refine ⟨3244359222506586093754865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8651624593350896250012973 3244359222506586093754865)
                      ·
                        rfl

theorem cell23_6318367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_6318367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318367 prefixEnd_6318367 := by exact prefixLift 6318367
  have htrace : WordTrace (prefixWord ++ tailWord_6318367) baseStart_6318367 baseEnd_6318367 := by
    simpa [prefixWord, tailWord_6318367, baseEnd_6318367] using wordTrace_append hprefix tailTrace_6318367
  have hstable : (prefixWord ++ tailWord_6318367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318367).length < 2 ^ (prefixWord ++ tailWord_6318367).sum := by decide
  have hdescent : baseEnd_6318367 < baseStart_6318367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318381 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_6318381 : Nat := 118140960795 + 6318381 * 2 ^ 59
def prefixEnd_6318381 : Nat := 4983230072969 + 3 ^ 40 * 6318381 * 2
def baseEnd_6318381 : Nat := 3244366411235749038979801

theorem tailTrace_6318381 : CollatzResearch.WordTrace tailWord_6318381 prefixEnd_6318381 3244366411235749038979801 := by
  unfold tailWord_6318381
  simp only [CollatzResearch.WordTrace]
  refine ⟨230450287322592205408882997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153633524881728136939255331 230450287322592205408882997)
  ·
    refine ⟨21604714436493019257082781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 230450287322592205408882997 21604714436493019257082781)
    ·
      refine ⟨8101767913684882221406043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21604714436493019257082781 8101767913684882221406043)
      ·
        refine ⟨12152651870527323332109065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8101767913684882221406043 12152651870527323332109065)
        ·
          refine ⟨9114488902895492499081799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12152651870527323332109065 9114488902895492499081799)
          ·
            refine ⟨13671733354343238748622699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9114488902895492499081799 13671733354343238748622699)
            ·
              refine ⟨20507600031514858122934049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13671733354343238748622699 20507600031514858122934049)
              ·
                refine ⟨15380700023636143592200537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20507600031514858122934049 15380700023636143592200537)
                ·
                  refine ⟨11535525017727107694150403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15380700023636143592200537 11535525017727107694150403)
                  ·
                    refine ⟨17303287526590661541225605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11535525017727107694150403 17303287526590661541225605)
                    ·
                      refine ⟨3244366411235749038979801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17303287526590661541225605 3244366411235749038979801)
                      ·
                        rfl

theorem cell23_6318381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_6318381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318381 prefixEnd_6318381 := by exact prefixLift 6318381
  have htrace : WordTrace (prefixWord ++ tailWord_6318381) baseStart_6318381 baseEnd_6318381 := by
    simpa [prefixWord, tailWord_6318381, baseEnd_6318381] using wordTrace_append hprefix tailTrace_6318381
  have hstable : (prefixWord ++ tailWord_6318381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318381).length < 2 ^ (prefixWord ++ tailWord_6318381).sum := by decide
  have hdescent : baseEnd_6318381 < baseStart_6318381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318417 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 3, 5]
def baseStart_6318417 : Nat := 118140960795 + 6318417 * 2 ^ 59
def prefixEnd_6318417 : Nat := 4983230072969 + 3 ^ 40 * 6318417 * 2
def baseEnd_6318417 : Nat := 1081461632179770299376545

theorem tailTrace_6318417 : CollatzResearch.WordTrace tailWord_6318417 prefixEnd_6318417 1081461632179770299376545 := by
  unfold tailWord_6318417
  simp only [CollatzResearch.WordTrace]
  refine ⟨230451600350461783557193505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153634400233641189038129003 230451600350461783557193505)
  ·
    refine ⟨172838700262846337667895129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230451600350461783557193505 172838700262846337667895129)
    ·
      refine ⟨129629025197134753250921347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172838700262846337667895129 129629025197134753250921347)
      ·
        refine ⟨194443537795702129876382021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129629025197134753250921347 194443537795702129876382021)
        ·
          refine ⟨36458163336694149351821629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194443537795702129876382021 36458163336694149351821629)
          ·
            refine ⟨13671811251260306006933111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36458163336694149351821629 13671811251260306006933111)
            ·
              refine ⟨20507716876890459010399667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13671811251260306006933111 20507716876890459010399667)
              ·
                refine ⟨30761575315335688515599501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20507716876890459010399667 30761575315335688515599501)
                ·
                  refine ⟨11535590743250883193349813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30761575315335688515599501 11535590743250883193349813)
                  ·
                    refine ⟨1081461632179770299376545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11535590743250883193349813 1081461632179770299376545)
                    ·
                      rfl

theorem cell23_6318417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_6318417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318417 prefixEnd_6318417 := by exact prefixLift 6318417
  have htrace : WordTrace (prefixWord ++ tailWord_6318417) baseStart_6318417 baseEnd_6318417 := by
    simpa [prefixWord, tailWord_6318417, baseEnd_6318417] using wordTrace_append hprefix tailTrace_6318417
  have hstable : (prefixWord ++ tailWord_6318417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318417).length < 2 ^ (prefixWord ++ tailWord_6318417).sum := by decide
  have hdescent : baseEnd_6318417 < baseStart_6318417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318448 : List Nat := [2, 1, 1, 1, 4, 3, 4, 2, 1, 1, 3]
def baseStart_6318448 : Nat := 118140960795 + 6318448 * 2 ^ 59
def prefixEnd_6318448 : Nat := 4983230072969 + 3 ^ 40 * 6318448 * 2
def baseEnd_6318448 : Nat := 3244400814439600276841993

theorem tailTrace_6318448 : CollatzResearch.WordTrace tailWord_6318448 prefixEnd_6318448 3244400814439600276841993 := by
  unfold tailWord_6318448
  simp only [CollatzResearch.WordTrace]
  refine ⟨115226365506674737925785999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153635154008899650567714665 115226365506674737925785999)
  ·
    refine ⟨172839548260012106888678999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115226365506674737925785999 172839548260012106888678999)
    ·
      refine ⟨259259322390018160333018499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172839548260012106888678999 259259322390018160333018499)
      ·
        refine ⟨388888983585027240499527749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259259322390018160333018499 388888983585027240499527749)
        ·
          refine ⟨72916684422192607593661453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 388888983585027240499527749 72916684422192607593661453)
          ·
            refine ⟨27343756658322227847623045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72916684422192607593661453 27343756658322227847623045)
            ·
              refine ⟨5126954373435417721429321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27343756658322227847623045 5126954373435417721429321)
              ·
                refine ⟨3845215780076563291071991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5126954373435417721429321 3845215780076563291071991)
                ·
                  refine ⟨5767823670114844936607987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845215780076563291071991 5767823670114844936607987)
                  ·
                    refine ⟨8651735505172267404911981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5767823670114844936607987 8651735505172267404911981)
                    ·
                      refine ⟨3244400814439600276841993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8651735505172267404911981 3244400814439600276841993)
                      ·
                        rfl

theorem cell23_6318448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 1, 1, 3].length) (baseStart_6318448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318448 prefixEnd_6318448 := by exact prefixLift 6318448
  have htrace : WordTrace (prefixWord ++ tailWord_6318448) baseStart_6318448 baseEnd_6318448 := by
    simpa [prefixWord, tailWord_6318448, baseEnd_6318448] using wordTrace_append hprefix tailTrace_6318448
  have hstable : (prefixWord ++ tailWord_6318448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318448).length < 2 ^ (prefixWord ++ tailWord_6318448).sum := by decide
  have hdescent : baseEnd_6318448 < baseStart_6318448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318460 : List Nat := [2, 2, 2, 1, 1, 1, 2, 12]
def baseStart_6318460 : Nat := 118140960795 + 6318460 * 2 ^ 59
def prefixEnd_6318460 : Nat := 4983230072969 + 3 ^ 40 * 6318460 * 2
def baseEnd_6318460 : Nat := 120163221341016823329331

theorem tailTrace_6318460 : CollatzResearch.WordTrace tailWord_6318460 prefixEnd_6318460 120163221341016823329331 := by
  unfold tailWord_6318460
  simp only [CollatzResearch.WordTrace]
  refine ⟨115226584344653000950504417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153635445792870667934005889 115226584344653000950504417)
  ·
    refine ⟨86419938258489750712878313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115226584344653000950504417 86419938258489750712878313)
    ·
      refine ⟨64814953693867313034658735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86419938258489750712878313 64814953693867313034658735)
      ·
        refine ⟨97222430540800969551988103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64814953693867313034658735 97222430540800969551988103)
        ·
          refine ⟨145833645811201454327982155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97222430540800969551988103 145833645811201454327982155)
          ·
            refine ⟨218750468716802181491973233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145833645811201454327982155 218750468716802181491973233)
            ·
              refine ⟨164062851537601636118979925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218750468716802181491973233 164062851537601636118979925)
              ·
                refine ⟨120163221341016823329331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 164062851537601636118979925 120163221341016823329331)
                ·
                  rfl

theorem cell23_6318460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 12].length) (baseStart_6318460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318460 prefixEnd_6318460 := by exact prefixLift 6318460
  have htrace : WordTrace (prefixWord ++ tailWord_6318460) baseStart_6318460 baseEnd_6318460 := by
    simpa [prefixWord, tailWord_6318460, baseEnd_6318460] using wordTrace_append hprefix tailTrace_6318460
  have hstable : (prefixWord ++ tailWord_6318460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318460).length < 2 ^ (prefixWord ++ tailWord_6318460).sum := by decide
  have hdescent : baseEnd_6318460 < baseStart_6318460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318471 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 3, 2, 2]
def baseStart_6318471 : Nat := 118140960795 + 6318471 * 2 ^ 59
def prefixEnd_6318471 : Nat := 4983230072969 + 3 ^ 40 * 6318471 * 2
def baseEnd_6318471 : Nat := 3244412624494653686854387

theorem tailTrace_6318471 : CollatzResearch.WordTrace tailWord_6318471 prefixEnd_6318471 3244412624494653686854387 := by
  unfold tailWord_6318471
  simp only [CollatzResearch.WordTrace]
  refine ⟨230453569892266150779659267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153635713261510767186439511 230453569892266150779659267)
  ·
    refine ⟨345680354838399226169488901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230453569892266150779659267 345680354838399226169488901)
    ·
      refine ⟨64815066532199854906779169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345680354838399226169488901 64815066532199854906779169)
      ·
        refine ⟨48611299899149891180084377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64815066532199854906779169 48611299899149891180084377)
        ·
          refine ⟨36458474924362418385063283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48611299899149891180084377 36458474924362418385063283)
          ·
            refine ⟨54687712386543627577594925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36458474924362418385063283 54687712386543627577594925)
            ·
              refine ⟨20507892144953860341598097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54687712386543627577594925 20507892144953860341598097)
              ·
                refine ⟨15380919108715395256198573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20507892144953860341598097 15380919108715395256198573)
                ·
                  refine ⟨5767844665768273221074465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15380919108715395256198573 5767844665768273221074465)
                  ·
                    refine ⟨4325883499326204915805849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5767844665768273221074465 4325883499326204915805849)
                    ·
                      refine ⟨3244412624494653686854387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325883499326204915805849 3244412624494653686854387)
                      ·
                        rfl

theorem cell23_6318471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_6318471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318471 prefixEnd_6318471 := by exact prefixLift 6318471
  have htrace : WordTrace (prefixWord ++ tailWord_6318471) baseStart_6318471 baseEnd_6318471 := by
    simpa [prefixWord, tailWord_6318471, baseEnd_6318471] using wordTrace_append hprefix tailTrace_6318471
  have hstable : (prefixWord ++ tailWord_6318471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318471).length < 2 ^ (prefixWord ++ tailWord_6318471).sum := by decide
  have hdescent : baseEnd_6318471 < baseStart_6318471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318480 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 6]
def baseStart_6318480 : Nat := 118140960795 + 6318480 * 2 ^ 59
def prefixEnd_6318480 : Nat := 4983230072969 + 3 ^ 40 * 6318480 * 2
def baseEnd_6318480 : Nat := 3244417245820544151641845

theorem tailTrace_6318480 : CollatzResearch.WordTrace tailWord_6318480 prefixEnd_6318480 3244417245820544151641845 := by
  unfold tailWord_6318480
  simp only [CollatzResearch.WordTrace]
  refine ⟨115226949074616772658368447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153635932099489030211157929 115226949074616772658368447)
  ·
    refine ⟨172840423611925158987552671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115226949074616772658368447 172840423611925158987552671)
    ·
      refine ⟨259260635417887738481329007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172840423611925158987552671 259260635417887738481329007)
      ·
        refine ⟨388890953126831607721993511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259260635417887738481329007 388890953126831607721993511)
        ·
          refine ⟨583336429690247411582990267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388890953126831607721993511 583336429690247411582990267)
          ·
            refine ⟨875004644535371117374485401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583336429690247411582990267 875004644535371117374485401)
            ·
              refine ⟨656253483401528338030864051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875004644535371117374485401 656253483401528338030864051)
              ·
                refine ⟨984380225102292507046296077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656253483401528338030864051 984380225102292507046296077)
                ·
                  refine ⟨369142584413359690142361029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 984380225102292507046296077 369142584413359690142361029)
                  ·
                    refine ⟨69214234577504941901692693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 369142584413359690142361029 69214234577504941901692693)
                    ·
                      refine ⟨3244417245820544151641845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69214234577504941901692693 3244417245820544151641845)
                      ·
                        rfl

theorem cell23_6318480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_6318480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318480 prefixEnd_6318480 := by exact prefixLift 6318480
  have htrace : WordTrace (prefixWord ++ tailWord_6318480) baseStart_6318480 baseEnd_6318480 := by
    simpa [prefixWord, tailWord_6318480, baseEnd_6318480] using wordTrace_append hprefix tailTrace_6318480
  have hstable : (prefixWord ++ tailWord_6318480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318480).length < 2 ^ (prefixWord ++ tailWord_6318480).sum := by decide
  have hdescent : baseEnd_6318480 < baseStart_6318480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318488 : List Nat := [2, 1, 2, 5, 1, 3, 2, 1, 1, 1, 4]
def baseStart_6318488 : Nat := 118140960795 + 6318488 * 2 ^ 59
def prefixEnd_6318488 : Nat := 4983230072969 + 3 ^ 40 * 6318488 * 2
def baseEnd_6318488 : Nat := 3244421353665780120341809

theorem tailTrace_6318488 : CollatzResearch.WordTrace tailWord_6318488 prefixEnd_6318488 3244421353665780120341809 := by
  unfold tailWord_6318488
  simp only [CollatzResearch.WordTrace]
  refine ⟨115227094966602281341514059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153636126622136375122018745 115227094966602281341514059)
  ·
    refine ⟨172840642449903422012271089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115227094966602281341514059 172840642449903422012271089)
    ·
      refine ⟨129630481837427566509203317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172840642449903422012271089 129630481837427566509203317)
      ·
        refine ⟨12152857672258834360237811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129630481837427566509203317 12152857672258834360237811)
        ·
          refine ⟨18229286508388251540356717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12152857672258834360237811 18229286508388251540356717)
          ·
            refine ⟨6835982440645594327633769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18229286508388251540356717 6835982440645594327633769)
            ·
              refine ⟨5126986830484195745725327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6835982440645594327633769 5126986830484195745725327)
              ·
                refine ⟨7690480245726293618587991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5126986830484195745725327 7690480245726293618587991)
                ·
                  refine ⟨11535720368589440427881987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7690480245726293618587991 11535720368589440427881987)
                  ·
                    refine ⟨17303580552884160641822981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11535720368589440427881987 17303580552884160641822981)
                    ·
                      refine ⟨3244421353665780120341809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17303580552884160641822981 3244421353665780120341809)
                      ·
                        rfl

theorem cell23_6318488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_6318488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318488 prefixEnd_6318488 := by exact prefixLift 6318488
  have htrace : WordTrace (prefixWord ++ tailWord_6318488) baseStart_6318488 baseEnd_6318488 := by
    simpa [prefixWord, tailWord_6318488, baseEnd_6318488] using wordTrace_append hprefix tailTrace_6318488
  have hstable : (prefixWord ++ tailWord_6318488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318488).length < 2 ^ (prefixWord ++ tailWord_6318488).sum := by decide
  have hdescent : baseEnd_6318488 < baseStart_6318488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318494 : List Nat := [4, 3, 1, 2, 1, 2, 10]
def baseStart_6318494 : Nat := 118140960795 + 6318494 * 2 ^ 59
def prefixEnd_6318494 : Nat := 4983230072969 + 3 ^ 40 * 6318494 * 2
def baseEnd_6318494 : Nat := 40054622648761816010701

theorem tailTrace_6318494 : CollatzResearch.WordTrace tailWord_6318494 prefixEnd_6318494 40054622648761816010701 := by
  unfold tailWord_6318494
  simp only [CollatzResearch.WordTrace]
  refine ⟨28806801096397853213468317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153636272514121883805164357 28806801096397853213468317)
  ·
    refine ⟨10802550411149194955050619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28806801096397853213468317 10802550411149194955050619)
    ·
      refine ⟨16203825616723792432575929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10802550411149194955050619 16203825616723792432575929)
      ·
        refine ⟨12152869212542844324431947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16203825616723792432575929 12152869212542844324431947)
        ·
          refine ⟨18229303818814266486647921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12152869212542844324431947 18229303818814266486647921)
          ·
            refine ⟨13671977864110699864985941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18229303818814266486647921 13671977864110699864985941)
            ·
              refine ⟨40054622648761816010701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13671977864110699864985941 40054622648761816010701)
              ·
                rfl

theorem cell23_6318494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 10].length) (baseStart_6318494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318494 prefixEnd_6318494 := by exact prefixLift 6318494
  have htrace : WordTrace (prefixWord ++ tailWord_6318494) baseStart_6318494 baseEnd_6318494 := by
    simpa [prefixWord, tailWord_6318494, baseEnd_6318494] using wordTrace_append hprefix tailTrace_6318494
  have hstable : (prefixWord ++ tailWord_6318494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318494).length < 2 ^ (prefixWord ++ tailWord_6318494).sum := by decide
  have hdescent : baseEnd_6318494 < baseStart_6318494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318521 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 1, 3, 3]
def baseStart_6318521 : Nat := 118140960795 + 6318521 * 2 ^ 59
def prefixEnd_6318521 : Nat := 4983230072969 + 3 ^ 40 * 6318521 * 2
def baseEnd_6318521 : Nat := 3244438298527378491229157

theorem tailTrace_6318521 : CollatzResearch.WordTrace tailWord_6318521 prefixEnd_6318521 3244438298527378491229157 := by
  unfold tailWord_6318521
  simp only [CollatzResearch.WordTrace]
  refine ⟨230455393542085009318979417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153636929028056672879319611 230455393542085009318979417)
  ·
    refine ⟨172841545156563756989234563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230455393542085009318979417 172841545156563756989234563)
    ·
      refine ⟨259262317734845635483851845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172841545156563756989234563 259262317734845635483851845)
      ·
        refine ⟨48611684575283556653222221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259262317734845635483851845 48611684575283556653222221)
        ·
          refine ⟨18229381715731333744958333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48611684575283556653222221 18229381715731333744958333)
          ·
            refine ⟨6836018143399250154359375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18229381715731333744958333 6836018143399250154359375)
            ·
              refine ⟨10254027215098875231539063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6836018143399250154359375 10254027215098875231539063)
              ·
                refine ⟨15381040822648312847308595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10254027215098875231539063 15381040822648312847308595)
                ·
                  refine ⟨23071561233972469270962893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15381040822648312847308595 23071561233972469270962893)
                  ·
                    refine ⟨8651835462739675976611085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23071561233972469270962893 8651835462739675976611085)
                    ·
                      refine ⟨3244438298527378491229157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8651835462739675976611085 3244438298527378491229157)
                      ·
                        rfl

theorem cell23_6318521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_6318521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318521 prefixEnd_6318521 := by exact prefixLift 6318521
  have htrace : WordTrace (prefixWord ++ tailWord_6318521) baseStart_6318521 baseEnd_6318521 := by
    simpa [prefixWord, tailWord_6318521, baseEnd_6318521] using wordTrace_append hprefix tailTrace_6318521
  have hstable : (prefixWord ++ tailWord_6318521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318521).length < 2 ^ (prefixWord ++ tailWord_6318521).sum := by decide
  have hdescent : baseEnd_6318521 < baseStart_6318521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318548 : List Nat := [2, 4, 1, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_6318548 : Nat := 118140960795 + 6318548 * 2 ^ 59
def prefixEnd_6318548 : Nat := 4983230072969 + 3 ^ 40 * 6318548 * 2
def baseEnd_6318548 : Nat := 3244452162505049885591533

theorem tailTrace_6318548 : CollatzResearch.WordTrace tailWord_6318548 prefixEnd_6318548 3244452162505049885591533 := by
  unfold tailWord_6318548
  simp only [CollatzResearch.WordTrace]
  refine ⟨115228189156493596465106149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153637585541991461953474865 115228189156493596465106149)
  ·
    refine ⟨21605285466842549337207403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115228189156493596465106149 21605285466842549337207403)
    ·
      refine ⟨32407928200263824005811105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21605285466842549337207403 32407928200263824005811105)
      ·
        refine ⟨24305946150197868004358329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32407928200263824005811105 24305946150197868004358329)
        ·
          refine ⟨18229459612648401003268747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24305946150197868004358329 18229459612648401003268747)
          ·
            refine ⟨27344189418972601504903121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18229459612648401003268747 27344189418972601504903121)
            ·
              refine ⟨20508142064229451128677341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27344189418972601504903121 20508142064229451128677341)
              ·
                refine ⟨7690553274086044173254003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20508142064229451128677341 7690553274086044173254003)
                ·
                  refine ⟨11535829911129066259881005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7690553274086044173254003 11535829911129066259881005)
                  ·
                    refine ⟨4325936216673399847455377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11535829911129066259881005 4325936216673399847455377)
                    ·
                      refine ⟨3244452162505049885591533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325936216673399847455377 3244452162505049885591533)
                      ·
                        rfl

theorem cell23_6318548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_6318548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318548 prefixEnd_6318548 := by exact prefixLift 6318548
  have htrace : WordTrace (prefixWord ++ tailWord_6318548) baseStart_6318548 baseEnd_6318548 := by
    simpa [prefixWord, tailWord_6318548, baseEnd_6318548] using wordTrace_append hprefix tailTrace_6318548
  have hstable : (prefixWord ++ tailWord_6318548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318548).length < 2 ^ (prefixWord ++ tailWord_6318548).sum := by decide
  have hdescent : baseEnd_6318548 < baseStart_6318548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318561 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 4, 2, 2]
def baseStart_6318561 : Nat := 118140960795 + 6318561 * 2 ^ 59
def prefixEnd_6318561 : Nat := 4983230072969 + 3 ^ 40 * 6318561 * 2
def baseEnd_6318561 : Nat := 3244458837753558334728973

theorem tailTrace_6318561 : CollatzResearch.WordTrace tailWord_6318561 prefixEnd_6318561 3244458837753558334728973 := by
  unfold tailWord_6318561
  simp only [CollatzResearch.WordTrace]
  refine ⟨230456852461940096150435537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153637901641293397433623691 230456852461940096150435537)
  ·
    refine ⟨172842639346455072112826653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230456852461940096150435537 172842639346455072112826653)
    ·
      refine ⟨64815989754920652042309995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172842639346455072112826653 64815989754920652042309995)
      ·
        refine ⟨97223984632380978063464993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64815989754920652042309995 97223984632380978063464993)
        ·
          refine ⟨72917988474285733547598745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97223984632380978063464993 72917988474285733547598745)
          ·
            refine ⟨54688491355714300160699059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72917988474285733547598745 54688491355714300160699059)
            ·
              refine ⟨82032737033571450241048589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54688491355714300160699059 82032737033571450241048589)
              ·
                refine ⟨30762276387589293840393221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82032737033571450241048589 30762276387589293840393221)
                ·
                  refine ⟨5767926822672992595073729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30762276387589293840393221 5767926822672992595073729)
                  ·
                    refine ⟨4325945117004744446305297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5767926822672992595073729 4325945117004744446305297)
                    ·
                      refine ⟨3244458837753558334728973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325945117004744446305297 3244458837753558334728973)
                      ·
                        rfl

theorem cell23_6318561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_6318561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318561 prefixEnd_6318561 := by exact prefixLift 6318561
  have htrace : WordTrace (prefixWord ++ tailWord_6318561) baseStart_6318561 baseEnd_6318561 := by
    simpa [prefixWord, tailWord_6318561, baseEnd_6318561] using wordTrace_append hprefix tailTrace_6318561
  have hstable : (prefixWord ++ tailWord_6318561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318561).length < 2 ^ (prefixWord ++ tailWord_6318561).sum := by decide
  have hdescent : baseEnd_6318561 < baseStart_6318561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318597 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 1, 7]
def baseStart_6318597 : Nat := 118140960795 + 6318597 * 2 ^ 59
def prefixEnd_6318597 : Nat := 4983230072969 + 3 ^ 40 * 6318597 * 2
def baseEnd_6318597 : Nat := 1081492441019040064626269

theorem tailTrace_6318597 : CollatzResearch.WordTrace tailWord_6318597 prefixEnd_6318597 1081492441019040064626269 := by
  unfold tailWord_6318597
  simp only [CollatzResearch.WordTrace]
  refine ⟨230458165489809674298746045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153638776993206449532497363 230458165489809674298746045)
  ·
    refine ⟨86421812058678627862029767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230458165489809674298746045 86421812058678627862029767)
    ·
      refine ⟨129632718088017941793044651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86421812058678627862029767 129632718088017941793044651)
      ·
        refine ⟨194449077132026912689566977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129632718088017941793044651 194449077132026912689566977)
        ·
          refine ⟨145836807849020184517175233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194449077132026912689566977 145836807849020184517175233)
          ·
            refine ⟨109377605886765138387881425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145836807849020184517175233 109377605886765138387881425)
            ·
              refine ⟨82033204415073853790911069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109377605886765138387881425 82033204415073853790911069)
              ·
                refine ⟨30762451655652695171591651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82033204415073853790911069 30762451655652695171591651)
                ·
                  refine ⟨46143677483479042757387477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30762451655652695171591651 46143677483479042757387477)
                  ·
                    refine ⟨1081492441019040064626269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46143677483479042757387477 1081492441019040064626269)
                    ·
                      rfl

theorem cell23_6318597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_6318597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318597 prefixEnd_6318597 := by exact prefixLift 6318597
  have htrace : WordTrace (prefixWord ++ tailWord_6318597) baseStart_6318597 baseEnd_6318597 := by
    simpa [prefixWord, tailWord_6318597, baseEnd_6318597] using wordTrace_append hprefix tailTrace_6318597
  have hstable : (prefixWord ++ tailWord_6318597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318597).length < 2 ^ (prefixWord ++ tailWord_6318597).sum := by decide
  have hdescent : baseEnd_6318597 < baseStart_6318597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318607 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 5]
def baseStart_6318607 : Nat := 118140960795 + 6318607 * 2 ^ 59
def prefixEnd_6318607 : Nat := 4983230072969 + 3 ^ 40 * 6318607 * 2
def baseEnd_6318607 : Nat := 3244482457863665154753761

theorem tailTrace_6318607 : CollatzResearch.WordTrace tailWord_6318607 prefixEnd_6318607 3244482457863665154753761 := by
  unfold tailWord_6318607
  simp only [CollatzResearch.WordTrace]
  refine ⟨230458530219773446006610075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153639020146515630671073383 230458530219773446006610075)
  ·
    refine ⟨345687795329660169009915113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230458530219773446006610075 345687795329660169009915113)
    ·
      refine ⟨259265846497245126757436335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345687795329660169009915113 259265846497245126757436335)
      ·
        refine ⟨388898769745867690136154503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259265846497245126757436335 388898769745867690136154503)
        ·
          refine ⟨583348154618801535204231755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388898769745867690136154503 583348154618801535204231755)
          ·
            refine ⟨875022231928202302806347633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583348154618801535204231755 875022231928202302806347633)
            ·
              refine ⟨656266673946151727104760725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875022231928202302806347633 656266673946151727104760725)
              ·
                refine ⟨30762500341225862208035659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 656266673946151727104760725 30762500341225862208035659)
                ·
                  refine ⟨46143750511838793312053489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30762500341225862208035659 46143750511838793312053489)
                  ·
                    refine ⟨34607812883879094984040117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46143750511838793312053489 34607812883879094984040117)
                    ·
                      refine ⟨3244482457863665154753761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34607812883879094984040117 3244482457863665154753761)
                      ·
                        rfl

theorem cell23_6318607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_6318607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318607 prefixEnd_6318607 := by exact prefixLift 6318607
  have htrace : WordTrace (prefixWord ++ tailWord_6318607) baseStart_6318607 baseEnd_6318607 := by
    simpa [prefixWord, tailWord_6318607, baseEnd_6318607] using wordTrace_append hprefix tailTrace_6318607
  have hstable : (prefixWord ++ tailWord_6318607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318607).length < 2 ^ (prefixWord ++ tailWord_6318607).sum := by decide
  have hdescent : baseEnd_6318607 < baseStart_6318607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318612 : List Nat := [2, 4, 3, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_6318612 : Nat := 118140960795 + 6318612 * 2 ^ 59
def prefixEnd_6318612 : Nat := 4983230072969 + 3 ^ 40 * 6318612 * 2
def baseEnd_6318612 : Nat := 3244485025266937635191239

theorem tailTrace_6318612 : CollatzResearch.WordTrace tailWord_6318612 prefixEnd_6318612 3244485025266937635191239 := by
  unfold tailWord_6318612
  simp only [CollatzResearch.WordTrace]
  refine ⟨115229356292377665930271045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153639141723170221240361393 115229356292377665930271045)
  ·
    refine ⟨21605504304820812361925821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115229356292377665930271045 21605504304820812361925821)
    ·
      refine ⟨8102064114307804635722183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21605504304820812361925821 8102064114307804635722183)
      ·
        refine ⟨12153096171461706953583275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8102064114307804635722183 12153096171461706953583275)
        ·
          refine ⟨18229644257192560430374913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12153096171461706953583275 18229644257192560430374913)
          ·
            refine ⟨13672233192894420322781185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18229644257192560430374913 13672233192894420322781185)
            ·
              refine ⟨10254174894670815242085889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13672233192894420322781185 10254174894670815242085889)
              ·
                refine ⟨7690631171003111431564417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10254174894670815242085889 7690631171003111431564417)
                ·
                  refine ⟨5767973378252333573673313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7690631171003111431564417 5767973378252333573673313)
                  ·
                    refine ⟨4325980033689250180254985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5767973378252333573673313 4325980033689250180254985)
                    ·
                      refine ⟨3244485025266937635191239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325980033689250180254985 3244485025266937635191239)
                      ·
                        rfl

theorem cell23_6318612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_6318612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318612 prefixEnd_6318612 := by exact prefixLift 6318612
  have htrace : WordTrace (prefixWord ++ tailWord_6318612) baseStart_6318612 baseEnd_6318612 := by
    simpa [prefixWord, tailWord_6318612, baseEnd_6318612] using wordTrace_append hprefix tailTrace_6318612
  have hstable : (prefixWord ++ tailWord_6318612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318612).length < 2 ^ (prefixWord ++ tailWord_6318612).sum := by decide
  have hdescent : baseEnd_6318612 < baseStart_6318612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318621 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_6318621 : Nat := 118140960795 + 6318621 * 2 ^ 59
def prefixEnd_6318621 : Nat := 4983230072969 + 3 ^ 40 * 6318621 * 2
def baseEnd_6318621 : Nat := 3244489646592828099978697

theorem tailTrace_6318621 : CollatzResearch.WordTrace tailWord_6318621 prefixEnd_6318621 3244489646592828099978697 := by
  unfold tailWord_6318621
  simp only [CollatzResearch.WordTrace]
  refine ⟨230459040841722726397619717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153639360561148484265079811 230459040841722726397619717)
  ·
    refine ⟨43211070157823011199553697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230459040841722726397619717 43211070157823011199553697)
    ·
      refine ⟨32408302618367258399665273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43211070157823011199553697 32408302618367258399665273)
      ·
        refine ⟨24306226963775443799748955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32408302618367258399665273 24306226963775443799748955)
        ·
          refine ⟨36459340445663165699623433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24306226963775443799748955 36459340445663165699623433)
          ·
            refine ⟨27344505334247374274717575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36459340445663165699623433 27344505334247374274717575)
            ·
              refine ⟨41016758001371061412076363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27344505334247374274717575 41016758001371061412076363)
              ·
                refine ⟨61525137002056592118114545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41016758001371061412076363 61525137002056592118114545)
                ·
                  refine ⟨46143852751542444088585909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61525137002056592118114545 46143852751542444088585909)
                  ·
                    refine ⟨4325986195457104133304929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46143852751542444088585909 4325986195457104133304929)
                    ·
                      refine ⟨3244489646592828099978697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4325986195457104133304929 3244489646592828099978697)
                      ·
                        rfl

theorem cell23_6318621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_6318621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318621 prefixEnd_6318621 := by exact prefixLift 6318621
  have htrace : WordTrace (prefixWord ++ tailWord_6318621) baseStart_6318621 baseEnd_6318621 := by
    simpa [prefixWord, tailWord_6318621, baseEnd_6318621] using wordTrace_append hprefix tailTrace_6318621
  have hstable : (prefixWord ++ tailWord_6318621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318621).length < 2 ^ (prefixWord ++ tailWord_6318621).sum := by decide
  have hdescent : baseEnd_6318621 < baseStart_6318621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318628 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 2, 3, 3]
def baseStart_6318628 : Nat := 118140960795 + 6318628 * 2 ^ 59
def prefixEnd_6318628 : Nat := 4983230072969 + 3 ^ 40 * 6318628 * 2
def baseEnd_6318628 : Nat := 3244493240957409572591165

theorem tailTrace_6318628 : CollatzResearch.WordTrace tailWord_6318628 prefixEnd_6318628 3244493240957409572591165 := by
  unfold tailWord_6318628
  simp only [CollatzResearch.WordTrace]
  refine ⟨115229648076348683296562269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153639530768464911062083025 115229648076348683296562269)
  ·
    refine ⟨43211118028630756236210851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115229648076348683296562269 43211118028630756236210851)
    ·
      refine ⟨64816677042946134354316277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43211118028630756236210851 64816677042946134354316277)
      ·
        refine ⟨6076563472776200095717151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64816677042946134354316277 6076563472776200095717151)
        ·
          refine ⟨9114845209164300143575727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076563472776200095717151 9114845209164300143575727)
          ·
            refine ⟨13672267813746450215363591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9114845209164300143575727 13672267813746450215363591)
            ·
              refine ⟨20508401720619675323045387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13672267813746450215363591 20508401720619675323045387)
              ·
                refine ⟨30762602580929512984568081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20508401720619675323045387 30762602580929512984568081)
                ·
                  refine ⟨23071951935697134738426061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30762602580929512984568081 23071951935697134738426061)
                  ·
                    refine ⟨8651981975886425526909773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23071951935697134738426061 8651981975886425526909773)
                    ·
                      refine ⟨3244493240957409572591165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8651981975886425526909773 3244493240957409572591165)
                      ·
                        rfl

theorem cell23_6318628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_6318628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318628 prefixEnd_6318628 := by exact prefixLift 6318628
  have htrace : WordTrace (prefixWord ++ tailWord_6318628) baseStart_6318628 baseEnd_6318628 := by
    simpa [prefixWord, tailWord_6318628, baseEnd_6318628] using wordTrace_append hprefix tailTrace_6318628
  have hstable : (prefixWord ++ tailWord_6318628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318628).length < 2 ^ (prefixWord ++ tailWord_6318628).sum := by decide
  have hdescent : baseEnd_6318628 < baseStart_6318628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318674 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 8]
def baseStart_6318674 : Nat := 118140960795 + 6318674 * 2 ^ 59
def prefixEnd_6318674 : Nat := 4983230072969 + 3 ^ 40 * 6318674 * 2
def baseEnd_6318674 : Nat := 360501873451946265846217

theorem tailTrace_6318674 : CollatzResearch.WordTrace tailWord_6318674 prefixEnd_6318674 360501873451946265846217 := by
  unfold tailWord_6318674
  simp only [CollatzResearch.WordTrace]
  refine ⟨57615243477632679112324769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153640649273687144299532717 57615243477632679112324769)
  ·
    refine ⟨43211432608224509334243577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57615243477632679112324769 43211432608224509334243577)
    ·
      refine ⟨32408574456168382000682683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43211432608224509334243577 32408574456168382000682683)
      ·
        refine ⟨48612861684252573001024025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32408574456168382000682683 48612861684252573001024025)
        ·
          refine ⟨36459646263189429750768019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48612861684252573001024025 36459646263189429750768019)
          ·
            refine ⟨54689469394784144626152029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36459646263189429750768019 54689469394784144626152029)
            ·
              refine ⟨20508551023044054234807011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54689469394784144626152029 20508551023044054234807011)
              ·
                refine ⟨30762826534566081352210517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20508551023044054234807011 30762826534566081352210517)
                ·
                  refine ⟨360501873451946265846217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30762826534566081352210517 360501873451946265846217)
                  ·
                    rfl

theorem cell23_6318674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_6318674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318674 prefixEnd_6318674 := by exact prefixLift 6318674
  have htrace : WordTrace (prefixWord ++ tailWord_6318674) baseStart_6318674 baseEnd_6318674 := by
    simpa [prefixWord, tailWord_6318674, baseEnd_6318674] using wordTrace_append hprefix tailTrace_6318674
  have hstable : (prefixWord ++ tailWord_6318674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318674).length < 2 ^ (prefixWord ++ tailWord_6318674).sum := by decide
  have hdescent : baseEnd_6318674 < baseStart_6318674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318691 : List Nat := [1, 1, 1, 5, 1, 2, 5, 1, 6]
def baseStart_6318691 : Nat := 118140960795 + 6318691 * 2 ^ 59
def prefixEnd_6318691 : Nat := 4983230072969 + 3 ^ 40 * 6318691 * 2
def baseEnd_6318691 : Nat := 360502843359849202900375

theorem tailTrace_6318691 : CollatzResearch.WordTrace tailWord_6318691 prefixEnd_6318691 360502843359849202900375 := by
  unfold tailWord_6318691
  simp only [CollatzResearch.WordTrace]
  refine ⟨230461593951469128352667927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153641062634312752235111951 230461593951469128352667927)
  ·
    refine ⟨345692390927203692529001891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230461593951469128352667927 345692390927203692529001891)
    ·
      refine ⟨518538586390805538793502837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345692390927203692529001891 518538586390805538793502837)
      ·
        refine ⟨48612992474138019261890891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 518538586390805538793502837 48612992474138019261890891)
        ·
          refine ⟨72919488711207028892836337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48612992474138019261890891 72919488711207028892836337)
          ·
            refine ⟨54689616533405271669627253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72919488711207028892836337 54689616533405271669627253)
            ·
              refine ⟨5127151550006744219027555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54689616533405271669627253 5127151550006744219027555)
              ·
                refine ⟨7690727325010116328541333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5127151550006744219027555 7690727325010116328541333)
                ·
                  refine ⟨360502843359849202900375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7690727325010116328541333 360502843359849202900375)
                  ·
                    rfl

theorem cell23_6318691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 6].length) (baseStart_6318691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318691 prefixEnd_6318691 := by exact prefixLift 6318691
  have htrace : WordTrace (prefixWord ++ tailWord_6318691) baseStart_6318691 baseEnd_6318691 := by
    simpa [prefixWord, tailWord_6318691, baseEnd_6318691] using wordTrace_append hprefix tailTrace_6318691
  have hstable : (prefixWord ++ tailWord_6318691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318691).length < 2 ^ (prefixWord ++ tailWord_6318691).sum := by decide
  have hdescent : baseEnd_6318691 < baseStart_6318691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318711 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 1, 5, 2]
def baseStart_6318711 : Nat := 118140960795 + 6318711 * 2 ^ 59
def prefixEnd_6318711 : Nat := 4983230072969 + 3 ^ 40 * 6318711 * 2
def baseEnd_6318711 : Nat := 3244535859851732747853283

theorem tailTrace_6318711 : CollatzResearch.WordTrace tailWord_6318711 prefixEnd_6318711 3244535859851732747853283 := by
  unfold tailWord_6318711
  simp only [CollatzResearch.WordTrace]
  refine ⟨230462323411396671768395987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153641548940931114512263991 230462323411396671768395987)
  ·
    refine ⟨345693485117095007652593981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230462323411396671768395987 345693485117095007652593981)
    ·
      refine ⟨129635056918910627869722743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345693485117095007652593981 129635056918910627869722743)
      ·
        refine ⟨194452585378365941804584115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129635056918910627869722743 194452585378365941804584115)
        ·
          refine ⟨291678878067548912706876173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194452585378365941804584115 291678878067548912706876173)
          ·
            refine ⟨109379579275330842265078565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291678878067548912706876173 109379579275330842265078565)
            ·
              refine ⟨20508671114124532924702231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109379579275330842265078565 20508671114124532924702231)
              ·
                refine ⟨30763006671186799387053347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20508671114124532924702231 30763006671186799387053347)
                ·
                  refine ⟨46144510006780199080580021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30763006671186799387053347 46144510006780199080580021)
                  ·
                    refine ⟨4326047813135643663804377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46144510006780199080580021 4326047813135643663804377)
                    ·
                      refine ⟨3244535859851732747853283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326047813135643663804377 3244535859851732747853283)
                      ·
                        rfl

theorem cell23_6318711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 5, 2].length) (baseStart_6318711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318711 prefixEnd_6318711 := by exact prefixLift 6318711
  have htrace : WordTrace (prefixWord ++ tailWord_6318711) baseStart_6318711 baseEnd_6318711 := by
    simpa [prefixWord, tailWord_6318711, baseEnd_6318711] using wordTrace_append hprefix tailTrace_6318711
  have hstable : (prefixWord ++ tailWord_6318711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318711).length < 2 ^ (prefixWord ++ tailWord_6318711).sum := by decide
  have hdescent : baseEnd_6318711 < baseStart_6318711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318721 : List Nat := [1, 2, 4, 2, 1, 1, 1, 5, 1, 5]
def baseStart_6318721 : Nat := 118140960795 + 6318721 * 2 ^ 59
def prefixEnd_6318721 : Nat := 4983230072969 + 3 ^ 40 * 6318721 * 2
def baseEnd_6318721 : Nat := 1081513664886092569576079

theorem tailTrace_6318721 : CollatzResearch.WordTrace tailWord_6318721 prefixEnd_6318721 1081513664886092569576079 := by
  unfold tailWord_6318721
  simp only [CollatzResearch.WordTrace]
  refine ⟨230462688141360443476260017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153641792094240295650840011 230462688141360443476260017)
  ·
    refine ⟨172847016106020332607195013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230462688141360443476260017 172847016106020332607195013)
    ·
      refine ⟨32408815519878812363849065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172847016106020332607195013 32408815519878812363849065)
      ·
        refine ⟨24306611639909109272886799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32408815519878812363849065 24306611639909109272886799)
        ·
          refine ⟨36459917459863663909330199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24306611639909109272886799 36459917459863663909330199)
          ·
            refine ⟨54689876189795495863995299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36459917459863663909330199 54689876189795495863995299)
            ·
              refine ⟨82034814284693243795992949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54689876189795495863995299 82034814284693243795992949)
              ·
                refine ⟨7690763839189991605874339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82034814284693243795992949 7690763839189991605874339)
                ·
                  refine ⟨11536145758784987408811509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7690763839189991605874339 11536145758784987408811509)
                  ·
                    refine ⟨1081513664886092569576079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11536145758784987408811509 1081513664886092569576079)
                    ·
                      rfl

theorem cell23_6318721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_6318721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318721 prefixEnd_6318721 := by exact prefixLift 6318721
  have htrace : WordTrace (prefixWord ++ tailWord_6318721) baseStart_6318721 baseEnd_6318721 := by
    simpa [prefixWord, tailWord_6318721, baseEnd_6318721] using wordTrace_append hprefix tailTrace_6318721
  have hstable : (prefixWord ++ tailWord_6318721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318721).length < 2 ^ (prefixWord ++ tailWord_6318721).sum := by decide
  have hdescent : baseEnd_6318721 < baseStart_6318721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318771 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 4]
def baseStart_6318771 : Nat := 118140960795 + 6318771 * 2 ^ 59
def prefixEnd_6318771 : Nat := 4983230072969 + 3 ^ 40 * 6318771 * 2
def baseEnd_6318771 : Nat := 3244566668691002513103007

theorem tailTrace_6318771 : CollatzResearch.WordTrace tailWord_6318771 prefixEnd_6318771 3244566668691002513103007 := by
  unfold tailWord_6318771
  simp only [CollatzResearch.WordTrace]
  refine ⟨230464511791179302015580167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153643007860786201343720111 230464511791179302015580167)
  ·
    refine ⟨345696767686768953023370251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230464511791179302015580167 345696767686768953023370251)
    ·
      refine ⟨518545151530153429535055377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345696767686768953023370251 518545151530153429535055377)
      ·
        refine ⟨388908863647615072151291533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 518545151530153429535055377 388908863647615072151291533)
        ·
          refine ⟨145840823867855652056734325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388908863647615072151291533 145840823867855652056734325)
          ·
            refine ⟨13672577237611467380318843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145840823867855652056734325 13672577237611467380318843)
            ·
              refine ⟨20508865856417201070478265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13672577237611467380318843 20508865856417201070478265)
              ·
                refine ⟨15381649392312900802858699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20508865856417201070478265 15381649392312900802858699)
                ·
                  refine ⟨23072474088469351204288049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15381649392312900802858699 23072474088469351204288049)
                  ·
                    refine ⟨17304355566352013403216037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23072474088469351204288049 17304355566352013403216037)
                    ·
                      refine ⟨3244566668691002513103007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17304355566352013403216037 3244566668691002513103007)
                      ·
                        rfl

theorem cell23_6318771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_6318771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318771 prefixEnd_6318771 := by exact prefixLift 6318771
  have htrace : WordTrace (prefixWord ++ tailWord_6318771) baseStart_6318771 baseEnd_6318771 := by
    simpa [prefixWord, tailWord_6318771, baseEnd_6318771] using wordTrace_append hprefix tailTrace_6318771
  have hstable : (prefixWord ++ tailWord_6318771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318771).length < 2 ^ (prefixWord ++ tailWord_6318771).sum := by decide
  have hdescent : baseEnd_6318771 < baseStart_6318771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318775 : List Nat := [1, 1, 3, 1, 6, 1, 3, 1, 1, 1, 4]
def baseStart_6318775 : Nat := 118140960795 + 6318775 * 2 ^ 59
def prefixEnd_6318775 : Nat := 4983230072969 + 3 ^ 40 * 6318775 * 2
def baseEnd_6318775 : Nat := 3244568722613620497452989

theorem tailTrace_6318775 : CollatzResearch.WordTrace tailWord_6318775 prefixEnd_6318775 3244568722613620497452989 := by
  unfold tailWord_6318775
  simp only [CollatzResearch.WordTrace]
  refine ⟨230464657683164810698725779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153643105122109873799150519 230464657683164810698725779)
  ·
    refine ⟨345696986524747216048088669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230464657683164810698725779 345696986524747216048088669)
    ·
      refine ⟨129636369946780206018033251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345696986524747216048088669 129636369946780206018033251)
      ·
        refine ⟨194454554920170309027049877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129636369946780206018033251 194454554920170309027049877)
        ·
          refine ⟨9115057261882983235642963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 194454554920170309027049877 9115057261882983235642963)
          ·
            refine ⟨13672585892824474853464445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9115057261882983235642963 13672585892824474853464445)
            ·
              refine ⟨5127219709809178070049167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13672585892824474853464445 5127219709809178070049167)
              ·
                refine ⟨7690829564713767105073751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5127219709809178070049167 7690829564713767105073751)
                ·
                  refine ⟨11536244347070650657610627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7690829564713767105073751 11536244347070650657610627)
                  ·
                    refine ⟨17304366520605975986415941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11536244347070650657610627 17304366520605975986415941)
                    ·
                      refine ⟨3244568722613620497452989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17304366520605975986415941 3244568722613620497452989)
                      ·
                        rfl

theorem cell23_6318775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 1, 1, 4].length) (baseStart_6318775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318775 prefixEnd_6318775 := by exact prefixLift 6318775
  have htrace : WordTrace (prefixWord ++ tailWord_6318775) baseStart_6318775 baseEnd_6318775 := by
    simpa [prefixWord, tailWord_6318775, baseEnd_6318775] using wordTrace_append hprefix tailTrace_6318775
  have hstable : (prefixWord ++ tailWord_6318775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318775).length < 2 ^ (prefixWord ++ tailWord_6318775).sum := by decide
  have hdescent : baseEnd_6318775 < baseStart_6318775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318792 : List Nat := [2, 1, 3, 1, 2, 4, 1, 4, 1, 2, 2]
def baseStart_6318792 : Nat := 118140960795 + 6318792 * 2 ^ 59
def prefixEnd_6318792 : Nat := 4983230072969 + 3 ^ 40 * 6318792 * 2
def baseEnd_6318792 : Nat := 3244577451784746930940411

theorem tailTrace_6318792 : CollatzResearch.WordTrace tailWord_6318792 prefixEnd_6318792 3244577451784746930940411 := by
  unfold tailWord_6318792
  simp only [CollatzResearch.WordTrace]
  refine ⟨115232638862051611301047315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153643518482735481734729753 115232638862051611301047315)
  ·
    refine ⟨172848958293077416951570973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115232638862051611301047315 172848958293077416951570973)
    ·
      refine ⟨64818359359904031356839115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172848958293077416951570973 64818359359904031356839115)
      ·
        refine ⟨97227539039856047035258673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64818359359904031356839115 97227539039856047035258673)
        ·
          refine ⟨72920654279892035276444005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97227539039856047035258673 72920654279892035276444005)
          ·
            refine ⟨13672622677479756614333251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72920654279892035276444005 13672622677479756614333251)
            ·
              refine ⟨20508934016219634921499877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13672622677479756614333251 20508934016219634921499877)
              ·
                refine ⟨3845425128041181547781227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20508934016219634921499877 3845425128041181547781227)
                ·
                  refine ⟨5768137692061772321671841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845425128041181547781227 5768137692061772321671841)
                  ·
                    refine ⟨4326103269046329241253881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5768137692061772321671841 4326103269046329241253881)
                    ·
                      refine ⟨3244577451784746930940411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326103269046329241253881 3244577451784746930940411)
                      ·
                        rfl

theorem cell23_6318792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_6318792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318792 prefixEnd_6318792 := by exact prefixLift 6318792
  have htrace : WordTrace (prefixWord ++ tailWord_6318792) baseStart_6318792 baseEnd_6318792 := by
    simpa [prefixWord, tailWord_6318792, baseEnd_6318792] using wordTrace_append hprefix tailTrace_6318792
  have hstable : (prefixWord ++ tailWord_6318792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318792).length < 2 ^ (prefixWord ++ tailWord_6318792).sum := by decide
  have hdescent : baseEnd_6318792 < baseStart_6318792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318805 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6318805 : Nat := 118140960795 + 6318805 * 2 ^ 59
def prefixEnd_6318805 : Nat := 4983230072969 + 3 ^ 40 * 6318805 * 2
def baseEnd_6318805 : Nat := 3244584127033255380077851

theorem tailTrace_6318805 : CollatzResearch.WordTrace tailWord_6318805 prefixEnd_6318805 3244584127033255380077851 := by
  unfold tailWord_6318805
  simp only [CollatzResearch.WordTrace]
  refine ⟨230465751873056125822317869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153643834582037417214878579 230465751873056125822317869)
  ·
    refine ⟨86424656952396047183369201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230465751873056125822317869 86424656952396047183369201)
    ·
      refine ⟨64818492714297035387526901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86424656952396047183369201 64818492714297035387526901)
      ·
        refine ⟨6076733691965347067580647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64818492714297035387526901 6076733691965347067580647)
        ·
          refine ⟨9115100537948020601370971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076733691965347067580647 9115100537948020601370971)
          ·
            refine ⟨13672650806922030902056457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9115100537948020601370971 13672650806922030902056457)
            ·
              refine ⟨10254488105191523176542343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13672650806922030902056457 10254488105191523176542343)
              ·
                refine ⟨15381732157787284764813515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10254488105191523176542343 15381732157787284764813515)
                ·
                  refine ⟨23072598236680927147220273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15381732157787284764813515 23072598236680927147220273)
                  ·
                    refine ⟨17304448677510695360415205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23072598236680927147220273 17304448677510695360415205)
                    ·
                      refine ⟨3244584127033255380077851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17304448677510695360415205 3244584127033255380077851)
                      ·
                        rfl

theorem cell23_6318805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6318805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318805 prefixEnd_6318805 := by exact prefixLift 6318805
  have htrace : WordTrace (prefixWord ++ tailWord_6318805) baseStart_6318805 baseEnd_6318805 := by
    simpa [prefixWord, tailWord_6318805, baseEnd_6318805] using wordTrace_append hprefix tailTrace_6318805
  have hstable : (prefixWord ++ tailWord_6318805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318805).length < 2 ^ (prefixWord ++ tailWord_6318805).sum := by decide
  have hdescent : baseEnd_6318805 < baseStart_6318805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318808 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 1, 3, 3]
def baseStart_6318808 : Nat := 118140960795 + 6318808 * 2 ^ 59
def prefixEnd_6318808 : Nat := 4983230072969 + 3 ^ 40 * 6318808 * 2
def baseEnd_6318808 : Nat := 3244585667475218868340337

theorem tailTrace_6318808 : CollatzResearch.WordTrace tailWord_6318808 prefixEnd_6318808 3244585667475218868340337 := by
  unfold tailWord_6318808
  simp only [CollatzResearch.WordTrace]
  refine ⟨115232930646022628667338539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153643907528030171556451385 115232930646022628667338539)
  ·
    refine ⟨172849395969033943001007809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115232930646022628667338539 172849395969033943001007809)
    ·
      refine ⟨129637046976775457250755857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172849395969033943001007809 129637046976775457250755857)
      ·
        refine ⟨97227785232581592938066893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129637046976775457250755857 97227785232581592938066893)
        ·
          refine ⟨36460419462218097351775085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97227785232581592938066893 36460419462218097351775085)
          ·
            refine ⟨13672657298331786506915657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36460419462218097351775085 13672657298331786506915657)
            ·
              refine ⟨10254492973748839880186743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13672657298331786506915657 10254492973748839880186743)
              ·
                refine ⟨15381739460623259820280115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10254492973748839880186743 15381739460623259820280115)
                ·
                  refine ⟨23072609190934889730420173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15381739460623259820280115 23072609190934889730420173)
                  ·
                    refine ⟨8652228446600583648907565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23072609190934889730420173 8652228446600583648907565)
                    ·
                      refine ⟨3244585667475218868340337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8652228446600583648907565 3244585667475218868340337)
                      ·
                        rfl

theorem cell23_6318808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_6318808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318808 prefixEnd_6318808 := by exact prefixLift 6318808
  have htrace : WordTrace (prefixWord ++ tailWord_6318808) baseStart_6318808 baseEnd_6318808 := by
    simpa [prefixWord, tailWord_6318808, baseEnd_6318808] using wordTrace_append hprefix tailTrace_6318808
  have hstable : (prefixWord ++ tailWord_6318808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318808).length < 2 ^ (prefixWord ++ tailWord_6318808).sum := by decide
  have hdescent : baseEnd_6318808 < baseStart_6318808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318836 : List Nat := [2, 6, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_6318836 : Nat := 118140960795 + 6318836 * 2 ^ 59
def prefixEnd_6318836 : Nat := 4983230072969 + 3 ^ 40 * 6318836 * 2
def baseEnd_6318836 : Nat := 1081533348311181586263403

theorem tailTrace_6318836 : CollatzResearch.WordTrace tailWord_6318836 prefixEnd_6318836 1081533348311181586263403 := by
  unfold tailWord_6318836
  simp only [CollatzResearch.WordTrace]
  refine ⟨115233441267971909058348181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153644588357295878744464241 115233441267971909058348181)
  ·
    refine ⟨5401567559436183237110071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115233441267971909058348181 5401567559436183237110071)
    ·
      refine ⟨8102351339154274855665107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5401567559436183237110071 8102351339154274855665107)
      ·
        refine ⟨12153527008731412283497661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8102351339154274855665107 12153527008731412283497661)
        ·
          refine ⟨4557572628274279606311623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12153527008731412283497661 4557572628274279606311623)
          ·
            refine ⟨6836358942411419409467435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4557572628274279606311623 6836358942411419409467435)
            ·
              refine ⟨10254538413617129114201153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6836358942411419409467435 10254538413617129114201153)
              ·
                refine ⟨7690903810212846835650865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10254538413617129114201153 7690903810212846835650865)
                ·
                  refine ⟨5768177857659635126738149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7690903810212846835650865 5768177857659635126738149)
                  ·
                    refine ⟨1081533348311181586263403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5768177857659635126738149 1081533348311181586263403)
                    ·
                      rfl

theorem cell23_6318836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_6318836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318836 prefixEnd_6318836 := by exact prefixLift 6318836
  have htrace : WordTrace (prefixWord ++ tailWord_6318836) baseStart_6318836 baseEnd_6318836 := by
    simpa [prefixWord, tailWord_6318836, baseEnd_6318836] using wordTrace_append hprefix tailTrace_6318836
  have hstable : (prefixWord ++ tailWord_6318836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318836).length < 2 ^ (prefixWord ++ tailWord_6318836).sum := by decide
  have hdescent : baseEnd_6318836 < baseStart_6318836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318865 : List Nat := [1, 2, 2, 1, 1, 3, 2, 5, 2, 2, 2]
def baseStart_6318865 : Nat := 118140960795 + 6318865 * 2 ^ 59
def prefixEnd_6318865 : Nat := 4983230072969 + 3 ^ 40 * 6318865 * 2
def baseEnd_6318865 : Nat := 3244614935872525145327575

theorem tailTrace_6318865 : CollatzResearch.WordTrace tailWord_6318865 prefixEnd_6318865 3244614935872525145327575 := by
  unfold tailWord_6318865
  simp only [CollatzResearch.WordTrace]
  refine ⟨230467940252838756069502049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153645293501892504046334699 230467940252838756069502049)
  ·
    refine ⟨172850955189629067052126537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230467940252838756069502049 172850955189629067052126537)
    ·
      refine ⟨129638216392221800289094903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172850955189629067052126537 129638216392221800289094903)
      ·
        refine ⟨194457324588332700433642355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129638216392221800289094903 194457324588332700433642355)
        ·
          refine ⟨291685986882499050650463533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194457324588332700433642355 291685986882499050650463533)
          ·
            refine ⟨109382245080937143993923825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291685986882499050650463533 109382245080937143993923825)
            ·
              refine ⟨82036683810702857995442869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109382245080937143993923825 82036683810702857995442869)
              ·
                refine ⟨7690939107253392937072769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82036683810702857995442869 7690939107253392937072769)
                ·
                  refine ⟨5768204330440044702804577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7690939107253392937072769 5768204330440044702804577)
                  ·
                    refine ⟨4326153247830033527103433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5768204330440044702804577 4326153247830033527103433)
                    ·
                      refine ⟨3244614935872525145327575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326153247830033527103433 3244614935872525145327575)
                      ·
                        rfl

theorem cell23_6318865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 2, 2].length) (baseStart_6318865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318865 prefixEnd_6318865 := by exact prefixLift 6318865
  have htrace : WordTrace (prefixWord ++ tailWord_6318865) baseStart_6318865 baseEnd_6318865 := by
    simpa [prefixWord, tailWord_6318865, baseEnd_6318865] using wordTrace_append hprefix tailTrace_6318865
  have hstable : (prefixWord ++ tailWord_6318865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318865).length < 2 ^ (prefixWord ++ tailWord_6318865).sum := by decide
  have hdescent : baseEnd_6318865 < baseStart_6318865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318908 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 2, 5, 2]
def baseStart_6318908 : Nat := 118140960795 + 6318908 * 2 ^ 59
def prefixEnd_6318908 : Nat := 4983230072969 + 3 ^ 40 * 6318908 * 2
def baseEnd_6318908 : Nat := 3244637015540668477089877

theorem tailTrace_6318908 : CollatzResearch.WordTrace tailWord_6318908 prefixEnd_6318908 3244637015540668477089877 := by
  unfold tailWord_6318908
  simp only [CollatzResearch.WordTrace]
  refine ⟨115234754295841487206658689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153646339061121982942211585 115234754295841487206658689)
  ·
    refine ⟨86426065721881115404994017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115234754295841487206658689 86426065721881115404994017)
    ·
      refine ⟨64819549291410836553745513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86426065721881115404994017 64819549291410836553745513)
      ·
        refine ⟨48614661968558127415309135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64819549291410836553745513 48614661968558127415309135)
        ·
          refine ⟨72921992952837191122963703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48614661968558127415309135 72921992952837191122963703)
          ·
            refine ⟨109382989429255786684445555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72921992952837191122963703 109382989429255786684445555)
            ·
              refine ⟨164074484143883680026668333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109382989429255786684445555 164074484143883680026668333)
              ·
                refine ⟨61527931553956380010000625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164074484143883680026668333 61527931553956380010000625)
                ·
                  refine ⟨46145948665467285007500469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61527931553956380010000625 46145948665467285007500469)
                  ·
                    refine ⟨4326182687387557969453169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46145948665467285007500469 4326182687387557969453169)
                    ·
                      refine ⟨3244637015540668477089877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326182687387557969453169 3244637015540668477089877)
                      ·
                        rfl

theorem cell23_6318908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_6318908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318908 prefixEnd_6318908 := by exact prefixLift 6318908
  have htrace : WordTrace (prefixWord ++ tailWord_6318908) baseStart_6318908 baseEnd_6318908 := by
    simpa [prefixWord, tailWord_6318908, baseEnd_6318908] using wordTrace_append hprefix tailTrace_6318908
  have hstable : (prefixWord ++ tailWord_6318908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318908).length < 2 ^ (prefixWord ++ tailWord_6318908).sum := by decide
  have hdescent : baseEnd_6318908 < baseStart_6318908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318911 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 7]
def baseStart_6318911 : Nat := 118140960795 + 6318911 * 2 ^ 59
def prefixEnd_6318911 : Nat := 4983230072969 + 3 ^ 40 * 6318911 * 2
def baseEnd_6318911 : Nat := 3244638555982631965352363

theorem tailTrace_6318911 : CollatzResearch.WordTrace tailWord_6318911 prefixEnd_6318911 3244638555982631965352363 := by
  unfold tailWord_6318911
  simp only [CollatzResearch.WordTrace]
  refine ⟨230469618010672105925676587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153646412007114737283784391 230469618010672105925676587)
  ·
    refine ⟨345704427016008158888514881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230469618010672105925676587 345704427016008158888514881)
    ·
      refine ⟨259278320262006119166386161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345704427016008158888514881 259278320262006119166386161)
      ·
        refine ⟨194458740196504589374789621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259278320262006119166386161 194458740196504589374789621)
        ·
          refine ⟨18230506893422305253886527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194458740196504589374789621 18230506893422305253886527)
          ·
            refine ⟨27345760340133457880829791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18230506893422305253886527 27345760340133457880829791)
            ·
              refine ⟨41018640510200186821244687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27345760340133457880829791 41018640510200186821244687)
              ·
                refine ⟨61527960765300280231867031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41018640510200186821244687 61527960765300280231867031)
                ·
                  refine ⟨92291941147950420347800547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61527960765300280231867031 92291941147950420347800547)
                  ·
                    refine ⟨138437911721925630521700821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92291941147950420347800547 138437911721925630521700821)
                    ·
                      refine ⟨3244638555982631965352363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138437911721925630521700821 3244638555982631965352363)
                      ·
                        rfl

theorem cell23_6318911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_6318911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318911 prefixEnd_6318911 := by exact prefixLift 6318911
  have htrace : WordTrace (prefixWord ++ tailWord_6318911) baseStart_6318911 baseEnd_6318911 := by
    simpa [prefixWord, tailWord_6318911, baseEnd_6318911] using wordTrace_append hprefix tailTrace_6318911
  have hstable : (prefixWord ++ tailWord_6318911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318911).length < 2 ^ (prefixWord ++ tailWord_6318911).sum := by decide
  have hdescent : baseEnd_6318911 < baseStart_6318911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318916 : List Nat := [2, 3, 4, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_6318916 : Nat := 118140960795 + 6318916 * 2 ^ 59
def prefixEnd_6318916 : Nat := 4983230072969 + 3 ^ 40 * 6318916 * 2
def baseEnd_6318916 : Nat := 3244641123385904445789841

theorem tailTrace_6318916 : CollatzResearch.WordTrace tailWord_6318916 prefixEnd_6318916 3244641123385904445789841 := by
  unfold tailWord_6318916
  simp only [CollatzResearch.WordTrace]
  refine ⟨115234900187826995889804301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153646533583769327853072401 115234900187826995889804301)
  ·
    refine ⟨43213087570435123458676613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115234900187826995889804301 43213087570435123458676613)
    ·
      refine ⟨8102453919456585648501865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43213087570435123458676613 8102453919456585648501865)
      ·
        refine ⟨6076840439592439236376399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8102453919456585648501865 6076840439592439236376399)
        ·
          refine ⟨9115260659388658854564599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076840439592439236376399 9115260659388658854564599)
          ·
            refine ⟨13672890989082988281846899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9115260659388658854564599 13672890989082988281846899)
            ·
              refine ⟨20509336483624482422770349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13672890989082988281846899 20509336483624482422770349)
              ·
                refine ⟨7691001181359180908538881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20509336483624482422770349 7691001181359180908538881)
                ·
                  refine ⟨5768250886019385681404161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7691001181359180908538881 5768250886019385681404161)
                  ·
                    refine ⟨4326188164514539261053121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5768250886019385681404161 4326188164514539261053121)
                    ·
                      refine ⟨3244641123385904445789841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326188164514539261053121 3244641123385904445789841)
                      ·
                        rfl

theorem cell23_6318916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_6318916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318916 prefixEnd_6318916 := by exact prefixLift 6318916
  have htrace : WordTrace (prefixWord ++ tailWord_6318916) baseStart_6318916 baseEnd_6318916 := by
    simpa [prefixWord, tailWord_6318916, baseEnd_6318916] using wordTrace_append hprefix tailTrace_6318916
  have hstable : (prefixWord ++ tailWord_6318916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318916).length < 2 ^ (prefixWord ++ tailWord_6318916).sum := by decide
  have hdescent : baseEnd_6318916 < baseStart_6318916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6318938 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4]
def baseStart_6318938 : Nat := 118140960795 + 6318938 * 2 ^ 59
def prefixEnd_6318938 : Nat := 4983230072969 + 3 ^ 40 * 6318938 * 2
def baseEnd_6318938 : Nat := 3244652419960303359714739

theorem tailTrace_6318938 : CollatzResearch.WordTrace tailWord_6318938 prefixEnd_6318938 3244652419960303359714739 := by
  unfold tailWord_6318938
  simp only [CollatzResearch.WordTrace]
  refine ⟨57617650695393572384227367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153647068521049526357939645 57617650695393572384227367)
  ·
    refine ⟨86426476043090358576341051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57617650695393572384227367 86426476043090358576341051)
    ·
      refine ⟨129639714064635537864511577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86426476043090358576341051 129639714064635537864511577)
      ·
        refine ⟨97229785548476653398383683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129639714064635537864511577 97229785548476653398383683)
        ·
          refine ⟨145844678322714980097575525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97229785548476653398383683 145844678322714980097575525)
          ·
            refine ⟨27345877185509058768295411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145844678322714980097575525 27345877185509058768295411)
            ·
              refine ⟨41018815778263588152443117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27345877185509058768295411 41018815778263588152443117)
              ·
                refine ⟨15382055916848845557166169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41018815778263588152443117 15382055916848845557166169)
                ·
                  refine ⟨11536541937636634167874627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15382055916848845557166169 11536541937636634167874627)
                  ·
                    refine ⟨17304812906454951251811941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11536541937636634167874627 17304812906454951251811941)
                    ·
                      refine ⟨3244652419960303359714739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17304812906454951251811941 3244652419960303359714739)
                      ·
                        rfl

theorem cell23_6318938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_6318938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6318938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6318938 prefixEnd_6318938 := by exact prefixLift 6318938
  have htrace : WordTrace (prefixWord ++ tailWord_6318938) baseStart_6318938 baseEnd_6318938 := by
    simpa [prefixWord, tailWord_6318938, baseEnd_6318938] using wordTrace_append hprefix tailTrace_6318938
  have hstable : (prefixWord ++ tailWord_6318938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6318938).length < 2 ^ (prefixWord ++ tailWord_6318938).sum := by decide
  have hdescent : baseEnd_6318938 < baseStart_6318938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6318938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319001 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 2, 4, 5]
def baseStart_6319001 : Nat := 118140960795 + 6319001 * 2 ^ 59
def prefixEnd_6319001 : Nat := 4983230072969 + 3 ^ 40 * 6319001 * 2
def baseEnd_6319001 : Nat := 3244684769241536613226949

theorem tailTrace_6319001 : CollatzResearch.WordTrace tailWord_6319001 prefixEnd_6319001 3244684769241536613226949 := by
  unfold tailWord_6319001
  simp only [CollatzResearch.WordTrace]
  refine ⟨230472900580346051296452857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153648600386897367530968571 230472900580346051296452857)
  ·
    refine ⟨172854675435259538472339643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230472900580346051296452857 172854675435259538472339643)
    ·
      refine ⟨259282013152889307708509465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172854675435259538472339643 259282013152889307708509465)
      ·
        refine ⟨194461509864666980781382099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259282013152889307708509465 194461509864666980781382099)
        ·
          refine ⟨291692264797000471172073149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194461509864666980781382099 291692264797000471172073149)
          ·
            refine ⟨109384599298875176689527431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291692264797000471172073149 109384599298875176689527431)
            ·
              refine ⟨164076898948312765034291147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109384599298875176689527431 164076898948312765034291147)
              ·
                refine ⟨246115348422469147551436721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164076898948312765034291147 246115348422469147551436721)
                ·
                  refine ⟨184586511316851860663577541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246115348422469147551436721 184586511316851860663577541)
                  ·
                    refine ⟨34609970871909723874420789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 184586511316851860663577541 34609970871909723874420789)
                    ·
                      refine ⟨3244684769241536613226949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34609970871909723874420789 3244684769241536613226949)
                      ·
                        rfl

theorem cell23_6319001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_6319001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319001 prefixEnd_6319001 := by exact prefixLift 6319001
  have htrace : WordTrace (prefixWord ++ tailWord_6319001) baseStart_6319001 baseEnd_6319001 := by
    simpa [prefixWord, tailWord_6319001, baseEnd_6319001] using wordTrace_append hprefix tailTrace_6319001
  have hstable : (prefixWord ++ tailWord_6319001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319001).length < 2 ^ (prefixWord ++ tailWord_6319001).sum := by decide
  have hdescent : baseEnd_6319001 < baseStart_6319001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319005 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_6319005 : Nat := 118140960795 + 6319005 * 2 ^ 59
def prefixEnd_6319005 : Nat := 4983230072969 + 3 ^ 40 * 6319005 * 2
def baseEnd_6319005 : Nat := 3244686823164154597576931

theorem tailTrace_6319005 : CollatzResearch.WordTrace tailWord_6319005 prefixEnd_6319005 3244686823164154597576931 := by
  unfold tailWord_6319005
  simp only [CollatzResearch.WordTrace]
  refine ⟨230473046472331559979598469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153648697648221039986398979 230473046472331559979598469)
  ·
    refine ⟨43213696213562167496174713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230473046472331559979598469 43213696213562167496174713)
    ·
      refine ⟨32410272160171625622131035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43213696213562167496174713 32410272160171625622131035)
      ·
        refine ⟨48615408240257438433196553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32410272160171625622131035 48615408240257438433196553)
        ·
          refine ⟨36461556180193078824897415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48615408240257438433196553 36461556180193078824897415)
          ·
            refine ⟨54692334270289618237346123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36461556180193078824897415 54692334270289618237346123)
            ·
              refine ⟨82038501405434427356019185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54692334270289618237346123 82038501405434427356019185)
              ·
                refine ⟨61528876054075820517014389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82038501405434427356019185 61528876054075820517014389)
                ·
                  refine ⟨5768332130069608173470099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61528876054075820517014389 5768332130069608173470099)
                  ·
                    refine ⟨8652498195104412260205149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5768332130069608173470099 8652498195104412260205149)
                    ·
                      refine ⟨3244686823164154597576931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8652498195104412260205149 3244686823164154597576931)
                      ·
                        rfl

theorem cell23_6319005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_6319005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319005 prefixEnd_6319005 := by exact prefixLift 6319005
  have htrace : WordTrace (prefixWord ++ tailWord_6319005) baseStart_6319005 baseEnd_6319005 := by
    simpa [prefixWord, tailWord_6319005, baseEnd_6319005] using wordTrace_append hprefix tailTrace_6319005
  have hstable : (prefixWord ++ tailWord_6319005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319005).length < 2 ^ (prefixWord ++ tailWord_6319005).sum := by decide
  have hdescent : baseEnd_6319005 < baseStart_6319005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319065 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 1, 1, 5]
def baseStart_6319065 : Nat := 118140960795 + 6319065 * 2 ^ 59
def prefixEnd_6319065 : Nat := 4983230072969 + 3 ^ 40 * 6319065 * 2
def baseEnd_6319065 : Nat := 3244717632003424362826655

theorem tailTrace_6319065 : CollatzResearch.WordTrace tailWord_6319065 prefixEnd_6319065 3244717632003424362826655 := by
  unfold tailWord_6319065
  simp only [CollatzResearch.WordTrace]
  refine ⟨230475234852114190226782649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153650156568076126817855099 230475234852114190226782649)
  ·
    refine ⟨172856426139085642670086987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230475234852114190226782649 172856426139085642670086987)
    ·
      refine ⟨259284639208628464005130481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172856426139085642670086987 259284639208628464005130481)
      ·
        refine ⟨194463479406471348003847861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259284639208628464005130481 194463479406471348003847861)
        ·
          refine ⟨18230951194356688875360737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194463479406471348003847861 18230951194356688875360737)
          ·
            refine ⟨13673213395767516656520553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18230951194356688875360737 13673213395767516656520553)
            ·
              refine ⟨10254910046825637492390415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13673213395767516656520553 10254910046825637492390415)
              ·
                refine ⟨15382365070238456238585623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10254910046825637492390415 15382365070238456238585623)
                ·
                  refine ⟨23073547605357684357878435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15382365070238456238585623 23073547605357684357878435)
                  ·
                    refine ⟨34610321408036526536817653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23073547605357684357878435 34610321408036526536817653)
                    ·
                      refine ⟨3244717632003424362826655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34610321408036526536817653 3244717632003424362826655)
                      ·
                        rfl

theorem cell23_6319065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_6319065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319065 prefixEnd_6319065 := by exact prefixLift 6319065
  have htrace : WordTrace (prefixWord ++ tailWord_6319065) baseStart_6319065 baseEnd_6319065 := by
    simpa [prefixWord, tailWord_6319065, baseEnd_6319065] using wordTrace_append hprefix tailTrace_6319065
  have hstable : (prefixWord ++ tailWord_6319065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319065).length < 2 ^ (prefixWord ++ tailWord_6319065).sum := by decide
  have hdescent : baseEnd_6319065 < baseStart_6319065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319079 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_6319079 : Nat := 118140960795 + 6319079 * 2 ^ 59
def prefixEnd_6319079 : Nat := 4983230072969 + 3 ^ 40 * 6319079 * 2
def baseEnd_6319079 : Nat := 3244724820732587308051591

theorem tailTrace_6319079 : CollatzResearch.WordTrace tailWord_6319079 prefixEnd_6319079 3244724820732587308051591 := by
  unfold tailWord_6319079
  simp only [CollatzResearch.WordTrace]
  refine ⟨230475745474063470617792291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153650496982708980411861527 230475745474063470617792291)
  ·
    refine ⟨345713618211095205926688437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230475745474063470617792291 345713618211095205926688437)
    ·
      refine ⟨32410651707290175555627041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 345713618211095205926688437 32410651707290175555627041)
      ·
        refine ⟨24307988780467631666720281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32410651707290175555627041 24307988780467631666720281)
        ·
          refine ⟨18230991585350723750040211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24307988780467631666720281 18230991585350723750040211)
          ·
            refine ⟨27346487378026085625060317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18230991585350723750040211 27346487378026085625060317)
            ·
              refine ⟨10254932766759782109397619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27346487378026085625060317 10254932766759782109397619)
              ·
                refine ⟨15382399150139673164096429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10254932766759782109397619 15382399150139673164096429)
                ·
                  refine ⟨5768399681302377436536161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15382399150139673164096429 5768399681302377436536161)
                  ·
                    refine ⟨4326299760976783077402121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5768399681302377436536161 4326299760976783077402121)
                    ·
                      refine ⟨3244724820732587308051591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326299760976783077402121 3244724820732587308051591)
                      ·
                        rfl

theorem cell23_6319079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_6319079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319079 prefixEnd_6319079 := by exact prefixLift 6319079
  have htrace : WordTrace (prefixWord ++ tailWord_6319079) baseStart_6319079 baseEnd_6319079 := by
    simpa [prefixWord, tailWord_6319079, baseEnd_6319079] using wordTrace_append hprefix tailTrace_6319079
  have hstable : (prefixWord ++ tailWord_6319079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319079).length < 2 ^ (prefixWord ++ tailWord_6319079).sum := by decide
  have hdescent : baseEnd_6319079 < baseStart_6319079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319089 : List Nat := [1, 2, 2, 2, 4, 3, 2, 1, 2, 4]
def baseStart_6319089 : Nat := 118140960795 + 6319089 * 2 ^ 59
def prefixEnd_6319089 : Nat := 4983230072969 + 3 ^ 40 * 6319089 * 2
def baseEnd_6319089 : Nat := 1081576651846377422975515

theorem tailTrace_6319089 : CollatzResearch.WordTrace tailWord_6319089 prefixEnd_6319089 1081576651846377422975515 := by
  unfold tailWord_6319089
  simp only [CollatzResearch.WordTrace]
  refine ⟨230476110204027242325656321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153650740136018161550437547 230476110204027242325656321)
  ·
    refine ⟨172857082653020431744242241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230476110204027242325656321 172857082653020431744242241)
    ·
      refine ⟨129642811989765323808181681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172857082653020431744242241 129642811989765323808181681)
      ·
        refine ⟨97232108992323992856136261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129642811989765323808181681 97232108992323992856136261)
        ·
          refine ⟨18231020436060748660525549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97232108992323992856136261 18231020436060748660525549)
          ·
            refine ⟨6836632663522780747697081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18231020436060748660525549 6836632663522780747697081)
            ·
              refine ⟨5127474497642085560772811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6836632663522780747697081 5127474497642085560772811)
              ·
                refine ⟨7691211746463128341159217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5127474497642085560772811 7691211746463128341159217)
                ·
                  refine ⟨5768408809847346255869413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7691211746463128341159217 5768408809847346255869413)
                  ·
                    refine ⟨1081576651846377422975515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5768408809847346255869413 1081576651846377422975515)
                    ·
                      rfl

theorem cell23_6319089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_6319089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319089 prefixEnd_6319089 := by exact prefixLift 6319089
  have htrace : WordTrace (prefixWord ++ tailWord_6319089) baseStart_6319089 baseEnd_6319089 := by
    simpa [prefixWord, tailWord_6319089, baseEnd_6319089] using wordTrace_append hprefix tailTrace_6319089
  have hstable : (prefixWord ++ tailWord_6319089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319089).length < 2 ^ (prefixWord ++ tailWord_6319089).sum := by decide
  have hdescent : baseEnd_6319089 < baseStart_6319089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319152 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 1, 4, 2]
def baseStart_6319152 : Nat := 118140960795 + 6319152 * 2 ^ 59
def prefixEnd_6319152 : Nat := 4983230072969 + 3 ^ 40 * 6319152 * 2
def baseEnd_6319152 : Nat := 3244762304820365522438755

theorem tailTrace_6319152 : CollatzResearch.WordTrace tailWord_6319152 prefixEnd_6319152 3244762304820365522438755 := by
  unfold tailWord_6319152
  simp only [CollatzResearch.WordTrace]
  refine ⟨115239204001399502042599855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153652272001866002723466473 115239204001399502042599855)
  ·
    refine ⟨172858806002099253063899783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115239204001399502042599855 172858806002099253063899783)
    ·
      refine ⟨259288209003148879595849675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172858806002099253063899783 259288209003148879595849675)
      ·
        refine ⟨388932313504723319393774513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259288209003148879595849675 388932313504723319393774513)
        ·
          refine ⟨291699235128542489545330885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388932313504723319393774513 291699235128542489545330885)
          ·
            refine ⟨54693606586601716789749541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291699235128542489545330885 54693606586601716789749541)
            ·
              refine ⟨10255051234987821898078039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54693606586601716789749541 10255051234987821898078039)
              ·
                refine ⟨15382576852481732847117059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10255051234987821898078039 15382576852481732847117059)
                ·
                  refine ⟨23073865278722599270675589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15382576852481732847117059 23073865278722599270675589)
                  ·
                    refine ⟨4326349739760487363251673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23073865278722599270675589 4326349739760487363251673)
                    ·
                      refine ⟨3244762304820365522438755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326349739760487363251673 3244762304820365522438755)
                      ·
                        rfl

theorem cell23_6319152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 1, 4, 2].length) (baseStart_6319152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319152 prefixEnd_6319152 := by exact prefixLift 6319152
  have htrace : WordTrace (prefixWord ++ tailWord_6319152) baseStart_6319152 baseEnd_6319152 := by
    simpa [prefixWord, tailWord_6319152, baseEnd_6319152] using wordTrace_append hprefix tailTrace_6319152
  have hstable : (prefixWord ++ tailWord_6319152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319152).length < 2 ^ (prefixWord ++ tailWord_6319152).sum := by decide
  have hdescent : baseEnd_6319152 < baseStart_6319152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319185 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 2, 3, 3]
def baseStart_6319185 : Nat := 118140960795 + 6319185 * 2 ^ 59
def prefixEnd_6319185 : Nat := 4983230072969 + 3 ^ 40 * 6319185 * 2
def baseEnd_6319185 : Nat := 3244779249681963893326103

theorem tailTrace_6319185 : CollatzResearch.WordTrace tailWord_6319185 prefixEnd_6319185 3244779249681963893326103 := by
  unfold tailWord_6319185
  simp only [CollatzResearch.WordTrace]
  refine ⟨230479611611679450721151009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153653074407786300480767339 230479611611679450721151009)
  ·
    refine ⟨172859708708759588040863257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230479611611679450721151009 172859708708759588040863257)
    ·
      refine ⟨129644781531569691030647443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172859708708759588040863257 129644781531569691030647443)
      ·
        refine ⟨194467172297354536545971165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129644781531569691030647443 194467172297354536545971165)
        ·
          refine ⟨72925189611507951204739187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194467172297354536545971165 72925189611507951204739187)
          ·
            refine ⟨109387784417261926807108781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72925189611507951204739187 109387784417261926807108781)
            ·
              refine ⟨41020419156473222552665793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109387784417261926807108781 41020419156473222552665793)
              ·
                refine ⟨30765314367354916914499345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41020419156473222552665793 30765314367354916914499345)
                ·
                  refine ⟨23073985775516187685874509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30765314367354916914499345 23073985775516187685874509)
                  ·
                    refine ⟨8652744665818570382202941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23073985775516187685874509 8652744665818570382202941)
                    ·
                      refine ⟨3244779249681963893326103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8652744665818570382202941 3244779249681963893326103)
                      ·
                        rfl

theorem cell23_6319185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_6319185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319185 prefixEnd_6319185 := by exact prefixLift 6319185
  have htrace : WordTrace (prefixWord ++ tailWord_6319185) baseStart_6319185 baseEnd_6319185 := by
    simpa [prefixWord, tailWord_6319185, baseEnd_6319185] using wordTrace_append hprefix tailTrace_6319185
  have hstable : (prefixWord ++ tailWord_6319185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319185).length < 2 ^ (prefixWord ++ tailWord_6319185).sum := by decide
  have hdescent : baseEnd_6319185 < baseStart_6319185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319186 : List Nat := [3, 2, 2, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_6319186 : Nat := 118140960795 + 6319186 * 2 ^ 59
def prefixEnd_6319186 : Nat := 4983230072969 + 3 ^ 40 * 6319186 * 2
def baseEnd_6319186 : Nat := 3244779763162618389413599

theorem tailTrace_6319186 : CollatzResearch.WordTrace tailWord_6319186 prefixEnd_6319186 3244779763162618389413599 := by
  unfold tailWord_6319186
  simp only [CollatzResearch.WordTrace]
  refine ⟨57619912021168956972984353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153653098723117218594624941 57619912021168956972984353)
  ·
    refine ⟨43214934015876717729738265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57619912021168956972984353 43214934015876717729738265)
    ·
      refine ⟨32411200511907538297303699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43214934015876717729738265 32411200511907538297303699)
      ·
        refine ⟨48616800767861307445955549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32411200511907538297303699 48616800767861307445955549)
        ·
          refine ⟨18231300287947990292233331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48616800767861307445955549 18231300287947990292233331)
          ·
            refine ⟨27346950431921985438349997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18231300287947990292233331 27346950431921985438349997)
            ·
              refine ⟨10255106411970744539381249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27346950431921985438349997 10255106411970744539381249)
              ·
                refine ⟨7691329808978058404535937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10255106411970744539381249 7691329808978058404535937)
                ·
                  refine ⟨5768497356733543803401953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7691329808978058404535937 5768497356733543803401953)
                  ·
                    refine ⟨4326373017550157852551465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5768497356733543803401953 4326373017550157852551465)
                    ·
                      refine ⟨3244779763162618389413599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326373017550157852551465 3244779763162618389413599)
                      ·
                        rfl

theorem cell23_6319186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_6319186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319186 prefixEnd_6319186 := by exact prefixLift 6319186
  have htrace : WordTrace (prefixWord ++ tailWord_6319186) baseStart_6319186 baseEnd_6319186 := by
    simpa [prefixWord, tailWord_6319186, baseEnd_6319186] using wordTrace_append hprefix tailTrace_6319186
  have hstable : (prefixWord ++ tailWord_6319186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319186).length < 2 ^ (prefixWord ++ tailWord_6319186).sum := by decide
  have hdescent : baseEnd_6319186 < baseStart_6319186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319222 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_6319222 : Nat := 118140960795 + 6319222 * 2 ^ 59
def prefixEnd_6319222 : Nat := 4983230072969 + 3 ^ 40 * 6319222 * 2
def baseEnd_6319222 : Nat := 1081599416155393416187811

theorem tailTrace_6319222 : CollatzResearch.WordTrace tailWord_6319222 prefixEnd_6319222 1081599416155393416187811 := by
  unfold tailWord_6319222
  simp only [CollatzResearch.WordTrace]
  refine ⟨14405060069534087877515495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153653974075030270693498613 14405060069534087877515495)
  ·
    refine ⟨21607590104301131816273243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14405060069534087877515495 21607590104301131816273243)
    ·
      refine ⟨32411385156451697724409865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21607590104301131816273243 32411385156451697724409865)
      ·
        refine ⟨24308538867338773293307399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32411385156451697724409865 24308538867338773293307399)
        ·
          refine ⟨36462808301008159939961099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24308538867338773293307399 36462808301008159939961099)
          ·
            refine ⟨54694212451512239909941649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36462808301008159939961099 54694212451512239909941649)
            ·
              refine ⟨41020659338634179932456237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54694212451512239909941649 41020659338634179932456237)
              ·
                refine ⟨15382747251987817474671089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41020659338634179932456237 15382747251987817474671089)
                ·
                  refine ⟨11537060438990863106003317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15382747251987817474671089 11537060438990863106003317)
                  ·
                    refine ⟨1081599416155393416187811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11537060438990863106003317 1081599416155393416187811)
                    ·
                      rfl

theorem cell23_6319222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_6319222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319222 prefixEnd_6319222 := by exact prefixLift 6319222
  have htrace : WordTrace (prefixWord ++ tailWord_6319222) baseStart_6319222 baseEnd_6319222 := by
    simpa [prefixWord, tailWord_6319222, baseEnd_6319222] using wordTrace_append hprefix tailTrace_6319222
  have hstable : (prefixWord ++ tailWord_6319222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319222).length < 2 ^ (prefixWord ++ tailWord_6319222).sum := by decide
  have hdescent : baseEnd_6319222 < baseStart_6319222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319242 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_6319242 : Nat := 118140960795 + 6319242 * 2 ^ 59
def prefixEnd_6319242 : Nat := 4983230072969 + 3 ^ 40 * 6319242 * 2
def baseEnd_6319242 : Nat := 3244808518079270170313341

theorem tailTrace_6319242 : CollatzResearch.WordTrace tailWord_6319242 prefixEnd_6319242 3244808518079270170313341 := by
  unfold tailWord_6319242
  simp only [CollatzResearch.WordTrace]
  refine ⟨57620422643118237363993995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153654460381648632970650653 57620422643118237363993995)
  ·
    refine ⟨86430633964677356045990993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57620422643118237363993995 86430633964677356045990993)
    ·
      refine ⟨64822975473508017034493245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86430633964677356045990993 64822975473508017034493245)
      ·
        refine ⟨24308615802565506387934967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64822975473508017034493245 24308615802565506387934967)
        ·
          refine ⟨36462923703848259581902451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24308615802565506387934967 36462923703848259581902451)
          ·
            refine ⟨54694385555772389372853677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36462923703848259581902451 54694385555772389372853677)
            ·
              refine ⟨20510394583414646014820129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54694385555772389372853677 20510394583414646014820129)
              ·
                refine ⟨15382795937560984511115097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20510394583414646014820129 15382795937560984511115097)
                ·
                  refine ⟨11537096953170738383336323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15382795937560984511115097 11537096953170738383336323)
                  ·
                    refine ⟨17305645429756107575004485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11537096953170738383336323 17305645429756107575004485)
                    ·
                      refine ⟨3244808518079270170313341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17305645429756107575004485 3244808518079270170313341)
                      ·
                        rfl

theorem cell23_6319242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_6319242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319242 prefixEnd_6319242 := by exact prefixLift 6319242
  have htrace : WordTrace (prefixWord ++ tailWord_6319242) baseStart_6319242 baseEnd_6319242 := by
    simpa [prefixWord, tailWord_6319242, baseEnd_6319242] using wordTrace_append hprefix tailTrace_6319242
  have hstable : (prefixWord ++ tailWord_6319242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319242).length < 2 ^ (prefixWord ++ tailWord_6319242).sum := by decide
  have hdescent : baseEnd_6319242 < baseStart_6319242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319332 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_6319332 : Nat := 118140960795 + 6319332 * 2 ^ 59
def prefixEnd_6319332 : Nat := 4983230072969 + 3 ^ 40 * 6319332 * 2
def baseEnd_6319332 : Nat := 3244854731338174818187927

theorem tailTrace_6319332 : CollatzResearch.WordTrace tailWord_6319332 prefixEnd_6319332 3244854731338174818187927 := by
  unfold tailWord_6319332
  simp only [CollatzResearch.WordTrace]
  refine ⟨115242486571073447413376125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153656648761431263217834833 115242486571073447413376125)
  ·
    refine ⟨43215932464152542780016047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115242486571073447413376125 43215932464152542780016047)
    ·
      refine ⟨64823898696228814170024071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43215932464152542780016047 64823898696228814170024071)
      ·
        refine ⟨97235848044343221255036107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64823898696228814170024071 97235848044343221255036107)
        ·
          refine ⟨145853772066514831882554161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97235848044343221255036107 145853772066514831882554161)
          ·
            refine ⟨109390329049886123911915621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145853772066514831882554161 109390329049886123911915621)
            ·
              refine ⟨20510686696853648233484179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109390329049886123911915621 20510686696853648233484179)
              ·
                refine ⟨30766030045280472350226269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20510686696853648233484179 30766030045280472350226269)
                ·
                  refine ⟨11537261266980177131334851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30766030045280472350226269 11537261266980177131334851)
                  ·
                    refine ⟨17305891900470265697002277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11537261266980177131334851 17305891900470265697002277)
                    ·
                      refine ⟨3244854731338174818187927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17305891900470265697002277 3244854731338174818187927)
                      ·
                        rfl

theorem cell23_6319332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_6319332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319332 prefixEnd_6319332 := by exact prefixLift 6319332
  have htrace : WordTrace (prefixWord ++ tailWord_6319332) baseStart_6319332 baseEnd_6319332 := by
    simpa [prefixWord, tailWord_6319332, baseEnd_6319332] using wordTrace_append hprefix tailTrace_6319332
  have hstable : (prefixWord ++ tailWord_6319332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319332).length < 2 ^ (prefixWord ++ tailWord_6319332).sum := by decide
  have hdescent : baseEnd_6319332 < baseStart_6319332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319342 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_6319342 : Nat := 118140960795 + 6319342 * 2 ^ 59
def prefixEnd_6319342 : Nat := 4983230072969 + 3 ^ 40 * 6319342 * 2
def baseEnd_6319342 : Nat := 1081619955381573259687627

theorem tailTrace_6319342 : CollatzResearch.WordTrace tailWord_6319342 prefixEnd_6319342 1081619955381573259687627 := by
  unfold tailWord_6319342
  simp only [CollatzResearch.WordTrace]
  refine ⟨28810667234013833316827035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153656891914740444356410853 28810667234013833316827035)
  ·
    refine ⟨43216000851020749975240553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28810667234013833316827035 43216000851020749975240553)
    ·
      refine ⟨32412000638265562481430415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43216000851020749975240553 32412000638265562481430415)
      ·
        refine ⟨48618000957398343722145623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32412000638265562481430415 48618000957398343722145623)
        ·
          refine ⟨72927001436097515583218435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48618000957398343722145623 72927001436097515583218435)
          ·
            refine ⟨109390502154146273374827653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72927001436097515583218435 109390502154146273374827653)
            ·
              refine ⟨20510719153902426257780185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109390502154146273374827653 20510719153902426257780185)
              ·
                refine ⟨15383039365426819693335139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20510719153902426257780185 15383039365426819693335139)
                ·
                  refine ⟨23074559048140229540002709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15383039365426819693335139 23074559048140229540002709)
                  ·
                    refine ⟨1081619955381573259687627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23074559048140229540002709 1081619955381573259687627)
                    ·
                      rfl

theorem cell23_6319342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_6319342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319342 prefixEnd_6319342 := by exact prefixLift 6319342
  have htrace : WordTrace (prefixWord ++ tailWord_6319342) baseStart_6319342 baseEnd_6319342 := by
    simpa [prefixWord, tailWord_6319342, baseEnd_6319342] using wordTrace_append hprefix tailTrace_6319342
  have hstable : (prefixWord ++ tailWord_6319342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319342).length < 2 ^ (prefixWord ++ tailWord_6319342).sum := by decide
  have hdescent : baseEnd_6319342 < baseStart_6319342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319343 : List Nat := [1, 1, 2, 1, 7, 1, 2, 3, 1, 1, 3]
def baseStart_6319343 : Nat := 118140960795 + 6319343 * 2 ^ 59
def prefixEnd_6319343 : Nat := 4983230072969 + 3 ^ 40 * 6319343 * 2
def baseEnd_6319343 : Nat := 3244860379625374275150377

theorem tailTrace_6319343 : CollatzResearch.WordTrace tailWord_6319343 prefixEnd_6319343 3244860379625374275150377 := by
  unfold tailWord_6319343
  simp only [CollatzResearch.WordTrace]
  refine ⟨230485374345107043705402683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153656916230071362470268455 230485374345107043705402683)
  ·
    refine ⟨345728061517660565558104025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230485374345107043705402683 345728061517660565558104025)
    ·
      refine ⟨259296046138245424168578019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345728061517660565558104025 259296046138245424168578019)
      ·
        refine ⟨388944069207368136252867029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259296046138245424168578019 388944069207368136252867029)
        ·
          refine ⟨9115876622047690693426571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 388944069207368136252867029 9115876622047690693426571)
          ·
            refine ⟨13673814933071536040139857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9115876622047690693426571 13673814933071536040139857)
            ·
              refine ⟨10255361199803652030104893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13673814933071536040139857 10255361199803652030104893)
              ·
                refine ⟨3845760449926369511289335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10255361199803652030104893 3845760449926369511289335)
                ·
                  refine ⟨5768640674889554266934003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845760449926369511289335 5768640674889554266934003)
                  ·
                    refine ⟨8652961012334331400401005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5768640674889554266934003 8652961012334331400401005)
                    ·
                      refine ⟨3244860379625374275150377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8652961012334331400401005 3244860379625374275150377)
                      ·
                        rfl

theorem cell23_6319343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 1, 1, 3].length) (baseStart_6319343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319343 prefixEnd_6319343 := by exact prefixLift 6319343
  have htrace : WordTrace (prefixWord ++ tailWord_6319343) baseStart_6319343 baseEnd_6319343 := by
    simpa [prefixWord, tailWord_6319343, baseEnd_6319343] using wordTrace_append hprefix tailTrace_6319343
  have hstable : (prefixWord ++ tailWord_6319343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319343).length < 2 ^ (prefixWord ++ tailWord_6319343).sum := by decide
  have hdescent : baseEnd_6319343 < baseStart_6319343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319345 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_6319345 : Nat := 118140960795 + 6319345 * 2 ^ 59
def prefixEnd_6319345 : Nat := 4983230072969 + 3 ^ 40 * 6319345 * 2
def baseEnd_6319345 : Nat := 3244861406586683267325367

theorem tailTrace_6319345 : CollatzResearch.WordTrace tailWord_6319345 prefixEnd_6319345 3244861406586683267325367 := by
  unfold tailWord_6319345
  simp only [CollatzResearch.WordTrace]
  refine ⟨230485447291099798046975489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153656964860733198697983659 230485447291099798046975489)
  ·
    refine ⟨172864085468324848535231617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230485447291099798046975489 172864085468324848535231617)
    ·
      refine ⟨129648064101243636401423713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172864085468324848535231617 129648064101243636401423713)
      ·
        refine ⟨97236048075932727301067785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129648064101243636401423713 97236048075932727301067785)
        ·
          refine ⟨72927036056949545475800839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97236048075932727301067785 72927036056949545475800839)
          ·
            refine ⟨109390554085424318213701259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72927036056949545475800839 109390554085424318213701259)
            ·
              refine ⟨164085831128136477320551889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109390554085424318213701259 164085831128136477320551889)
              ·
                refine ⟨123064373346102357990413917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164085831128136477320551889 123064373346102357990413917)
                ·
                  refine ⟨46149140004788384246405219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123064373346102357990413917 46149140004788384246405219)
                  ·
                    refine ⟨69223710007182576369607829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46149140004788384246405219 69223710007182576369607829)
                    ·
                      refine ⟨3244861406586683267325367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69223710007182576369607829 3244861406586683267325367)
                      ·
                        rfl

theorem cell23_6319345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_6319345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319345 prefixEnd_6319345 := by exact prefixLift 6319345
  have htrace : WordTrace (prefixWord ++ tailWord_6319345) baseStart_6319345 baseEnd_6319345 := by
    simpa [prefixWord, tailWord_6319345, baseEnd_6319345] using wordTrace_append hprefix tailTrace_6319345
  have hstable : (prefixWord ++ tailWord_6319345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319345).length < 2 ^ (prefixWord ++ tailWord_6319345).sum := by decide
  have hdescent : baseEnd_6319345 < baseStart_6319345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319359 : List Nat := [1, 1, 2, 2, 1, 5, 3, 2, 2, 4]
def baseStart_6319359 : Nat := 118140960795 + 6319359 * 2 ^ 59
def prefixEnd_6319359 : Nat := 4983230072969 + 3 ^ 40 * 6319359 * 2
def baseEnd_6319359 : Nat := 1081622865105282070850101

theorem tailTrace_6319359 : CollatzResearch.WordTrace tailWord_6319359 prefixEnd_6319359 1081622865105282070850101 := by
  unfold tailWord_6319359
  simp only [CollatzResearch.WordTrace]
  refine ⟨230485957913049078437985131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153657305275366052291990087 230485957913049078437985131)
  ·
    refine ⟨345728936869573617656977697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230485957913049078437985131 345728936869573617656977697)
    ·
      refine ⟨259296702652180213242733273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345728936869573617656977697 259296702652180213242733273)
      ·
        refine ⟨194472526989135159932049955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259296702652180213242733273 194472526989135159932049955)
        ·
          refine ⟨291708790483702739898074933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194472526989135159932049955 291708790483702739898074933)
          ·
            refine ⟨27347699107847131865444525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 291708790483702739898074933 27347699107847131865444525)
            ·
              refine ⟨10255387165442674449541697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27347699107847131865444525 10255387165442674449541697)
              ·
                refine ⟨7691540374082005837156273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10255387165442674449541697 7691540374082005837156273)
                ·
                  refine ⟨5768655280561504377867205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7691540374082005837156273 5768655280561504377867205)
                  ·
                    refine ⟨1081622865105282070850101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5768655280561504377867205 1081622865105282070850101)
                    ·
                      rfl

theorem cell23_6319359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 4].length) (baseStart_6319359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319359 prefixEnd_6319359 := by exact prefixLift 6319359
  have htrace : WordTrace (prefixWord ++ tailWord_6319359) baseStart_6319359 baseEnd_6319359 := by
    simpa [prefixWord, tailWord_6319359, baseEnd_6319359] using wordTrace_append hprefix tailTrace_6319359
  have hstable : (prefixWord ++ tailWord_6319359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319359).length < 2 ^ (prefixWord ++ tailWord_6319359).sum := by decide
  have hdescent : baseEnd_6319359 < baseStart_6319359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319386 : List Nat := [3, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3]
def baseStart_6319386 : Nat := 118140960795 + 6319386 * 2 ^ 59
def prefixEnd_6319386 : Nat := 4983230072969 + 3 ^ 40 * 6319386 * 2
def baseEnd_6319386 : Nat := 3244882459293517606912679

theorem tailTrace_6319386 : CollatzResearch.WordTrace tailWord_6319386 prefixEnd_6319386 3244882459293517606912679 := by
  unfold tailWord_6319386
  simp only [CollatzResearch.WordTrace]
  refine ⟨57621735670987815512304503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153657961789300841366145341 57621735670987815512304503)
  ·
    refine ⟨86432603506481723268456755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57621735670987815512304503 86432603506481723268456755)
    ·
      refine ⟨129648905259722584902685133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86432603506481723268456755 129648905259722584902685133)
      ·
        refine ⟨48618339472395969338506925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129648905259722584902685133 48618339472395969338506925)
        ·
          refine ⟨18231877302148488501940097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48618339472395969338506925 18231877302148488501940097)
          ·
            refine ⟨13673907976611366376455073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18231877302148488501940097 13673907976611366376455073)
            ·
              refine ⟨10255430982458524782341305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13673907976611366376455073 10255430982458524782341305)
              ·
                refine ⟨7691573236843893586755979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10255430982458524782341305 7691573236843893586755979)
                ·
                  refine ⟨11537359855265840380133969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7691573236843893586755979 11537359855265840380133969)
                  ·
                    refine ⟨8653019891449380285100477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11537359855265840380133969 8653019891449380285100477)
                    ·
                      refine ⟨3244882459293517606912679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8653019891449380285100477 3244882459293517606912679)
                      ·
                        rfl

theorem cell23_6319386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_6319386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319386 prefixEnd_6319386 := by exact prefixLift 6319386
  have htrace : WordTrace (prefixWord ++ tailWord_6319386) baseStart_6319386 baseEnd_6319386 := by
    simpa [prefixWord, tailWord_6319386, baseEnd_6319386] using wordTrace_append hprefix tailTrace_6319386
  have hstable : (prefixWord ++ tailWord_6319386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319386).length < 2 ^ (prefixWord ++ tailWord_6319386).sum := by decide
  have hdescent : baseEnd_6319386 < baseStart_6319386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319389 : List Nat := [1, 4, 2, 3, 1, 1, 4, 7]
def baseStart_6319389 : Nat := 118140960795 + 6319389 * 2 ^ 59
def prefixEnd_6319389 : Nat := 4983230072969 + 3 ^ 40 * 6319389 * 2
def baseEnd_6319389 : Nat := 120180888879091892413895

theorem tailTrace_6319389 : CollatzResearch.WordTrace tailWord_6319389 prefixEnd_6319389 120180888879091892413895 := by
  unfold tailWord_6319389
  simp only [CollatzResearch.WordTrace]
  refine ⟨230487052102940393561577221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153658034735293595707718147 230487052102940393561577221)
  ·
    refine ⟨43216322269301323792795729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230487052102940393561577221 43216322269301323792795729)
    ·
      refine ⟨32412241701975992844596797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43216322269301323792795729 32412241701975992844596797)
      ·
        refine ⟨12154590638240997316723799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32412241701975992844596797 12154590638240997316723799)
        ·
          refine ⟨18231885957361495975085699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12154590638240997316723799 18231885957361495975085699)
          ·
            refine ⟨27347828936042243962628549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18231885957361495975085699 27347828936042243962628549)
            ·
              refine ⟨5127717925507920742992853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27347828936042243962628549 5127717925507920742992853)
              ·
                refine ⟨120180888879091892413895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5127717925507920742992853 120180888879091892413895)
                ·
                  rfl

theorem cell23_6319389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 7].length) (baseStart_6319389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319389 prefixEnd_6319389 := by exact prefixLift 6319389
  have htrace : WordTrace (prefixWord ++ tailWord_6319389) baseStart_6319389 baseEnd_6319389 := by
    simpa [prefixWord, tailWord_6319389, baseEnd_6319389] using wordTrace_append hprefix tailTrace_6319389
  have hstable : (prefixWord ++ tailWord_6319389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319389).length < 2 ^ (prefixWord ++ tailWord_6319389).sum := by decide
  have hdescent : baseEnd_6319389 < baseStart_6319389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319400 : List Nat := [2, 1, 5, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_6319400 : Nat := 118140960795 + 6319400 * 2 ^ 59
def prefixEnd_6319400 : Nat := 4983230072969 + 3 ^ 40 * 6319400 * 2
def baseEnd_6319400 : Nat := 3244889648022680552137615

theorem tailTrace_6319400 : CollatzResearch.WordTrace tailWord_6319400 prefixEnd_6319400 3244889648022680552137615 := by
  unfold tailWord_6319400
  simp only [CollatzResearch.WordTrace]
  refine ⟨115243726652950271220113827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153658302203933694960151769 115243726652950271220113827)
  ·
    refine ⟨172865589979425406830170741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115243726652950271220113827 172865589979425406830170741)
    ·
      refine ⟨16206149060571131890328507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172865589979425406830170741 16206149060571131890328507)
      ·
        refine ⟨24309223590856697835492761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16206149060571131890328507 24309223590856697835492761)
        ·
          refine ⟨18231917693142523376619571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24309223590856697835492761 18231917693142523376619571)
          ·
            refine ⟨27347876539713785064929357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18231917693142523376619571 27347876539713785064929357)
            ·
              refine ⟨10255453702392669399348509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27347876539713785064929357 10255453702392669399348509)
              ·
                refine ⟨3845795138397251024755691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10255453702392669399348509 3845795138397251024755691)
                ·
                  refine ⟨5768692707595876537133537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845795138397251024755691 5768692707595876537133537)
                  ·
                    refine ⟨4326519530696907402850153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5768692707595876537133537 4326519530696907402850153)
                    ·
                      refine ⟨3244889648022680552137615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326519530696907402850153 3244889648022680552137615)
                      ·
                        rfl

theorem cell23_6319400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_6319400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319400 prefixEnd_6319400 := by exact prefixLift 6319400
  have htrace : WordTrace (prefixWord ++ tailWord_6319400) baseStart_6319400 baseEnd_6319400 := by
    simpa [prefixWord, tailWord_6319400, baseEnd_6319400] using wordTrace_append hprefix tailTrace_6319400
  have hstable : (prefixWord ++ tailWord_6319400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319400).length < 2 ^ (prefixWord ++ tailWord_6319400).sum := by decide
  have hdescent : baseEnd_6319400 < baseStart_6319400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319417 : List Nat := [1, 2, 1, 6, 2, 1, 3, 2, 1, 2, 2]
def baseStart_6319417 : Nat := 118140960795 + 6319417 * 2 ^ 59
def prefixEnd_6319417 : Nat := 4983230072969 + 3 ^ 40 * 6319417 * 2
def baseEnd_6319417 : Nat := 3244898377193806985625037

theorem tailTrace_6319417 : CollatzResearch.WordTrace tailWord_6319417 prefixEnd_6319417 3244898377193806985625037 := by
  unfold tailWord_6319417
  simp only [CollatzResearch.WordTrace]
  refine ⟨230488073346838954343596505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153658715564559302895731003 230488073346838954343596505)
  ·
    refine ⟨172866055010129215757697379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230488073346838954343596505 172866055010129215757697379)
    ·
      refine ⟨259299082515193823636546069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172866055010129215757697379 259299082515193823636546069)
      ·
        refine ⟨12154644492899710482963097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 259299082515193823636546069 12154644492899710482963097)
        ·
          refine ⟨9115983369674782862222323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12154644492899710482963097 9115983369674782862222323)
          ·
            refine ⟨13673975054512174293333485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9115983369674782862222323 13673975054512174293333485)
            ·
              refine ⟨5127740645442065360000057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13673975054512174293333485 5127740645442065360000057)
              ·
                refine ⟨3845805484081549020000043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5127740645442065360000057 3845805484081549020000043)
                ·
                  refine ⟨5768708226122323530000065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845805484081549020000043 5768708226122323530000065)
                  ·
                    refine ⟨4326531169591742647500049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5768708226122323530000065 4326531169591742647500049)
                    ·
                      refine ⟨3244898377193806985625037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326531169591742647500049 3244898377193806985625037)
                      ·
                        rfl

theorem cell23_6319417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_6319417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319417 prefixEnd_6319417 := by exact prefixLift 6319417
  have htrace : WordTrace (prefixWord ++ tailWord_6319417) baseStart_6319417 baseEnd_6319417 := by
    simpa [prefixWord, tailWord_6319417, baseEnd_6319417] using wordTrace_append hprefix tailTrace_6319417
  have hstable : (prefixWord ++ tailWord_6319417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319417).length < 2 ^ (prefixWord ++ tailWord_6319417).sum := by decide
  have hdescent : baseEnd_6319417 < baseStart_6319417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319437 : List Nat := [1, 6, 1, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_6319437 : Nat := 118140960795 + 6319437 * 2 ^ 59
def prefixEnd_6319437 : Nat := 4983230072969 + 3 ^ 40 * 6319437 * 2
def baseEnd_6319437 : Nat := 3244908646806896907374945

theorem tailTrace_6319437 : CollatzResearch.WordTrace tailWord_6319437 prefixEnd_6319437 3244908646806896907374945 := by
  unfold tailWord_6319437
  simp only [CollatzResearch.WordTrace]
  refine ⟨230488802806766497759324565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153659201871177665172883043 230488802806766497759324565)
  ·
    refine ⟨10804162631567179582468339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 230488802806766497759324565 10804162631567179582468339)
    ·
      refine ⟨16206243947350769373702509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10804162631567179582468339 16206243947350769373702509)
      ·
        refine ⟨6077341480256538515138441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16206243947350769373702509 6077341480256538515138441)
        ·
          refine ⟨4558006110192403886353831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6077341480256538515138441 4558006110192403886353831)
          ·
            refine ⟨6837009165288605829530747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4558006110192403886353831 6837009165288605829530747)
            ·
              refine ⟨10255513747932908744296121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6837009165288605829530747 10255513747932908744296121)
              ·
                refine ⟨7691635310949681558222091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10255513747932908744296121 7691635310949681558222091)
                ·
                  refine ⟨11537452966424522337333137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7691635310949681558222091 11537452966424522337333137)
                  ·
                    refine ⟨8653089724818391752999853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11537452966424522337333137 8653089724818391752999853)
                    ·
                      refine ⟨3244908646806896907374945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8653089724818391752999853 3244908646806896907374945)
                      ·
                        rfl

theorem cell23_6319437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_6319437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319437 prefixEnd_6319437 := by exact prefixLift 6319437
  have htrace : WordTrace (prefixWord ++ tailWord_6319437) baseStart_6319437 baseEnd_6319437 := by
    simpa [prefixWord, tailWord_6319437, baseEnd_6319437] using wordTrace_append hprefix tailTrace_6319437
  have hstable : (prefixWord ++ tailWord_6319437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319437).length < 2 ^ (prefixWord ++ tailWord_6319437).sum := by decide
  have hdescent : baseEnd_6319437 < baseStart_6319437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319456 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 1, 4, 2]
def baseStart_6319456 : Nat := 118140960795 + 6319456 * 2 ^ 59
def prefixEnd_6319456 : Nat := 4983230072969 + 3 ^ 40 * 6319456 * 2
def baseEnd_6319456 : Nat := 3244918402939332333037357

theorem tailTrace_6319456 : CollatzResearch.WordTrace tailWord_6319456 prefixEnd_6319456 3244918402939332333037357 := by
  unfold tailWord_6319456
  simp only [CollatzResearch.WordTrace]
  refine ⟨115244747896848832002133111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153659663862465109336177481 115244747896848832002133111)
  ·
    refine ⟨172867121845273248003199667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115244747896848832002133111 172867121845273248003199667)
    ·
      refine ⟨259300682767909872004799501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172867121845273248003199667 259300682767909872004799501)
      ·
        refine ⟨97237756037966202001799813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259300682767909872004799501 97237756037966202001799813)
        ·
          refine ⟨18232079257118662875337465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97237756037966202001799813 18232079257118662875337465)
          ·
            refine ⟨13674059442838997156503099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18232079257118662875337465 13674059442838997156503099)
            ·
              refine ⟨20511089164258495734754649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13674059442838997156503099 20511089164258495734754649)
              ·
                refine ⟨15383316873193871801065987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20511089164258495734754649 15383316873193871801065987)
                ·
                  refine ⟨23074975309790807701598981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15383316873193871801065987 23074975309790807701598981)
                  ·
                    refine ⟨4326557870585776444049809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23074975309790807701598981 4326557870585776444049809)
                    ·
                      refine ⟨3244918402939332333037357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326557870585776444049809 3244918402939332333037357)
                      ·
                        rfl

theorem cell23_6319456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_6319456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319456 prefixEnd_6319456 := by exact prefixLift 6319456
  have htrace : WordTrace (prefixWord ++ tailWord_6319456) baseStart_6319456 baseEnd_6319456 := by
    simpa [prefixWord, tailWord_6319456, baseEnd_6319456] using wordTrace_append hprefix tailTrace_6319456
  have hstable : (prefixWord ++ tailWord_6319456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319456).length < 2 ^ (prefixWord ++ tailWord_6319456).sum := by decide
  have hdescent : baseEnd_6319456 < baseStart_6319456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319479 : List Nat := [1, 1, 3, 1, 1, 2, 5, 4, 5]
def baseStart_6319479 : Nat := 118140960795 + 6319479 * 2 ^ 59
def prefixEnd_6319479 : Nat := 4983230072969 + 3 ^ 40 * 6319479 * 2
def baseEnd_6319479 : Nat := 360547801443820638116639

theorem tailTrace_6319479 : CollatzResearch.WordTrace tailWord_6319479 prefixEnd_6319479 360547801443820638116639 := by
  unfold tailWord_6319479
  simp only [CollatzResearch.WordTrace]
  refine ⟨230490334672614338932353491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153660223115076225954902327 230490334672614338932353491)
  ·
    refine ⟨345735502008921508398530237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230490334672614338932353491 345735502008921508398530237)
    ·
      refine ⟨129650813253345565649448839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345735502008921508398530237 129650813253345565649448839)
      ·
        refine ⟨194476219880018348474173259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129650813253345565649448839 194476219880018348474173259)
        ·
          refine ⟨291714329820027522711259889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194476219880018348474173259 291714329820027522711259889)
          ·
            refine ⟨218785747365020642033444917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291714329820027522711259889 218785747365020642033444917)
            ·
              refine ⟨20511163815470685190635461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 218785747365020642033444917 20511163815470685190635461)
              ·
                refine ⟨3845843215400753473244149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20511163815470685190635461 3845843215400753473244149)
                ·
                  refine ⟨360547801443820638116639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3845843215400753473244149 360547801443820638116639)
                  ·
                    rfl

theorem cell23_6319479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 5].length) (baseStart_6319479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319479 prefixEnd_6319479 := by exact prefixLift 6319479
  have htrace : WordTrace (prefixWord ++ tailWord_6319479) baseStart_6319479 baseEnd_6319479 := by
    simpa [prefixWord, tailWord_6319479, baseEnd_6319479] using wordTrace_append hprefix tailTrace_6319479
  have hstable : (prefixWord ++ tailWord_6319479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319479).length < 2 ^ (prefixWord ++ tailWord_6319479).sum := by decide
  have hdescent : baseEnd_6319479 < baseStart_6319479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319490 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_6319490 : Nat := 118140960795 + 6319490 * 2 ^ 59
def prefixEnd_6319490 : Nat := 4983230072969 + 3 ^ 40 * 6319490 * 2
def baseEnd_6319490 : Nat := 3244935861281585200012201

theorem tailTrace_6319490 : CollatzResearch.WordTrace tailWord_6319490 prefixEnd_6319490 3244935861281585200012201 := by
  unfold tailWord_6319490
  simp only [CollatzResearch.WordTrace]
  refine ⟨57622683968893621952750981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153660490583716325207335949 57622683968893621952750981)
  ·
    refine ⟨10804253244167554116140809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57622683968893621952750981 10804253244167554116140809)
    ·
      refine ⟨8103189933125665587105607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10804253244167554116140809 8103189933125665587105607)
      ·
        refine ⟨12154784899688498380658411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8103189933125665587105607 12154784899688498380658411)
        ·
          refine ⟨18232177349532747570987617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12154784899688498380658411 18232177349532747570987617)
          ·
            refine ⟨13674133012149560678240713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18232177349532747570987617 13674133012149560678240713)
            ·
              refine ⟨10255599759112170508680535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13674133012149560678240713 10255599759112170508680535)
              ·
                refine ⟨15383399638668255763020803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10255599759112170508680535 15383399638668255763020803)
                ·
                  refine ⟨23075099458002383644531205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15383399638668255763020803 23075099458002383644531205)
                  ·
                    refine ⟨4326581148375446933349601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23075099458002383644531205 4326581148375446933349601)
                    ·
                      refine ⟨3244935861281585200012201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326581148375446933349601 3244935861281585200012201)
                      ·
                        rfl

theorem cell23_6319490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_6319490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319490 prefixEnd_6319490 := by exact prefixLift 6319490
  have htrace : WordTrace (prefixWord ++ tailWord_6319490) baseStart_6319490 baseEnd_6319490 := by
    simpa [prefixWord, tailWord_6319490, baseEnd_6319490] using wordTrace_append hprefix tailTrace_6319490
  have hstable : (prefixWord ++ tailWord_6319490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319490).length < 2 ^ (prefixWord ++ tailWord_6319490).sum := by decide
  have hdescent : baseEnd_6319490 < baseStart_6319490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319499 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 2, 5, 2]
def baseStart_6319499 : Nat := 118140960795 + 6319499 * 2 ^ 59
def prefixEnd_6319499 : Nat := 4983230072969 + 3 ^ 40 * 6319499 * 2
def baseEnd_6319499 : Nat := 3244940482607475664799659

theorem tailTrace_6319499 : CollatzResearch.WordTrace tailWord_6319499 prefixEnd_6319499 3244940482607475664799659 := by
  unfold tailWord_6319499
  simp only [CollatzResearch.WordTrace]
  refine ⟨230491064132541882348081551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153660709421694588232054367 230491064132541882348081551)
  ·
    refine ⟨345736596198812823522122327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230491064132541882348081551 345736596198812823522122327)
    ·
      refine ⟨518604894298219235283183491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345736596198812823522122327 518604894298219235283183491)
      ·
        refine ⟨777907341447328852924775237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518604894298219235283183491 777907341447328852924775237)
        ·
          refine ⟨145857626521374159923395357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 777907341447328852924775237 145857626521374159923395357)
          ·
            refine ⟨54696609945515309971273259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145857626521374159923395357 54696609945515309971273259)
            ·
              refine ⟨82044914918272964956909889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54696609945515309971273259 82044914918272964956909889)
              ·
                refine ⟨61533686188704723717682417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82044914918272964956909889 61533686188704723717682417)
                ·
                  refine ⟨46150264641528542788261813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61533686188704723717682417 46150264641528542788261813)
                  ·
                    refine ⟨4326587310143300886399545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46150264641528542788261813 4326587310143300886399545)
                    ·
                      refine ⟨3244940482607475664799659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326587310143300886399545 3244940482607475664799659)
                      ·
                        rfl

theorem cell23_6319499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 5, 2].length) (baseStart_6319499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319499 prefixEnd_6319499 := by exact prefixLift 6319499
  have htrace : WordTrace (prefixWord ++ tailWord_6319499) baseStart_6319499 baseEnd_6319499 := by
    simpa [prefixWord, tailWord_6319499, baseEnd_6319499] using wordTrace_append hprefix tailTrace_6319499
  have hstable : (prefixWord ++ tailWord_6319499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319499).length < 2 ^ (prefixWord ++ tailWord_6319499).sum := by decide
  have hdescent : baseEnd_6319499 < baseStart_6319499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319509 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 2, 5]
def baseStart_6319509 : Nat := 118140960795 + 6319509 * 2 ^ 59
def prefixEnd_6319509 : Nat := 4983230072969 + 3 ^ 40 * 6319509 * 2
def baseEnd_6319509 : Nat := 1081648539138006875224871

theorem tailTrace_6319509 : CollatzResearch.WordTrace tailWord_6319509 prefixEnd_6319509 1081648539138006875224871 := by
  unfold tailWord_6319509
  simp only [CollatzResearch.WordTrace]
  refine ⟨230491428862505654055945581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153660952575003769370630387 230491428862505654055945581)
  ·
    refine ⟨86434285823439620270979593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230491428862505654055945581 86434285823439620270979593)
    ·
      refine ⟨64825714367579715203234695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86434285823439620270979593 64825714367579715203234695)
      ·
        refine ⟨97238571551369572804852043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64825714367579715203234695 97238571551369572804852043)
        ·
          refine ⟨145857857327054359207278065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97238571551369572804852043 145857857327054359207278065)
          ·
            refine ⟨109393392995290769405458549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145857857327054359207278065 109393392995290769405458549)
            ·
              refine ⟨10255630593308509631761739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109393392995290769405458549 10255630593308509631761739)
              ·
                refine ⟨15383445889962764447642609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10255630593308509631761739 15383445889962764447642609)
                ·
                  refine ⟨11537584417472073335731957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15383445889962764447642609 11537584417472073335731957)
                  ·
                    refine ⟨1081648539138006875224871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11537584417472073335731957 1081648539138006875224871)
                    ·
                      rfl

theorem cell23_6319509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_6319509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319509 prefixEnd_6319509 := by exact prefixLift 6319509
  have htrace : WordTrace (prefixWord ++ tailWord_6319509) baseStart_6319509 baseEnd_6319509 := by
    simpa [prefixWord, tailWord_6319509, baseEnd_6319509] using wordTrace_append hprefix tailTrace_6319509
  have hstable : (prefixWord ++ tailWord_6319509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319509).length < 2 ^ (prefixWord ++ tailWord_6319509).sum := by decide
  have hdescent : baseEnd_6319509 < baseStart_6319509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319532 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_6319532 : Nat := 118140960795 + 6319532 * 2 ^ 59
def prefixEnd_6319532 : Nat := 4983230072969 + 3 ^ 40 * 6319532 * 2
def baseEnd_6319532 : Nat := 3244957427469074035687007

theorem tailTrace_6319532 : CollatzResearch.WordTrace tailWord_6319532 prefixEnd_6319532 3244957427469074035687007 := by
  unfold tailWord_6319532
  simp only [CollatzResearch.WordTrace]
  refine ⟨115246133870711164492016425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153661511827614885989355233 115246133870711164492016425)
  ·
    refine ⟨86434600403033373369012319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115246133870711164492016425 86434600403033373369012319)
    ·
      refine ⟨129651900604550060053518479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86434600403033373369012319 129651900604550060053518479)
      ·
        refine ⟨194477850906825090080277719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129651900604550060053518479 194477850906825090080277719)
        ·
          refine ⟨291716776360237635120416579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194477850906825090080277719 291716776360237635120416579)
          ·
            refine ⟨437575164540356452680624869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291716776360237635120416579 437575164540356452680624869)
            ·
              refine ⟨82045343351316834877617163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 437575164540356452680624869 82045343351316834877617163)
              ·
                refine ⟨123068015026975252316425745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82045343351316834877617163 123068015026975252316425745)
                ·
                  refine ⟨92301011270231439237319309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123068015026975252316425745 92301011270231439237319309)
                  ·
                    refine ⟨34612879226336789713994741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92301011270231439237319309 34612879226336789713994741)
                    ·
                      refine ⟨3244957427469074035687007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34612879226336789713994741 3244957427469074035687007)
                      ·
                        rfl

theorem cell23_6319532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_6319532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319532 prefixEnd_6319532 := by exact prefixLift 6319532
  have htrace : WordTrace (prefixWord ++ tailWord_6319532) baseStart_6319532 baseEnd_6319532 := by
    simpa [prefixWord, tailWord_6319532, baseEnd_6319532] using wordTrace_append hprefix tailTrace_6319532
  have hstable : (prefixWord ++ tailWord_6319532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319532).length < 2 ^ (prefixWord ++ tailWord_6319532).sum := by decide
  have hdescent : baseEnd_6319532 < baseStart_6319532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319549 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_6319549 : Nat := 118140960795 + 6319549 * 2 ^ 59
def prefixEnd_6319549 : Nat := 4983230072969 + 3 ^ 40 * 6319549 * 2
def baseEnd_6319549 : Nat := 3244966156640200469174429

theorem tailTrace_6319549 : CollatzResearch.WordTrace tailWord_6319549 prefixEnd_6319549 3244966156640200469174429 := by
  unfold tailWord_6319549
  simp only [CollatzResearch.WordTrace]
  refine ⟨230492887782360740887401701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153661925188240493924934467 230492887782360740887401701)
  ·
    refine ⟨43217416459192638916387819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230492887782360740887401701 43217416459192638916387819)
    ·
      refine ⟨64826124688788958374581729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43217416459192638916387819 64826124688788958374581729)
      ·
        refine ⟨48619593516591718780936297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64826124688788958374581729 48619593516591718780936297)
        ·
          refine ⟨36464695137443789085702223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48619593516591718780936297 36464695137443789085702223)
          ·
            refine ⟨54697042706165683628553335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36464695137443789085702223 54697042706165683628553335)
            ·
              refine ⟨82045564059248525442830003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54697042706165683628553335 82045564059248525442830003)
              ·
                refine ⟨123068346088872788164245005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82045564059248525442830003 123068346088872788164245005)
                ·
                  refine ⟨46150629783327295561591877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123068346088872788164245005 46150629783327295561591877)
                  ·
                    refine ⟨8653243084373867917798477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46150629783327295561591877 8653243084373867917798477)
                    ·
                      refine ⟨3244966156640200469174429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8653243084373867917798477 3244966156640200469174429)
                      ·
                        rfl

theorem cell23_6319549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_6319549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319549 prefixEnd_6319549 := by exact prefixLift 6319549
  have htrace : WordTrace (prefixWord ++ tailWord_6319549) baseStart_6319549 baseEnd_6319549 := by
    simpa [prefixWord, tailWord_6319549, baseEnd_6319549] using wordTrace_append hprefix tailTrace_6319549
  have hstable : (prefixWord ++ tailWord_6319549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319549).length < 2 ^ (prefixWord ++ tailWord_6319549).sum := by decide
  have hdescent : baseEnd_6319549 < baseStart_6319549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319596 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 3]
def baseStart_6319596 : Nat := 118140960795 + 6319596 * 2 ^ 59
def prefixEnd_6319596 : Nat := 4983230072969 + 3 ^ 40 * 6319596 * 2
def baseEnd_6319596 : Nat := 3244990290230961785286713

theorem tailTrace_6319596 : CollatzResearch.WordTrace tailWord_6319596 prefixEnd_6319596 3244990290230961785286713 := by
  unfold tailWord_6319596
  simp only [CollatzResearch.WordTrace]
  refine ⟨115247301006595233957181321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153663068008793645276241761 115247301006595233957181321)
  ·
    refine ⟨86435475754946425467885991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115247301006595233957181321 86435475754946425467885991)
    ·
      refine ⟨129653213632419638201828987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86435475754946425467885991 129653213632419638201828987)
      ·
        refine ⟨194479820448629457302743481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129653213632419638201828987 194479820448629457302743481)
        ·
          refine ⟨145859865336472092977057611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194479820448629457302743481 145859865336472092977057611)
          ·
            refine ⟨218789798004708139465586417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145859865336472092977057611 218789798004708139465586417)
            ·
              refine ⟨164092348503531104599189813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218789798004708139465586417 164092348503531104599189813)
              ·
                refine ⟨15383657672206041056174045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164092348503531104599189813 15383657672206041056174045)
                ·
                  refine ⟨5768871627077265396065267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15383657672206041056174045 5768871627077265396065267)
                  ·
                    refine ⟨8653307440615898094097901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5768871627077265396065267 8653307440615898094097901)
                    ·
                      refine ⟨3244990290230961785286713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8653307440615898094097901 3244990290230961785286713)
                      ·
                        rfl

theorem cell23_6319596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_6319596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319596 prefixEnd_6319596 := by exact prefixLift 6319596
  have htrace : WordTrace (prefixWord ++ tailWord_6319596) baseStart_6319596 baseEnd_6319596 := by
    simpa [prefixWord, tailWord_6319596, baseEnd_6319596] using wordTrace_append hprefix tailTrace_6319596
  have hstable : (prefixWord ++ tailWord_6319596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319596).length < 2 ^ (prefixWord ++ tailWord_6319596).sum := by decide
  have hdescent : baseEnd_6319596 < baseStart_6319596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319623 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 2, 3, 2]
def baseStart_6319623 : Nat := 118140960795 + 6319623 * 2 ^ 59
def prefixEnd_6319623 : Nat := 4983230072969 + 3 ^ 40 * 6319623 * 2
def baseEnd_6319623 : Nat := 3245004154208633179649089

theorem tailTrace_6319623 : CollatzResearch.WordTrace tailWord_6319623 prefixEnd_6319623 3245004154208633179649089 := by
  unfold tailWord_6319623
  simp only [CollatzResearch.WordTrace]
  refine ⟨230495586784092651525595523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153663724522728434350397015 230495586784092651525595523)
  ·
    refine ⟨345743380176138977288393285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230495586784092651525595523 345743380176138977288393285)
    ·
      refine ⟨64826883783026058241573741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345743380176138977288393285 64826883783026058241573741)
      ·
        refine ⟨24310081418634771840590153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64826883783026058241573741 24310081418634771840590153)
        ·
          refine ⟨18232561063976078880442615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24310081418634771840590153 18232561063976078880442615)
          ·
            refine ⟨27348841595964118320663923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18232561063976078880442615 27348841595964118320663923)
            ·
              refine ⟨41023262393946177480995885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27348841595964118320663923 41023262393946177480995885)
              ·
                refine ⟨15383723397729816555373457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41023262393946177480995885 15383723397729816555373457)
                ·
                  refine ⟨11537792548297362416530093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15383723397729816555373457 11537792548297362416530093)
                  ·
                    refine ⟨4326672205611510906198785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11537792548297362416530093 4326672205611510906198785)
                    ·
                      refine ⟨3245004154208633179649089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326672205611510906198785 3245004154208633179649089)
                      ·
                        rfl

theorem cell23_6319623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_6319623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319623 prefixEnd_6319623 := by exact prefixLift 6319623
  have htrace : WordTrace (prefixWord ++ tailWord_6319623) baseStart_6319623 baseEnd_6319623 := by
    simpa [prefixWord, tailWord_6319623, baseEnd_6319623] using wordTrace_append hprefix tailTrace_6319623
  have hstable : (prefixWord ++ tailWord_6319623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319623).length < 2 ^ (prefixWord ++ tailWord_6319623).sum := by decide
  have hdescent : baseEnd_6319623 < baseStart_6319623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319653 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 3, 2, 2]
def baseStart_6319653 : Nat := 118140960795 + 6319653 * 2 ^ 59
def prefixEnd_6319653 : Nat := 4983230072969 + 3 ^ 40 * 6319653 * 2
def baseEnd_6319653 : Nat := 3245019558628268062273951

theorem tailTrace_6319653 : CollatzResearch.WordTrace tailWord_6319653 prefixEnd_6319653 3245019558628268062273951 := by
  unfold tailWord_6319653
  simp only [CollatzResearch.WordTrace]
  refine ⟨230496680973983966649187613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153664453982655977766125075 230496680973983966649187613)
  ·
    refine ⟨86436255365243987493445355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230496680973983966649187613 86436255365243987493445355)
    ·
      refine ⟨129654383047865981240168033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86436255365243987493445355 129654383047865981240168033)
      ·
        refine ⟨97240787285899485930126025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129654383047865981240168033 97240787285899485930126025)
        ·
          refine ⟨72930590464424614447594519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97240787285899485930126025 72930590464424614447594519)
          ·
            refine ⟨109395885696636921671391779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72930590464424614447594519 109395885696636921671391779)
            ·
              refine ⟨164093828544955382507087669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109395885696636921671391779 164093828544955382507087669)
              ·
                refine ⟨15383796426089567110039469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164093828544955382507087669 15383796426089567110039469)
                ·
                  refine ⟨5768923659783587666264801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15383796426089567110039469 5768923659783587666264801)
                  ·
                    refine ⟨4326692744837690749698601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5768923659783587666264801 4326692744837690749698601)
                    ·
                      refine ⟨3245019558628268062273951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326692744837690749698601 3245019558628268062273951)
                      ·
                        rfl

theorem cell23_6319653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_6319653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319653 prefixEnd_6319653 := by exact prefixLift 6319653
  have htrace : WordTrace (prefixWord ++ tailWord_6319653) baseStart_6319653 baseEnd_6319653 := by
    simpa [prefixWord, tailWord_6319653, baseEnd_6319653] using wordTrace_append hprefix tailTrace_6319653
  have hstable : (prefixWord ++ tailWord_6319653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319653).length < 2 ^ (prefixWord ++ tailWord_6319653).sum := by decide
  have hdescent : baseEnd_6319653 < baseStart_6319653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319687 : List Nat := [1, 1, 4, 1, 6, 1, 2, 1, 1, 1, 4]
def baseStart_6319687 : Nat := 118140960795 + 6319687 * 2 ^ 59
def prefixEnd_6319687 : Nat := 4983230072969 + 3 ^ 40 * 6319687 * 2
def baseEnd_6319687 : Nat := 3245037016970520929248795

theorem tailTrace_6319687 : CollatzResearch.WordTrace tailWord_6319687 prefixEnd_6319687 3245037016970520929248795 := by
  unfold tailWord_6319687
  simp only [CollatzResearch.WordTrace]
  refine ⟨230497921055860790455925315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153665280703907193637283543 230497921055860790455925315)
  ·
    refine ⟨345746881583791185683887973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230497921055860790455925315 345746881583791185683887973)
    ·
      refine ⟨64827540296960847315728995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345746881583791185683887973 64827540296960847315728995)
      ·
        refine ⟨97241310445441270973593493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64827540296960847315728995 97241310445441270973593493)
        ·
          refine ⟨4558186427130059576887195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97241310445441270973593493 4558186427130059576887195)
          ·
            refine ⟨6837279640695089365330793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4558186427130059576887195 6837279640695089365330793)
            ·
              refine ⟨5127959730521317023998095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6837279640695089365330793 5127959730521317023998095)
              ·
                refine ⟨7691939595781975535997143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5127959730521317023998095 7691939595781975535997143)
                ·
                  refine ⟨11537909393672963303995715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7691939595781975535997143 11537909393672963303995715)
                  ·
                    refine ⟨17306864090509444955993573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11537909393672963303995715 17306864090509444955993573)
                    ·
                      refine ⟨3245037016970520929248795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17306864090509444955993573 3245037016970520929248795)
                      ·
                        rfl

theorem cell23_6319687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_6319687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319687 prefixEnd_6319687 := by exact prefixLift 6319687
  have htrace : WordTrace (prefixWord ++ tailWord_6319687) baseStart_6319687 baseEnd_6319687 := by
    simpa [prefixWord, tailWord_6319687, baseEnd_6319687] using wordTrace_append hprefix tailTrace_6319687
  have hstable : (prefixWord ++ tailWord_6319687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319687).length < 2 ^ (prefixWord ++ tailWord_6319687).sum := by decide
  have hdescent : baseEnd_6319687 < baseStart_6319687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319703 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 4, 1, 3]
def baseStart_6319703 : Nat := 118140960795 + 6319703 * 2 ^ 59
def prefixEnd_6319703 : Nat := 4983230072969 + 3 ^ 40 * 6319703 * 2
def baseEnd_6319703 : Nat := 3245045232660992866648721

theorem tailTrace_6319703 : CollatzResearch.WordTrace tailWord_6319703 prefixEnd_6319703 3245045232660992866648721 := by
  unfold tailWord_6319703
  simp only [CollatzResearch.WordTrace]
  refine ⟨230498504623802825188507763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153665669749201883459005175 230498504623802825188507763)
  ·
    refine ⟨345747756935704237782761645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230498504623802825188507763 345747756935704237782761645)
    ·
      refine ⟨129655408850889089168535617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345747756935704237782761645 129655408850889089168535617)
      ·
        refine ⟨97241556638166816876401713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129655408850889089168535617 97241556638166816876401713)
        ·
          refine ⟨72931167478625112657301285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97241556638166816876401713 72931167478625112657301285)
          ·
            refine ⟨13674593902242208623243991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72931167478625112657301285 13674593902242208623243991)
            ·
              refine ⟨20511890853363312934865987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13674593902242208623243991 20511890853363312934865987)
              ·
                refine ⟨30767836280044969402298981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20511890853363312934865987 30767836280044969402298981)
                ·
                  refine ⟨5768969302508431762931059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30767836280044969402298981 5768969302508431762931059)
                  ·
                    refine ⟨8653453953762647644396589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5768969302508431762931059 8653453953762647644396589)
                    ·
                      refine ⟨3245045232660992866648721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8653453953762647644396589 3245045232660992866648721)
                      ·
                        rfl

theorem cell23_6319703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_6319703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319703 prefixEnd_6319703 := by exact prefixLift 6319703
  have htrace : WordTrace (prefixWord ++ tailWord_6319703) baseStart_6319703 baseEnd_6319703 := by
    simpa [prefixWord, tailWord_6319703, baseEnd_6319703] using wordTrace_append hprefix tailTrace_6319703
  have hstable : (prefixWord ++ tailWord_6319703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319703).length < 2 ^ (prefixWord ++ tailWord_6319703).sum := by decide
  have hdescent : baseEnd_6319703 < baseStart_6319703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319720 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_6319720 : Nat := 118140960795 + 6319720 * 2 ^ 59
def prefixEnd_6319720 : Nat := 4983230072969 + 3 ^ 40 * 6319720 * 2
def baseEnd_6319720 : Nat := 3245053961832119300136143

theorem tailTrace_6319720 : CollatzResearch.WordTrace tailWord_6319720 prefixEnd_6319720 3245053961832119300136143 := by
  unfold tailWord_6319720
  simp only [CollatzResearch.WordTrace]
  refine ⟨115249562332370618545938307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153666083109827491394584409 115249562332370618545938307)
  ·
    refine ⟨172874343498555927818907461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115249562332370618545938307 172874343498555927818907461)
    ·
      refine ⟨32413939405979236466045149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172874343498555927818907461 32413939405979236466045149)
      ·
        refine ⟨12155227277242213674766931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32413939405979236466045149 12155227277242213674766931)
        ·
          refine ⟨18232840915863320512150397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12155227277242213674766931 18232840915863320512150397)
          ·
            refine ⟨6837315343448745192056399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18232840915863320512150397 6837315343448745192056399)
            ·
              refine ⟨10255973015173117788084599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6837315343448745192056399 10255973015173117788084599)
              ·
                refine ⟨15383959522759676682126899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10255973015173117788084599 15383959522759676682126899)
                ·
                  refine ⟨23075939284139515023190349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15383959522759676682126899 23075939284139515023190349)
                  ·
                    refine ⟨8653477231552318133696381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23075939284139515023190349 8653477231552318133696381)
                    ·
                      refine ⟨3245053961832119300136143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8653477231552318133696381 3245053961832119300136143)
                      ·
                        rfl

theorem cell23_6319720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_6319720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319720 prefixEnd_6319720 := by exact prefixLift 6319720
  have htrace : WordTrace (prefixWord ++ tailWord_6319720) baseStart_6319720 baseEnd_6319720 := by
    simpa [prefixWord, tailWord_6319720, baseEnd_6319720] using wordTrace_append hprefix tailTrace_6319720
  have hstable : (prefixWord ++ tailWord_6319720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319720).length < 2 ^ (prefixWord ++ tailWord_6319720).sum := by decide
  have hdescent : baseEnd_6319720 < baseStart_6319720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319729 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_6319729 : Nat := 118140960795 + 6319729 * 2 ^ 59
def prefixEnd_6319729 : Nat := 4983230072969 + 3 ^ 40 * 6319729 * 2
def baseEnd_6319729 : Nat := 3245058583158009764923601

theorem tailTrace_6319729 : CollatzResearch.WordTrace tailWord_6319729 prefixEnd_6319729 3245058583158009764923601 := by
  unfold tailWord_6319729
  simp only [CollatzResearch.WordTrace]
  refine ⟨230499452921708631628954241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153666301947805754419302827 230499452921708631628954241)
  ·
    refine ⟨172874589691281473721715681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230499452921708631628954241 172874589691281473721715681)
    ·
      refine ⟨129655942268461105291286761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172874589691281473721715681 129655942268461105291286761)
      ·
        refine ⟨97241956701345828968465071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129655942268461105291286761 97241956701345828968465071)
        ·
          refine ⟨145862935052018743452697607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97241956701345828968465071 145862935052018743452697607)
          ·
            refine ⟨218794402578028115179046411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145862935052018743452697607 218794402578028115179046411)
            ·
              refine ⟨328191603867042172768569617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218794402578028115179046411 328191603867042172768569617)
              ·
                refine ⟨246143702900281629576427213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328191603867042172768569617 246143702900281629576427213)
                ·
                  refine ⟨92303888587605611091160205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246143702900281629576427213 92303888587605611091160205)
                  ·
                    refine ⟨34613958220352104159185077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92303888587605611091160205 34613958220352104159185077)
                    ·
                      refine ⟨3245058583158009764923601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34613958220352104159185077 3245058583158009764923601)
                      ·
                        rfl

theorem cell23_6319729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_6319729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319729 prefixEnd_6319729 := by exact prefixLift 6319729
  have htrace : WordTrace (prefixWord ++ tailWord_6319729) baseStart_6319729 baseEnd_6319729 := by
    simpa [prefixWord, tailWord_6319729, baseEnd_6319729] using wordTrace_append hprefix tailTrace_6319729
  have hstable : (prefixWord ++ tailWord_6319729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319729).length < 2 ^ (prefixWord ++ tailWord_6319729).sum := by decide
  have hdescent : baseEnd_6319729 < baseStart_6319729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319730 : List Nat := [3, 2, 1, 2, 3, 1, 1, 4, 1, 3, 2]
def baseStart_6319730 : Nat := 118140960795 + 6319730 * 2 ^ 59
def prefixEnd_6319730 : Nat := 4983230072969 + 3 ^ 40 * 6319730 * 2
def baseEnd_6319730 : Nat := 3245059096638664261011097

theorem tailTrace_6319730 : CollatzResearch.WordTrace tailWord_6319730 prefixEnd_6319730 3245059096638664261011097 := by
  unfold tailWord_6319730
  simp only [CollatzResearch.WordTrace]
  refine ⟨57624872348676252199935161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153666326263136672533160429 57624872348676252199935161)
  ·
    refine ⟨43218654261507189149951371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57624872348676252199935161 43218654261507189149951371)
    ·
      refine ⟨64827981392260783724927057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43218654261507189149951371 64827981392260783724927057)
      ·
        refine ⟨48620986044195587793695293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64827981392260783724927057 48620986044195587793695293)
        ·
          refine ⟨18232869766573345422635735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48620986044195587793695293 18232869766573345422635735)
          ·
            refine ⟨27349304649860018133953603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18232869766573345422635735 27349304649860018133953603)
            ·
              refine ⟨41023956974790027200930405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27349304649860018133953603 41023956974790027200930405)
              ·
                refine ⟨7691991932773130100174451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41023956974790027200930405 7691991932773130100174451)
                ·
                  refine ⟨11537987899159695150261677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7691991932773130100174451 11537987899159695150261677)
                  ·
                    refine ⟨4326745462184885681348129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11537987899159695150261677 4326745462184885681348129)
                    ·
                      refine ⟨3245059096638664261011097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326745462184885681348129 3245059096638664261011097)
                      ·
                        rfl

theorem cell23_6319730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_6319730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319730 prefixEnd_6319730 := by exact prefixLift 6319730
  have htrace : WordTrace (prefixWord ++ tailWord_6319730) baseStart_6319730 baseEnd_6319730 := by
    simpa [prefixWord, tailWord_6319730, baseEnd_6319730] using wordTrace_append hprefix tailTrace_6319730
  have hstable : (prefixWord ++ tailWord_6319730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319730).length < 2 ^ (prefixWord ++ tailWord_6319730).sum := by decide
  have hdescent : baseEnd_6319730 < baseStart_6319730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319769 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 8]
def baseStart_6319769 : Nat := 118140960795 + 6319769 * 2 ^ 59
def prefixEnd_6319769 : Nat := 4983230072969 + 3 ^ 40 * 6319769 * 2
def baseEnd_6319769 : Nat := 3245079122384189608423417

theorem tailTrace_6319769 : CollatzResearch.WordTrace tailWord_6319769 prefixEnd_6319769 3245079122384189608423417 := by
  unfold tailWord_6319769
  simp only [CollatzResearch.WordTrace]
  refine ⟨230500911841563718460410361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153667274561042478973606907 230500911841563718460410361)
  ·
    refine ⟨172875683881172788845307771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230500911841563718460410361 172875683881172788845307771)
    ·
      refine ⟨259313525821759183267961657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172875683881172788845307771 259313525821759183267961657)
      ·
        refine ⟨194485144366319387450971243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259313525821759183267961657 194485144366319387450971243)
        ·
          refine ⟨291727716549479081176456865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194485144366319387450971243 291727716549479081176456865)
          ·
            refine ⟨218795787412109310882342649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291727716549479081176456865 218795787412109310882342649)
            ·
              refine ⟨164096840559081983161756987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218795787412109310882342649 164096840559081983161756987)
              ·
                refine ⟨246145260838622974742635481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164096840559081983161756987 246145260838622974742635481)
                ·
                  refine ⟨184608945628967231056976611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 246145260838622974742635481 184608945628967231056976611)
                  ·
                    refine ⟨276913418443450846585464917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 184608945628967231056976611 276913418443450846585464917)
                    ·
                      refine ⟨3245079122384189608423417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 276913418443450846585464917 3245079122384189608423417)
                      ·
                        rfl

theorem cell23_6319769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_6319769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319769 prefixEnd_6319769 := by exact prefixLift 6319769
  have htrace : WordTrace (prefixWord ++ tailWord_6319769) baseStart_6319769 baseEnd_6319769 := by
    simpa [prefixWord, tailWord_6319769, baseEnd_6319769] using wordTrace_append hprefix tailTrace_6319769
  have hstable : (prefixWord ++ tailWord_6319769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319769).length < 2 ^ (prefixWord ++ tailWord_6319769).sum := by decide
  have hdescent : baseEnd_6319769 < baseStart_6319769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319777 : List Nat := [1, 2, 3, 3, 2, 2, 1, 3, 2, 2, 2]
def baseStart_6319777 : Nat := 118140960795 + 6319777 * 2 ^ 59
def prefixEnd_6319777 : Nat := 4983230072969 + 3 ^ 40 * 6319777 * 2
def baseEnd_6319777 : Nat := 3245083230229425577123381

theorem tailTrace_6319777 : CollatzResearch.WordTrace tailWord_6319777 prefixEnd_6319777 3245083230229425577123381 := by
  unfold tailWord_6319777
  simp only [CollatzResearch.WordTrace]
  refine ⟨230501203625534735826701585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153667469083689823884467723 230501203625534735826701585)
  ·
    refine ⟨172875902719151051870026189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230501203625534735826701585 172875902719151051870026189)
    ·
      refine ⟨64828463519681644451259821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172875902719151051870026189 64828463519681644451259821)
      ·
        refine ⟨24310673819880616669222433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64828463519681644451259821 24310673819880616669222433)
        ·
          refine ⟨18233005364910462501916825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24310673819880616669222433 18233005364910462501916825)
          ·
            refine ⟨13674754023682846876437619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18233005364910462501916825 13674754023682846876437619)
            ·
              refine ⟨20512131035524270314656429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13674754023682846876437619 20512131035524270314656429)
              ·
                refine ⟨7692049138321601367996161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20512131035524270314656429 7692049138321601367996161)
                ·
                  refine ⟨5769036853741201025997121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7692049138321601367996161 5769036853741201025997121)
                  ·
                    refine ⟨4326777640305900769497841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5769036853741201025997121 4326777640305900769497841)
                    ·
                      refine ⟨3245083230229425577123381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326777640305900769497841 3245083230229425577123381)
                      ·
                        rfl

theorem cell23_6319777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_6319777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319777 prefixEnd_6319777 := by exact prefixLift 6319777
  have htrace : WordTrace (prefixWord ++ tailWord_6319777) baseStart_6319777 baseEnd_6319777 := by
    simpa [prefixWord, tailWord_6319777, baseEnd_6319777] using wordTrace_append hprefix tailTrace_6319777
  have hstable : (prefixWord ++ tailWord_6319777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319777).length < 2 ^ (prefixWord ++ tailWord_6319777).sum := by decide
  have hdescent : baseEnd_6319777 < baseStart_6319777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319833 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 1, 6, 2]
def baseStart_6319833 : Nat := 118140960795 + 6319833 * 2 ^ 59
def prefixEnd_6319833 : Nat := 4983230072969 + 3 ^ 40 * 6319833 * 2
def baseEnd_6319833 : Nat := 3245111985146077358023123

theorem tailTrace_6319833 : CollatzResearch.WordTrace tailWord_6319833 prefixEnd_6319833 3245111985146077358023123 := by
  unfold tailWord_6319833
  simp only [CollatzResearch.WordTrace]
  refine ⟨230503246113331857390740153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153668830742221238260493435 230503246113331857390740153)
  ·
    refine ⟨172877434584998893043055115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230503246113331857390740153 172877434584998893043055115)
    ·
      refine ⟨259316151877498339564582673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172877434584998893043055115 259316151877498339564582673)
      ·
        refine ⟨194487113908123754673437005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259316151877498339564582673 194487113908123754673437005)
        ·
          refine ⟨72932667715546408002538877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194487113908123754673437005 72932667715546408002538877)
          ·
            refine ⟨27349750393329903000952079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72932667715546408002538877 27349750393329903000952079)
            ·
              refine ⟨41024625589994854501428119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27349750393329903000952079 41024625589994854501428119)
              ·
                refine ⟨61536938384992281752142179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41024625589994854501428119 61536938384992281752142179)
                ·
                  refine ⟨92305407577488422628213269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61536938384992281752142179 92305407577488422628213269)
                  ·
                    refine ⟨4326815980194769810697497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92305407577488422628213269 4326815980194769810697497)
                    ·
                      refine ⟨3245111985146077358023123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326815980194769810697497 3245111985146077358023123)
                      ·
                        rfl

theorem cell23_6319833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 6, 2].length) (baseStart_6319833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319833 prefixEnd_6319833 := by exact prefixLift 6319833
  have htrace : WordTrace (prefixWord ++ tailWord_6319833) baseStart_6319833 baseEnd_6319833 := by
    simpa [prefixWord, tailWord_6319833, baseEnd_6319833] using wordTrace_append hprefix tailTrace_6319833
  have hstable : (prefixWord ++ tailWord_6319833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319833).length < 2 ^ (prefixWord ++ tailWord_6319833).sum := by decide
  have hdescent : baseEnd_6319833 < baseStart_6319833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319847 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 2, 5]
def baseStart_6319847 : Nat := 118140960795 + 6319847 * 2 ^ 59
def prefixEnd_6319847 : Nat := 4983230072969 + 3 ^ 40 * 6319847 * 2
def baseEnd_6319847 : Nat := 1081706391291746767749353

theorem tailTrace_6319847 : CollatzResearch.WordTrace tailWord_6319847 prefixEnd_6319847 1081706391291746767749353 := by
  unfold tailWord_6319847
  simp only [CollatzResearch.WordTrace]
  refine ⟨230503756735281137781749795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153669171156854091854499863 230503756735281137781749795)
  ·
    refine ⟨345755635102921706672624693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230503756735281137781749795 345755635102921706672624693)
    ·
      refine ⟨32414590790898910000558565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 345755635102921706672624693 32414590790898910000558565)
      ·
        refine ⟨6077735773293545625104731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32414590790898910000558565 6077735773293545625104731)
        ·
          refine ⟨9116603659940318437657097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6077735773293545625104731 9116603659940318437657097)
          ·
            refine ⟨6837452744955238828242823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9116603659940318437657097 6837452744955238828242823)
            ·
              refine ⟨10256179117432858242364235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6837452744955238828242823 10256179117432858242364235)
              ·
                refine ⟨15384268676149287363546353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10256179117432858242364235 15384268676149287363546353)
                ·
                  refine ⟨11538201507111965522659765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15384268676149287363546353 11538201507111965522659765)
                  ·
                    refine ⟨1081706391291746767749353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11538201507111965522659765 1081706391291746767749353)
                    ·
                      rfl

theorem cell23_6319847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_6319847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319847 prefixEnd_6319847 := by exact prefixLift 6319847
  have htrace : WordTrace (prefixWord ++ tailWord_6319847) baseStart_6319847 baseEnd_6319847 := by
    simpa [prefixWord, tailWord_6319847, baseEnd_6319847] using wordTrace_append hprefix tailTrace_6319847
  have hstable : (prefixWord ++ tailWord_6319847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319847).length < 2 ^ (prefixWord ++ tailWord_6319847).sum := by decide
  have hdescent : baseEnd_6319847 < baseStart_6319847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319873 : List Nat := [1, 2, 4, 1, 1, 1, 5, 2, 6]
def baseStart_6319873 : Nat := 118140960795 + 6319873 * 2 ^ 59
def prefixEnd_6319873 : Nat := 4983230072969 + 3 ^ 40 * 6319873 * 2
def baseEnd_6319873 : Nat := 360570280485806355724771

theorem tailTrace_6319873 : CollatzResearch.WordTrace tailWord_6319873 prefixEnd_6319873 360570280485806355724771 := by
  unfold tailWord_6319873
  simp only [CollatzResearch.WordTrace]
  refine ⟨230504705033186944222196273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153669803355457962814797515 230504705033186944222196273)
  ·
    refine ⟨172878528774890208166647205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230504705033186944222196273 172878528774890208166647205)
    ·
      refine ⟨32414724145291914031246351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172878528774890208166647205 32414724145291914031246351)
      ·
        refine ⟨48622086217937871046869527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32414724145291914031246351 48622086217937871046869527)
        ·
          refine ⟨72933129326906806570304291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48622086217937871046869527 72933129326906806570304291)
          ·
            refine ⟨109399693990360209855456437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72933129326906806570304291 109399693990360209855456437)
            ·
              refine ⟨10256221311596269673949041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109399693990360209855456437 10256221311596269673949041)
              ·
                refine ⟨7692165983697202255461781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10256221311596269673949041 7692165983697202255461781)
                ·
                  refine ⟨360570280485806355724771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7692165983697202255461781 360570280485806355724771)
                  ·
                    rfl

theorem cell23_6319873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 6].length) (baseStart_6319873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319873 prefixEnd_6319873 := by exact prefixLift 6319873
  have htrace : WordTrace (prefixWord ++ tailWord_6319873) baseStart_6319873 baseEnd_6319873 := by
    simpa [prefixWord, tailWord_6319873, baseEnd_6319873] using wordTrace_append hprefix tailTrace_6319873
  have hstable : (prefixWord ++ tailWord_6319873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319873).length < 2 ^ (prefixWord ++ tailWord_6319873).sum := by decide
  have hdescent : baseEnd_6319873 < baseStart_6319873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319896 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_6319896 : Nat := 118140960795 + 6319896 * 2 ^ 59
def prefixEnd_6319896 : Nat := 4983230072969 + 3 ^ 40 * 6319896 * 2
def baseEnd_6319896 : Nat := 3245144334427310611535333

theorem tailTrace_6319896 : CollatzResearch.WordTrace tailWord_6319896 prefixEnd_6319896 3245144334427310611535333 := by
  unfold tailWord_6319896
  simp only [CollatzResearch.WordTrace]
  refine ⟨115252771956051809575141771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153670362608069079433522361 115252771956051809575141771)
  ·
    refine ⟨172879157934077714362712657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115252771956051809575141771 172879157934077714362712657)
    ·
      refine ⟨129659368450558285772034493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172879157934077714362712657 129659368450558285772034493)
      ·
        refine ⟨48622263168959357164512935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129659368450558285772034493 48622263168959357164512935)
        ·
          refine ⟨72933394753439035746769403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48622263168959357164512935 72933394753439035746769403)
          ·
            refine ⟨109400092130158553620154105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72933394753439035746769403 109400092130158553620154105)
            ·
              refine ⟨82050069097618915215115579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109400092130158553620154105 82050069097618915215115579)
              ·
                refine ⟨123075103646428372822673369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82050069097618915215115579 123075103646428372822673369)
                ·
                  refine ⟨92306327734821279617005027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123075103646428372822673369 92306327734821279617005027)
                  ·
                    refine ⟨138459491602231919425507541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92306327734821279617005027 138459491602231919425507541)
                    ·
                      refine ⟨3245144334427310611535333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138459491602231919425507541 3245144334427310611535333)
                      ·
                        rfl

theorem cell23_6319896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_6319896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319896 prefixEnd_6319896 := by exact prefixLift 6319896
  have htrace : WordTrace (prefixWord ++ tailWord_6319896) baseStart_6319896 baseEnd_6319896 := by
    simpa [prefixWord, tailWord_6319896, baseEnd_6319896] using wordTrace_append hprefix tailTrace_6319896
  have hstable : (prefixWord ++ tailWord_6319896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319896).length < 2 ^ (prefixWord ++ tailWord_6319896).sum := by decide
  have hdescent : baseEnd_6319896 < baseStart_6319896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319900 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_6319900 : Nat := 118140960795 + 6319900 * 2 ^ 59
def prefixEnd_6319900 : Nat := 4983230072969 + 3 ^ 40 * 6319900 * 2
def baseEnd_6319900 : Nat := 3245146388349928595885315

theorem tailTrace_6319900 : CollatzResearch.WordTrace tailWord_6319900 prefixEnd_6319900 3245146388349928595885315 := by
  unfold tailWord_6319900
  simp only [CollatzResearch.WordTrace]
  refine ⟨115252844902044563916714577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153670459869392751888952769 115252844902044563916714577)
  ·
    refine ⟨86439633676533422937535933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115252844902044563916714577 86439633676533422937535933)
    ·
      refine ⟨32414862628700033601575975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86439633676533422937535933 32414862628700033601575975)
      ·
        refine ⟨48622293943050050402363963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32414862628700033601575975 48622293943050050402363963)
        ·
          refine ⟨72933440914575075603545945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48622293943050050402363963 72933440914575075603545945)
          ·
            refine ⟨54700080685931306702659459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72933440914575075603545945 54700080685931306702659459)
            ·
              refine ⟨82050121028896960053989189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54700080685931306702659459 82050121028896960053989189)
              ·
                refine ⟨15384397692918180010122973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82050121028896960053989189 15384397692918180010122973)
                ·
                  refine ⟨5769149134844317503796115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15384397692918180010122973 5769149134844317503796115)
                  ·
                    refine ⟨8653723702266476255694173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5769149134844317503796115 8653723702266476255694173)
                    ·
                      refine ⟨3245146388349928595885315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8653723702266476255694173 3245146388349928595885315)
                      ·
                        rfl

theorem cell23_6319900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_6319900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319900 prefixEnd_6319900 := by exact prefixLift 6319900
  have htrace : WordTrace (prefixWord ++ tailWord_6319900) baseStart_6319900 baseEnd_6319900 := by
    simpa [prefixWord, tailWord_6319900, baseEnd_6319900] using wordTrace_append hprefix tailTrace_6319900
  have hstable : (prefixWord ++ tailWord_6319900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319900).length < 2 ^ (prefixWord ++ tailWord_6319900).sum := by decide
  have hdescent : baseEnd_6319900 < baseStart_6319900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319934 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_6319934 : Nat := 118140960795 + 6319934 * 2 ^ 59
def prefixEnd_6319934 : Nat := 4983230072969 + 3 ^ 40 * 6319934 * 2
def baseEnd_6319934 : Nat := 3245163846692181462860159

theorem tailTrace_6319934 : CollatzResearch.WordTrace tailWord_6319934 prefixEnd_6319934 3245163846692181462860159 := by
  unfold tailWord_6319934
  simp only [CollatzResearch.WordTrace]
  refine ⟨28813366235745743955020857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153671286590643967760111237 28813366235745743955020857)
  ·
    refine ⟨21610024676809307966265643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28813366235745743955020857 21610024676809307966265643)
    ·
      refine ⟨32415037015213961949398465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21610024676809307966265643 32415037015213961949398465)
      ·
        refine ⟨24311277761410471462048849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32415037015213961949398465 24311277761410471462048849)
        ·
          refine ⟨18233458321057853596536637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24311277761410471462048849 18233458321057853596536637)
          ·
            refine ⟨6837546870396695098701239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18233458321057853596536637 6837546870396695098701239)
            ·
              refine ⟨10256320305595042648051859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6837546870396695098701239 10256320305595042648051859)
              ·
                refine ⟨15384480458392563972077789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10256320305595042648051859 15384480458392563972077789)
                ·
                  refine ⟨5769180171897211489529171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15384480458392563972077789 5769180171897211489529171)
                  ·
                    refine ⟨8653770257845817234293757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5769180171897211489529171 8653770257845817234293757)
                    ·
                      refine ⟨3245163846692181462860159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8653770257845817234293757 3245163846692181462860159)
                      ·
                        rfl

theorem cell23_6319934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_6319934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319934 prefixEnd_6319934 := by exact prefixLift 6319934
  have htrace : WordTrace (prefixWord ++ tailWord_6319934) baseStart_6319934 baseEnd_6319934 := by
    simpa [prefixWord, tailWord_6319934, baseEnd_6319934] using wordTrace_append hprefix tailTrace_6319934
  have hstable : (prefixWord ++ tailWord_6319934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319934).length < 2 ^ (prefixWord ++ tailWord_6319934).sum := by decide
  have hdescent : baseEnd_6319934 < baseStart_6319934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319943 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_6319943 : Nat := 118140960795 + 6319943 * 2 ^ 59
def prefixEnd_6319943 : Nat := 4983230072969 + 3 ^ 40 * 6319943 * 2
def baseEnd_6319943 : Nat := 3245168468018071927647617

theorem tailTrace_6319943 : CollatzResearch.WordTrace tailWord_6319943 prefixEnd_6319943 3245168468018071927647617 := by
  unfold tailWord_6319943
  simp only [CollatzResearch.WordTrace]
  refine ⟨230507258142933346177244483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153671505428622230784829655 230507258142933346177244483)
  ·
    refine ⟨345760887214400019265866725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230507258142933346177244483 345760887214400019265866725)
    ·
      refine ⟨64830166352700003612350011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345760887214400019265866725 64830166352700003612350011)
      ·
        refine ⟨97245249529050005418525017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64830166352700003612350011 97245249529050005418525017)
        ·
          refine ⟨72933937146787504063893763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97245249529050005418525017 72933937146787504063893763)
          ·
            refine ⟨109400905720181256095840645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72933937146787504063893763 109400905720181256095840645)
            ·
              refine ⟨20512669822533985517970121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109400905720181256095840645 20512669822533985517970121)
              ·
                refine ⟨15384502366900489138477591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20512669822533985517970121 15384502366900489138477591)
                ·
                  refine ⟨23076753550350733707716387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15384502366900489138477591 23076753550350733707716387)
                  ·
                    refine ⟨34615130325526100561574581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23076753550350733707716387 34615130325526100561574581)
                    ·
                      refine ⟨3245168468018071927647617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34615130325526100561574581 3245168468018071927647617)
                      ·
                        rfl

theorem cell23_6319943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_6319943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319943 prefixEnd_6319943 := by exact prefixLift 6319943
  have htrace : WordTrace (prefixWord ++ tailWord_6319943) baseStart_6319943 baseEnd_6319943 := by
    simpa [prefixWord, tailWord_6319943, baseEnd_6319943] using wordTrace_append hprefix tailTrace_6319943
  have hstable : (prefixWord ++ tailWord_6319943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319943).length < 2 ^ (prefixWord ++ tailWord_6319943).sum := by decide
  have hdescent : baseEnd_6319943 < baseStart_6319943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319953 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_6319953 : Nat := 118140960795 + 6319953 * 2 ^ 59
def prefixEnd_6319953 : Nat := 4983230072969 + 3 ^ 40 * 6319953 * 2
def baseEnd_6319953 : Nat := 3245173602824616888522571

theorem tailTrace_6319953 : CollatzResearch.WordTrace tailWord_6319953 prefixEnd_6319953 3245173602824616888522571 := by
  unfold tailWord_6319953
  simp only [CollatzResearch.WordTrace]
  refine ⟨230507622872897117885108513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153671748581931411923405675 230507622872897117885108513)
  ·
    refine ⟨172880717154672838413831385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230507622872897117885108513 172880717154672838413831385)
    ·
      refine ⟨129660537866004628810373539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172880717154672838413831385 129660537866004628810373539)
      ·
        refine ⟨194490806799006943215560309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129660537866004628810373539 194490806799006943215560309)
        ·
          refine ⟨18233513137406900926458779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194490806799006943215560309 18233513137406900926458779)
          ·
            refine ⟨27350269706110351389688169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18233513137406900926458779 27350269706110351389688169)
            ·
              refine ⟨20512702279582763542266127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27350269706110351389688169 20512702279582763542266127)
              ·
                refine ⟨30769053419374145313399191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20512702279582763542266127 30769053419374145313399191)
                ·
                  refine ⟨46153580129061217970098787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30769053419374145313399191 46153580129061217970098787)
                  ·
                    refine ⟨69230370193591826955148181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46153580129061217970098787 69230370193591826955148181)
                    ·
                      refine ⟨3245173602824616888522571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69230370193591826955148181 3245173602824616888522571)
                      ·
                        rfl

theorem cell23_6319953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_6319953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319953 prefixEnd_6319953 := by exact prefixLift 6319953
  have htrace : WordTrace (prefixWord ++ tailWord_6319953) baseStart_6319953 baseEnd_6319953 := by
    simpa [prefixWord, tailWord_6319953, baseEnd_6319953] using wordTrace_append hprefix tailTrace_6319953
  have hstable : (prefixWord ++ tailWord_6319953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319953).length < 2 ^ (prefixWord ++ tailWord_6319953).sum := by decide
  have hdescent : baseEnd_6319953 < baseStart_6319953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319957 : List Nat := [1, 3, 2, 2, 2, 4, 1, 2, 1, 1, 4]
def baseStart_6319957 : Nat := 118140960795 + 6319957 * 2 ^ 59
def prefixEnd_6319957 : Nat := 4983230072969 + 3 ^ 40 * 6319957 * 2
def baseEnd_6319957 : Nat := 3245175656747234872872553

theorem tailTrace_6319957 : CollatzResearch.WordTrace tailWord_6319957 prefixEnd_6319957 3245175656747234872872553 := by
  unfold tailWord_6319957
  simp only [CollatzResearch.WordTrace]
  refine ⟨230507768764882626568254125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153671845843255084378836083 230507768764882626568254125)
  ·
    refine ⟨86440413286830984963095297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230507768764882626568254125 86440413286830984963095297)
    ·
      refine ⟨64830309965123238722321473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86440413286830984963095297 64830309965123238722321473)
      ·
        refine ⟨48622732473842429041741105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64830309965123238722321473 48622732473842429041741105)
        ·
          refine ⟨36467049355381821781305829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48622732473842429041741105 36467049355381821781305829)
          ·
            refine ⟨6837571754134091583994843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36467049355381821781305829 6837571754134091583994843)
            ·
              refine ⟨10256357631201137375992265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6837571754134091583994843 10256357631201137375992265)
              ·
                refine ⟨7692268223400853031994199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10256357631201137375992265 7692268223400853031994199)
                ·
                  refine ⟨11538402335101279547991299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7692268223400853031994199 11538402335101279547991299)
                  ·
                    refine ⟨17307603502651919321986949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11538402335101279547991299 17307603502651919321986949)
                    ·
                      refine ⟨3245175656747234872872553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17307603502651919321986949 3245175656747234872872553)
                      ·
                        rfl

theorem cell23_6319957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_6319957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319957 prefixEnd_6319957 := by exact prefixLift 6319957
  have htrace : WordTrace (prefixWord ++ tailWord_6319957) baseStart_6319957 baseEnd_6319957 := by
    simpa [prefixWord, tailWord_6319957, baseEnd_6319957] using wordTrace_append hprefix tailTrace_6319957
  have hstable : (prefixWord ++ tailWord_6319957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319957).length < 2 ^ (prefixWord ++ tailWord_6319957).sum := by decide
  have hdescent : baseEnd_6319957 < baseStart_6319957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6319970 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_6319970 : Nat := 118140960795 + 6319970 * 2 ^ 59
def prefixEnd_6319970 : Nat := 4983230072969 + 3 ^ 40 * 6319970 * 2
def baseEnd_6319970 : Nat := 3245182331995743322009993

theorem tailTrace_6319970 : CollatzResearch.WordTrace tailWord_6319970 prefixEnd_6319970 3245182331995743322009993 := by
  unfold tailWord_6319970
  simp only [CollatzResearch.WordTrace]
  refine ⟨57627060728458882447119341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153672161942557019858984909 57627060728458882447119341)
  ·
    refine ⟨21610147773172080917669753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57627060728458882447119341 21610147773172080917669753)
    ·
      refine ⟨16207610829879060688252315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21610147773172080917669753 16207610829879060688252315)
      ·
        refine ⟨24311416244818591032378473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16207610829879060688252315 24311416244818591032378473)
        ·
          refine ⟨18233562183613943274283855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24311416244818591032378473 18233562183613943274283855)
          ·
            refine ⟨27350343275420914911425783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18233562183613943274283855 27350343275420914911425783)
            ·
              refine ⟨41025514913131372367138675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27350343275420914911425783 41025514913131372367138675)
              ·
                refine ⟨61538272369697058550708013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41025514913131372367138675 61538272369697058550708013)
                ·
                  refine ⟨23076852138636396956515505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61538272369697058550708013 23076852138636396956515505)
                  ·
                    refine ⟨17307639103977297717386629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23076852138636396956515505 17307639103977297717386629)
                    ·
                      refine ⟨3245182331995743322009993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17307639103977297717386629 3245182331995743322009993)
                      ·
                        rfl

theorem cell23_6319970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_6319970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6319970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6319970 prefixEnd_6319970 := by exact prefixLift 6319970
  have htrace : WordTrace (prefixWord ++ tailWord_6319970) baseStart_6319970 baseEnd_6319970 := by
    simpa [prefixWord, tailWord_6319970, baseEnd_6319970] using wordTrace_append hprefix tailTrace_6319970
  have hstable : (prefixWord ++ tailWord_6319970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6319970).length < 2 ^ (prefixWord ++ tailWord_6319970).sum := by decide
  have hdescent : baseEnd_6319970 < baseStart_6319970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6319970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320000 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 5, 3, 2]
def baseStart_6320000 : Nat := 118140960795 + 6320000 * 2 ^ 59
def prefixEnd_6320000 : Nat := 4983230072969 + 3 ^ 40 * 6320000 * 2
def baseEnd_6320000 : Nat := 3245197736415378204634855

theorem tailTrace_6320000 : CollatzResearch.WordTrace tailWord_6320000 prefixEnd_6320000 3245197736415378204634855 := by
  unfold tailWord_6320000
  simp only [CollatzResearch.WordTrace]
  refine ⟨115254668551863422456034727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153672891402484563274712969 115254668551863422456034727)
  ·
    refine ⟨172882002827795133684052091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115254668551863422456034727 172882002827795133684052091)
    ·
      refine ⟨259323004241692700526078137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172882002827795133684052091 259323004241692700526078137)
      ·
        refine ⟨194492253181269525394558603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259323004241692700526078137 194492253181269525394558603)
        ·
          refine ⟨291738379771904288091837905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194492253181269525394558603 291738379771904288091837905)
          ·
            refine ⟨218803784828928216068878429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291738379771904288091837905 218803784828928216068878429)
            ·
              refine ⟨82051419310848081025829411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218803784828928216068878429 82051419310848081025829411)
              ·
                refine ⟨123077128966272121538744117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82051419310848081025829411 123077128966272121538744117)
                ·
                  refine ⟨11538480840588011394257261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123077128966272121538744117 11538480840588011394257261)
                  ·
                    refine ⟨4326930315220504272846473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11538480840588011394257261 4326930315220504272846473)
                    ·
                      refine ⟨3245197736415378204634855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326930315220504272846473 3245197736415378204634855)
                      ·
                        rfl

theorem cell23_6320000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5, 3, 2].length) (baseStart_6320000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320000 prefixEnd_6320000 := by exact prefixLift 6320000
  have htrace : WordTrace (prefixWord ++ tailWord_6320000) baseStart_6320000 baseEnd_6320000 := by
    simpa [prefixWord, tailWord_6320000, baseEnd_6320000] using wordTrace_append hprefix tailTrace_6320000
  have hstable : (prefixWord ++ tailWord_6320000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320000).length < 2 ^ (prefixWord ++ tailWord_6320000).sum := by decide
  have hdescent : baseEnd_6320000 < baseStart_6320000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320007 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_6320007 : Nat := 118140960795 + 6320007 * 2 ^ 59
def prefixEnd_6320007 : Nat := 4983230072969 + 3 ^ 40 * 6320007 * 2
def baseEnd_6320007 : Nat := 3245201330779959677247323

theorem tailTrace_6320007 : CollatzResearch.WordTrace tailWord_6320007 prefixEnd_6320007 3245201330779959677247323 := by
  unfold tailWord_6320007
  simp only [CollatzResearch.WordTrace]
  refine ⟨230509592414701485107574275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153673061609800990071716183 230509592414701485107574275)
  ·
    refine ⟨345764388622052227661361413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230509592414701485107574275 345764388622052227661361413)
    ·
      refine ⟨64830822866634792686505265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345764388622052227661361413 64830822866634792686505265)
      ·
        refine ⟨48623117149976094514878949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64830822866634792686505265 48623117149976094514878949)
        ·
          refine ⟨9116834465620517721539803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48623117149976094514878949 9116834465620517721539803)
          ·
            refine ⟨13675251698430776582309705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9116834465620517721539803 13675251698430776582309705)
            ·
              refine ⟨10256438773823082436732279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13675251698430776582309705 10256438773823082436732279)
              ·
                refine ⟨15384658160734623655098419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10256438773823082436732279 15384658160734623655098419)
                ·
                  refine ⟨23076987241101935482647629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15384658160734623655098419 23076987241101935482647629)
                  ·
                    refine ⟨8653870215413225805992861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23076987241101935482647629 8653870215413225805992861)
                    ·
                      refine ⟨3245201330779959677247323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8653870215413225805992861 3245201330779959677247323)
                      ·
                        rfl

theorem cell23_6320007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_6320007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320007 prefixEnd_6320007 := by exact prefixLift 6320007
  have htrace : WordTrace (prefixWord ++ tailWord_6320007) baseStart_6320007 baseEnd_6320007 := by
    simpa [prefixWord, tailWord_6320007, baseEnd_6320007] using wordTrace_append hprefix tailTrace_6320007
  have hstable : (prefixWord ++ tailWord_6320007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320007).length < 2 ^ (prefixWord ++ tailWord_6320007).sum := by decide
  have hdescent : baseEnd_6320007 < baseStart_6320007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320047 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 4, 2, 2]
def baseStart_6320047 : Nat := 118140960795 + 6320047 * 2 ^ 59
def prefixEnd_6320047 : Nat := 4983230072969 + 3 ^ 40 * 6320047 * 2
def baseEnd_6320047 : Nat := 3245221870006139520747139

theorem tailTrace_6320047 : CollatzResearch.WordTrace tailWord_6320047 prefixEnd_6320047 3245221870006139520747139 := by
  unfold tailWord_6320047
  simp only [CollatzResearch.WordTrace]
  refine ⟨230511051334556571939030395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153674034223037714626020263 230511051334556571939030395)
  ·
    refine ⟨345766577001834857908545593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230511051334556571939030395 345766577001834857908545593)
    ·
      refine ⟨259324932751376143431409195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345766577001834857908545593 259324932751376143431409195)
      ·
        refine ⟨388987399127064215147113793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259324932751376143431409195 388987399127064215147113793)
        ·
          refine ⟨291740549345298161360335345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388987399127064215147113793 291740549345298161360335345)
          ·
            refine ⟨218805412008973621020251509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291740549345298161360335345 218805412008973621020251509)
            ·
              refine ⟨20513007375841276970648579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 218805412008973621020251509 20513007375841276970648579)
              ·
                refine ⟨30769511063761915455972869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20513007375841276970648579 30769511063761915455972869)
                ·
                  refine ⟨5769283324455359147994913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30769511063761915455972869 5769283324455359147994913)
                  ·
                    refine ⟨4326962493341519360996185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5769283324455359147994913 4326962493341519360996185)
                    ·
                      refine ⟨3245221870006139520747139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4326962493341519360996185 3245221870006139520747139)
                      ·
                        rfl

theorem cell23_6320047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 2, 2].length) (baseStart_6320047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320047 prefixEnd_6320047 := by exact prefixLift 6320047
  have htrace : WordTrace (prefixWord ++ tailWord_6320047) baseStart_6320047 baseEnd_6320047 := by
    simpa [prefixWord, tailWord_6320047, baseEnd_6320047] using wordTrace_append hprefix tailTrace_6320047
  have hstable : (prefixWord ++ tailWord_6320047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320047).length < 2 ^ (prefixWord ++ tailWord_6320047).sum := by decide
  have hdescent : baseEnd_6320047 < baseStart_6320047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320100 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_6320100 : Nat := 118140960795 + 6320100 * 2 ^ 59
def prefixEnd_6320100 : Nat := 4983230072969 + 3 ^ 40 * 6320100 * 2
def baseEnd_6320100 : Nat := 1081749694826942604461465

theorem tailTrace_6320100 : CollatzResearch.WordTrace tailWord_6320100 prefixEnd_6320100 1081749694826942604461465 := by
  unfold tailWord_6320100
  simp only [CollatzResearch.WordTrace]
  refine ⟨115256492201682280995354877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153675322935576374660473169 115256492201682280995354877)
  ·
    refine ⟨43221184575630855373258079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115256492201682280995354877 43221184575630855373258079)
    ·
      refine ⟨64831776863446283059887119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43221184575630855373258079 64831776863446283059887119)
      ·
        refine ⟨97247665295169424589830679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64831776863446283059887119 97247665295169424589830679)
        ·
          refine ⟨145871497942754136884746019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97247665295169424589830679 145871497942754136884746019)
          ·
            refine ⟨218807246914131205327119029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145871497942754136884746019 218807246914131205327119029)
            ·
              refine ⟨20513179398199800499417409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 218807246914131205327119029 20513179398199800499417409)
              ·
                refine ⟨15384884548649850374563057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20513179398199800499417409 15384884548649850374563057)
                ·
                  refine ⟨11538663411487387780922293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15384884548649850374563057 11538663411487387780922293)
                  ·
                    refine ⟨1081749694826942604461465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11538663411487387780922293 1081749694826942604461465)
                    ·
                      rfl

theorem cell23_6320100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_6320100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320100 prefixEnd_6320100 := by exact prefixLift 6320100
  have htrace : WordTrace (prefixWord ++ tailWord_6320100) baseStart_6320100 baseEnd_6320100 := by
    simpa [prefixWord, tailWord_6320100, baseEnd_6320100] using wordTrace_append hprefix tailTrace_6320100
  have hstable : (prefixWord ++ tailWord_6320100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320100).length < 2 ^ (prefixWord ++ tailWord_6320100).sum := by decide
  have hdescent : baseEnd_6320100 < baseStart_6320100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320110 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_6320110 : Nat := 118140960795 + 6320110 * 2 ^ 59
def prefixEnd_6320110 : Nat := 4983230072969 + 3 ^ 40 * 6320110 * 2
def baseEnd_6320110 : Nat := 3245254219287372774259349

theorem tailTrace_6320110 : CollatzResearch.WordTrace tailWord_6320110 prefixEnd_6320110 3245254219287372774259349 := by
  unfold tailWord_6320110
  simp only [CollatzResearch.WordTrace]
  refine ⟨28814168641666041712321723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153675566088885555799049189 28814168641666041712321723)
  ·
    refine ⟨43221252962499062568482585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28814168641666041712321723 43221252962499062568482585)
    ·
      refine ⟨32415939721874296926361939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43221252962499062568482585 32415939721874296926361939)
      ·
        refine ⟨48623909582811445389542909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32415939721874296926361939 48623909582811445389542909)
        ·
          refine ⟨18233966093554292021078591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48623909582811445389542909 18233966093554292021078591)
          ·
            refine ⟨27350949140331438031617887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18233966093554292021078591 27350949140331438031617887)
            ·
              refine ⟨41026423710497157047426831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27350949140331438031617887 41026423710497157047426831)
              ·
                refine ⟨61539635565745735571140247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41026423710497157047426831 61539635565745735571140247)
                ·
                  refine ⟨92309453348618603356710371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61539635565745735571140247 92309453348618603356710371)
                  ·
                    refine ⟨138464180022927905035065557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92309453348618603356710371 138464180022927905035065557)
                    ·
                      refine ⟨3245254219287372774259349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138464180022927905035065557 3245254219287372774259349)
                      ·
                        rfl

theorem cell23_6320110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_6320110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320110 prefixEnd_6320110 := by exact prefixLift 6320110
  have htrace : WordTrace (prefixWord ++ tailWord_6320110) baseStart_6320110 baseEnd_6320110 := by
    simpa [prefixWord, tailWord_6320110, baseEnd_6320110] using wordTrace_append hprefix tailTrace_6320110
  have hstable : (prefixWord ++ tailWord_6320110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320110).length < 2 ^ (prefixWord ++ tailWord_6320110).sum := by decide
  have hdescent : baseEnd_6320110 < baseStart_6320110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320187 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 3, 1, 3]
def baseStart_6320187 : Nat := 118140960795 + 6320187 * 2 ^ 59
def prefixEnd_6320187 : Nat := 4983230072969 + 3 ^ 40 * 6320187 * 2
def baseEnd_6320187 : Nat := 3245293757297768972996495

theorem tailTrace_6320187 : CollatzResearch.WordTrace tailWord_6320187 prefixEnd_6320187 3245293757297768972996495 := by
  unfold tailWord_6320187
  simp only [CollatzResearch.WordTrace]
  refine ⟨230516157554049375849126815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153677438369366250566084543 230516157554049375849126815)
  ·
    refine ⟨345774236331074063773690223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230516157554049375849126815 345774236331074063773690223)
    ·
      refine ⟨518661354496611095660535335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345774236331074063773690223 518661354496611095660535335)
      ·
        refine ⟨777992031744916643490803003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518661354496611095660535335 777992031744916643490803003)
        ·
          refine ⟨1166988047617374965236204505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777992031744916643490803003 1166988047617374965236204505)
          ·
            refine ⟨875241035713031223927153379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166988047617374965236204505 875241035713031223927153379)
            ·
              refine ⟨1312861553569546835890730069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875241035713031223927153379 1312861553569546835890730069)
              ·
                refine ⟨15385096330893126983094493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1312861553569546835890730069 15385096330893126983094493)
                ·
                  refine ⟨5769411124084922618660435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15385096330893126983094493 5769411124084922618660435)
                  ·
                    refine ⟨8654116686127383927990653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5769411124084922618660435 8654116686127383927990653)
                    ·
                      refine ⟨3245293757297768972996495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8654116686127383927990653 3245293757297768972996495)
                      ·
                        rfl

theorem cell23_6320187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 1, 3].length) (baseStart_6320187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320187 prefixEnd_6320187 := by exact prefixLift 6320187
  have htrace : WordTrace (prefixWord ++ tailWord_6320187) baseStart_6320187 baseEnd_6320187 := by
    simpa [prefixWord, tailWord_6320187, baseEnd_6320187] using wordTrace_append hprefix tailTrace_6320187
  have hstable : (prefixWord ++ tailWord_6320187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320187).length < 2 ^ (prefixWord ++ tailWord_6320187).sum := by decide
  have hdescent : baseEnd_6320187 < baseStart_6320187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320198 : List Nat := [6, 1, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_6320198 : Nat := 118140960795 + 6320198 * 2 ^ 59
def prefixEnd_6320198 : Nat := 4983230072969 + 3 ^ 40 * 6320198 * 2
def baseEnd_6320198 : Nat := 1081766468528322809986315

theorem tailTrace_6320198 : CollatzResearch.WordTrace tailWord_6320198 prefixEnd_6320198 1081766468528322809986315 := by
  unfold tailWord_6320198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7203642461156547647743039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153677705838006349818518165 7203642461156547647743039)
  ·
    refine ⟨10805463691734821471614559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7203642461156547647743039 10805463691734821471614559)
    ·
      refine ⟨16208195537602232207421839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10805463691734821471614559 16208195537602232207421839)
      ·
        refine ⟨24312293306403348311132759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16208195537602232207421839 24312293306403348311132759)
        ·
          refine ⟨36468439959605022466699139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24312293306403348311132759 36468439959605022466699139)
          ·
            refine ⟨54702659939407533700048709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36468439959605022466699139 54702659939407533700048709)
            ·
              refine ⟨10256748738638912568759133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54702659939407533700048709 10256748738638912568759133)
              ·
                refine ⟨3846280776989592213284675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10256748738638912568759133 3846280776989592213284675)
                ·
                  refine ⟨5769421165484388319927013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846280776989592213284675 5769421165484388319927013)
                  ·
                    refine ⟨1081766468528322809986315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5769421165484388319927013 1081766468528322809986315)
                    ·
                      rfl

theorem cell23_6320198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_6320198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320198 prefixEnd_6320198 := by exact prefixLift 6320198
  have htrace : WordTrace (prefixWord ++ tailWord_6320198) baseStart_6320198 baseEnd_6320198 := by
    simpa [prefixWord, tailWord_6320198, baseEnd_6320198] using wordTrace_append hprefix tailTrace_6320198
  have hstable : (prefixWord ++ tailWord_6320198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320198).length < 2 ^ (prefixWord ++ tailWord_6320198).sum := by decide
  have hdescent : baseEnd_6320198 < baseStart_6320198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320214 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_6320214 : Nat := 118140960795 + 6320214 * 2 ^ 59
def prefixEnd_6320214 : Nat := 4983230072969 + 3 ^ 40 * 6320214 * 2
def baseEnd_6320214 : Nat := 3245307621275440367358871

theorem tailTrace_6320214 : CollatzResearch.WordTrace tailWord_6320214 prefixEnd_6320214 3245307621275440367358871 := by
  unfold tailWord_6320214
  simp only [CollatzResearch.WordTrace]
  refine ⟨14407321395309472466272481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153678094883301039640239797 14407321395309472466272481)
  ·
    refine ⟨10805491046482104349704361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14407321395309472466272481 10805491046482104349704361)
    ·
      refine ⟨8104118284861578262278271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10805491046482104349704361 8104118284861578262278271)
      ·
        refine ⟨12156177427292367393417407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8104118284861578262278271 12156177427292367393417407)
        ·
          refine ⟨18234266140938551090126111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12156177427292367393417407 18234266140938551090126111)
          ·
            refine ⟨27351399211407826635189167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18234266140938551090126111 27351399211407826635189167)
            ·
              refine ⟨41027098817111739952783751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27351399211407826635189167 41027098817111739952783751)
              ·
                refine ⟨61540648225667609929175627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41027098817111739952783751 61540648225667609929175627)
                ·
                  refine ⟨92310972338501414893763441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61540648225667609929175627 92310972338501414893763441)
                  ·
                    refine ⟨69233229253876061170322581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92310972338501414893763441 69233229253876061170322581)
                    ·
                      refine ⟨3245307621275440367358871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69233229253876061170322581 3245307621275440367358871)
                      ·
                        rfl

theorem cell23_6320214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_6320214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320214 prefixEnd_6320214 := by exact prefixLift 6320214
  have htrace : WordTrace (prefixWord ++ tailWord_6320214) baseStart_6320214 baseEnd_6320214 := by
    simpa [prefixWord, tailWord_6320214, baseEnd_6320214] using wordTrace_append hprefix tailTrace_6320214
  have hstable : (prefixWord ++ tailWord_6320214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320214).length < 2 ^ (prefixWord ++ tailWord_6320214).sum := by decide
  have hdescent : baseEnd_6320214 < baseStart_6320214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320221 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_6320221 : Nat := 118140960795 + 6320221 * 2 ^ 59
def prefixEnd_6320221 : Nat := 4983230072969 + 3 ^ 40 * 6320221 * 2
def baseEnd_6320221 : Nat := 3245311215640021839971339

theorem tailTrace_6320221 : CollatzResearch.WordTrace tailWord_6320221 prefixEnd_6320221 3245311215640021839971339 := by
  unfold tailWord_6320221
  simp only [CollatzResearch.WordTrace]
  refine ⟨230517397635926199655864517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153678265090617466437243011 230517397635926199655864517)
  ·
    refine ⟨43222012056736162435474597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 230517397635926199655864517 43222012056736162435474597)
    ·
      refine ⟨8104127260638030456651487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43222012056736162435474597 8104127260638030456651487)
      ·
        refine ⟨12156190890957045684977231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8104127260638030456651487 12156190890957045684977231)
        ·
          refine ⟨18234286336435568527465847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12156190890957045684977231 18234286336435568527465847)
          ·
            refine ⟨27351429504653352791198771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18234286336435568527465847 27351429504653352791198771)
            ·
              refine ⟨41027144256980029186798157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27351429504653352791198771 41027144256980029186798157)
              ·
                refine ⟨15385179096367510945049309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41027144256980029186798157 15385179096367510945049309)
                ·
                  refine ⟨5769442161137816604393491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15385179096367510945049309 5769442161137816604393491)
                  ·
                    refine ⟨8654163241706724906590237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5769442161137816604393491 8654163241706724906590237)
                    ·
                      refine ⟨3245311215640021839971339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8654163241706724906590237 3245311215640021839971339)
                      ·
                        rfl

theorem cell23_6320221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_6320221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320221 prefixEnd_6320221 := by exact prefixLift 6320221
  have htrace : WordTrace (prefixWord ++ tailWord_6320221) baseStart_6320221 baseEnd_6320221 := by
    simpa [prefixWord, tailWord_6320221, baseEnd_6320221] using wordTrace_append hprefix tailTrace_6320221
  have hstable : (prefixWord ++ tailWord_6320221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320221).length < 2 ^ (prefixWord ++ tailWord_6320221).sum := by decide
  have hdescent : baseEnd_6320221 < baseStart_6320221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320264 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_6320264 : Nat := 118140960795 + 6320264 * 2 ^ 59
def prefixEnd_6320264 : Nat := 4983230072969 + 3 ^ 40 * 6320264 * 2
def baseEnd_6320264 : Nat := 3245333295308165171733641

theorem tailTrace_6320264 : CollatzResearch.WordTrace tailWord_6320264 prefixEnd_6320264 3245333295308165171733641 := by
  unfold tailWord_6320264
  simp only [CollatzResearch.WordTrace]
  refine ⟨115259482987385208999839923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153679310649846945333119897 115259482987385208999839923)
  ·
    refine ⟨172889224481077813499759885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115259482987385208999839923 172889224481077813499759885)
    ·
      refine ⟨64833459180404180062409957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172889224481077813499759885 64833459180404180062409957)
      ·
        refine ⟨12156273596325783761701867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64833459180404180062409957 12156273596325783761701867)
        ·
          refine ⟨18234410394488675642552801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12156273596325783761701867 18234410394488675642552801)
          ·
            refine ⟨13675807795866506731914601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18234410394488675642552801 13675807795866506731914601)
            ·
              refine ⟨10256855846899880048935951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13675807795866506731914601 10256855846899880048935951)
              ·
                refine ⟨15385283770349820073403927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10256855846899880048935951 15385283770349820073403927)
                ·
                  refine ⟨23077925655524730110105891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15385283770349820073403927 23077925655524730110105891)
                  ·
                    refine ⟨34616888483287095165158837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23077925655524730110105891 34616888483287095165158837)
                    ·
                      refine ⟨3245333295308165171733641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34616888483287095165158837 3245333295308165171733641)
                      ·
                        rfl

theorem cell23_6320264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_6320264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320264 prefixEnd_6320264 := by exact prefixLift 6320264
  have htrace : WordTrace (prefixWord ++ tailWord_6320264) baseStart_6320264 baseEnd_6320264 := by
    simpa [prefixWord, tailWord_6320264, baseEnd_6320264] using wordTrace_append hprefix tailTrace_6320264
  have hstable : (prefixWord ++ tailWord_6320264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320264).length < 2 ^ (prefixWord ++ tailWord_6320264).sum := by decide
  have hdescent : baseEnd_6320264 < baseStart_6320264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320337 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 2, 4, 3]
def baseStart_6320337 : Nat := 118140960795 + 6320337 * 2 ^ 59
def prefixEnd_6320337 : Nat := 4983230072969 + 3 ^ 40 * 6320337 * 2
def baseEnd_6320337 : Nat := 3245370779395943386120805

theorem tailTrace_6320337 : CollatzResearch.WordTrace tailWord_6320337 prefixEnd_6320337 3245370779395943386120805 := by
  unfold tailWord_6320337
  simp only [CollatzResearch.WordTrace]
  refine ⟨230521628503505951467087265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153681085669003967644724843 230521628503505951467087265)
  ·
    refine ⟨172891221377629463600315449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230521628503505951467087265 172891221377629463600315449)
    ·
      refine ⟨129668416033222097700236587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172891221377629463600315449 129668416033222097700236587)
      ·
        refine ⟨194502624049833146550354881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129668416033222097700236587 194502624049833146550354881)
        ·
          refine ⟨145876968037374859912766161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194502624049833146550354881 145876968037374859912766161)
          ·
            refine ⟨109407726028031144934574621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145876968037374859912766161 109407726028031144934574621)
            ·
              refine ⟨41027897260511679350465483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109407726028031144934574621 41027897260511679350465483)
              ·
                refine ⟨61541845890767519025698225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41027897260511679350465483 61541845890767519025698225)
                ·
                  refine ⟨46156384418075639269273669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61541845890767519025698225 46156384418075639269273669)
                  ·
                    refine ⟨8654322078389182362988813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46156384418075639269273669 8654322078389182362988813)
                    ·
                      refine ⟨3245370779395943386120805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8654322078389182362988813 3245370779395943386120805)
                      ·
                        rfl

theorem cell23_6320337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_6320337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320337 prefixEnd_6320337 := by exact prefixLift 6320337
  have htrace : WordTrace (prefixWord ++ tailWord_6320337) baseStart_6320337 baseEnd_6320337 := by
    simpa [prefixWord, tailWord_6320337, baseEnd_6320337] using wordTrace_append hprefix tailTrace_6320337
  have hstable : (prefixWord ++ tailWord_6320337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320337).length < 2 ^ (prefixWord ++ tailWord_6320337).sum := by decide
  have hdescent : baseEnd_6320337 < baseStart_6320337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320357 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 9]
def baseStart_6320357 : Nat := 118140960795 + 6320357 * 2 ^ 59
def prefixEnd_6320357 : Nat := 4983230072969 + 3 ^ 40 * 6320357 * 2
def baseEnd_6320357 : Nat := 360597894334337034207857

theorem tailTrace_6320357 : CollatzResearch.WordTrace tailWord_6320357 prefixEnd_6320357 360597894334337034207857 := by
  unfold tailWord_6320357
  simp only [CollatzResearch.WordTrace]
  refine ⟨230522357963433494882815325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153681571975622329921876883 230522357963433494882815325)
  ·
    refine ⟨86445884236287560581055747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230522357963433494882815325 86445884236287560581055747)
    ·
      refine ⟨129668826354431340871583621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86445884236287560581055747 129668826354431340871583621)
      ·
        refine ⟨24312904941455876413421929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129668826354431340871583621 24312904941455876413421929)
        ·
          refine ⟨18234678706091907310066447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24312904941455876413421929 18234678706091907310066447)
          ·
            refine ⟨27352018059137860965099671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18234678706091907310066447 27352018059137860965099671)
            ·
              refine ⟨41028027088706791447649507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27352018059137860965099671 41028027088706791447649507)
              ·
                refine ⟨61542040633060187171474261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41028027088706791447649507 61542040633060187171474261)
                ·
                  refine ⟨360597894334337034207857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61542040633060187171474261 360597894334337034207857)
                  ·
                    rfl

theorem cell23_6320357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_6320357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320357 prefixEnd_6320357 := by exact prefixLift 6320357
  have htrace : WordTrace (prefixWord ++ tailWord_6320357) baseStart_6320357 baseEnd_6320357 := by
    simpa [prefixWord, tailWord_6320357, baseEnd_6320357] using wordTrace_append hprefix tailTrace_6320357
  have hstable : (prefixWord ++ tailWord_6320357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320357).length < 2 ^ (prefixWord ++ tailWord_6320357).sum := by decide
  have hdescent : baseEnd_6320357 < baseStart_6320357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320387 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 4, 5]
def baseStart_6320387 : Nat := 118140960795 + 6320387 * 2 ^ 59
def prefixEnd_6320387 : Nat := 4983230072969 + 3 ^ 40 * 6320387 * 2
def baseEnd_6320387 : Nat := 1081798817809556063498525

theorem tailTrace_6320387 : CollatzResearch.WordTrace tailWord_6320387 prefixEnd_6320387 1081798817809556063498525 := by
  unfold tailWord_6320387
  simp only [CollatzResearch.WordTrace]
  refine ⟨230523452153324810006407415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153682301435549873337604943 230523452153324810006407415)
  ·
    refine ⟨345785178229987215009611123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230523452153324810006407415 345785178229987215009611123)
    ·
      refine ⟨518677767344980822514416685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345785178229987215009611123 518677767344980822514416685)
      ·
        refine ⟨194504162754367808442906257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 518677767344980822514416685 194504162754367808442906257)
        ·
          refine ⟨145878122065775856332179693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194504162754367808442906257 145878122065775856332179693)
          ·
            refine ⟨54704295774665946124567385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145878122065775856332179693 54704295774665946124567385)
            ·
              refine ⟨41028221830999459593425539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54704295774665946124567385 41028221830999459593425539)
              ·
                refine ⟨61542332746499189390138309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41028221830999459593425539 61542332746499189390138309)
                ·
                  refine ⟨11539187389968598010650933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61542332746499189390138309 11539187389968598010650933)
                  ·
                    refine ⟨1081798817809556063498525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11539187389968598010650933 1081798817809556063498525)
                    ·
                      rfl

theorem cell23_6320387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 5].length) (baseStart_6320387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320387 prefixEnd_6320387 := by exact prefixLift 6320387
  have htrace : WordTrace (prefixWord ++ tailWord_6320387) baseStart_6320387 baseEnd_6320387 := by
    simpa [prefixWord, tailWord_6320387, baseEnd_6320387] using wordTrace_append hprefix tailTrace_6320387
  have hstable : (prefixWord ++ tailWord_6320387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320387).length < 2 ^ (prefixWord ++ tailWord_6320387).sum := by decide
  have hdescent : baseEnd_6320387 < baseStart_6320387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320391 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 7]
def baseStart_6320391 : Nat := 118140960795 + 6320391 * 2 ^ 59
def prefixEnd_6320391 : Nat := 4983230072969 + 3 ^ 40 * 6320391 * 2
def baseEnd_6320391 : Nat := 360599834150142908316173

theorem tailTrace_6320391 : CollatzResearch.WordTrace tailWord_6320391 prefixEnd_6320391 360599834150142908316173 := by
  unfold tailWord_6320391
  simp only [CollatzResearch.WordTrace]
  refine ⟨230523598045310318689553027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153682398696873545793035351 230523598045310318689553027)
  ·
    refine ⟨345785397067965478034329541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230523598045310318689553027 345785397067965478034329541)
    ·
      refine ⟨64834761950243527131436789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345785397067965478034329541 64834761950243527131436789)
      ·
        refine ⟨6078258932835330668572199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64834761950243527131436789 6078258932835330668572199)
        ·
          refine ⟨9117388399252996002858299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6078258932835330668572199 9117388399252996002858299)
          ·
            refine ⟨13676082598879494004287449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9117388399252996002858299 13676082598879494004287449)
            ·
              refine ⟨10257061949159620503215587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13676082598879494004287449 10257061949159620503215587)
              ·
                refine ⟨15385592923739430754823381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10257061949159620503215587 15385592923739430754823381)
                ·
                  refine ⟨360599834150142908316173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15385592923739430754823381 360599834150142908316173)
                  ·
                    rfl

theorem cell23_6320391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 7].length) (baseStart_6320391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320391 prefixEnd_6320391 := by exact prefixLift 6320391
  have htrace : WordTrace (prefixWord ++ tailWord_6320391) baseStart_6320391 baseEnd_6320391 := by
    simpa [prefixWord, tailWord_6320391, baseEnd_6320391] using wordTrace_append hprefix tailTrace_6320391
  have hstable : (prefixWord ++ tailWord_6320391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320391).length < 2 ^ (prefixWord ++ tailWord_6320391).sum := by decide
  have hdescent : baseEnd_6320391 < baseStart_6320391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320394 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2]
def baseStart_6320394 : Nat := 118140960795 + 6320394 * 2 ^ 59
def prefixEnd_6320394 : Nat := 4983230072969 + 3 ^ 40 * 6320394 * 2
def baseEnd_6320394 : Nat := 3245400047793249663108043

theorem tailTrace_6320394 : CollatzResearch.WordTrace tailWord_6320394 prefixEnd_6320394 3245400047793249663108043 := by
  unfold tailWord_6320394
  simp only [CollatzResearch.WordTrace]
  refine ⟨57630926866074862550478059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153682471642866300134608157 57630926866074862550478059)
  ·
    refine ⟨86446390299112293825717089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57630926866074862550478059 86446390299112293825717089)
    ·
      refine ⟨64834792724334220369287817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86446390299112293825717089 64834792724334220369287817)
      ·
        refine ⟨48626094543250665276965863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64834792724334220369287817 48626094543250665276965863)
        ·
          refine ⟨72939141814875997915448795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48626094543250665276965863 72939141814875997915448795)
          ·
            refine ⟨109408712722313996873173193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72939141814875997915448795 109408712722313996873173193)
            ·
              refine ⟨82056534541735497654879895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109408712722313996873173193 82056534541735497654879895)
              ·
                refine ⟨123084801812603246482319843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82056534541735497654879895 123084801812603246482319843)
                ·
                  refine ⟨184627202718904869723479765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123084801812603246482319843 184627202718904869723479765)
                  ·
                    refine ⟨4327200063724332884144057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 184627202718904869723479765 4327200063724332884144057)
                    ·
                      refine ⟨3245400047793249663108043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4327200063724332884144057 3245400047793249663108043)
                      ·
                        rfl

theorem cell23_6320394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_6320394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320394 prefixEnd_6320394 := by exact prefixLift 6320394
  have htrace : WordTrace (prefixWord ++ tailWord_6320394) baseStart_6320394 baseEnd_6320394 := by
    simpa [prefixWord, tailWord_6320394, baseEnd_6320394] using wordTrace_append hprefix tailTrace_6320394
  have hstable : (prefixWord ++ tailWord_6320394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320394).length < 2 ^ (prefixWord ++ tailWord_6320394).sum := by decide
  have hdescent : baseEnd_6320394 < baseStart_6320394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320441 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6320441 : Nat := 118140960795 + 6320441 * 2 ^ 59
def prefixEnd_6320441 : Nat := 4983230072969 + 3 ^ 40 * 6320441 * 2
def baseEnd_6320441 : Nat := 3245424181384010979220327

theorem tailTrace_6320441 : CollatzResearch.WordTrace tailWord_6320441 prefixEnd_6320441 3245424181384010979220327 := by
  unfold tailWord_6320441
  simp only [CollatzResearch.WordTrace]
  refine ⟨230525421695129177228873177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153683614463419451485915451 230525421695129177228873177)
  ·
    refine ⟨172894066271346882921654883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230525421695129177228873177 172894066271346882921654883)
    ·
      refine ⟨259341099407020324382482325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172894066271346882921654883 259341099407020324382482325)
      ·
        refine ⟨12156614034704077705428859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 259341099407020324382482325 12156614034704077705428859)
        ·
          refine ⟨18234921052056116558143289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12156614034704077705428859 18234921052056116558143289)
          ·
            refine ⟨13676190789042087418607467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18234921052056116558143289 13676190789042087418607467)
            ·
              refine ⟨20514286183563131127911201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13676190789042087418607467 20514286183563131127911201)
              ·
                refine ⟨15385714637672348345933401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20514286183563131127911201 15385714637672348345933401)
                ·
                  refine ⟨11539285978254261259450051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15385714637672348345933401 11539285978254261259450051)
                  ·
                    refine ⟨17308928967381391889175077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11539285978254261259450051 17308928967381391889175077)
                    ·
                      refine ⟨3245424181384010979220327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17308928967381391889175077 3245424181384010979220327)
                      ·
                        rfl

theorem cell23_6320441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6320441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320441 prefixEnd_6320441 := by exact prefixLift 6320441
  have htrace : WordTrace (prefixWord ++ tailWord_6320441) baseStart_6320441 baseEnd_6320441 := by
    simpa [prefixWord, tailWord_6320441, baseEnd_6320441] using wordTrace_append hprefix tailTrace_6320441
  have hstable : (prefixWord ++ tailWord_6320441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320441).length < 2 ^ (prefixWord ++ tailWord_6320441).sum := by decide
  have hdescent : baseEnd_6320441 < baseStart_6320441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320447 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 8]
def baseStart_6320447 : Nat := 118140960795 + 6320447 * 2 ^ 59
def prefixEnd_6320447 : Nat := 4983230072969 + 3 ^ 40 * 6320447 * 2
def baseEnd_6320447 : Nat := 360603029140881995082811

theorem tailTrace_6320447 : CollatzResearch.WordTrace tailWord_6320447 prefixEnd_6320447 360603029140881995082811 := by
  unfold tailWord_6320447
  simp only [CollatzResearch.WordTrace]
  refine ⟨230525640533107440253591595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153683760355404960169061063 230525640533107440253591595)
  ·
    refine ⟨345788460799661160380387393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230525640533107440253591595 345788460799661160380387393)
    ·
      refine ⟨259341345599745870285290545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345788460799661160380387393 259341345599745870285290545)
      ·
        refine ⟨194506009199809402713967909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259341345599745870285290545 194506009199809402713967909)
        ·
          refine ⟨36469876724964263008868983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194506009199809402713967909 36469876724964263008868983)
          ·
            refine ⟨54704815087446394513303475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36469876724964263008868983 54704815087446394513303475)
            ·
              refine ⟨82057222631169591769955213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54704815087446394513303475 82057222631169591769955213)
              ·
                refine ⟨30771458486688596913733205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82057222631169591769955213 30771458486688596913733205)
                ·
                  refine ⟨360603029140881995082811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30771458486688596913733205 360603029140881995082811)
                  ·
                    rfl

theorem cell23_6320447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 8].length) (baseStart_6320447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320447 prefixEnd_6320447 := by exact prefixLift 6320447
  have htrace : WordTrace (prefixWord ++ tailWord_6320447) baseStart_6320447 baseEnd_6320447 := by
    simpa [prefixWord, tailWord_6320447, baseEnd_6320447] using wordTrace_append hprefix tailTrace_6320447
  have hstable : (prefixWord ++ tailWord_6320447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320447).length < 2 ^ (prefixWord ++ tailWord_6320447).sum := by decide
  have hdescent : baseEnd_6320447 < baseStart_6320447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320451 : List Nat := [1, 1, 1, 3, 1, 3, 2, 6, 1, 4]
def baseStart_6320451 : Nat := 118140960795 + 6320451 * 2 ^ 59
def prefixEnd_6320451 : Nat := 4983230072969 + 3 ^ 40 * 6320451 * 2
def baseEnd_6320451 : Nat := 1081809772063518646698427

theorem tailTrace_6320451 : CollatzResearch.WordTrace tailWord_6320451 prefixEnd_6320451 1081809772063518646698427 := by
  unfold tailWord_6320451
  simp only [CollatzResearch.WordTrace]
  refine ⟨230525786425092948936737207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153683857616728632624491471 230525786425092948936737207)
  ·
    refine ⟨345788679637639423405105811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230525786425092948936737207 345788679637639423405105811)
    ·
      refine ⟨518683019456459135107658717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345788679637639423405105811 518683019456459135107658717)
      ·
        refine ⟨194506132296172175665372019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 518683019456459135107658717 194506132296172175665372019)
        ·
          refine ⟨291759198444258263498058029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194506132296172175665372019 291759198444258263498058029)
          ·
            refine ⟨109409699416596848811771761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291759198444258263498058029 109409699416596848811771761)
            ·
              refine ⟨82057274562447636608828821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109409699416596848811771761 82057274562447636608828821)
              ·
                refine ⟨3846434745114732966038851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82057274562447636608828821 3846434745114732966038851)
                ·
                  refine ⟨5769652117672099449058277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846434745114732966038851 5769652117672099449058277)
                  ·
                    refine ⟨1081809772063518646698427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5769652117672099449058277 1081809772063518646698427)
                    ·
                      rfl

theorem cell23_6320451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 1, 4].length) (baseStart_6320451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320451 prefixEnd_6320451 := by exact prefixLift 6320451
  have htrace : WordTrace (prefixWord ++ tailWord_6320451) baseStart_6320451 baseEnd_6320451 := by
    simpa [prefixWord, tailWord_6320451, baseEnd_6320451] using wordTrace_append hprefix tailTrace_6320451
  have hstable : (prefixWord ++ tailWord_6320451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320451).length < 2 ^ (prefixWord ++ tailWord_6320451).sum := by decide
  have hdescent : baseEnd_6320451 < baseStart_6320451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320464 : List Nat := [2, 1, 1, 1, 1, 7, 1, 3, 6]
def baseStart_6320464 : Nat := 118140960795 + 6320464 * 2 ^ 59
def prefixEnd_6320464 : Nat := 4983230072969 + 3 ^ 40 * 6320464 * 2
def baseEnd_6320464 : Nat := 360603999048784932136969

theorem tailTrace_6320464 : CollatzResearch.WordTrace tailWord_6320464 prefixEnd_6320464 360603999048784932136969 := by
  unfold tailWord_6320464
  simp only [CollatzResearch.WordTrace]
  refine ⟨115263130287022926078480223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153684173716030568104640297 115263130287022926078480223)
  ·
    refine ⟨172894695430534389117720335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115263130287022926078480223 172894695430534389117720335)
    ·
      refine ⟨259342043145801583676580503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172894695430534389117720335 259342043145801583676580503)
      ·
        refine ⟨389013064718702375514870755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259342043145801583676580503 389013064718702375514870755)
        ·
          refine ⟨583519597078053563272306133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389013064718702375514870755 583519597078053563272306133)
          ·
            refine ⟨13676240556516880389194675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 583519597078053563272306133 13676240556516880389194675)
            ·
              refine ⟨20514360834775320583792013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13676240556516880389194675 20514360834775320583792013)
              ·
                refine ⟨7692885313040745218922005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20514360834775320583792013 7692885313040745218922005)
                ·
                  refine ⟨360603999048784932136969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7692885313040745218922005 360603999048784932136969)
                  ·
                    rfl

theorem cell23_6320464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 6].length) (baseStart_6320464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320464 prefixEnd_6320464 := by exact prefixLift 6320464
  have htrace : WordTrace (prefixWord ++ tailWord_6320464) baseStart_6320464 baseEnd_6320464 := by
    simpa [prefixWord, tailWord_6320464, baseEnd_6320464] using wordTrace_append hprefix tailTrace_6320464
  have hstable : (prefixWord ++ tailWord_6320464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320464).length < 2 ^ (prefixWord ++ tailWord_6320464).sum := by decide
  have hdescent : baseEnd_6320464 < baseStart_6320464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320502 : List Nat := [5, 1, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_6320502 : Nat := 118140960795 + 6320502 * 2 ^ 59
def prefixEnd_6320502 : Nat := 4983230072969 + 3 ^ 40 * 6320502 * 2
def baseEnd_6320502 : Nat := 1081818501234645080185849

theorem tailTrace_6320502 : CollatzResearch.WordTrace tailWord_6320502 prefixEnd_6320502 1081818501234645080185849 := by
  unfold tailWord_6320502
  simp only [CollatzResearch.WordTrace]
  refine ⟨14407977909244261540427735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153685097698605456431229173 14407977909244261540427735)
  ·
    refine ⟨21611966863866392310641603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14407977909244261540427735 21611966863866392310641603)
    ·
      refine ⟨32417950295799588465962405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21611966863866392310641603 32417950295799588465962405)
      ·
        refine ⟨6078365680462422837367951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32417950295799588465962405 6078365680462422837367951)
        ·
          refine ⟨9117548520693634256051927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6078365680462422837367951 9117548520693634256051927)
          ·
            refine ⟨13676322781040451384077891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9117548520693634256051927 13676322781040451384077891)
            ·
              refine ⟨20514484171560677076116837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13676322781040451384077891 20514484171560677076116837)
              ·
                refine ⟨3846465782167626951771907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20514484171560677076116837 3846465782167626951771907)
                ·
                  refine ⟨5769698673251440427657861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846465782167626951771907 5769698673251440427657861)
                  ·
                    refine ⟨1081818501234645080185849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5769698673251440427657861 1081818501234645080185849)
                    ·
                      rfl

theorem cell23_6320502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_6320502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320502 prefixEnd_6320502 := by exact prefixLift 6320502
  have htrace : WordTrace (prefixWord ++ tailWord_6320502) baseStart_6320502 baseEnd_6320502 := by
    simpa [prefixWord, tailWord_6320502, baseEnd_6320502] using wordTrace_append hprefix tailTrace_6320502
  have hstable : (prefixWord ++ tailWord_6320502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320502).length < 2 ^ (prefixWord ++ tailWord_6320502).sum := by decide
  have hdescent : baseEnd_6320502 < baseStart_6320502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320524 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 1, 6]
def baseStart_6320524 : Nat := 118140960795 + 6320524 * 2 ^ 59
def prefixEnd_6320524 : Nat := 4983230072969 + 3 ^ 40 * 6320524 * 2
def baseEnd_6320524 : Nat := 1081822266759444718160815

theorem tailTrace_6320524 : CollatzResearch.WordTrace tailWord_6320524 prefixEnd_6320524 1081822266759444718160815 := by
  unfold tailWord_6320524
  simp only [CollatzResearch.WordTrace]
  refine ⟨115264224476914241202072313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153685632635885654936096417 115264224476914241202072313)
  ·
    refine ⟨86448168357685680901554235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115264224476914241202072313 86448168357685680901554235)
    ·
      refine ⟨129672252536528521352331353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86448168357685680901554235 129672252536528521352331353)
      ·
        refine ⟨97254189402396391014248515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129672252536528521352331353 97254189402396391014248515)
        ·
          refine ⟨145881284103594586521372773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97254189402396391014248515 145881284103594586521372773)
          ·
            refine ⟨27352740769423984972757395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145881284103594586521372773 27352740769423984972757395)
            ·
              refine ⟨41029111154135977459136093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27352740769423984972757395 41029111154135977459136093)
              ·
                refine ⟨15385916682800991547176035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41029111154135977459136093 15385916682800991547176035)
                ·
                  refine ⟨23078875024201487320764053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15385916682800991547176035 23078875024201487320764053)
                  ·
                    refine ⟨1081822266759444718160815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23078875024201487320764053 1081822266759444718160815)
                    ·
                      rfl

theorem cell23_6320524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_6320524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320524 prefixEnd_6320524 := by exact prefixLift 6320524
  have htrace : WordTrace (prefixWord ++ tailWord_6320524) baseStart_6320524 baseEnd_6320524 := by
    simpa [prefixWord, tailWord_6320524, baseEnd_6320524] using wordTrace_append hprefix tailTrace_6320524
  have hstable : (prefixWord ++ tailWord_6320524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320524).length < 2 ^ (prefixWord ++ tailWord_6320524).sum := by decide
  have hdescent : baseEnd_6320524 < baseStart_6320524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320542 : List Nat := [4, 3, 1, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_6320542 : Nat := 118140960795 + 6320542 * 2 ^ 59
def prefixEnd_6320542 : Nat := 4983230072969 + 3 ^ 40 * 6320542 * 2
def baseEnd_6320542 : Nat := 3245476042930115084057363

theorem tailTrace_6320542 : CollatzResearch.WordTrace tailWord_6320542 prefixEnd_6320542 3245476042930115084057363 := by
  unfold tailWord_6320542
  simp only [CollatzResearch.WordTrace]
  refine ⟨28816138183470408934787485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153686070311842180985533253 28816138183470408934787485)
  ·
    refine ⟨10806051818801403350545307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28816138183470408934787485 10806051818801403350545307)
    ·
      refine ⟨16209077728202105025817961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10806051818801403350545307 16209077728202105025817961)
      ·
        refine ⟨12156808296151578769363471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16209077728202105025817961 12156808296151578769363471)
        ·
          refine ⟨18235212444227368154045207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12156808296151578769363471 18235212444227368154045207)
          ·
            refine ⟨27352818666341052231067811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18235212444227368154045207 27352818666341052231067811)
            ·
              refine ⟨41029227999511578346601717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27352818666341052231067811 41029227999511578346601717)
              ·
                refine ⟨3846490124954210469993911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41029227999511578346601717 3846490124954210469993911)
                ·
                  refine ⟨5769735187431315704990867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846490124954210469993911 5769735187431315704990867)
                  ·
                    refine ⟨8654602781146973557486301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5769735187431315704990867 8654602781146973557486301)
                    ·
                      refine ⟨3245476042930115084057363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8654602781146973557486301 3245476042930115084057363)
                      ·
                        rfl

theorem cell23_6320542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_6320542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320542 prefixEnd_6320542 := by exact prefixLift 6320542
  have htrace : WordTrace (prefixWord ++ tailWord_6320542) baseStart_6320542 baseEnd_6320542 := by
    simpa [prefixWord, tailWord_6320542, baseEnd_6320542] using wordTrace_append hprefix tailTrace_6320542
  have hstable : (prefixWord ++ tailWord_6320542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320542).length < 2 ^ (prefixWord ++ tailWord_6320542).sum := by decide
  have hdescent : baseEnd_6320542 < baseStart_6320542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320548 : List Nat := [2, 3, 1, 2, 1, 1, 6, 1, 1, 1, 4]
def baseStart_6320548 : Nat := 118140960795 + 6320548 * 2 ^ 59
def prefixEnd_6320548 : Nat := 4983230072969 + 3 ^ 40 * 6320548 * 2
def baseEnd_6320548 : Nat := 3245479123814042060582335

theorem tailTrace_6320548 : CollatzResearch.WordTrace tailWord_6320548 prefixEnd_6320548 3245479123814042060582335 := by
  unfold tailWord_6320548
  simp only [CollatzResearch.WordTrace]
  refine ⟨115264662152870767251509149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153686216203827689668678865 115264662152870767251509149)
  ·
    refine ⟨43224248307326537719315931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115264662152870767251509149 43224248307326537719315931)
    ·
      refine ⟨64836372460989806578973897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43224248307326537719315931 64836372460989806578973897)
      ·
        refine ⟨48627279345742354934230423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64836372460989806578973897 48627279345742354934230423)
        ·
          refine ⟨72940919018613532401345635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48627279345742354934230423 72940919018613532401345635)
          ·
            refine ⟨109411378527920298602018453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72940919018613532401345635 109411378527920298602018453)
            ·
              refine ⟨5128658368496263996969615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109411378527920298602018453 5128658368496263996969615)
              ·
                refine ⟨7692987552744395995454423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5128658368496263996969615 7692987552744395995454423)
                ·
                  refine ⟨11539481329116593993181635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7692987552744395995454423 11539481329116593993181635)
                  ·
                    refine ⟨17309221993674890989772453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11539481329116593993181635 17309221993674890989772453)
                    ·
                      refine ⟨3245479123814042060582335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17309221993674890989772453 3245479123814042060582335)
                      ·
                        rfl

theorem cell23_6320548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_6320548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320548 prefixEnd_6320548 := by exact prefixLift 6320548
  have htrace : WordTrace (prefixWord ++ tailWord_6320548) baseStart_6320548 baseEnd_6320548 := by
    simpa [prefixWord, tailWord_6320548, baseEnd_6320548] using wordTrace_append hprefix tailTrace_6320548
  have hstable : (prefixWord ++ tailWord_6320548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320548).length < 2 ^ (prefixWord ++ tailWord_6320548).sum := by decide
  have hdescent : baseEnd_6320548 < baseStart_6320548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320588 : List Nat := [2, 2, 1, 4, 3, 2, 2, 7]
def baseStart_6320588 : Nat := 118140960795 + 6320588 * 2 ^ 59
def prefixEnd_6320588 : Nat := 4983230072969 + 3 ^ 40 * 6320588 * 2
def baseEnd_6320588 : Nat := 120203691223711922373413

theorem tailTrace_6320588 : CollatzResearch.WordTrace tailWord_6320588 prefixEnd_6320588 120203691223711922373413 := by
  unfold tailWord_6320588
  simp only [CollatzResearch.WordTrace]
  refine ⟨115265391612798310667237209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153687188817064414222982945 115265391612798310667237209)
  ·
    refine ⟨86449043709598733000427907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115265391612798310667237209 86449043709598733000427907)
    ·
      refine ⟨129673565564398099500641861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86449043709598733000427907 129673565564398099500641861)
      ·
        refine ⟨24313793543324643656370349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129673565564398099500641861 24313793543324643656370349)
        ·
          refine ⟨9117672578746741371138881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24313793543324643656370349 9117672578746741371138881)
          ·
            refine ⟨6838254434060056028354161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9117672578746741371138881 6838254434060056028354161)
            ·
              refine ⟨5128690825545042021265621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6838254434060056028354161 5128690825545042021265621)
              ·
                refine ⟨120203691223711922373413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5128690825545042021265621 120203691223711922373413)
                ·
                  rfl

theorem cell23_6320588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 7].length) (baseStart_6320588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320588 prefixEnd_6320588 := by exact prefixLift 6320588
  have htrace : WordTrace (prefixWord ++ tailWord_6320588) baseStart_6320588 baseEnd_6320588 := by
    simpa [prefixWord, tailWord_6320588, baseEnd_6320588] using wordTrace_append hprefix tailTrace_6320588
  have hstable : (prefixWord ++ tailWord_6320588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320588).length < 2 ^ (prefixWord ++ tailWord_6320588).sum := by decide
  have hdescent : baseEnd_6320588 < baseStart_6320588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320598 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_6320598 : Nat := 118140960795 + 6320598 * 2 ^ 59
def prefixEnd_6320598 : Nat := 4983230072969 + 3 ^ 40 * 6320598 * 2
def baseEnd_6320598 : Nat := 3245504797846766864957105

theorem tailTrace_6320598 : CollatzResearch.WordTrace tailWord_6320598 prefixEnd_6320598 3245504797846766864957105 := by
  unfold tailWord_6320598
  simp only [CollatzResearch.WordTrace]
  refine ⟨14408196747222524565146153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153687431970373595361558965 14408196747222524565146153)
  ·
    refine ⟨10806147560416893423859615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14408196747222524565146153 10806147560416893423859615)
    ·
      refine ⟨16209221340625340135789423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10806147560416893423859615 16209221340625340135789423)
      ·
        refine ⟨24313832010938010203684135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16209221340625340135789423 24313832010938010203684135)
        ·
          refine ⟨36470748016407015305526203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24313832010938010203684135 36470748016407015305526203)
          ·
            refine ⟨54706122024610522958289305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36470748016407015305526203 54706122024610522958289305)
            ·
              refine ⟨41029591518457892218716979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54706122024610522958289305 41029591518457892218716979)
              ·
                refine ⟨61544387277686838328075469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41029591518457892218716979 61544387277686838328075469)
                ·
                  refine ⟨23079145229132564373028301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61544387277686838328075469 23079145229132564373028301)
                  ·
                    refine ⟨8654679460924711639885613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23079145229132564373028301 8654679460924711639885613)
                    ·
                      refine ⟨3245504797846766864957105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8654679460924711639885613 3245504797846766864957105)
                      ·
                        rfl

theorem cell23_6320598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_6320598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320598 prefixEnd_6320598 := by exact prefixLift 6320598
  have htrace : WordTrace (prefixWord ++ tailWord_6320598) baseStart_6320598 baseEnd_6320598 := by
    simpa [prefixWord, tailWord_6320598, baseEnd_6320598] using wordTrace_append hprefix tailTrace_6320598
  have hstable : (prefixWord ++ tailWord_6320598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320598).length < 2 ^ (prefixWord ++ tailWord_6320598).sum := by decide
  have hdescent : baseEnd_6320598 < baseStart_6320598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320608 : List Nat := [2, 1, 1, 3, 1, 1, 3, 5, 1, 3, 2]
def baseStart_6320608 : Nat := 118140960795 + 6320608 * 2 ^ 59
def prefixEnd_6320608 : Nat := 4983230072969 + 3 ^ 40 * 6320608 * 2
def baseEnd_6320608 : Nat := 3245509932653311825832059

theorem tailTrace_6320608 : CollatzResearch.WordTrace tailWord_6320608 prefixEnd_6320608 3245509932653311825832059 := by
  unfold tailWord_6320608
  simp only [CollatzResearch.WordTrace]
  refine ⟨115265756342762082375101239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153687675123682776500134985 115265756342762082375101239)
  ·
    refine ⟨172898634514143123562651859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115265756342762082375101239 172898634514143123562651859)
    ·
      refine ⟨259347951771214685343977789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172898634514143123562651859 259347951771214685343977789)
      ·
        refine ⟨97255481914205507003991671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259347951771214685343977789 97255481914205507003991671)
        ·
          refine ⟨145883222871308260505987507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97255481914205507003991671 145883222871308260505987507)
          ·
            refine ⟨218824834306962390758981261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145883222871308260505987507 218824834306962390758981261)
            ·
              refine ⟨82059312865110896534617973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218824834306962390758981261 82059312865110896534617973)
              ·
                refine ⟨7693060581104146550120435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82059312865110896534617973 7693060581104146550120435)
                ·
                  refine ⟨11539590871656219825180653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7693060581104146550120435 11539590871656219825180653)
                  ·
                    refine ⟨4327346576871082434442745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11539590871656219825180653 4327346576871082434442745)
                    ·
                      refine ⟨3245509932653311825832059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4327346576871082434442745 3245509932653311825832059)
                      ·
                        rfl

theorem cell23_6320608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_6320608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320608 prefixEnd_6320608 := by exact prefixLift 6320608
  have htrace : WordTrace (prefixWord ++ tailWord_6320608) baseStart_6320608 baseEnd_6320608 := by
    simpa [prefixWord, tailWord_6320608, baseEnd_6320608] using wordTrace_append hprefix tailTrace_6320608
  have hstable : (prefixWord ++ tailWord_6320608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320608).length < 2 ^ (prefixWord ++ tailWord_6320608).sum := by decide
  have hdescent : baseEnd_6320608 < baseStart_6320608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320624 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 5]
def baseStart_6320624 : Nat := 118140960795 + 6320624 * 2 ^ 59
def prefixEnd_6320624 : Nat := 4983230072969 + 3 ^ 40 * 6320624 * 2
def baseEnd_6320624 : Nat := 3245518148343783763231985

theorem tailTrace_6320624 : CollatzResearch.WordTrace tailWord_6320624 prefixEnd_6320624 3245518148343783763231985 := by
  unfold tailWord_6320624
  simp only [CollatzResearch.WordTrace]
  refine ⟨115266048126733099741392463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153688064168977466321856617 115266048126733099741392463)
  ·
    refine ⟨172899072190099649612088695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115266048126733099741392463 172899072190099649612088695)
    ·
      refine ⟨259348608285149474418133043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172899072190099649612088695 259348608285149474418133043)
      ·
        refine ⟨389022912427724211627199565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259348608285149474418133043 389022912427724211627199565)
        ·
          refine ⟨145883592160396579360199837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389022912427724211627199565 145883592160396579360199837)
          ·
            refine ⟨54706347060148717260074939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145883592160396579360199837 54706347060148717260074939)
            ·
              refine ⟨82059520590223075890112409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54706347060148717260074939 82059520590223075890112409)
              ·
                refine ⟨61544640442667306917584307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82059520590223075890112409 61544640442667306917584307)
                ·
                  refine ⟨92316960664000960376376461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61544640442667306917584307 92316960664000960376376461)
                  ·
                    refine ⟨34618860249000360141141173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92316960664000960376376461 34618860249000360141141173)
                    ·
                      refine ⟨3245518148343783763231985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34618860249000360141141173 3245518148343783763231985)
                      ·
                        rfl

theorem cell23_6320624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_6320624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320624 prefixEnd_6320624 := by exact prefixLift 6320624
  have htrace : WordTrace (prefixWord ++ tailWord_6320624) baseStart_6320624 baseEnd_6320624 := by
    simpa [prefixWord, tailWord_6320624, baseEnd_6320624] using wordTrace_append hprefix tailTrace_6320624
  have hstable : (prefixWord ++ tailWord_6320624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320624).length < 2 ^ (prefixWord ++ tailWord_6320624).sum := by decide
  have hdescent : baseEnd_6320624 < baseStart_6320624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320641 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_6320641 : Nat := 118140960795 + 6320641 * 2 ^ 59
def prefixEnd_6320641 : Nat := 4983230072969 + 3 ^ 40 * 6320641 * 2
def baseEnd_6320641 : Nat := 3245526877514910196719407

theorem tailTrace_6320641 : CollatzResearch.WordTrace tailWord_6320641 prefixEnd_6320641 3245526877514910196719407 := by
  unfold tailWord_6320641
  simp only [CollatzResearch.WordTrace]
  refine ⟨230532716294404611386153777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153688477529603074257435851 230532716294404611386153777)
  ·
    refine ⟨172899537220803458539615333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230532716294404611386153777 172899537220803458539615333)
    ·
      refine ⟨32418663228900648476177875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172899537220803458539615333 32418663228900648476177875)
      ·
        refine ⟨48627994843350972714266813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32418663228900648476177875 48627994843350972714266813)
        ·
          refine ⟨18235498066256614767850055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48627994843350972714266813 18235498066256614767850055)
          ·
            refine ⟨27353247099384922151775083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18235498066256614767850055 27353247099384922151775083)
            ·
              refine ⟨41029870649077383227662625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27353247099384922151775083 41029870649077383227662625)
              ·
                refine ⟨30772402986808037420746969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41029870649077383227662625 30772402986808037420746969)
                ·
                  refine ⟨23079302240106028065560227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30772402986808037420746969 23079302240106028065560227)
                  ·
                    refine ⟨34618953360159042098340341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23079302240106028065560227 34618953360159042098340341)
                    ·
                      refine ⟨3245526877514910196719407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34618953360159042098340341 3245526877514910196719407)
                      ·
                        rfl

theorem cell23_6320641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_6320641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320641 prefixEnd_6320641 := by exact prefixLift 6320641
  have htrace : WordTrace (prefixWord ++ tailWord_6320641) baseStart_6320641 baseEnd_6320641 := by
    simpa [prefixWord, tailWord_6320641, baseEnd_6320641] using wordTrace_append hprefix tailTrace_6320641
  have hstable : (prefixWord ++ tailWord_6320641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320641).length < 2 ^ (prefixWord ++ tailWord_6320641).sum := by decide
  have hdescent : baseEnd_6320641 < baseStart_6320641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320642 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_6320642 : Nat := 118140960795 + 6320642 * 2 ^ 59
def prefixEnd_6320642 : Nat := 4983230072969 + 3 ^ 40 * 6320642 * 2
def baseEnd_6320642 : Nat := 3245527390995564692806903

theorem tailTrace_6320642 : CollatzResearch.WordTrace tailWord_6320642 prefixEnd_6320642 3245527390995564692806903 := by
  unfold tailWord_6320642
  simp only [CollatzResearch.WordTrace]
  refine ⟨57633188191850247139235045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153688501844933992371293453 57633188191850247139235045)
  ·
    refine ⟨10806222785971921338606571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57633188191850247139235045 10806222785971921338606571)
    ·
      refine ⟨16209334178957882007909857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10806222785971921338606571 16209334178957882007909857)
      ·
        refine ⟨12157000634218411505932393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16209334178957882007909857 12157000634218411505932393)
        ·
          refine ⟨9117750475663808629449295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12157000634218411505932393 9117750475663808629449295)
          ·
            refine ⟨13676625713495712944173943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9117750475663808629449295 13676625713495712944173943)
            ·
              refine ⟨20514938570243569416260915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13676625713495712944173943 20514938570243569416260915)
              ·
                refine ⟨30772407855365354124391373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20514938570243569416260915 30772407855365354124391373)
                ·
                  refine ⟨11539652945762007796646765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30772407855365354124391373 11539652945762007796646765)
                  ·
                    refine ⟨4327369854660752923742537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11539652945762007796646765 4327369854660752923742537)
                    ·
                      refine ⟨3245527390995564692806903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4327369854660752923742537 3245527390995564692806903)
                      ·
                        rfl

theorem cell23_6320642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_6320642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320642 prefixEnd_6320642 := by exact prefixLift 6320642
  have htrace : WordTrace (prefixWord ++ tailWord_6320642) baseStart_6320642 baseEnd_6320642 := by
    simpa [prefixWord, tailWord_6320642, baseEnd_6320642] using wordTrace_append hprefix tailTrace_6320642
  have hstable : (prefixWord ++ tailWord_6320642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320642).length < 2 ^ (prefixWord ++ tailWord_6320642).sum := by decide
  have hdescent : baseEnd_6320642 < baseStart_6320642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320671 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 3]
def baseStart_6320671 : Nat := 118140960795 + 6320671 * 2 ^ 59
def prefixEnd_6320671 : Nat := 4983230072969 + 3 ^ 40 * 6320671 * 2
def baseEnd_6320671 : Nat := 3245542281934545079344269

theorem tailTrace_6320671 : CollatzResearch.WordTrace tailWord_6320671 prefixEnd_6320671 3245542281934545079344269 := by
  unfold tailWord_6320671
  simp only [CollatzResearch.WordTrace]
  refine ⟨230533810484295926509745867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153689206989530617673163911 230533810484295926509745867)
  ·
    refine ⟨345800715726443889764618801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230533810484295926509745867 345800715726443889764618801)
    ·
      refine ⟨259350536794832917323464101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345800715726443889764618801 259350536794832917323464101)
      ·
        refine ⟨48628225649031171998149519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259350536794832917323464101 48628225649031171998149519)
        ·
          refine ⟨72942338473546757997224279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48628225649031171998149519 72942338473546757997224279)
          ·
            refine ⟨109413507710320136995836419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72942338473546757997224279 109413507710320136995836419)
            ·
              refine ⟨164120261565480205493754629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109413507710320136995836419 164120261565480205493754629)
              ·
                refine ⟨30772549043527538530078993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164120261565480205493754629 30772549043527538530078993)
                ·
                  refine ⟨23079411782645653897559245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30772549043527538530078993 23079411782645653897559245)
                  ·
                    refine ⟨8654779418492120211584717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23079411782645653897559245 8654779418492120211584717)
                    ·
                      refine ⟨3245542281934545079344269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8654779418492120211584717 3245542281934545079344269)
                      ·
                        rfl

theorem cell23_6320671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_6320671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320671 prefixEnd_6320671 := by exact prefixLift 6320671
  have htrace : WordTrace (prefixWord ++ tailWord_6320671) baseStart_6320671 baseEnd_6320671 := by
    simpa [prefixWord, tailWord_6320671, baseEnd_6320671] using wordTrace_append hprefix tailTrace_6320671
  have hstable : (prefixWord ++ tailWord_6320671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320671).length < 2 ^ (prefixWord ++ tailWord_6320671).sum := by decide
  have hdescent : baseEnd_6320671 < baseStart_6320671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320728 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 2, 4, 2]
def baseStart_6320728 : Nat := 118140960795 + 6320728 * 2 ^ 59
def prefixEnd_6320728 : Nat := 4983230072969 + 3 ^ 40 * 6320728 * 2
def baseEnd_6320728 : Nat := 3245571550331851356331507

theorem tailTrace_6320728 : CollatzResearch.WordTrace tailWord_6320728 prefixEnd_6320728 3245571550331851356331507 := by
  unfold tailWord_6320728
  simp only [CollatzResearch.WordTrace]
  refine ⟨115267944722544712622285419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153690592963392950163047225 115267944722544712622285419)
  ·
    refine ⟨172901917083817068933428129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115267944722544712622285419 172901917083817068933428129)
    ·
      refine ⟨129676437812862801700071097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172901917083817068933428129 129676437812862801700071097)
      ·
        refine ⟨97257328359647101275053323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129676437812862801700071097 97257328359647101275053323)
        ·
          refine ⟨145885992539470651912579985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97257328359647101275053323 145885992539470651912579985)
          ·
            refine ⟨109414494404602988934434989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145885992539470651912579985 109414494404602988934434989)
            ·
              refine ⟨41030435401726120850413121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109414494404602988934434989 41030435401726120850413121)
              ·
                refine ⟨30772826551294590637809841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41030435401726120850413121 30772826551294590637809841)
                ·
                  refine ⟨23079619913470942978357381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30772826551294590637809841 23079619913470942978357381)
                  ·
                    refine ⟨4327428733775801808442009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23079619913470942978357381 4327428733775801808442009)
                    ·
                      refine ⟨3245571550331851356331507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4327428733775801808442009 3245571550331851356331507)
                      ·
                        rfl

theorem cell23_6320728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_6320728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320728 prefixEnd_6320728 := by exact prefixLift 6320728
  have htrace : WordTrace (prefixWord ++ tailWord_6320728) baseStart_6320728 baseEnd_6320728 := by
    simpa [prefixWord, tailWord_6320728, baseEnd_6320728] using wordTrace_append hprefix tailTrace_6320728
  have hstable : (prefixWord ++ tailWord_6320728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320728).length < 2 ^ (prefixWord ++ tailWord_6320728).sum := by decide
  have hdescent : baseEnd_6320728 < baseStart_6320728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320751 : List Nat := [1, 1, 2, 1, 3, 2, 2, 5, 6]
def baseStart_6320751 : Nat := 118140960795 + 6320751 * 2 ^ 59
def prefixEnd_6320751 : Nat := 4983230072969 + 3 ^ 40 * 6320751 * 2
def baseEnd_6320751 : Nat := 360620373376322751815989

theorem tailTrace_6320751 : CollatzResearch.WordTrace tailWord_6320751 prefixEnd_6320751 360620373376322751815989 := by
  unfold tailWord_6320751
  simp only [CollatzResearch.WordTrace]
  refine ⟨230536728324006100172658107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153691152216004066781772071 230536728324006100172658107)
  ·
    refine ⟨345805092486009150258987161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230536728324006100172658107 345805092486009150258987161)
    ·
      refine ⟨259353819364506862694240371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345805092486009150258987161 259353819364506862694240371)
      ·
        refine ⟨389030729046760294041360557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259353819364506862694240371 389030729046760294041360557)
        ·
          refine ⟨145886523392535110265510209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389030729046760294041360557 145886523392535110265510209)
          ·
            refine ⟨109414892544401332699132657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145886523392535110265510209 109414892544401332699132657)
            ·
              refine ⟨82061169408300999524349493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109414892544401332699132657 82061169408300999524349493)
              ·
                refine ⟨7693234632028218705407765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82061169408300999524349493 7693234632028218705407765)
                ·
                  refine ⟨360620373376322751815989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7693234632028218705407765 360620373376322751815989)
                  ·
                    rfl

theorem cell23_6320751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 6].length) (baseStart_6320751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320751 prefixEnd_6320751 := by exact prefixLift 6320751
  have htrace : WordTrace (prefixWord ++ tailWord_6320751) baseStart_6320751 baseEnd_6320751 := by
    simpa [prefixWord, tailWord_6320751, baseEnd_6320751] using wordTrace_append hprefix tailTrace_6320751
  have hstable : (prefixWord ++ tailWord_6320751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320751).length < 2 ^ (prefixWord ++ tailWord_6320751).sum := by decide
  have hdescent : baseEnd_6320751 < baseStart_6320751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320772 : List Nat := [2, 3, 2, 1, 3, 1, 3, 3, 1, 4]
def baseStart_6320772 : Nat := 118140960795 + 6320772 * 2 ^ 59
def prefixEnd_6320772 : Nat := 4983230072969 + 3 ^ 40 * 6320772 * 2
def baseEnd_6320772 : Nat := 1081864714493549728060435

theorem tailTrace_6320772 : CollatzResearch.WordTrace tailWord_6320772 prefixEnd_6320772 1081864714493549728060435 := by
  unfold tailWord_6320772
  simp only [CollatzResearch.WordTrace]
  refine ⟨115268747128465010379586285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153691662837953347172781713 115268747128465010379586285)
  ·
    refine ⟨43225780173174378892344857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115268747128465010379586285 43225780173174378892344857)
    ·
      refine ⟨32419335129880784169258643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43225780173174378892344857 32419335129880784169258643)
      ·
        refine ⟨48629002694821176253887965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32419335129880784169258643 48629002694821176253887965)
        ·
          refine ⟨18235876010557941095207987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48629002694821176253887965 18235876010557941095207987)
          ·
            refine ⟨27353814015836911642811981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18235876010557941095207987 27353814015836911642811981)
            ·
              refine ⟨10257680255938841866054493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27353814015836911642811981 10257680255938841866054493)
              ·
                refine ⟨3846630095977065699770435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10257680255938841866054493 3846630095977065699770435)
                ·
                  refine ⟨5769945143965598549655653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846630095977065699770435 5769945143965598549655653)
                  ·
                    refine ⟨1081864714493549728060435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5769945143965598549655653 1081864714493549728060435)
                    ·
                      rfl

theorem cell23_6320772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_6320772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320772 prefixEnd_6320772 := by exact prefixLift 6320772
  have htrace : WordTrace (prefixWord ++ tailWord_6320772) baseStart_6320772 baseEnd_6320772 := by
    simpa [prefixWord, tailWord_6320772, baseEnd_6320772] using wordTrace_append hprefix tailTrace_6320772
  have hstable : (prefixWord ++ tailWord_6320772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320772).length < 2 ^ (prefixWord ++ tailWord_6320772).sum := by decide
  have hdescent : baseEnd_6320772 < baseStart_6320772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320815 : List Nat := [1, 1, 2, 1, 2, 7, 1, 2, 1, 5]
def baseStart_6320815 : Nat := 118140960795 + 6320815 * 2 ^ 59
def prefixEnd_6320815 : Nat := 4983230072969 + 3 ^ 40 * 6320815 * 2
def baseEnd_6320815 : Nat := 1081872074382930838647869

theorem tailTrace_6320815 : CollatzResearch.WordTrace tailWord_6320815 prefixEnd_6320815 1081872074382930838647869 := by
  unfold tailWord_6320815
  simp only [CollatzResearch.WordTrace]
  refine ⟨230539062595774239102987899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153692708397182826068658599 230539062595774239102987899)
  ·
    refine ⟨345808593893661358654481849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230539062595774239102987899 345808593893661358654481849)
    ·
      refine ⟨259356445420246018990861387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345808593893661358654481849 259356445420246018990861387)
      ·
        refine ⟨389034668130369028486292081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259356445420246018990861387 389034668130369028486292081)
        ·
          refine ⟨291776001097776771364719061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389034668130369028486292081 291776001097776771364719061)
          ·
            refine ⟨6838500025729143078860603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 291776001097776771364719061 6838500025729143078860603)
            ·
              refine ⟨10257750038593714618290905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6838500025729143078860603 10257750038593714618290905)
              ·
                refine ⟨7693312528945285963718179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10257750038593714618290905 7693312528945285963718179)
                ·
                  refine ⟨11539968793417928945577269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7693312528945285963718179 11539968793417928945577269)
                  ·
                    refine ⟨1081872074382930838647869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11539968793417928945577269 1081872074382930838647869)
                    ·
                      rfl

theorem cell23_6320815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 5].length) (baseStart_6320815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320815 prefixEnd_6320815 := by exact prefixLift 6320815
  have htrace : WordTrace (prefixWord ++ tailWord_6320815) baseStart_6320815 baseEnd_6320815 := by
    simpa [prefixWord, tailWord_6320815, baseEnd_6320815] using wordTrace_append hprefix tailTrace_6320815
  have hstable : (prefixWord ++ tailWord_6320815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320815).length < 2 ^ (prefixWord ++ tailWord_6320815).sum := by decide
  have hdescent : baseEnd_6320815 < baseStart_6320815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320828 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 1, 6]
def baseStart_6320828 : Nat := 118140960795 + 6320828 * 2 ^ 59
def prefixEnd_6320828 : Nat := 4983230072969 + 3 ^ 40 * 6320828 * 2
def baseEnd_6320828 : Nat := 1081874299465766988360349

theorem tailTrace_6320828 : CollatzResearch.WordTrace tailWord_6320828 prefixEnd_6320828 1081874299465766988360349 := by
  unfold tailWord_6320828
  simp only [CollatzResearch.WordTrace]
  refine ⟨115269768372363571161605569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153693024496484761548807425 115269768372363571161605569)
  ·
    refine ⟨86452326279272678371204177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115269768372363571161605569 86452326279272678371204177)
    ·
      refine ⟨64839244709454508778403133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86452326279272678371204177 64839244709454508778403133)
      ·
        refine ⟨24314716766045440791901175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64839244709454508778403133 24314716766045440791901175)
        ·
          refine ⟨36472075149068161187851763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24314716766045440791901175 36472075149068161187851763)
          ·
            refine ⟨54708112723602241781777645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36472075149068161187851763 54708112723602241781777645)
            ·
              refine ⟨20515542271350840668166617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54708112723602241781777645 20515542271350840668166617)
              ·
                refine ⟨15386656703513130501124963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20515542271350840668166617 15386656703513130501124963)
                ·
                  refine ⟨23079985055269695751687445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15386656703513130501124963 23079985055269695751687445)
                  ·
                    refine ⟨1081874299465766988360349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23079985055269695751687445 1081874299465766988360349)
                    ·
                      rfl

theorem cell23_6320828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_6320828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320828 prefixEnd_6320828 := by exact prefixLift 6320828
  have htrace : WordTrace (prefixWord ++ tailWord_6320828) baseStart_6320828 baseEnd_6320828 := by
    simpa [prefixWord, tailWord_6320828, baseEnd_6320828] using wordTrace_append hprefix tailTrace_6320828
  have hstable : (prefixWord ++ tailWord_6320828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320828).length < 2 ^ (prefixWord ++ tailWord_6320828).sum := by decide
  have hdescent : baseEnd_6320828 < baseStart_6320828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320846 : List Nat := [4, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3]
def baseStart_6320846 : Nat := 118140960795 + 6320846 * 2 ^ 59
def prefixEnd_6320846 : Nat := 4983230072969 + 3 ^ 40 * 6320846 * 2
def baseEnd_6320846 : Nat := 3245632141049081894655965

theorem tailTrace_6320846 : CollatzResearch.WordTrace tailWord_6320846 prefixEnd_6320846 3245632141049081894655965 := by
  unfold tailWord_6320846
  simp only [CollatzResearch.WordTrace]
  refine ⟨28817524157332741424670799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153693462172441287598244261 28817524157332741424670799)
  ·
    refine ⟨43226286235999112137006199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28817524157332741424670799 43226286235999112137006199)
    ·
      refine ⟨64839429353998668205509299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43226286235999112137006199 64839429353998668205509299)
      ·
        refine ⟨97259144030998002308263949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64839429353998668205509299 97259144030998002308263949)
        ·
          refine ⟨36472179011624250865598981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97259144030998002308263949 36472179011624250865598981)
          ·
            refine ⟨6838533564679547037299809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36472179011624250865598981 6838533564679547037299809)
            ·
              refine ⟨5128900173509660277974857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6838533564679547037299809 5128900173509660277974857)
              ·
                refine ⟨3846675130132245208481143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5128900173509660277974857 3846675130132245208481143)
                ·
                  refine ⟨5770012695198367812721715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846675130132245208481143 5770012695198367812721715)
                  ·
                    refine ⟨8655019042797551719082573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5770012695198367812721715 8655019042797551719082573)
                    ·
                      refine ⟨3245632141049081894655965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8655019042797551719082573 3245632141049081894655965)
                      ·
                        rfl

theorem cell23_6320846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_6320846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320846 prefixEnd_6320846 := by exact prefixLift 6320846
  have htrace : WordTrace (prefixWord ++ tailWord_6320846) baseStart_6320846 baseEnd_6320846 := by
    simpa [prefixWord, tailWord_6320846, baseEnd_6320846] using wordTrace_append hprefix tailTrace_6320846
  have hstable : (prefixWord ++ tailWord_6320846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320846).length < 2 ^ (prefixWord ++ tailWord_6320846).sum := by decide
  have hdescent : baseEnd_6320846 < baseStart_6320846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320865 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_6320865 : Nat := 118140960795 + 6320865 * 2 ^ 59
def prefixEnd_6320865 : Nat := 4983230072969 + 3 ^ 40 * 6320865 * 2
def baseEnd_6320865 : Nat := 3245641897181517320318377

theorem tailTrace_6320865 : CollatzResearch.WordTrace tailWord_6320865 prefixEnd_6320865 3245641897181517320318377 := by
  unfold tailWord_6320865
  simp only [CollatzResearch.WordTrace]
  refine ⟨230540886245593097642308049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153693924163728731761538699 230540886245593097642308049)
  ·
    refine ⟨172905664684194823231731037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230540886245593097642308049 172905664684194823231731037)
    ·
      refine ⟨64839624256573058711899139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172905664684194823231731037 64839624256573058711899139)
      ·
        refine ⟨97259436384859588067848709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64839624256573058711899139 97259436384859588067848709)
        ·
          refine ⟨18236144322161172762721633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97259436384859588067848709 18236144322161172762721633)
          ·
            refine ⟨13677108241620879572041225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18236144322161172762721633 13677108241620879572041225)
            ·
              refine ⟨10257831181215659679030919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13677108241620879572041225 10257831181215659679030919)
              ·
                refine ⟨15386746771823489518546379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10257831181215659679030919 15386746771823489518546379)
                ·
                  refine ⟨23080120157735234277819569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15386746771823489518546379 23080120157735234277819569)
                  ·
                    refine ⟨17310090118301425708364677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23080120157735234277819569 17310090118301425708364677)
                    ·
                      refine ⟨3245641897181517320318377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17310090118301425708364677 3245641897181517320318377)
                      ·
                        rfl

theorem cell23_6320865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_6320865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320865 prefixEnd_6320865 := by exact prefixLift 6320865
  have htrace : WordTrace (prefixWord ++ tailWord_6320865) baseStart_6320865 baseEnd_6320865 := by
    simpa [prefixWord, tailWord_6320865, baseEnd_6320865] using wordTrace_append hprefix tailTrace_6320865
  have hstable : (prefixWord ++ tailWord_6320865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320865).length < 2 ^ (prefixWord ++ tailWord_6320865).sum := by decide
  have hdescent : baseEnd_6320865 < baseStart_6320865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320886 : List Nat := [5, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2]
def baseStart_6320886 : Nat := 118140960795 + 6320886 * 2 ^ 59
def prefixEnd_6320886 : Nat := 4983230072969 + 3 ^ 40 * 6320886 * 2
def baseEnd_6320886 : Nat := 3245652680275261738155781

theorem tailTrace_6320886 : CollatzResearch.WordTrace tailWord_6320886 prefixEnd_6320886 3245652680275261738155781 := by
  unfold tailWord_6320886
  simp only [CollatzResearch.WordTrace]
  refine ⟨14408853261157313639301407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153694434785678012152548341 14408853261157313639301407)
  ·
    refine ⟨21613279891735970458952111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14408853261157313639301407 21613279891735970458952111)
    ·
      refine ⟨32419919837603955688428167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21613279891735970458952111 32419919837603955688428167)
      ·
        refine ⟨48629879756405933532642251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32419919837603955688428167 48629879756405933532642251)
        ·
          refine ⟨72944819634608900298963377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48629879756405933532642251 72944819634608900298963377)
          ·
            refine ⟨54708614725956675224222533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72944819634608900298963377 54708614725956675224222533)
            ·
              refine ⟨10257865261116876604541725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54708614725956675224222533 10257865261116876604541725)
              ·
                refine ⟨3846699472918828726703147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10257865261116876604541725 3846699472918828726703147)
                ·
                  refine ⟨5770049209378243090054721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846699472918828726703147 5770049209378243090054721)
                  ·
                    refine ⟨4327536907033682317541041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5770049209378243090054721 4327536907033682317541041)
                    ·
                      refine ⟨3245652680275261738155781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4327536907033682317541041 3245652680275261738155781)
                      ·
                        rfl

theorem cell23_6320886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_6320886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320886 prefixEnd_6320886 := by exact prefixLift 6320886
  have htrace : WordTrace (prefixWord ++ tailWord_6320886) baseStart_6320886 baseEnd_6320886 := by
    simpa [prefixWord, tailWord_6320886, baseEnd_6320886] using wordTrace_append hprefix tailTrace_6320886
  have hstable : (prefixWord ++ tailWord_6320886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320886).length < 2 ^ (prefixWord ++ tailWord_6320886).sum := by decide
  have hdescent : baseEnd_6320886 < baseStart_6320886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320919 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 1, 3, 3]
def baseStart_6320919 : Nat := 118140960795 + 6320919 * 2 ^ 59
def prefixEnd_6320919 : Nat := 4983230072969 + 3 ^ 40 * 6320919 * 2
def baseEnd_6320919 : Nat := 3245669625136860109043129

theorem tailTrace_6320919 : CollatzResearch.WordTrace tailWord_6320919 prefixEnd_6320919 3245669625136860109043129 := by
  unfold tailWord_6320919
  simp only [CollatzResearch.WordTrace]
  refine ⟨230542855787397464864773811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153695237191598309909849207 230542855787397464864773811)
  ·
    refine ⟨345814283681096197297160717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230542855787397464864773811 345814283681096197297160717)
    ·
      refine ⟨129680356380411073986435269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345814283681096197297160717 129680356380411073986435269)
      ·
        refine ⟨24315066821327076372456613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129680356380411073986435269 24315066821327076372456613)
        ·
          refine ⟨4559075028998826819835615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24315066821327076372456613 4559075028998826819835615)
          ·
            refine ⟨6838612543498240229753423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4559075028998826819835615 6838612543498240229753423)
            ·
              refine ⟨10257918815247360344630135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6838612543498240229753423 10257918815247360344630135)
              ·
                refine ⟨15386878222871040516945203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10257918815247360344630135 15386878222871040516945203)
                ·
                  refine ⟨23080317334306560775417805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15386878222871040516945203 23080317334306560775417805)
                  ·
                    refine ⟨8655119000364960290781677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23080317334306560775417805 8655119000364960290781677)
                    ·
                      refine ⟨3245669625136860109043129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8655119000364960290781677 3245669625136860109043129)
                      ·
                        rfl

theorem cell23_6320919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_6320919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320919 prefixEnd_6320919 := by exact prefixLift 6320919
  have htrace : WordTrace (prefixWord ++ tailWord_6320919) baseStart_6320919 baseEnd_6320919 := by
    simpa [prefixWord, tailWord_6320919, baseEnd_6320919] using wordTrace_append hprefix tailTrace_6320919
  have hstable : (prefixWord ++ tailWord_6320919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320919).length < 2 ^ (prefixWord ++ tailWord_6320919).sum := by decide
  have hdescent : baseEnd_6320919 < baseStart_6320919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6320995 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 2, 5]
def baseStart_6320995 : Nat := 118140960795 + 6320995 * 2 ^ 59
def prefixEnd_6320995 : Nat := 4983230072969 + 3 ^ 40 * 6320995 * 2
def baseEnd_6320995 : Nat := 1081902883222200603897593

theorem tailTrace_6320995 : CollatzResearch.WordTrace tailWord_6320995 prefixEnd_6320995 1081902883222200603897593 := by
  unfold tailWord_6320995
  simp only [CollatzResearch.WordTrace]
  refine ⟨230545627735122129844540439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153697085156748086563026959 230545627735122129844540439)
  ·
    refine ⟨345818441602683194766810659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230545627735122129844540439 345818441602683194766810659)
    ·
      refine ⟨518727662404024792150215989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345818441602683194766810659 518727662404024792150215989)
      ·
        refine ⟨48630718350377324264082749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 518727662404024792150215989 48630718350377324264082749)
        ·
          refine ⟨18236519381391496599031031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48630718350377324264082749 18236519381391496599031031)
          ·
            refine ⟨27354779072087244898546547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18236519381391496599031031 27354779072087244898546547)
            ·
              refine ⟨41032168608130867347819821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27354779072087244898546547 41032168608130867347819821)
              ·
                refine ⟨15387063228049075255432433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41032168608130867347819821 15387063228049075255432433)
                ·
                  refine ⟨11540297421036806441574325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15387063228049075255432433 11540297421036806441574325)
                  ·
                    refine ⟨1081902883222200603897593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11540297421036806441574325 1081902883222200603897593)
                    ·
                      rfl

theorem cell23_6320995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 5].length) (baseStart_6320995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6320995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6320995 prefixEnd_6320995 := by exact prefixLift 6320995
  have htrace : WordTrace (prefixWord ++ tailWord_6320995) baseStart_6320995 baseEnd_6320995 := by
    simpa [prefixWord, tailWord_6320995, baseEnd_6320995] using wordTrace_append hprefix tailTrace_6320995
  have hstable : (prefixWord ++ tailWord_6320995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6320995).length < 2 ^ (prefixWord ++ tailWord_6320995).sum := by decide
  have hdescent : baseEnd_6320995 < baseStart_6320995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6320995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321015 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 3, 6, 2]
def baseStart_6321015 : Nat := 118140960795 + 6321015 * 2 ^ 59
def prefixEnd_6321015 : Nat := 4983230072969 + 3 ^ 40 * 6321015 * 2
def baseEnd_6321015 : Nat := 3245718919279691733442687

theorem tailTrace_6321015 : CollatzResearch.WordTrace tailWord_6321015 prefixEnd_6321015 3245718919279691733442687 := by
  unfold tailWord_6321015
  simp only [CollatzResearch.WordTrace]
  refine ⟨230546357195049673260268499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153697571463366448840178999 230546357195049673260268499)
  ·
    refine ⟨345819535792574509890402749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230546357195049673260268499 345819535792574509890402749)
    ·
      refine ⟨129682325922215441208901031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 345819535792574509890402749 129682325922215441208901031)
      ·
        refine ⟨194523488883323161813351547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129682325922215441208901031 194523488883323161813351547)
        ·
          refine ⟨291785233324984742720027321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194523488883323161813351547 291785233324984742720027321)
          ·
            refine ⟨218838924993738557040020491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291785233324984742720027321 218838924993738557040020491)
            ·
              refine ⟨328258387490607835560030737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218838924993738557040020491 328258387490607835560030737)
              ·
                refine ⟨246193790617955876670023053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328258387490607835560030737 246193790617955876670023053)
                ·
                  refine ⟨92322671481733453751258645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246193790617955876670023053 92322671481733453751258645)
                  ·
                    refine ⟨4327625225706255644590249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92322671481733453751258645 4327625225706255644590249)
                    ·
                      refine ⟨3245718919279691733442687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4327625225706255644590249 3245718919279691733442687)
                      ·
                        rfl

theorem cell23_6321015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 6, 2].length) (baseStart_6321015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321015 prefixEnd_6321015 := by exact prefixLift 6321015
  have htrace : WordTrace (prefixWord ++ tailWord_6321015) baseStart_6321015 baseEnd_6321015 := by
    simpa [prefixWord, tailWord_6321015, baseEnd_6321015] using wordTrace_append hprefix tailTrace_6321015
  have hstable : (prefixWord ++ tailWord_6321015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321015).length < 2 ^ (prefixWord ++ tailWord_6321015).sum := by decide
  have hdescent : baseEnd_6321015 < baseStart_6321015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321018 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_6321018 : Nat := 118140960795 + 6321018 * 2 ^ 59
def prefixEnd_6321018 : Nat := 4983230072969 + 3 ^ 40 * 6321018 * 2
def baseEnd_6321018 : Nat := 3245720459721655221705173

theorem tailTrace_6321018 : CollatzResearch.WordTrace tailWord_6321018 prefixEnd_6321018 3245720459721655221705173 := by
  unfold tailWord_6321018
  simp only [CollatzResearch.WordTrace]
  refine ⟨57636616653509701193156927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153697644409359203181751805 57636616653509701193156927)
  ·
    refine ⟨86454924980264551789735391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57636616653509701193156927 86454924980264551789735391)
    ·
      refine ⟨129682387470396827684603087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86454924980264551789735391 129682387470396827684603087)
      ·
        refine ⟨194523581205595241526904631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129682387470396827684603087 194523581205595241526904631)
        ·
          refine ⟨291785371808392862290356947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194523581205595241526904631 291785371808392862290356947)
          ·
            refine ⟨437678057712589293435535421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291785371808392862290356947 437678057712589293435535421)
            ·
              refine ⟨164129271642220985038325783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 437678057712589293435535421 164129271642220985038325783)
              ·
                refine ⟨246193907463331477557488675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164129271642220985038325783 246193907463331477557488675)
                ·
                  refine ⟨369290861194997216336233013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246193907463331477557488675 369290861194997216336233013)
                  ·
                    refine ⟨34621018237030989031521845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 369290861194997216336233013 34621018237030989031521845)
                    ·
                      refine ⟨3245720459721655221705173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34621018237030989031521845 3245720459721655221705173)
                      ·
                        rfl

theorem cell23_6321018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_6321018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321018 prefixEnd_6321018 := by exact prefixLift 6321018
  have htrace : WordTrace (prefixWord ++ tailWord_6321018) baseStart_6321018 baseEnd_6321018 := by
    simpa [prefixWord, tailWord_6321018, baseEnd_6321018] using wordTrace_append hprefix tailTrace_6321018
  have hstable : (prefixWord ++ tailWord_6321018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321018).length < 2 ^ (prefixWord ++ tailWord_6321018).sum := by decide
  have hdescent : baseEnd_6321018 < baseStart_6321018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321026 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_6321026 : Nat := 118140960795 + 6321026 * 2 ^ 59
def prefixEnd_6321026 : Nat := 4983230072969 + 3 ^ 40 * 6321026 * 2
def baseEnd_6321026 : Nat := 3245724567566891190405137

theorem tailTrace_6321026 : CollatzResearch.WordTrace tailWord_6321026 prefixEnd_6321026 3245724567566891190405137 := by
  unfold tailWord_6321026
  simp only [CollatzResearch.WordTrace]
  refine ⟨57636689599502455534729733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153697838932006548092612621 57636689599502455534729733)
  ·
    refine ⟨10806879299906710412761825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57636689599502455534729733 10806879299906710412761825)
    ·
      refine ⟨8105159474930032809571369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10806879299906710412761825 8105159474930032809571369)
      ·
        refine ⟨6078869606197524607178527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8105159474930032809571369 6078869606197524607178527)
        ·
          refine ⟨9118304409296286910767791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6078869606197524607178527 9118304409296286910767791)
          ·
            refine ⟨13677456613944430366151687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9118304409296286910767791 13677456613944430366151687)
            ·
              refine ⟨20516184920916645549227531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13677456613944430366151687 20516184920916645549227531)
              ·
                refine ⟨30774277381374968323841297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20516184920916645549227531 30774277381374968323841297)
                ·
                  refine ⟨23080708036031226242880973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30774277381374968323841297 23080708036031226242880973)
                  ·
                    refine ⟨8655265513511709841080365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23080708036031226242880973 8655265513511709841080365)
                    ·
                      refine ⟨3245724567566891190405137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8655265513511709841080365 3245724567566891190405137)
                      ·
                        rfl

theorem cell23_6321026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_6321026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321026 prefixEnd_6321026 := by exact prefixLift 6321026
  have htrace : WordTrace (prefixWord ++ tailWord_6321026) baseStart_6321026 baseEnd_6321026 := by
    simpa [prefixWord, tailWord_6321026, baseEnd_6321026] using wordTrace_append hprefix tailTrace_6321026
  have hstable : (prefixWord ++ tailWord_6321026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321026).length < 2 ^ (prefixWord ++ tailWord_6321026).sum := by decide
  have hdescent : baseEnd_6321026 < baseStart_6321026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321032 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 1, 6, 2]
def baseStart_6321032 : Nat := 118140960795 + 6321032 * 2 ^ 59
def prefixEnd_6321032 : Nat := 4983230072969 + 3 ^ 40 * 6321032 * 2
def baseEnd_6321032 : Nat := 3245727648450818166930109

theorem tailTrace_6321032 : CollatzResearch.WordTrace tailWord_6321032 prefixEnd_6321032 3245727648450818166930109 := by
  unfold tailWord_6321032
  simp only [CollatzResearch.WordTrace]
  refine ⟨115273488617994042581818675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153697984823992056775758233 115273488617994042581818675)
  ·
    refine ⟨172910232926991063872728013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115273488617994042581818675 172910232926991063872728013)
    ·
      refine ⟨64841337347621648952273005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172910232926991063872728013 64841337347621648952273005)
      ·
        refine ⟨24315501505358118357102377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64841337347621648952273005 24315501505358118357102377)
        ·
          refine ⟨18236626129018588767826783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24315501505358118357102377 18236626129018588767826783)
          ·
            refine ⟨27354939193527883151740175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18236626129018588767826783 27354939193527883151740175)
            ·
              refine ⟨41032408790291824727610263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27354939193527883151740175 41032408790291824727610263)
              ·
                refine ⟨61548613185437737091415395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41032408790291824727610263 61548613185437737091415395)
                ·
                  refine ⟨92322919778156605637123093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61548613185437737091415395 92322919778156605637123093)
                  ·
                    refine ⟨4327636864601090889240145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92322919778156605637123093 4327636864601090889240145)
                    ·
                      refine ⟨3245727648450818166930109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4327636864601090889240145 3245727648450818166930109)
                      ·
                        rfl

theorem cell23_6321032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_6321032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321032 prefixEnd_6321032 := by exact prefixLift 6321032
  have htrace : WordTrace (prefixWord ++ tailWord_6321032) baseStart_6321032 baseEnd_6321032 := by
    simpa [prefixWord, tailWord_6321032, baseEnd_6321032] using wordTrace_append hprefix tailTrace_6321032
  have hstable : (prefixWord ++ tailWord_6321032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321032).length < 2 ^ (prefixWord ++ tailWord_6321032).sum := by decide
  have hdescent : baseEnd_6321032 < baseStart_6321032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321035 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 3]
def baseStart_6321035 : Nat := 118140960795 + 6321035 * 2 ^ 59
def prefixEnd_6321035 : Nat := 4983230072969 + 3 ^ 40 * 6321035 * 2
def baseEnd_6321035 : Nat := 3245729188892781655192595

theorem tailTrace_6321035 : CollatzResearch.WordTrace tailWord_6321035 prefixEnd_6321035 3245729188892781655192595 := by
  unfold tailWord_6321035
  simp only [CollatzResearch.WordTrace]
  refine ⟨230547086654977216675996559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153698057769984811117331039 230547086654977216675996559)
  ·
    refine ⟨345820629982465825013994839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230547086654977216675996559 345820629982465825013994839)
    ·
      refine ⟨518730944973698737520992259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345820629982465825013994839 518730944973698737520992259)
      ·
        refine ⟨778096417460548106281488389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518730944973698737520992259 778096417460548106281488389)
        ·
          refine ⟨145893078273852769927779073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 778096417460548106281488389 145893078273852769927779073)
          ·
            refine ⟨109419808705389577445834305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145893078273852769927779073 109419808705389577445834305)
            ·
              refine ⟨82064856529042183084375729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109419808705389577445834305 82064856529042183084375729)
              ·
                refine ⟨61548642396781637313281797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82064856529042183084375729 61548642396781637313281797)
                ·
                  refine ⟨11540370449396556996240337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61548642396781637313281797 11540370449396556996240337)
                  ·
                    refine ⟨8655277837047417747180253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11540370449396556996240337 8655277837047417747180253)
                    ·
                      refine ⟨3245729188892781655192595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8655277837047417747180253 3245729188892781655192595)
                      ·
                        rfl

theorem cell23_6321035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 3].length) (baseStart_6321035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321035 prefixEnd_6321035 := by exact prefixLift 6321035
  have htrace : WordTrace (prefixWord ++ tailWord_6321035) baseStart_6321035 baseEnd_6321035 := by
    simpa [prefixWord, tailWord_6321035, baseEnd_6321035] using wordTrace_append hprefix tailTrace_6321035
  have hstable : (prefixWord ++ tailWord_6321035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321035).length < 2 ^ (prefixWord ++ tailWord_6321035).sum := by decide
  have hdescent : baseEnd_6321035 < baseStart_6321035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321046 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_6321046 : Nat := 118140960795 + 6321046 * 2 ^ 59
def prefixEnd_6321046 : Nat := 4983230072969 + 3 ^ 40 * 6321046 * 2
def baseEnd_6321046 : Nat := 1081911612393327037385015

theorem tailTrace_6321046 : CollatzResearch.WordTrace tailWord_6321046 prefixEnd_6321046 1081911612393327037385015 := by
  unfold tailWord_6321046
  simp only [CollatzResearch.WordTrace]
  refine ⟨14409217991121085347165437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153698325238624910369764661 14409217991121085347165437)
  ·
    refine ⟨5403456746670407005187039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14409217991121085347165437 5403456746670407005187039)
    ·
      refine ⟨8105185120005610507780559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5403456746670407005187039 8105185120005610507780559)
      ·
        refine ⟨12157777680008415761670839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8105185120005610507780559 12157777680008415761670839)
        ·
          refine ⟨18236666520012623642506259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12157777680008415761670839 18236666520012623642506259)
          ·
            refine ⟨27354999780018935463759389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18236666520012623642506259 27354999780018935463759389)
            ·
              refine ⟨10258124917507100798909771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27354999780018935463759389 10258124917507100798909771)
              ·
                refine ⟨15387187376260651198364657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10258124917507100798909771 15387187376260651198364657)
                ·
                  refine ⟨11540390532195488398773493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15387187376260651198364657 11540390532195488398773493)
                  ·
                    refine ⟨1081911612393327037385015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11540390532195488398773493 1081911612393327037385015)
                    ·
                      rfl

theorem cell23_6321046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_6321046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321046 prefixEnd_6321046 := by exact prefixLift 6321046
  have htrace : WordTrace (prefixWord ++ tailWord_6321046) baseStart_6321046 baseEnd_6321046 := by
    simpa [prefixWord, tailWord_6321046, baseEnd_6321046] using wordTrace_append hprefix tailTrace_6321046
  have hstable : (prefixWord ++ tailWord_6321046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321046).length < 2 ^ (prefixWord ++ tailWord_6321046).sum := by decide
  have hdescent : baseEnd_6321046 < baseStart_6321046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321076 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_6321076 : Nat := 118140960795 + 6321076 * 2 ^ 59
def prefixEnd_6321076 : Nat := 4983230072969 + 3 ^ 40 * 6321076 * 2
def baseEnd_6321076 : Nat := 1081916747199871998259969

theorem tailTrace_6321076 : CollatzResearch.WordTrace tailWord_6321076 prefixEnd_6321076 1081916747199871998259969 := by
  unfold tailWord_6321076
  simp only [CollatzResearch.WordTrace]
  refine ⟨115274291023914340339119541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153699054698552453785492721 115274291023914340339119541)
  ·
    refine ⟨10806964783491969406792457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115274291023914340339119541 10806964783491969406792457)
    ·
      refine ⟨8105223587618977055094343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10806964783491969406792457 8105223587618977055094343)
      ·
        refine ⟨12157835381428465582641515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8105223587618977055094343 12157835381428465582641515)
        ·
          refine ⟨18236753072142698373962273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12157835381428465582641515 18236753072142698373962273)
          ·
            refine ⟨13677564804107023780471705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18236753072142698373962273 13677564804107023780471705)
            ·
              refine ⟨10258173603080267835353779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13677564804107023780471705 10258173603080267835353779)
              ·
                refine ⟨15387260404620401753030669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10258173603080267835353779 15387260404620401753030669)
                ·
                  refine ⟨5770222651732650657386501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15387260404620401753030669 5770222651732650657386501)
                  ·
                    refine ⟨1081916747199871998259969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5770222651732650657386501 1081916747199871998259969)
                    ·
                      rfl

theorem cell23_6321076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_6321076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321076 prefixEnd_6321076 := by exact prefixLift 6321076
  have htrace : WordTrace (prefixWord ++ tailWord_6321076) baseStart_6321076 baseEnd_6321076 := by
    simpa [prefixWord, tailWord_6321076, baseEnd_6321076] using wordTrace_append hprefix tailTrace_6321076
  have hstable : (prefixWord ++ tailWord_6321076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321076).length < 2 ^ (prefixWord ++ tailWord_6321076).sum := by decide
  have hdescent : baseEnd_6321076 < baseStart_6321076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321102 : List Nat := [4, 1, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_6321102 : Nat := 118140960795 + 6321102 * 2 ^ 59
def prefixEnd_6321102 : Nat := 4983230072969 + 3 ^ 40 * 6321102 * 2
def baseEnd_6321102 : Nat := 1081921197365544297684929

theorem tailTrace_6321102 : CollatzResearch.WordTrace tailWord_6321102 prefixEnd_6321102 1081921197365544297684929 := by
  unfold tailWord_6321102
  simp only [CollatzResearch.WordTrace]
  refine ⟨28818691293216810889835695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153699686897156324745790373 28818691293216810889835695)
  ·
    refine ⟨43228036939825216334753543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28818691293216810889835695 43228036939825216334753543)
    ·
      refine ⟨64842055409737824502130315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43228036939825216334753543 64842055409737824502130315)
      ·
        refine ⟨97263083114606736753195473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64842055409737824502130315 97263083114606736753195473)
        ·
          refine ⟨72947312335955052564896605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97263083114606736753195473 72947312335955052564896605)
          ·
            refine ⟨27355242125983144711836227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72947312335955052564896605 27355242125983144711836227)
            ·
              refine ⟨41032863188974717067754341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27355242125983144711836227 41032863188974717067754341)
              ·
                refine ⟨7693661847932759450203939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41032863188974717067754341 7693661847932759450203939)
                ·
                  refine ⟨11540492771899139175305909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7693661847932759450203939 11540492771899139175305909)
                  ·
                    refine ⟨1081921197365544297684929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11540492771899139175305909 1081921197365544297684929)
                    ·
                      rfl

theorem cell23_6321102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_6321102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321102 prefixEnd_6321102 := by exact prefixLift 6321102
  have htrace : WordTrace (prefixWord ++ tailWord_6321102) baseStart_6321102 baseEnd_6321102 := by
    simpa [prefixWord, tailWord_6321102, baseEnd_6321102] using wordTrace_append hprefix tailTrace_6321102
  have hstable : (prefixWord ++ tailWord_6321102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321102).length < 2 ^ (prefixWord ++ tailWord_6321102).sum := by decide
  have hdescent : baseEnd_6321102 < baseStart_6321102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321135 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 6]
def baseStart_6321135 : Nat := 118140960795 + 6321135 * 2 ^ 59
def prefixEnd_6321135 : Nat := 4983230072969 + 3 ^ 40 * 6321135 * 2
def baseEnd_6321135 : Nat := 3245780536958231263942135

theorem tailTrace_6321135 : CollatzResearch.WordTrace tailWord_6321135 prefixEnd_6321135 3245780536958231263942135 := by
  unfold tailWord_6321135
  simp only [CollatzResearch.WordTrace]
  refine ⟨230550733954614933754636859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153700489303076622503091239 230550733954614933754636859)
  ·
    refine ⟨345826100931922400631955289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230550733954614933754636859 345826100931922400631955289)
    ·
      refine ⟨259369575698941800473966467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345826100931922400631955289 259369575698941800473966467)
      ·
        refine ⟨389054363548412700710949701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259369575698941800473966467 389054363548412700710949701)
        ·
          refine ⟨72947693165327381383303069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389054363548412700710949701 72947693165327381383303069)
          ·
            refine ⟨27355384936997768018738651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72947693165327381383303069 27355384936997768018738651)
            ·
              refine ⟨41033077405496652028107977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27355384936997768018738651 41033077405496652028107977)
              ·
                refine ⟨30774808054122489021080983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41033077405496652028107977 30774808054122489021080983)
                ·
                  refine ⟨46162212081183733531621475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30774808054122489021080983 46162212081183733531621475)
                  ·
                    refine ⟨69243318121775600297432213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46162212081183733531621475 69243318121775600297432213)
                    ·
                      refine ⟨3245780536958231263942135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69243318121775600297432213 3245780536958231263942135)
                      ·
                        rfl

theorem cell23_6321135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_6321135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321135 prefixEnd_6321135 := by exact prefixLift 6321135
  have htrace : WordTrace (prefixWord ++ tailWord_6321135) baseStart_6321135 baseEnd_6321135 := by
    simpa [prefixWord, tailWord_6321135, baseEnd_6321135] using wordTrace_append hprefix tailTrace_6321135
  have hstable : (prefixWord ++ tailWord_6321135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321135).length < 2 ^ (prefixWord ++ tailWord_6321135).sum := by decide
  have hdescent : baseEnd_6321135 < baseStart_6321135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321145 : List Nat := [1, 2, 1, 3, 1, 3, 4, 8]
def baseStart_6321145 : Nat := 118140960795 + 6321145 * 2 ^ 59
def prefixEnd_6321145 : Nat := 4983230072969 + 3 ^ 40 * 6321145 * 2
def baseEnd_6321145 : Nat := 120214284139436156474707

theorem tailTrace_6321145 : CollatzResearch.WordTrace tailWord_6321145 prefixEnd_6321145 120214284139436156474707 := by
  unfold tailWord_6321145
  simp only [CollatzResearch.WordTrace]
  refine ⟨230551098684578705462500889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153700732456385803641667259 230551098684578705462500889)
  ·
    refine ⟨172913324013434029096875667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230551098684578705462500889 172913324013434029096875667)
    ·
      refine ⟨259369986020151043645313501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172913324013434029096875667 259369986020151043645313501)
      ·
        refine ⟨97263744757556641366992563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259369986020151043645313501 97263744757556641366992563)
        ·
          refine ⟨145895617136334962050488845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97263744757556641366992563 145895617136334962050488845)
          ·
            refine ⟨54710856426125610768933317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145895617136334962050488845 54710856426125610768933317)
            ·
              refine ⟨10258285579898552019174997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54710856426125610768933317 10258285579898552019174997)
              ·
                refine ⟨120214284139436156474707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10258285579898552019174997 120214284139436156474707)
                ·
                  rfl

theorem cell23_6321145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 8].length) (baseStart_6321145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321145 prefixEnd_6321145 := by exact prefixLift 6321145
  have htrace : WordTrace (prefixWord ++ tailWord_6321145) baseStart_6321145 baseEnd_6321145 := by
    simpa [prefixWord, tailWord_6321145, baseEnd_6321145] using wordTrace_append hprefix tailTrace_6321145
  have hstable : (prefixWord ++ tailWord_6321145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321145).length < 2 ^ (prefixWord ++ tailWord_6321145).sum := by decide
  have hdescent : baseEnd_6321145 < baseStart_6321145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321170 : List Nat := [3, 2, 5, 1, 1, 1, 3, 1, 1, 5]
def baseStart_6321170 : Nat := 118140960795 + 6321170 * 2 ^ 59
def prefixEnd_6321170 : Nat := 4983230072969 + 3 ^ 40 * 6321170 * 2
def baseEnd_6321170 : Nat := 1081932836260379542334825

theorem tailTrace_6321170 : CollatzResearch.WordTrace tailWord_6321170 prefixEnd_6321170 1081932836260379542334825 := by
  unfold tailWord_6321170
  simp only [CollatzResearch.WordTrace]
  refine ⟨57638002627372033683040241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153701340339658756488107309 57638002627372033683040241)
  ·
    refine ⟨43228501970529025262280181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57638002627372033683040241 43228501970529025262280181)
    ·
      refine ⟨4052672059737096118338767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43228501970529025262280181 4052672059737096118338767)
      ·
        refine ⟨6079008089605644177508151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4052672059737096118338767 6079008089605644177508151)
        ·
          refine ⟨9118512134408466266262227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6079008089605644177508151 9118512134408466266262227)
          ·
            refine ⟨13677768201612699399393341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9118512134408466266262227 13677768201612699399393341)
            ·
              refine ⟨5129163075604762274772503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13677768201612699399393341 5129163075604762274772503)
              ·
                refine ⟨7693744613407143412158755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129163075604762274772503 7693744613407143412158755)
                ·
                  refine ⟨11540616920110715118238133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7693744613407143412158755 11540616920110715118238133)
                  ·
                    refine ⟨1081932836260379542334825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11540616920110715118238133 1081932836260379542334825)
                    ·
                      rfl

theorem cell23_6321170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_6321170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321170 prefixEnd_6321170 := by exact prefixLift 6321170
  have htrace : WordTrace (prefixWord ++ tailWord_6321170) baseStart_6321170 baseEnd_6321170 := by
    simpa [prefixWord, tailWord_6321170, baseEnd_6321170] using wordTrace_append hprefix tailTrace_6321170
  have hstable : (prefixWord ++ tailWord_6321170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321170).length < 2 ^ (prefixWord ++ tailWord_6321170).sum := by decide
  have hdescent : baseEnd_6321170 < baseStart_6321170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321176 : List Nat := [2, 1, 2, 3, 2, 3, 3, 1, 1, 2, 3]
def baseStart_6321176 : Nat := 118140960795 + 6321176 * 2 ^ 59
def prefixEnd_6321176 : Nat := 4983230072969 + 3 ^ 40 * 6321176 * 2
def baseEnd_6321176 : Nat := 3245801589665065603529447

theorem tailTrace_6321176 : CollatzResearch.WordTrace tailWord_6321176 prefixEnd_6321176 3245801589665065603529447 := by
  unfold tailWord_6321176
  simp only [CollatzResearch.WordTrace]
  refine ⟨115276114673733198878439691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153701486231644265171252921 115276114673733198878439691)
  ·
    refine ⟨172914172010599798317659537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115276114673733198878439691 172914172010599798317659537)
    ·
      refine ⟨129685629007949848738244653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172914172010599798317659537 129685629007949848738244653)
      ·
        refine ⟨48632110877981193276841745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129685629007949848738244653 48632110877981193276841745)
        ·
          refine ⟨36474083158485894957631309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48632110877981193276841745 36474083158485894957631309)
          ·
            refine ⟨13677781184432210609111741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36474083158485894957631309 13677781184432210609111741)
            ·
              refine ⟨5129167944162078978416903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13677781184432210609111741 5129167944162078978416903)
              ·
                refine ⟨7693751916243118467625355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129167944162078978416903 7693751916243118467625355)
                ·
                  refine ⟨11540627874364677701438033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7693751916243118467625355 11540627874364677701438033)
                  ·
                    refine ⟨8655470905773508276078525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11540627874364677701438033 8655470905773508276078525)
                    ·
                      refine ⟨3245801589665065603529447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8655470905773508276078525 3245801589665065603529447)
                      ·
                        rfl

theorem cell23_6321176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_6321176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321176 prefixEnd_6321176 := by exact prefixLift 6321176
  have htrace : WordTrace (prefixWord ++ tailWord_6321176) baseStart_6321176 baseEnd_6321176 := by
    simpa [prefixWord, tailWord_6321176, baseEnd_6321176] using wordTrace_append hprefix tailTrace_6321176
  have hstable : (prefixWord ++ tailWord_6321176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321176).length < 2 ^ (prefixWord ++ tailWord_6321176).sum := by decide
  have hdescent : baseEnd_6321176 < baseStart_6321176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321195 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 4]
def baseStart_6321195 : Nat := 118140960795 + 6321195 * 2 ^ 59
def prefixEnd_6321195 : Nat := 4983230072969 + 3 ^ 40 * 6321195 * 2
def baseEnd_6321195 : Nat := 3245811345797501029191859

theorem tailTrace_6321195 : CollatzResearch.WordTrace tailWord_6321195 prefixEnd_6321195 3245811345797501029191859 := by
  unfold tailWord_6321195
  simp only [CollatzResearch.WordTrace]
  refine ⟨230552922334397564001821039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153701948222931709334547359 230552922334397564001821039)
  ·
    refine ⟨345829383501596346002731559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230552922334397564001821039 345829383501596346002731559)
    ·
      refine ⟨518744075252394519004097339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345829383501596346002731559 518744075252394519004097339)
      ·
        refine ⟨778116112878591778506146009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518744075252394519004097339 778116112878591778506146009)
        ·
          refine ⟨583587084658943833879609507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 778116112878591778506146009 583587084658943833879609507)
          ·
            refine ⟨875380626988415750819414261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583587084658943833879609507 875380626988415750819414261)
            ·
              refine ⟨82066933780163976639320087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 875380626988415750819414261 82066933780163976639320087)
              ·
                refine ⟨123100400670245964958980131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82066933780163976639320087 123100400670245964958980131)
                ·
                  refine ⟨184650601005368947438470197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123100400670245964958980131 184650601005368947438470197)
                  ·
                    refine ⟨17310993844253338822356581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 184650601005368947438470197 17310993844253338822356581)
                    ·
                      refine ⟨3245811345797501029191859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17310993844253338822356581 3245811345797501029191859)
                      ·
                        rfl

theorem cell23_6321195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 4].length) (baseStart_6321195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321195 prefixEnd_6321195 := by exact prefixLift 6321195
  have htrace : WordTrace (prefixWord ++ tailWord_6321195) baseStart_6321195 baseEnd_6321195 := by
    simpa [prefixWord, tailWord_6321195, baseEnd_6321195] using wordTrace_append hprefix tailTrace_6321195
  have hstable : (prefixWord ++ tailWord_6321195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321195).length < 2 ^ (prefixWord ++ tailWord_6321195).sum := by decide
  have hdescent : baseEnd_6321195 < baseStart_6321195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321206 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_6321206 : Nat := 118140960795 + 6321206 * 2 ^ 59
def prefixEnd_6321206 : Nat := 4983230072969 + 3 ^ 40 * 6321206 * 2
def baseEnd_6321206 : Nat := 3245816994084700486154309

theorem tailTrace_6321206 : CollatzResearch.WordTrace tailWord_6321206 prefixEnd_6321206 3245816994084700486154309 := by
  unfold tailWord_6321206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14409582721084857055029467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153702215691571808586980981 14409582721084857055029467)
  ·
    refine ⟨21614374081627285582544201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14409582721084857055029467 21614374081627285582544201)
    ·
      refine ⟨16210780561220464186908151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21614374081627285582544201 16210780561220464186908151)
      ·
        refine ⟨24316170841830696280362227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16210780561220464186908151 24316170841830696280362227)
        ·
          refine ⟨36474256262746044420543341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24316170841830696280362227 36474256262746044420543341)
          ·
            refine ⟨13677846098529766657703753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36474256262746044420543341 13677846098529766657703753)
            ·
              refine ⟨10258384573897324993277815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13677846098529766657703753 10258384573897324993277815)
              ·
                refine ⟨15387576860845987489916723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10258384573897324993277815 15387576860845987489916723)
                ·
                  refine ⟨23081365291268981234875085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15387576860845987489916723 23081365291268981234875085)
                  ·
                    refine ⟨8655511984225867963078157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23081365291268981234875085 8655511984225867963078157)
                    ·
                      refine ⟨3245816994084700486154309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8655511984225867963078157 3245816994084700486154309)
                      ·
                        rfl

theorem cell23_6321206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_6321206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321206 prefixEnd_6321206 := by exact prefixLift 6321206
  have htrace : WordTrace (prefixWord ++ tailWord_6321206) baseStart_6321206 baseEnd_6321206 := by
    simpa [prefixWord, tailWord_6321206, baseEnd_6321206] using wordTrace_append hprefix tailTrace_6321206
  have hstable : (prefixWord ++ tailWord_6321206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321206).length < 2 ^ (prefixWord ++ tailWord_6321206).sum := by decide
  have hdescent : baseEnd_6321206 < baseStart_6321206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321263 : List Nat := [1, 1, 2, 1, 3, 3, 5, 1, 2, 2, 2]
def baseStart_6321263 : Nat := 118140960795 + 6321263 * 2 ^ 59
def prefixEnd_6321263 : Nat := 4983230072969 + 3 ^ 40 * 6321263 * 2
def baseEnd_6321263 : Nat := 3245846262482006763141547

theorem tailTrace_6321263 : CollatzResearch.WordTrace tailWord_6321263 prefixEnd_6321263 3245846262482006763141547 := by
  unfold tailWord_6321263
  simp only [CollatzResearch.WordTrace]
  refine ⟨230555402498151211615296443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153703601665434141076864295 230555402498151211615296443)
  ·
    refine ⟨345833103747226817422944665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230555402498151211615296443 345833103747226817422944665)
    ·
      refine ⟨259374827810420113067208499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345833103747226817422944665 259374827810420113067208499)
      ·
        refine ⟨389062241715630169600812749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259374827810420113067208499 389062241715630169600812749)
        ·
          refine ⟨145898340643361313600304781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389062241715630169600812749 145898340643361313600304781)
          ·
            refine ⟨54711877741260492600114293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145898340643361313600304781 54711877741260492600114293)
            ·
              refine ⟨5129238538243171181260715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54711877741260492600114293 5129238538243171181260715)
              ·
                refine ⟨7693857807364756771891073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129238538243171181260715 7693857807364756771891073)
                ·
                  refine ⟨5770393355523567578918305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7693857807364756771891073 5770393355523567578918305)
                  ·
                    refine ⟨4327795016642675684188729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5770393355523567578918305 4327795016642675684188729)
                    ·
                      refine ⟨3245846262482006763141547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4327795016642675684188729 3245846262482006763141547)
                      ·
                        rfl

theorem cell23_6321263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 2, 2, 2].length) (baseStart_6321263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321263 prefixEnd_6321263 := by exact prefixLift 6321263
  have htrace : WordTrace (prefixWord ++ tailWord_6321263) baseStart_6321263 baseEnd_6321263 := by
    simpa [prefixWord, tailWord_6321263, baseEnd_6321263] using wordTrace_append hprefix tailTrace_6321263
  have hstable : (prefixWord ++ tailWord_6321263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321263).length < 2 ^ (prefixWord ++ tailWord_6321263).sum := by decide
  have hdescent : baseEnd_6321263 < baseStart_6321263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321314 : List Nat := [3, 3, 1, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_6321314 : Nat := 118140960795 + 6321314 * 2 ^ 59
def prefixEnd_6321314 : Nat := 4983230072969 + 3 ^ 40 * 6321314 * 2
def baseEnd_6321314 : Nat := 3245872449995386063603813

theorem tailTrace_6321314 : CollatzResearch.WordTrace tailWord_6321314 prefixEnd_6321314 3245872449995386063603813 := by
  unfold tailWord_6321314
  simp only [CollatzResearch.WordTrace]
  refine ⟨57639315655241611831350749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153704841747310964883601997 57639315655241611831350749)
  ·
    refine ⟨21614743370715604436756531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57639315655241611831350749 21614743370715604436756531)
    ·
      refine ⟨32422115056073406655134797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21614743370715604436756531 32422115056073406655134797)
      ·
        refine ⟨12158293146027527495675549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32422115056073406655134797 12158293146027527495675549)
        ·
          refine ⟨4559359929760322810878331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12158293146027527495675549 4559359929760322810878331)
          ·
            refine ⟨6839039894640484216317497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4559359929760322810878331 6839039894640484216317497)
            ·
              refine ⟨5129279920980363162238123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6839039894640484216317497 5129279920980363162238123)
              ·
                refine ⟨7693919881470544743357185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129279920980363162238123 7693919881470544743357185)
                ·
                  refine ⟨5770439911102908557517889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7693919881470544743357185 5770439911102908557517889)
                  ·
                    refine ⟨4327829933327181418138417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5770439911102908557517889 4327829933327181418138417)
                    ·
                      refine ⟨3245872449995386063603813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4327829933327181418138417 3245872449995386063603813)
                      ·
                        rfl

theorem cell23_6321314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_6321314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321314 prefixEnd_6321314 := by exact prefixLift 6321314
  have htrace : WordTrace (prefixWord ++ tailWord_6321314) baseStart_6321314 baseEnd_6321314 := by
    simpa [prefixWord, tailWord_6321314, baseEnd_6321314] using wordTrace_append hprefix tailTrace_6321314
  have hstable : (prefixWord ++ tailWord_6321314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321314).length < 2 ^ (prefixWord ++ tailWord_6321314).sum := by decide
  have hdescent : baseEnd_6321314 < baseStart_6321314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321386 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_6321386 : Nat := 118140960795 + 6321386 * 2 ^ 59
def prefixEnd_6321386 : Nat := 4983230072969 + 3 ^ 40 * 6321386 * 2
def baseEnd_6321386 : Nat := 3245909420602509781903481

theorem tailTrace_6321386 : CollatzResearch.WordTrace tailWord_6321386 prefixEnd_6321386 3245909420602509781903481 := by
  unfold tailWord_6321386
  simp only [CollatzResearch.WordTrace]
  refine ⟨57639972169176400905506003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153706592451137069081349341 57639972169176400905506003)
  ·
    refine ⟨86459958253764601358259005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57639972169176400905506003 86459958253764601358259005)
    ·
      refine ⟨32422484345161725509347127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86459958253764601358259005 32422484345161725509347127)
      ·
        refine ⟨48633726517742588264020691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32422484345161725509347127 48633726517742588264020691)
        ·
          refine ⟨72950589776613882396031037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48633726517742588264020691 72950589776613882396031037)
          ·
            refine ⟨27356471166230205898511639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72950589776613882396031037 27356471166230205898511639)
            ·
              refine ⟨41034706749345308847767459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27356471166230205898511639 41034706749345308847767459)
              ·
                refine ⟨61552060124017963271651189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41034706749345308847767459 61552060124017963271651189)
                ·
                  refine ⟨5770505636626684056717299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61552060124017963271651189 5770505636626684056717299)
                  ·
                    refine ⟨8655758454940026085075949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5770505636626684056717299 8655758454940026085075949)
                    ·
                      refine ⟨3245909420602509781903481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8655758454940026085075949 3245909420602509781903481)
                      ·
                        rfl

theorem cell23_6321386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_6321386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321386 prefixEnd_6321386 := by exact prefixLift 6321386
  have htrace : WordTrace (prefixWord ++ tailWord_6321386) baseStart_6321386 baseEnd_6321386 := by
    simpa [prefixWord, tailWord_6321386, baseEnd_6321386] using wordTrace_append hprefix tailTrace_6321386
  have hstable : (prefixWord ++ tailWord_6321386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321386).length < 2 ^ (prefixWord ++ tailWord_6321386).sum := by decide
  have hdescent : baseEnd_6321386 < baseStart_6321386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321410 : List Nat := [3, 4, 1, 1, 4, 1, 1, 2, 6]
def baseStart_6321410 : Nat := 118140960795 + 6321410 * 2 ^ 59
def prefixEnd_6321410 : Nat := 4983230072969 + 3 ^ 40 * 6321410 * 2
def baseEnd_6321410 : Nat := 360657971570913076444819

theorem tailTrace_6321410 : CollatzResearch.WordTrace tailWord_6321410 prefixEnd_6321410 360657971570913076444819 := by
  unfold tailWord_6321410
  simp only [CollatzResearch.WordTrace]
  refine ⟨57640191007154663930224421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153707176019079103813931789 57640191007154663930224421)
  ·
    refine ⟨10807535813841499486917079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57640191007154663930224421 10807535813841499486917079)
    ·
      refine ⟨16211303720762249230375619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10807535813841499486917079 16211303720762249230375619)
      ·
        refine ⟨24316955581143373845563429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16211303720762249230375619 24316955581143373845563429)
        ·
          refine ⟨4559429171464382596043143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24316955581143373845563429 4559429171464382596043143)
          ·
            refine ⟨6839143757196573894064715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4559429171464382596043143 6839143757196573894064715)
            ·
              refine ⟨10258715635794860841097073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6839143757196573894064715 10258715635794860841097073)
              ·
                refine ⟨7694036726846145630822805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10258715635794860841097073 7694036726846145630822805)
                ·
                  refine ⟨360657971570913076444819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7694036726846145630822805 360657971570913076444819)
                  ·
                    rfl

theorem cell23_6321410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_6321410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321410 prefixEnd_6321410 := by exact prefixLift 6321410
  have htrace : WordTrace (prefixWord ++ tailWord_6321410) baseStart_6321410 baseEnd_6321410 := by
    simpa [prefixWord, tailWord_6321410, baseEnd_6321410] using wordTrace_append hprefix tailTrace_6321410
  have hstable : (prefixWord ++ tailWord_6321410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321410).length < 2 ^ (prefixWord ++ tailWord_6321410).sum := by decide
  have hdescent : baseEnd_6321410 < baseStart_6321410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321436 : List Nat := [2, 2, 3, 1, 1, 1, 2, 5, 2, 4]
def baseStart_6321436 : Nat := 118140960795 + 6321436 * 2 ^ 59
def prefixEnd_6321436 : Nat := 4983230072969 + 3 ^ 40 * 6321436 * 2
def baseEnd_6321436 : Nat := 1081978364878411528759417

theorem tailTrace_6321436 : CollatzResearch.WordTrace tailWord_6321436 prefixEnd_6321436 1081978364878411528759417 := by
  unfold tailWord_6321436
  simp only [CollatzResearch.WordTrace]
  refine ⟨115280856163262231080672081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153707808217682974774229441 115280856163262231080672081)
  ·
    refine ⟨86460642122446673310504061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115280856163262231080672081 86460642122446673310504061)
    ·
      refine ⟨32422740795917502491439023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86460642122446673310504061 32422740795917502491439023)
      ·
        refine ⟨48634111193876253737158535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32422740795917502491439023 48634111193876253737158535)
        ·
          refine ⟨72951166790814380605737803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48634111193876253737158535 72951166790814380605737803)
          ·
            refine ⟨109426750186221570908606705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72951166790814380605737803 109426750186221570908606705)
            ·
              refine ⟨82070062639666178181455029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109426750186221570908606705 82070062639666178181455029)
              ·
                refine ⟨7694068372468704204511409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82070062639666178181455029 7694068372468704204511409)
                ·
                  refine ⟨5770551279351528153383557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7694068372468704204511409 5770551279351528153383557)
                  ·
                    refine ⟨1081978364878411528759417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5770551279351528153383557 1081978364878411528759417)
                    ·
                      rfl

theorem cell23_6321436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_6321436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321436 prefixEnd_6321436 := by exact prefixLift 6321436
  have htrace : WordTrace (prefixWord ++ tailWord_6321436) baseStart_6321436 baseEnd_6321436 := by
    simpa [prefixWord, tailWord_6321436, baseEnd_6321436] using wordTrace_append hprefix tailTrace_6321436
  have hstable : (prefixWord ++ tailWord_6321436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321436).length < 2 ^ (prefixWord ++ tailWord_6321436).sum := by decide
  have hdescent : baseEnd_6321436 < baseStart_6321436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321443 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 3, 2, 2]
def baseStart_6321443 : Nat := 118140960795 + 6321443 * 2 ^ 59
def prefixEnd_6321443 : Nat := 4983230072969 + 3 ^ 40 * 6321443 * 2
def baseEnd_6321443 : Nat := 3245938688999816058890719

theorem tailTrace_6321443 : CollatzResearch.WordTrace tailWord_6321443 prefixEnd_6321443 3245938688999816058890719 := by
  unfold tailWord_6321443
  simp only [CollatzResearch.WordTrace]
  refine ⟨230561967637499102356848983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153707978424999401571232655 230561967637499102356848983)
  ·
    refine ⟨345842951456248653535273475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230561967637499102356848983 345842951456248653535273475)
    ·
      refine ⟨518764427184372980302910213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345842951456248653535273475 518764427184372980302910213)
      ·
        refine ⟨97268330097069933806795665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 518764427184372980302910213 97268330097069933806795665)
        ·
          refine ⟨72951247572802450355096749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97268330097069933806795665 72951247572802450355096749)
          ·
            refine ⟨27356717839800918883161281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72951247572802450355096749 27356717839800918883161281)
            ·
              refine ⟨20517538379850689162370961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27356717839800918883161281 20517538379850689162370961)
              ·
                refine ⟨15388153784888016871778221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20517538379850689162370961 15388153784888016871778221)
                ·
                  refine ⟨5770557669333006326916833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15388153784888016871778221 5770557669333006326916833)
                  ·
                    refine ⟨4327918251999754745187625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5770557669333006326916833 4327918251999754745187625)
                    ·
                      refine ⟨3245938688999816058890719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4327918251999754745187625 3245938688999816058890719)
                      ·
                        rfl

theorem cell23_6321443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_6321443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321443 prefixEnd_6321443 := by exact prefixLift 6321443
  have htrace : WordTrace (prefixWord ++ tailWord_6321443) baseStart_6321443 baseEnd_6321443 := by
    simpa [prefixWord, tailWord_6321443, baseEnd_6321443] using wordTrace_append hprefix tailTrace_6321443
  have hstable : (prefixWord ++ tailWord_6321443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321443).length < 2 ^ (prefixWord ++ tailWord_6321443).sum := by decide
  have hdescent : baseEnd_6321443 < baseStart_6321443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321453 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_6321453 : Nat := 118140960795 + 6321453 * 2 ^ 59
def prefixEnd_6321453 : Nat := 4983230072969 + 3 ^ 40 * 6321453 * 2
def baseEnd_6321453 : Nat := 1081981274602120339921891

theorem tailTrace_6321453 : CollatzResearch.WordTrace tailWord_6321453 prefixEnd_6321453 1081981274602120339921891 := by
  unfold tailWord_6321453
  simp only [CollatzResearch.WordTrace]
  refine ⟨230562332367462874064713013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153708221578308582709808675 230562332367462874064713013)
  ·
    refine ⟨21615218659449644443566845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 230562332367462874064713013 21615218659449644443566845)
    ·
      refine ⟨8105706997293616666337567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21615218659449644443566845 8105706997293616666337567)
      ·
        refine ⟨12158560495940424999506351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8105706997293616666337567 12158560495940424999506351)
        ·
          refine ⟨18237840743910637499259527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12158560495940424999506351 18237840743910637499259527)
          ·
            refine ⟨27356761115865956248889291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18237840743910637499259527 27356761115865956248889291)
            ·
              refine ⟨41035141673798934373333937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27356761115865956248889291 41035141673798934373333937)
              ·
                refine ⟨30776356255349200780000453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41035141673798934373333937 30776356255349200780000453)
                ·
                  refine ⟨5770566797877975146250085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30776356255349200780000453 5770566797877975146250085)
                  ·
                    refine ⟨1081981274602120339921891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5770566797877975146250085 1081981274602120339921891)
                    ·
                      rfl

theorem cell23_6321453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_6321453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321453 prefixEnd_6321453 := by exact prefixLift 6321453
  have htrace : WordTrace (prefixWord ++ tailWord_6321453) baseStart_6321453 baseEnd_6321453 := by
    simpa [prefixWord, tailWord_6321453, baseEnd_6321453] using wordTrace_append hprefix tailTrace_6321453
  have hstable : (prefixWord ++ tailWord_6321453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321453).length < 2 ^ (prefixWord ++ tailWord_6321453).sum := by decide
  have hdescent : baseEnd_6321453 < baseStart_6321453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321519 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 5]
def baseStart_6321519 : Nat := 118140960795 + 6321519 * 2 ^ 59
def prefixEnd_6321519 : Nat := 4983230072969 + 3 ^ 40 * 6321519 * 2
def baseEnd_6321519 : Nat := 3245977713529557761540369

theorem tailTrace_6321519 : CollatzResearch.WordTrace tailWord_6321519 prefixEnd_6321519 3245977713529557761540369 := by
  unfold tailWord_6321519
  simp only [CollatzResearch.WordTrace]
  refine ⟨230564739585223767336615611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153709826390149178224410407 230564739585223767336615611)
  ·
    refine ⟨345847109377835651004923417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230564739585223767336615611 345847109377835651004923417)
    ·
      refine ⟨259385332033376738253692563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 345847109377835651004923417 259385332033376738253692563)
      ·
        refine ⟨389077998050065107380538845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259385332033376738253692563 389077998050065107380538845)
        ·
          refine ⟨145904249268774415267702067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389077998050065107380538845 145904249268774415267702067)
          ·
            refine ⟨218856373903161622901553101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145904249268774415267702067 218856373903161622901553101)
            ·
              refine ⟨82071140213685608588082413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218856373903161622901553101 82071140213685608588082413)
              ·
                refine ⟨30776677580132103220530905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82071140213685608588082413 30776677580132103220530905)
                ·
                  refine ⟨23082508185099077415398179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30776677580132103220530905 23082508185099077415398179)
                  ·
                    refine ⟨34623762277648616123097269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23082508185099077415398179 34623762277648616123097269)
                    ·
                      refine ⟨3245977713529557761540369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34623762277648616123097269 3245977713529557761540369)
                      ·
                        rfl

theorem cell23_6321519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_6321519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321519 prefixEnd_6321519 := by exact prefixLift 6321519
  have htrace : WordTrace (prefixWord ++ tailWord_6321519) baseStart_6321519 baseEnd_6321519 := by
    simpa [prefixWord, tailWord_6321519, baseEnd_6321519] using wordTrace_append hprefix tailTrace_6321519
  have hstable : (prefixWord ++ tailWord_6321519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321519).length < 2 ^ (prefixWord ++ tailWord_6321519).sum := by decide
  have hdescent : baseEnd_6321519 < baseStart_6321519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321520 : List Nat := [2, 1, 1, 1, 4, 2, 5, 1, 1, 3, 2]
def baseStart_6321520 : Nat := 118140960795 + 6321520 * 2 ^ 59
def prefixEnd_6321520 : Nat := 4983230072969 + 3 ^ 40 * 6321520 * 2
def baseEnd_6321520 : Nat := 3245978227010212257627865

theorem tailTrace_6321520 : CollatzResearch.WordTrace tailWord_6321520 prefixEnd_6321520 3245978227010212257627865 := by
  unfold tailWord_6321520
  simp only [CollatzResearch.WordTrace]
  refine ⟨115282388029110072253701007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153709850705480096338268009 115282388029110072253701007)
  ·
    refine ⟨172923582043665108380551511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115282388029110072253701007 172923582043665108380551511)
    ·
      refine ⟨259385373065497662570827267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172923582043665108380551511 259385373065497662570827267)
      ·
        refine ⟨389078059598246493856240901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259385373065497662570827267 389078059598246493856240901)
        ·
          refine ⟨72952136174671217598045169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389078059598246493856240901 72952136174671217598045169)
          ·
            refine ⟨54714102131003413198533877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72952136174671217598045169 54714102131003413198533877)
            ·
              refine ⟨5129447074781569987362551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54714102131003413198533877 5129447074781569987362551)
              ·
                refine ⟨7694170612172354981043827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129447074781569987362551 7694170612172354981043827)
                ·
                  refine ⟨11541255918258532471565741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7694170612172354981043827 11541255918258532471565741)
                  ·
                    refine ⟨4327970969346949676837153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11541255918258532471565741 4327970969346949676837153)
                    ·
                      refine ⟨3245978227010212257627865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4327970969346949676837153 3245978227010212257627865)
                      ·
                        rfl

theorem cell23_6321520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 1, 3, 2].length) (baseStart_6321520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321520 prefixEnd_6321520 := by exact prefixLift 6321520
  have htrace : WordTrace (prefixWord ++ tailWord_6321520) baseStart_6321520 baseEnd_6321520 := by
    simpa [prefixWord, tailWord_6321520, baseEnd_6321520] using wordTrace_append hprefix tailTrace_6321520
  have hstable : (prefixWord ++ tailWord_6321520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321520).length < 2 ^ (prefixWord ++ tailWord_6321520).sum := by decide
  have hdescent : baseEnd_6321520 < baseStart_6321520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321556 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 9]
def baseStart_6321556 : Nat := 118140960795 + 6321556 * 2 ^ 59
def prefixEnd_6321556 : Nat := 4983230072969 + 3 ^ 40 * 6321556 * 2
def baseEnd_6321556 : Nat := 360666301368197124086411

theorem tailTrace_6321556 : CollatzResearch.WordTrace tailWord_6321556 prefixEnd_6321556 360666301368197124086411 := by
  unfold tailWord_6321556
  simp only [CollatzResearch.WordTrace]
  refine ⟨115283044543044861327856261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153710726057393148437141681 115283044543044861327856261)
  ·
    refine ⟨21615570851820911498973049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115283044543044861327856261 21615570851820911498973049)
    ·
      refine ⟨16211678138865683624229787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21615570851820911498973049 16211678138865683624229787)
      ·
        refine ⟨24317517208298525436344681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16211678138865683624229787 24317517208298525436344681)
        ·
          refine ⟨18238137906223894077258511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24317517208298525436344681 18238137906223894077258511)
          ·
            refine ⟨27357206859335841115887767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18238137906223894077258511 27357206859335841115887767)
            ·
              refine ⟨41035810289003761673831651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27357206859335841115887767 41035810289003761673831651)
              ·
                refine ⟨61553715433505642510747477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41035810289003761673831651 61553715433505642510747477)
                ·
                  refine ⟨360666301368197124086411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61553715433505642510747477 360666301368197124086411)
                  ·
                    rfl

theorem cell23_6321556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_6321556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321556 prefixEnd_6321556 := by exact prefixLift 6321556
  have htrace : WordTrace (prefixWord ++ tailWord_6321556) baseStart_6321556 baseEnd_6321556 := by
    simpa [prefixWord, tailWord_6321556, baseEnd_6321556] using wordTrace_append hprefix tailTrace_6321556
  have hstable : (prefixWord ++ tailWord_6321556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321556).length < 2 ^ (prefixWord ++ tailWord_6321556).sum := by decide
  have hdescent : baseEnd_6321556 < baseStart_6321556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321646 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 8]
def baseStart_6321646 : Nat := 118140960795 + 6321646 * 2 ^ 59
def prefixEnd_6321646 : Nat := 4983230072969 + 3 ^ 40 * 6321646 * 2
def baseEnd_6321646 : Nat := 360671436174742084961365

theorem tailTrace_6321646 : CollatzResearch.WordTrace tailWord_6321646 prefixEnd_6321646 360671436174742084961365 := by
  unfold tailWord_6321646
  simp only [CollatzResearch.WordTrace]
  refine ⟨28821171456970458503311099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153712914437175778684325861 28821171456970458503311099)
  ·
    refine ⟨43231757185455687754966649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28821171456970458503311099 43231757185455687754966649)
    ·
      refine ⟨32423817889091765816224987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43231757185455687754966649 32423817889091765816224987)
      ·
        refine ⟨48635726833637648724337481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32423817889091765816224987 48635726833637648724337481)
        ·
          refine ⟨36476795125228236543253111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48635726833637648724337481 36476795125228236543253111)
          ·
            refine ⟨54715192687842354814879667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36476795125228236543253111 54715192687842354814879667)
            ·
              refine ⟨82072789031763532222319501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54715192687842354814879667 82072789031763532222319501)
              ·
                refine ⟨30777295886911324583369813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82072789031763532222319501 30777295886911324583369813)
                ·
                  refine ⟨360671436174742084961365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30777295886911324583369813 360671436174742084961365)
                  ·
                    rfl

theorem cell23_6321646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_6321646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321646 prefixEnd_6321646 := by exact prefixLift 6321646
  have htrace : WordTrace (prefixWord ++ tailWord_6321646) baseStart_6321646 baseEnd_6321646 := by
    simpa [prefixWord, tailWord_6321646, baseEnd_6321646] using wordTrace_append hprefix tailTrace_6321646
  have hstable : (prefixWord ++ tailWord_6321646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321646).length < 2 ^ (prefixWord ++ tailWord_6321646).sum := by decide
  have hdescent : baseEnd_6321646 < baseStart_6321646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321650 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_6321650 : Nat := 118140960795 + 6321650 * 2 ^ 59
def prefixEnd_6321650 : Nat := 4983230072969 + 3 ^ 40 * 6321650 * 2
def baseEnd_6321650 : Nat := 1082014993165098916334089

theorem tailTrace_6321650 : CollatzResearch.WordTrace tailWord_6321650 prefixEnd_6321650 1082014993165098916334089 := by
  unfold tailWord_6321650
  simp only [CollatzResearch.WordTrace]
  refine ⟨57642379386937294177408601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153713011698499451139756269 57642379386937294177408601)
  ·
    refine ⟨43231784540202970633056451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57642379386937294177408601 43231784540202970633056451)
    ·
      refine ⟨64847676810304455949584677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43231784540202970633056451 64847676810304455949584677)
      ·
        refine ⟨12158939401932085490547127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64847676810304455949584677 12158939401932085490547127)
        ·
          refine ⟨18238409102898128235820691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12158939401932085490547127 18238409102898128235820691)
          ·
            refine ⟨27357613654347192353731037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18238409102898128235820691 27357613654347192353731037)
            ·
              refine ⟨10259105120380197132649139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27357613654347192353731037 10259105120380197132649139)
              ·
                refine ⟨15388657680570295698973709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10259105120380197132649139 15388657680570295698973709)
                ·
                  refine ⟨5770746630213860887115141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15388657680570295698973709 5770746630213860887115141)
                  ·
                    refine ⟨1082014993165098916334089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5770746630213860887115141 1082014993165098916334089)
                    ·
                      rfl

theorem cell23_6321650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_6321650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321650 prefixEnd_6321650 := by exact prefixLift 6321650
  have htrace : WordTrace (prefixWord ++ tailWord_6321650) baseStart_6321650 baseEnd_6321650 := by
    simpa [prefixWord, tailWord_6321650, baseEnd_6321650] using wordTrace_append hprefix tailTrace_6321650
  have hstable : (prefixWord ++ tailWord_6321650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321650).length < 2 ^ (prefixWord ++ tailWord_6321650).sum := by decide
  have hdescent : baseEnd_6321650 < baseStart_6321650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321673 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 5, 1, 3]
def baseStart_6321673 : Nat := 118140960795 + 6321673 * 2 ^ 59
def prefixEnd_6321673 : Nat := 4983230072969 + 3 ^ 40 * 6321673 * 2
def baseEnd_6321673 : Nat := 3246056789550350159014661

theorem tailTrace_6321673 : CollatzResearch.WordTrace tailWord_6321673 prefixEnd_6321673 3246056789550350159014661 := by
  unfold tailWord_6321673
  simp only [CollatzResearch.WordTrace]
  refine ⟨230570356426665851637721673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153713570951110567758481115 230570356426665851637721673)
  ·
    refine ⟨172927767319999388728291255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230570356426665851637721673 172927767319999388728291255)
    ·
      refine ⟨259391650979999083092436883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172927767319999388728291255 259391650979999083092436883)
      ·
        refine ⟨389087476469998624638655325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259391650979999083092436883 389087476469998624638655325)
        ·
          refine ⟨145907803676249484239495747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389087476469998624638655325 145907803676249484239495747)
          ·
            refine ⟨218861705514374226359243621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145907803676249484239495747 218861705514374226359243621)
            ·
              refine ⟨41036569783945167442358179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218861705514374226359243621 41036569783945167442358179)
              ·
                refine ⟨61554854675917751163537269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41036569783945167442358179 61554854675917751163537269)
                ·
                  refine ⟨5770767625867289171581619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61554854675917751163537269 5770767625867289171581619)
                  ·
                    refine ⟨8656151438800933757372429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5770767625867289171581619 8656151438800933757372429)
                    ·
                      refine ⟨3246056789550350159014661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8656151438800933757372429 3246056789550350159014661)
                      ·
                        rfl

theorem cell23_6321673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 1, 3].length) (baseStart_6321673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321673 prefixEnd_6321673 := by exact prefixLift 6321673
  have htrace : WordTrace (prefixWord ++ tailWord_6321673) baseStart_6321673 baseEnd_6321673 := by
    simpa [prefixWord, tailWord_6321673, baseEnd_6321673] using wordTrace_append hprefix tailTrace_6321673
  have hstable : (prefixWord ++ tailWord_6321673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321673).length < 2 ^ (prefixWord ++ tailWord_6321673).sum := by decide
  have hdescent : baseEnd_6321673 < baseStart_6321673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321713 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 2, 6, 2]
def baseStart_6321713 : Nat := 118140960795 + 6321713 * 2 ^ 59
def prefixEnd_6321713 : Nat := 4983230072969 + 3 ^ 40 * 6321713 * 2
def baseEnd_6321713 : Nat := 3246077328776530002514477

theorem tailTrace_6321713 : CollatzResearch.WordTrace tailWord_6321713 prefixEnd_6321713 3246077328776530002514477 := by
  unfold tailWord_6321713
  simp only [CollatzResearch.WordTrace]
  refine ⟨230571815346520938469177793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153714543564347292312785195 230571815346520938469177793)
  ·
    refine ⟨172928861509890703851883345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230571815346520938469177793 172928861509890703851883345)
    ·
      refine ⟨129696646132418027888912509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172928861509890703851883345 129696646132418027888912509)
      ·
        refine ⟨48636242299656760458342191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129696646132418027888912509 48636242299656760458342191)
        ·
          refine ⟨72954363449485140687513287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48636242299656760458342191 72954363449485140687513287)
          ·
            refine ⟨109431545174227711031269931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72954363449485140687513287 109431545174227711031269931)
            ·
              refine ⟨164147317761341566546904897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109431545174227711031269931 164147317761341566546904897)
              ·
                refine ⟨123110488321006174910178673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164147317761341566546904897 123110488321006174910178673)
                ·
                  refine ⟨92332866240754631182634005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123110488321006174910178673 92332866240754631182634005)
                  ·
                    refine ⟨4328103105035373336685969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92332866240754631182634005 4328103105035373336685969)
                    ·
                      refine ⟨3246077328776530002514477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328103105035373336685969 3246077328776530002514477)
                      ·
                        rfl

theorem cell23_6321713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_6321713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321713 prefixEnd_6321713 := by exact prefixLift 6321713
  have htrace : WordTrace (prefixWord ++ tailWord_6321713) baseStart_6321713 baseEnd_6321713 := by
    simpa [prefixWord, tailWord_6321713, baseEnd_6321713] using wordTrace_append hprefix tailTrace_6321713
  have hstable : (prefixWord ++ tailWord_6321713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321713).length < 2 ^ (prefixWord ++ tailWord_6321713).sum := by decide
  have hdescent : baseEnd_6321713 < baseStart_6321713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321733 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 3, 2, 3]
def baseStart_6321733 : Nat := 118140960795 + 6321733 * 2 ^ 59
def prefixEnd_6321733 : Nat := 4983230072969 + 3 ^ 40 * 6321733 * 2
def baseEnd_6321733 : Nat := 3246087598389619924264385

theorem tailTrace_6321733 : CollatzResearch.WordTrace tailWord_6321733 prefixEnd_6321733 3246087598389619924264385 := by
  unfold tailWord_6321733
  simp only [CollatzResearch.WordTrace]
  refine ⟨230572544806448481884905853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153715029870965654589937235 230572544806448481884905853)
  ·
    refine ⟨86464704302418180706839695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230572544806448481884905853 86464704302418180706839695)
    ·
      refine ⟨129697056453627271060259543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86464704302418180706839695 129697056453627271060259543)
      ·
        refine ⟨194545584680440906590389315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129697056453627271060259543 194545584680440906590389315)
        ·
          refine ⟨291818377020661359885583973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194545584680440906590389315 291818377020661359885583973)
          ·
            refine ⟨54715945691374004978546995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291818377020661359885583973 54715945691374004978546995)
            ·
              refine ⟨82073918537061007467820493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54715945691374004978546995 82073918537061007467820493)
              ·
                refine ⟨30777719451397877800432685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82073918537061007467820493 30777719451397877800432685)
                ·
                  refine ⟨11541644794274204175162257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30777719451397877800432685 11541644794274204175162257)
                  ·
                    refine ⟨8656233595705653131371693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11541644794274204175162257 8656233595705653131371693)
                    ·
                      refine ⟨3246087598389619924264385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8656233595705653131371693 3246087598389619924264385)
                      ·
                        rfl

theorem cell23_6321733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_6321733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321733 prefixEnd_6321733 := by exact prefixLift 6321733
  have htrace : WordTrace (prefixWord ++ tailWord_6321733) baseStart_6321733 baseEnd_6321733 := by
    simpa [prefixWord, tailWord_6321733, baseEnd_6321733] using wordTrace_append hprefix tailTrace_6321733
  have hstable : (prefixWord ++ tailWord_6321733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321733).length < 2 ^ (prefixWord ++ tailWord_6321733).sum := by decide
  have hdescent : baseEnd_6321733 < baseStart_6321733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321734 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_6321734 : Nat := 118140960795 + 6321734 * 2 ^ 59
def prefixEnd_6321734 : Nat := 4983230072969 + 3 ^ 40 * 6321734 * 2
def baseEnd_6321734 : Nat := 3246088111870274420351881

theorem tailTrace_6321734 : CollatzResearch.WordTrace tailWord_6321734 prefixEnd_6321734 3246088111870274420351881 := by
  unfold tailWord_6321734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7205393164982651845490383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153715054186296572703794837 7205393164982651845490383)
  ·
    refine ⟨10808089747473977768235575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7205393164982651845490383 10808089747473977768235575)
    ·
      refine ⟨16212134621210966652353363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10808089747473977768235575 16212134621210966652353363)
      ·
        refine ⟨24318201931816449978530045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16212134621210966652353363 24318201931816449978530045)
        ·
          refine ⟨9119325724431168741948767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24318201931816449978530045 9119325724431168741948767)
          ·
            refine ⟨13678988586646753112923151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9119325724431168741948767 13678988586646753112923151)
            ·
              refine ⟨20518482879970129669384727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13678988586646753112923151 20518482879970129669384727)
              ·
                refine ⟨30777724319955194504077091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20518482879970129669384727 30777724319955194504077091)
                ·
                  refine ⟨46166586479932791756115637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30777724319955194504077091 46166586479932791756115637)
                  ·
                    refine ⟨4328117482493699227135841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46166586479932791756115637 4328117482493699227135841)
                    ·
                      refine ⟨3246088111870274420351881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328117482493699227135841 3246088111870274420351881)
                      ·
                        rfl

theorem cell23_6321734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_6321734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321734 prefixEnd_6321734 := by exact prefixLift 6321734
  have htrace : WordTrace (prefixWord ++ tailWord_6321734) baseStart_6321734 baseEnd_6321734 := by
    simpa [prefixWord, tailWord_6321734, baseEnd_6321734] using wordTrace_append hprefix tailTrace_6321734
  have hstable : (prefixWord ++ tailWord_6321734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321734).length < 2 ^ (prefixWord ++ tailWord_6321734).sum := by decide
  have hdescent : baseEnd_6321734 < baseStart_6321734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321741 : List Nat := [1, 6, 1, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_6321741 : Nat := 118140960795 + 6321741 * 2 ^ 59
def prefixEnd_6321741 : Nat := 4983230072969 + 3 ^ 40 * 6321741 * 2
def baseEnd_6321741 : Nat := 3246091706234855892964349

theorem tailTrace_6321741 : CollatzResearch.WordTrace tailWord_6321741 prefixEnd_6321741 3246091706234855892964349 := by
  unfold tailWord_6321741
  simp only [CollatzResearch.WordTrace]
  refine ⟨230572836590419499251197077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153715224393612999500798051 230572836590419499251197077)
  ·
    refine ⟨10808101715175914027399863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 230572836590419499251197077 10808101715175914027399863)
    ·
      refine ⟨16212152572763871041099795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10808101715175914027399863 16212152572763871041099795)
      ·
        refine ⟨24318228859145806561649693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16212152572763871041099795 24318228859145806561649693)
        ·
          refine ⟨9119335822179677460618635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24318228859145806561649693 9119335822179677460618635)
          ·
            refine ⟨13679003733269516190927953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9119335822179677460618635 13679003733269516190927953)
            ·
              refine ⟨10259252799952137143195965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13679003733269516190927953 10259252799952137143195965)
              ·
                refine ⟨3847219799982051428698487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10259252799952137143195965 3847219799982051428698487)
                ·
                  refine ⟨5770829699973077143047731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847219799982051428698487 5770829699973077143047731)
                  ·
                    refine ⟨8656244549959615714571597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5770829699973077143047731 8656244549959615714571597)
                    ·
                      refine ⟨3246091706234855892964349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8656244549959615714571597 3246091706234855892964349)
                      ·
                        rfl

theorem cell23_6321741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_6321741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321741 prefixEnd_6321741 := by exact prefixLift 6321741
  have htrace : WordTrace (prefixWord ++ tailWord_6321741) baseStart_6321741 baseEnd_6321741 := by
    simpa [prefixWord, tailWord_6321741, baseEnd_6321741] using wordTrace_append hprefix tailTrace_6321741
  have hstable : (prefixWord ++ tailWord_6321741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321741).length < 2 ^ (prefixWord ++ tailWord_6321741).sum := by decide
  have hdescent : baseEnd_6321741 < baseStart_6321741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321764 : List Nat := [2, 3, 1, 1, 2, 3, 2, 4, 1, 2, 2]
def baseStart_6321764 : Nat := 118140960795 + 6321764 * 2 ^ 59
def prefixEnd_6321764 : Nat := 4983230072969 + 3 ^ 40 * 6321764 * 2
def baseEnd_6321764 : Nat := 3246103516289909302976743

theorem tailTrace_6321764 : CollatzResearch.WordTrace tailWord_6321764 prefixEnd_6321764 3246103516289909302976743 := by
  unfold tailWord_6321764
  simp only [CollatzResearch.WordTrace]
  refine ⟨115286837734668087089642173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153715783646224116119522897 115286837734668087089642173)
  ·
    refine ⟨43232564150500532658615815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115286837734668087089642173 43232564150500532658615815)
    ·
      refine ⟨64848846225750798987923723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43232564150500532658615815 64848846225750798987923723)
      ·
        refine ⟨97273269338626198481885585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64848846225750798987923723 97273269338626198481885585)
        ·
          refine ⟨72954952003969648861414189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97273269338626198481885585 72954952003969648861414189)
          ·
            refine ⟨27358107001488618323030321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72954952003969648861414189 27358107001488618323030321)
            ·
              refine ⟨20518580251116463742272741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27358107001488618323030321 20518580251116463742272741)
              ·
                refine ⟨3847233797084336951676139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20518580251116463742272741 3847233797084336951676139)
                ·
                  refine ⟨5770850695626505427514209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847233797084336951676139 5770850695626505427514209)
                  ·
                    refine ⟨4328138021719879070635657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5770850695626505427514209 4328138021719879070635657)
                    ·
                      refine ⟨3246103516289909302976743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328138021719879070635657 3246103516289909302976743)
                      ·
                        rfl

theorem cell23_6321764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_6321764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321764 prefixEnd_6321764 := by exact prefixLift 6321764
  have htrace : WordTrace (prefixWord ++ tailWord_6321764) baseStart_6321764 baseEnd_6321764 := by
    simpa [prefixWord, tailWord_6321764, baseEnd_6321764] using wordTrace_append hprefix tailTrace_6321764
  have hstable : (prefixWord ++ tailWord_6321764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321764).length < 2 ^ (prefixWord ++ tailWord_6321764).sum := by decide
  have hdescent : baseEnd_6321764 < baseStart_6321764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321774 : List Nat := [4, 1, 2, 2, 3, 1, 3, 1, 2, 4]
def baseStart_6321774 : Nat := 118140960795 + 6321774 * 2 ^ 59
def prefixEnd_6321774 : Nat := 4983230072969 + 3 ^ 40 * 6321774 * 2
def baseEnd_6321774 : Nat := 1082036217032151421283899

theorem tailTrace_6321774 : CollatzResearch.WordTrace tailWord_6321774 prefixEnd_6321774 1082036217032151421283899 := by
  unfold tailWord_6321774
  simp only [CollatzResearch.WordTrace]
  refine ⟨28821755024912493235893547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153716026799533297258098917 28821755024912493235893547)
  ·
    refine ⟨43232632537368739853840321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28821755024912493235893547 43232632537368739853840321)
    ·
      refine ⟨32424474403026554890380241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43232632537368739853840321 32424474403026554890380241)
      ·
        refine ⟨24318355802269916167785181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32424474403026554890380241 24318355802269916167785181)
        ·
          refine ⟨9119383425851218562919443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24318355802269916167785181 9119383425851218562919443)
          ·
            refine ⟨13679075138776827844379165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9119383425851218562919443 13679075138776827844379165)
            ·
              refine ⟨5129653177041310441642187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13679075138776827844379165 5129653177041310441642187)
              ·
                refine ⟨7694479765561965662463281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129653177041310441642187 7694479765561965662463281)
                ·
                  refine ⟨5770859824171474246847461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7694479765561965662463281 5770859824171474246847461)
                  ·
                    refine ⟨1082036217032151421283899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5770859824171474246847461 1082036217032151421283899)
                    ·
                      rfl

theorem cell23_6321774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_6321774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321774 prefixEnd_6321774 := by exact prefixLift 6321774
  have htrace : WordTrace (prefixWord ++ tailWord_6321774) baseStart_6321774 baseEnd_6321774 := by
    simpa [prefixWord, tailWord_6321774, baseEnd_6321774] using wordTrace_append hprefix tailTrace_6321774
  have hstable : (prefixWord ++ tailWord_6321774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321774).length < 2 ^ (prefixWord ++ tailWord_6321774).sum := by decide
  have hdescent : baseEnd_6321774 < baseStart_6321774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321786 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_6321786 : Nat := 118140960795 + 6321786 * 2 ^ 59
def prefixEnd_6321786 : Nat := 4983230072969 + 3 ^ 40 * 6321786 * 2
def baseEnd_6321786 : Nat := 3246114812864308216901641

theorem tailTrace_6321786 : CollatzResearch.WordTrace tailWord_6321786 prefixEnd_6321786 3246114812864308216901641 := by
  unfold tailWord_6321786
  simp only [CollatzResearch.WordTrace]
  refine ⟨57643619468814117984146303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153716318583504314624390141 57643619468814117984146303)
  ·
    refine ⟨86465429203221176976219455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57643619468814117984146303 86465429203221176976219455)
    ·
      refine ⟨129698143804831765464329183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86465429203221176976219455 129698143804831765464329183)
      ·
        refine ⟨194547215707247648196493775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129698143804831765464329183 194547215707247648196493775)
        ·
          refine ⟨291820823560871472294740663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194547215707247648196493775 291820823560871472294740663)
          ·
            refine ⟨437731235341307208442110995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291820823560871472294740663 437731235341307208442110995)
            ·
              refine ⟨656596853011960812663166493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437731235341307208442110995 656596853011960812663166493)
              ·
                refine ⟨246223819879485304748687435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 656596853011960812663166493 246223819879485304748687435)
                ·
                  refine ⟨369335729819227957123031153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246223819879485304748687435 369335729819227957123031153)
                  ·
                    refine ⟨277001797364420967842273365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 369335729819227957123031153 277001797364420967842273365)
                    ·
                      refine ⟨3246114812864308216901641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 277001797364420967842273365 3246114812864308216901641)
                      ·
                        rfl

theorem cell23_6321786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_6321786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321786 prefixEnd_6321786 := by exact prefixLift 6321786
  have htrace : WordTrace (prefixWord ++ tailWord_6321786) baseStart_6321786 baseEnd_6321786 := by
    simpa [prefixWord, tailWord_6321786, baseEnd_6321786] using wordTrace_append hprefix tailTrace_6321786
  have hstable : (prefixWord ++ tailWord_6321786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321786).length < 2 ^ (prefixWord ++ tailWord_6321786).sum := by decide
  have hdescent : baseEnd_6321786 < baseStart_6321786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321793 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_6321793 : Nat := 118140960795 + 6321793 * 2 ^ 59
def prefixEnd_6321793 : Nat := 4983230072969 + 3 ^ 40 * 6321793 * 2
def baseEnd_6321793 : Nat := 3246118407228889689514109

theorem tailTrace_6321793 : CollatzResearch.WordTrace tailWord_6321793 prefixEnd_6321793 3246118407228889689514109 := by
  unfold tailWord_6321793
  simp only [CollatzResearch.WordTrace]
  refine ⟨230574733186231112132090033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153716488790820741421393355 230574733186231112132090033)
  ·
    refine ⟨172931049889673334099067525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 230574733186231112132090033 172931049889673334099067525)
    ·
      refine ⟨32424571854313750143575161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172931049889673334099067525 32424571854313750143575161)
      ·
        refine ⟨24318428890735312607681371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32424571854313750143575161 24318428890735312607681371)
        ·
          refine ⟨36477643336102968911522057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24318428890735312607681371 36477643336102968911522057)
          ·
            refine ⟨27358232502077226683641543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36477643336102968911522057 27358232502077226683641543)
            ·
              refine ⟨41037348753115840025462315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27358232502077226683641543 41037348753115840025462315)
              ·
                refine ⟨61556023129673760038193473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41037348753115840025462315 61556023129673760038193473)
                ·
                  refine ⟨46167017347255320028645105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61556023129673760038193473 46167017347255320028645105)
                  ·
                    refine ⟨34625263010441490021483829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46167017347255320028645105 34625263010441490021483829)
                    ·
                      refine ⟨3246118407228889689514109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34625263010441490021483829 3246118407228889689514109)
                      ·
                        rfl

theorem cell23_6321793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_6321793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321793 prefixEnd_6321793 := by exact prefixLift 6321793
  have htrace : WordTrace (prefixWord ++ tailWord_6321793) baseStart_6321793 baseEnd_6321793 := by
    simpa [prefixWord, tailWord_6321793, baseEnd_6321793] using wordTrace_append hprefix tailTrace_6321793
  have hstable : (prefixWord ++ tailWord_6321793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321793).length < 2 ^ (prefixWord ++ tailWord_6321793).sum := by decide
  have hdescent : baseEnd_6321793 < baseStart_6321793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321837 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_6321837 : Nat := 118140960795 + 6321837 * 2 ^ 59
def prefixEnd_6321837 : Nat := 4983230072969 + 3 ^ 40 * 6321837 * 2
def baseEnd_6321837 : Nat := 3246141000377687517363907

theorem tailTrace_6321837 : CollatzResearch.WordTrace tailWord_6321837 prefixEnd_6321837 3246141000377687517363907 := by
  unfold tailWord_6321837
  simp only [CollatzResearch.WordTrace]
  refine ⟨230576337998071707646691765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153717558665381138431127843 230576337998071707646691765)
  ·
    refine ⟨21616531687319222591877353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 230576337998071707646691765 21616531687319222591877353)
    ·
      refine ⟨16212398765489416943908015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21616531687319222591877353 16212398765489416943908015)
      ·
        refine ⟨24318598148234125415862023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16212398765489416943908015 24318598148234125415862023)
        ·
          refine ⟨36477897222351188123793035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24318598148234125415862023 36477897222351188123793035)
          ·
            refine ⟨54716845833526782185689553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36477897222351188123793035 54716845833526782185689553)
            ·
              refine ⟨41037634375145086639267165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54716845833526782185689553 41037634375145086639267165)
              ·
                refine ⟨15389112890679407489725187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41037634375145086639267165 15389112890679407489725187)
                ·
                  refine ⟨23083669336019111234587781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15389112890679407489725187 23083669336019111234587781)
                  ·
                    refine ⟨4328188000503583356485209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23083669336019111234587781 4328188000503583356485209)
                    ·
                      refine ⟨3246141000377687517363907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328188000503583356485209 3246141000377687517363907)
                      ·
                        rfl

theorem cell23_6321837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_6321837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321837 prefixEnd_6321837 := by exact prefixLift 6321837
  have htrace : WordTrace (prefixWord ++ tailWord_6321837) baseStart_6321837 baseEnd_6321837 := by
    simpa [prefixWord, tailWord_6321837, baseEnd_6321837] using wordTrace_append hprefix tailTrace_6321837
  have hstable : (prefixWord ++ tailWord_6321837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321837).length < 2 ^ (prefixWord ++ tailWord_6321837).sum := by decide
  have hdescent : baseEnd_6321837 < baseStart_6321837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321870 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_6321870 : Nat := 118140960795 + 6321870 * 2 ^ 59
def prefixEnd_6321870 : Nat := 4983230072969 + 3 ^ 40 * 6321870 * 2
def baseEnd_6321870 : Nat := 3246157945239285888251255

theorem tailTrace_6321870 : CollatzResearch.WordTrace tailWord_6321870 prefixEnd_6321870 3246157945239285888251255 := by
  unfold tailWord_6321870
  simp only [CollatzResearch.WordTrace]
  refine ⟨28822192700869019285330383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153718361071301436188428709 28822192700869019285330383)
  ·
    refine ⟨43233289051303528927995575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28822192700869019285330383 43233289051303528927995575)
    ·
      refine ⟨64849933576955293391993363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43233289051303528927995575 64849933576955293391993363)
      ·
        refine ⟨97274900365432940087990045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64849933576955293391993363 97274900365432940087990045)
        ·
          refine ⟨36478087637037352532996267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97274900365432940087990045 36478087637037352532996267)
          ·
            refine ⟨54717131455556028799494401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36478087637037352532996267 54717131455556028799494401)
            ·
              refine ⟨41037848591667021599620801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54717131455556028799494401 41037848591667021599620801)
              ·
                refine ⟨30778386443750266199715601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41037848591667021599620801 30778386443750266199715601)
                ·
                  refine ⟨23083789832812699649786701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30778386443750266199715601 23083789832812699649786701)
                  ·
                    refine ⟨8656421187304762368670013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23083789832812699649786701 8656421187304762368670013)
                    ·
                      refine ⟨3246157945239285888251255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8656421187304762368670013 3246157945239285888251255)
                      ·
                        rfl

theorem cell23_6321870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_6321870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321870 prefixEnd_6321870 := by exact prefixLift 6321870
  have htrace : WordTrace (prefixWord ++ tailWord_6321870) baseStart_6321870 baseEnd_6321870 := by
    simpa [prefixWord, tailWord_6321870, baseEnd_6321870] using wordTrace_append hprefix tailTrace_6321870
  have hstable : (prefixWord ++ tailWord_6321870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321870).length < 2 ^ (prefixWord ++ tailWord_6321870).sum := by decide
  have hdescent : baseEnd_6321870 < baseStart_6321870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321880 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 1, 7, 2]
def baseStart_6321880 : Nat := 118140960795 + 6321880 * 2 ^ 59
def prefixEnd_6321880 : Nat := 4983230072969 + 3 ^ 40 * 6321880 * 2
def baseEnd_6321880 : Nat := 3246163080045830849126209

theorem tailTrace_6321880 : CollatzResearch.WordTrace tailWord_6321880 prefixEnd_6321880 3246163080045830849126209 := by
  unfold tailWord_6321880
  simp only [CollatzResearch.WordTrace]
  refine ⟨115288953168457962995253547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153718604224610617327004729 115288953168457962995253547)
  ·
    refine ⟨172933429752686944492880321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115288953168457962995253547 172933429752686944492880321)
    ·
      refine ⟨129700072314515208369660241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172933429752686944492880321 129700072314515208369660241)
      ·
        refine ⟨97275054235886406277245181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129700072314515208369660241 97275054235886406277245181)
        ·
          refine ⟨36478145338457402353966943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97275054235886406277245181 36478145338457402353966943)
          ·
            refine ⟨54717218007686103530950415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36478145338457402353966943 54717218007686103530950415)
            ·
              refine ⟨82075827011529155296425623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54717218007686103530950415 82075827011529155296425623)
              ·
                refine ⟨123113740517293732944638435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82075827011529155296425623 123113740517293732944638435)
                ·
                  refine ⟨184670610775940599416957653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123113740517293732944638435 184670610775940599416957653)
                  ·
                    refine ⟨4328217440061107798834945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 184670610775940599416957653 4328217440061107798834945)
                    ·
                      refine ⟨3246163080045830849126209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328217440061107798834945 3246163080045830849126209)
                      ·
                        rfl

theorem cell23_6321880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_6321880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321880 prefixEnd_6321880 := by exact prefixLift 6321880
  have htrace : WordTrace (prefixWord ++ tailWord_6321880) baseStart_6321880 baseEnd_6321880 := by
    simpa [prefixWord, tailWord_6321880, baseEnd_6321880] using wordTrace_append hprefix tailTrace_6321880
  have hstable : (prefixWord ++ tailWord_6321880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321880).length < 2 ^ (prefixWord ++ tailWord_6321880).sum := by decide
  have hdescent : baseEnd_6321880 < baseStart_6321880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321923 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 6]
def baseStart_6321923 : Nat := 118140960795 + 6321923 * 2 ^ 59
def prefixEnd_6321923 : Nat := 4983230072969 + 3 ^ 40 * 6321923 * 2
def baseEnd_6321923 : Nat := 3246185159713974180888511

theorem tailTrace_6321923 : CollatzResearch.WordTrace tailWord_6321923 prefixEnd_6321923 3246185159713974180888511 := by
  unfold tailWord_6321923
  simp only [CollatzResearch.WordTrace]
  refine ⟨230579474675760144334322423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153719649783840096222881615 230579474675760144334322423)
  ·
    refine ⟨345869212013640216501483635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230579474675760144334322423 345869212013640216501483635)
    ·
      refine ⟨518803818020460324752225453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345869212013640216501483635 518803818020460324752225453)
      ·
        refine ⟨194551431757672621782084545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 518803818020460324752225453 194551431757672621782084545)
        ·
          refine ⟨145913573818254466336563409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194551431757672621782084545 145913573818254466336563409)
          ·
            refine ⟨109435180363690849752422557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145913573818254466336563409 109435180363690849752422557)
            ·
              refine ⟨41038192636384068657158459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109435180363690849752422557 41038192636384068657158459)
              ·
                refine ⟨61557288954576102985737689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41038192636384068657158459 61557288954576102985737689)
                ·
                  refine ⟨46167966715932077239303267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61557288954576102985737689 46167966715932077239303267)
                  ·
                    refine ⟨69251950073898115858954901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46167966715932077239303267 69251950073898115858954901)
                    ·
                      refine ⟨3246185159713974180888511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69251950073898115858954901 3246185159713974180888511)
                      ·
                        rfl

theorem cell23_6321923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_6321923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321923 prefixEnd_6321923 := by exact prefixLift 6321923
  have htrace : WordTrace (prefixWord ++ tailWord_6321923) baseStart_6321923 baseEnd_6321923 := by
    simpa [prefixWord, tailWord_6321923, baseEnd_6321923] using wordTrace_append hprefix tailTrace_6321923
  have hstable : (prefixWord ++ tailWord_6321923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321923).length < 2 ^ (prefixWord ++ tailWord_6321923).sum := by decide
  have hdescent : baseEnd_6321923 < baseStart_6321923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321971 : List Nat := [1, 1, 1, 2, 7, 2, 1, 3, 1, 4]
def baseStart_6321971 : Nat := 118140960795 + 6321971 * 2 ^ 59
def prefixEnd_6321971 : Nat := 4983230072969 + 3 ^ 40 * 6321971 * 2
def baseEnd_6321971 : Nat := 1082069935595129997696097

theorem tailTrace_6321971 : CollatzResearch.WordTrace tailWord_6321971 prefixEnd_6321971 1082069935595129997696097 := by
  unfold tailWord_6321971
  simp only [CollatzResearch.WordTrace]
  refine ⟨230581225379586248532069767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153720816919724165688046511 230581225379586248532069767)
  ·
    refine ⟨345871838069379372798104651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230581225379586248532069767 345871838069379372798104651)
    ·
      refine ⟨518807757104069059197156977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345871838069379372798104651 518807757104069059197156977)
      ·
        refine ⟨389105817828051794397867733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 518807757104069059197156977 389105817828051794397867733)
        ·
          refine ⟨9119667605344963931200025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 389105817828051794397867733 9119667605344963931200025)
          ·
            refine ⟨6839750704008722948400019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9119667605344963931200025 6839750704008722948400019)
            ·
              refine ⟨10259626056013084422600029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6839750704008722948400019 10259626056013084422600029)
              ·
                refine ⟨3847359771004906658475011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10259626056013084422600029 3847359771004906658475011)
                ·
                  refine ⟨5771039656507359987712517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847359771004906658475011 5771039656507359987712517)
                  ·
                    refine ⟨1082069935595129997696097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5771039656507359987712517 1082069935595129997696097)
                    ·
                      rfl

theorem cell23_6321971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 1, 4].length) (baseStart_6321971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321971 prefixEnd_6321971 := by exact prefixLift 6321971
  have htrace : WordTrace (prefixWord ++ tailWord_6321971) baseStart_6321971 baseEnd_6321971 := by
    simpa [prefixWord, tailWord_6321971, baseEnd_6321971] using wordTrace_append hprefix tailTrace_6321971
  have hstable : (prefixWord ++ tailWord_6321971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321971).length < 2 ^ (prefixWord ++ tailWord_6321971).sum := by decide
  have hdescent : baseEnd_6321971 < baseStart_6321971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6321987 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 4, 3, 2]
def baseStart_6321987 : Nat := 118140960795 + 6321987 * 2 ^ 59
def prefixEnd_6321987 : Nat := 4983230072969 + 3 ^ 40 * 6321987 * 2
def baseEnd_6321987 : Nat := 3246218022475861930488217

theorem tailTrace_6321987 : CollatzResearch.WordTrace tailWord_6321987 prefixEnd_6321987 3246218022475861930488217 := by
  unfold tailWord_6321987
  simp only [CollatzResearch.WordTrace]
  refine ⟨230581808947528283264652215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153721205965018855509768143 230581808947528283264652215)
  ·
    refine ⟨345872713421292424896978323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230581808947528283264652215 345872713421292424896978323)
    ·
      refine ⟨518809070131938637345467485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345872713421292424896978323 518809070131938637345467485)
      ·
        refine ⟨194553401299476989004550307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 518809070131938637345467485 194553401299476989004550307)
        ·
          refine ⟨291830101949215483506825461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194553401299476989004550307 291830101949215483506825461)
          ·
            refine ⟨27359072057738951578764887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 291830101949215483506825461 27359072057738951578764887)
            ·
              refine ⟨41038608086608427368147331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27359072057738951578764887 41038608086608427368147331)
              ·
                refine ⟨61557912129912641052220997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41038608086608427368147331 61557912129912641052220997)
                ·
                  refine ⟨11542108524358620197291437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61557912129912641052220997 11542108524358620197291437)
                  ·
                    refine ⟨4328290696634482573984289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11542108524358620197291437 4328290696634482573984289)
                    ·
                      refine ⟨3246218022475861930488217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4328290696634482573984289 3246218022475861930488217)
                      ·
                        rfl

theorem cell23_6321987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 3, 2].length) (baseStart_6321987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6321987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6321987 prefixEnd_6321987 := by exact prefixLift 6321987
  have htrace : WordTrace (prefixWord ++ tailWord_6321987) baseStart_6321987 baseEnd_6321987 := by
    simpa [prefixWord, tailWord_6321987, baseEnd_6321987] using wordTrace_append hprefix tailTrace_6321987
  have hstable : (prefixWord ++ tailWord_6321987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6321987).length < 2 ^ (prefixWord ++ tailWord_6321987).sum := by decide
  have hdescent : baseEnd_6321987 < baseStart_6321987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6321987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
