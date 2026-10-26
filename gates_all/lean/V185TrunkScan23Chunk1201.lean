import V185TrunkScan23Chunk1200

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7114993 : List Nat := [1, 2, 2, 2, 2, 1, 3, 4, 2, 2, 2]
def baseStart_7114993 : Nat := 118140960795 + 7114993 * 2 ^ 59
def prefixEnd_7114993 : Nat := 4983230072969 + 3 ^ 40 * 7114993 * 2
def baseEnd_7114993 : Nat := 3653411262375186290866249

theorem tailTrace_7114993 : CollatzResearch.WordTrace tailWord_7114993 prefixEnd_7114993 3653411262375186290866249 := by
  unfold tailWord_7114993
  simp only [CollatzResearch.WordTrace]
  refine ⟨259505113912602979906949633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173003409275068653271299755 259505113912602979906949633)
  ·
    refine ⟨194628835434452234930212225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259505113912602979906949633 194628835434452234930212225)
    ·
      refine ⟨145971626575839176197659169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194628835434452234930212225 145971626575839176197659169)
      ·
        refine ⟨109478719931879382148244377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145971626575839176197659169 109478719931879382148244377)
        ·
          refine ⟨82109039948909536611183283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109478719931879382148244377 82109039948909536611183283)
          ·
            refine ⟨123163559923364304916774925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82109039948909536611183283 123163559923364304916774925)
            ·
              refine ⟨46186334971261614343790597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123163559923364304916774925 46186334971261614343790597)
              ·
                refine ⟨8659937807111552689460737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46186334971261614343790597 8659937807111552689460737)
                ·
                  refine ⟨6494953355333664517095553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8659937807111552689460737 6494953355333664517095553)
                  ·
                    refine ⟨4871215016500248387821665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6494953355333664517095553 4871215016500248387821665)
                    ·
                      refine ⟨3653411262375186290866249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871215016500248387821665 3653411262375186290866249)
                      ·
                        rfl

theorem cell23_7114993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_7114993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7114993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7114993 prefixEnd_7114993 := by exact prefixLift 7114993
  have htrace : WordTrace (prefixWord ++ tailWord_7114993) baseStart_7114993 baseEnd_7114993 := by
    simpa [prefixWord, tailWord_7114993, baseEnd_7114993] using wordTrace_append hprefix tailTrace_7114993
  have hstable : (prefixWord ++ tailWord_7114993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7114993).length < 2 ^ (prefixWord ++ tailWord_7114993).sum := by decide
  have hdescent : baseEnd_7114993 < baseStart_7114993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7114993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115006 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_7115006 : Nat := 118140960795 + 7115006 * 2 ^ 59
def prefixEnd_7115006 : Nat := 4983230072969 + 3 ^ 40 * 7115006 * 2
def baseEnd_7115006 : Nat := 3653417937623694740003689

theorem tailTrace_7115006 : CollatzResearch.WordTrace tailWord_7115006 prefixEnd_7115006 3653417937623694740003689 := by
  unfold tailWord_7115006
  simp only [CollatzResearch.WordTrace]
  refine ⟨32438198507694485390896609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173003725374370588751448581 32438198507694485390896609)
  ·
    refine ⟨24328648880770864043172457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32438198507694485390896609 24328648880770864043172457)
    ·
      refine ⟨18246486660578148032379343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24328648880770864043172457 18246486660578148032379343)
      ·
        refine ⟨27369729990867222048569015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18246486660578148032379343 27369729990867222048569015)
        ·
          refine ⟨41054594986300833072853523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27369729990867222048569015 41054594986300833072853523)
          ·
            refine ⟨61581892479451249609280285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41054594986300833072853523 61581892479451249609280285)
            ·
              refine ⟨23093209679794218603480107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61581892479451249609280285 23093209679794218603480107)
              ·
                refine ⟨34639814519691327905220161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23093209679794218603480107 34639814519691327905220161)
                ·
                  refine ⟨25979860889768495928915121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34639814519691327905220161 25979860889768495928915121)
                  ·
                    refine ⟨19484895667326371946686341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25979860889768495928915121 19484895667326371946686341)
                    ·
                      refine ⟨3653417937623694740003689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19484895667326371946686341 3653417937623694740003689)
                      ·
                        rfl

theorem cell23_7115006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_7115006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115006 prefixEnd_7115006 := by exact prefixLift 7115006
  have htrace : WordTrace (prefixWord ++ tailWord_7115006) baseStart_7115006 baseEnd_7115006 := by
    simpa [prefixWord, tailWord_7115006, baseEnd_7115006] using wordTrace_append hprefix tailTrace_7115006
  have hstable : (prefixWord ++ tailWord_7115006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115006).length < 2 ^ (prefixWord ++ tailWord_7115006).sum := by decide
  have hdescent : baseEnd_7115006 < baseStart_7115006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115010 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_7115010 : Nat := 118140960795 + 7115010 * 2 ^ 59
def prefixEnd_7115010 : Nat := 4983230072969 + 3 ^ 40 * 7115010 * 2
def baseEnd_7115010 : Nat := 3653419991546312724353671

theorem tailTrace_7115010 : CollatzResearch.WordTrace tailWord_7115010 prefixEnd_7115010 3653419991546312724353671 := by
  unfold tailWord_7115010
  simp only [CollatzResearch.WordTrace]
  refine ⟨64876433488385347952579621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173003822635694261206878989 64876433488385347952579621)
  ·
    refine ⟨12164331279072252741108679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64876433488385347952579621 12164331279072252741108679)
    ·
      refine ⟨18246496918608379111663019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12164331279072252741108679 18246496918608379111663019)
      ·
        refine ⟨27369745377912568667494529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18246496918608379111663019 27369745377912568667494529)
        ·
          refine ⟨20527309033434426500620897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27369745377912568667494529 20527309033434426500620897)
          ·
            refine ⟨15395481775075819875465673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20527309033434426500620897 15395481775075819875465673)
            ·
              refine ⟨11546611331306864906599255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15395481775075819875465673 11546611331306864906599255)
              ·
                refine ⟨17319916996960297359898883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11546611331306864906599255 17319916996960297359898883)
                ·
                  refine ⟨25979875495440446039848325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17319916996960297359898883 25979875495440446039848325)
                  ·
                    refine ⟨4871226655395083632471561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25979875495440446039848325 4871226655395083632471561)
                    ·
                      refine ⟨3653419991546312724353671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871226655395083632471561 3653419991546312724353671)
                      ·
                        rfl

theorem cell23_7115010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_7115010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115010 prefixEnd_7115010 := by exact prefixLift 7115010
  have htrace : WordTrace (prefixWord ++ tailWord_7115010) baseStart_7115010 baseEnd_7115010 := by
    simpa [prefixWord, tailWord_7115010, baseEnd_7115010] using wordTrace_append hprefix tailTrace_7115010
  have hstable : (prefixWord ++ tailWord_7115010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115010).length < 2 ^ (prefixWord ++ tailWord_7115010).sum := by decide
  have hdescent : baseEnd_7115010 < baseStart_7115010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115079 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_7115079 : Nat := 118140960795 + 7115079 * 2 ^ 59
def prefixEnd_7115079 : Nat := 4983230072969 + 3 ^ 40 * 7115079 * 2
def baseEnd_7115079 : Nat := 3653455421711472954390853

theorem tailTrace_7115079 : CollatzResearch.WordTrace tailWord_7115079 prefixEnd_7115079 3653455421711472954390853 := by
  unfold tailWord_7115079
  simp only [CollatzResearch.WordTrace]
  refine ⟨259508250590291416594580291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173005500393527611063053527 259508250590291416594580291)
  ·
    refine ⟨389262375885437124891870437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259508250590291416594580291 389262375885437124891870437)
    ·
      refine ⟨72986695478519460917225707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389262375885437124891870437 72986695478519460917225707)
      ·
        refine ⟨109480043217779191375838561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72986695478519460917225707 109480043217779191375838561)
        ·
          refine ⟨82110032413334393531878921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109480043217779191375838561 82110032413334393531878921)
          ·
            refine ⟨61582524310000795148909191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82110032413334393531878921 61582524310000795148909191)
            ·
              refine ⟨92373786465001192723363787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61582524310000795148909191 92373786465001192723363787)
              ·
                refine ⟨138560679697501789085045681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92373786465001192723363787 138560679697501789085045681)
                ·
                  refine ⟨103920509773126341813784261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138560679697501789085045681 103920509773126341813784261)
                  ·
                    refine ⟨19485095582461189090084549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103920509773126341813784261 19485095582461189090084549)
                    ·
                      refine ⟨3653455421711472954390853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19485095582461189090084549 3653455421711472954390853)
                      ·
                        rfl

theorem cell23_7115079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_7115079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115079 prefixEnd_7115079 := by exact prefixLift 7115079
  have htrace : WordTrace (prefixWord ++ tailWord_7115079) baseStart_7115079 baseEnd_7115079 := by
    simpa [prefixWord, tailWord_7115079, baseEnd_7115079] using wordTrace_append hprefix tailTrace_7115079
  have hstable : (prefixWord ++ tailWord_7115079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115079).length < 2 ^ (prefixWord ++ tailWord_7115079).sum := by decide
  have hdescent : baseEnd_7115079 < baseStart_7115079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115089 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 8]
def baseStart_7115089 : Nat := 118140960795 + 7115089 * 2 ^ 59
def prefixEnd_7115089 : Nat := 4983230072969 + 3 ^ 40 * 7115089 * 2
def baseEnd_7115089 : Nat := 405940061835335323918423

theorem tailTrace_7115089 : CollatzResearch.WordTrace tailWord_7115089 prefixEnd_7115089 405940061835335323918423 := by
  unfold tailWord_7115089
  simp only [CollatzResearch.WordTrace]
  refine ⟨259508615320255188302444321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173005743546836792201629547 259508615320255188302444321)
  ·
    refine ⟨194631461490191391226833241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259508615320255188302444321 194631461490191391226833241)
    ·
      refine ⟨145973596117643543420124931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194631461490191391226833241 145973596117643543420124931)
      ·
        refine ⟨218960394176465315130187397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145973596117643543420124931 218960394176465315130187397)
        ·
          refine ⟨41055073908087246586910137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218960394176465315130187397 41055073908087246586910137)
          ·
            refine ⟨30791305431065434940182603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41055073908087246586910137 30791305431065434940182603)
            ·
              refine ⟨46186958146598152410273905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30791305431065434940182603 46186958146598152410273905)
              ·
                refine ⟨34640218609948614307705429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46186958146598152410273905 34640218609948614307705429)
                ·
                  refine ⟨405940061835335323918423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34640218609948614307705429 405940061835335323918423)
                  ·
                    rfl

theorem cell23_7115089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 8].length) (baseStart_7115089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115089 prefixEnd_7115089 := by exact prefixLift 7115089
  have htrace : WordTrace (prefixWord ++ tailWord_7115089) baseStart_7115089 baseEnd_7115089 := by
    simpa [prefixWord, tailWord_7115089, baseEnd_7115089] using wordTrace_append hprefix tailTrace_7115089
  have hstable : (prefixWord ++ tailWord_7115089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115089).length < 2 ^ (prefixWord ++ tailWord_7115089).sum := by decide
  have hdescent : baseEnd_7115089 < baseStart_7115089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115100 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_7115100 : Nat := 118140960795 + 7115100 * 2 ^ 59
def prefixEnd_7115100 : Nat := 4983230072969 + 3 ^ 40 * 7115100 * 2
def baseEnd_7115100 : Nat := 3653466204805217372228257

theorem tailTrace_7115100 : CollatzResearch.WordTrace tailWord_7115100 prefixEnd_7115100 3653466204805217372228257 := by
  unfold tailWord_7115100
  simp only [CollatzResearch.WordTrace]
  refine ⟨129754508261607668590547377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173006011015476891454063169 129754508261607668590547377)
  ·
    refine ⟨97315881196205751442910533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129754508261607668590547377 97315881196205751442910533)
    ·
      refine ⟨18246727724288578395545725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97315881196205751442910533 18246727724288578395545725)
      ·
        refine ⟨6842522896608216898329647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18246727724288578395545725 6842522896608216898329647)
        ·
          refine ⟨10263784344912325347494471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6842522896608216898329647 10263784344912325347494471)
          ·
            refine ⟨15395676517368488021241707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10263784344912325347494471 15395676517368488021241707)
            ·
              refine ⟨23093514776052732031862561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15395676517368488021241707 23093514776052732031862561)
              ·
                refine ⟨17320136082039549023896921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23093514776052732031862561 17320136082039549023896921)
                ·
                  refine ⟨12990102061529661767922691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17320136082039549023896921 12990102061529661767922691)
                  ·
                    refine ⟨19485153092294492651884037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12990102061529661767922691 19485153092294492651884037)
                    ·
                      refine ⟨3653466204805217372228257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19485153092294492651884037 3653466204805217372228257)
                      ·
                        rfl

theorem cell23_7115100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_7115100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115100 prefixEnd_7115100 := by exact prefixLift 7115100
  have htrace : WordTrace (prefixWord ++ tailWord_7115100) baseStart_7115100 baseEnd_7115100 := by
    simpa [prefixWord, tailWord_7115100, baseEnd_7115100] using wordTrace_append hprefix tailTrace_7115100
  have hstable : (prefixWord ++ tailWord_7115100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115100).length < 2 ^ (prefixWord ++ tailWord_7115100).sum := by decide
  have hdescent : baseEnd_7115100 < baseStart_7115100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115106 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 8]
def baseStart_7115106 : Nat := 118140960795 + 7115106 * 2 ^ 59
def prefixEnd_7115106 : Nat := 4983230072969 + 3 ^ 40 * 7115106 * 2
def baseEnd_7115106 : Nat := 405941031743238260972581

theorem tailTrace_7115106 : CollatzResearch.WordTrace tailWord_7115106 prefixEnd_7115106 405941031743238260972581 := by
  unfold tailWord_7115106
  simp only [CollatzResearch.WordTrace]
  refine ⟨64877308840298400051453293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173006156907462400137208781 64877308840298400051453293)
  ·
    refine ⟨24328990815111900019294985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64877308840298400051453293 24328990815111900019294985)
    ·
      refine ⟨18246743111333925014471239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24328990815111900019294985 18246743111333925014471239)
      ·
        refine ⟨27370114667000887521706859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18246743111333925014471239 27370114667000887521706859)
        ·
          refine ⟨41055172000501331282560289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27370114667000887521706859 41055172000501331282560289)
          ·
            refine ⟨30791379000375998461920217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41055172000501331282560289 30791379000375998461920217)
            ·
              refine ⟨23093534250281998846440163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30791379000375998461920217 23093534250281998846440163)
              ·
                refine ⟨34640301375422998269660245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23093534250281998846440163 34640301375422998269660245)
                ·
                  refine ⟨405941031743238260972581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34640301375422998269660245 405941031743238260972581)
                  ·
                    rfl

theorem cell23_7115106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_7115106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115106 prefixEnd_7115106 := by exact prefixLift 7115106
  have htrace : WordTrace (prefixWord ++ tailWord_7115106) baseStart_7115106 baseEnd_7115106 := by
    simpa [prefixWord, tailWord_7115106, baseEnd_7115106] using wordTrace_append hprefix tailTrace_7115106
  have hstable : (prefixWord ++ tailWord_7115106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115106).length < 2 ^ (prefixWord ++ tailWord_7115106).sum := by decide
  have hdescent : baseEnd_7115106 < baseStart_7115106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115160 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 2, 3, 2]
def baseStart_7115160 : Nat := 118140960795 + 7115160 * 2 ^ 59
def prefixEnd_7115160 : Nat := 4983230072969 + 3 ^ 40 * 7115160 * 2
def baseEnd_7115160 : Nat := 3653497013644487137477981

theorem tailTrace_7115160 : CollatzResearch.WordTrace tailWord_7115160 prefixEnd_7115160 3653497013644487137477981 := by
  unfold tailWord_7115160
  simp only [CollatzResearch.WordTrace]
  refine ⟨129755602451498983714139467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173007469935331978285519289 129755602451498983714139467)
  ·
    refine ⟨194633403677248475571209201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129755602451498983714139467 194633403677248475571209201)
    ·
      refine ⟨145975052757936356678406901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194633403677248475571209201 145975052757936356678406901)
      ·
        refine ⟨13685161196056533438600647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145975052757936356678406901 13685161196056533438600647)
        ·
          refine ⟨20527741794084800157900971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13685161196056533438600647 20527741794084800157900971)
          ·
            refine ⟨30791612691127200236851457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20527741794084800157900971 30791612691127200236851457)
            ·
              refine ⟨23093709518345400177638593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30791612691127200236851457 23093709518345400177638593)
              ·
                refine ⟨17320282138759050133228945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23093709518345400177638593 17320282138759050133228945)
                ·
                  refine ⟨12990211604069287599921709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17320282138759050133228945 12990211604069287599921709)
                  ·
                    refine ⟨4871329351525982849970641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12990211604069287599921709 4871329351525982849970641)
                    ·
                      refine ⟨3653497013644487137477981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871329351525982849970641 3653497013644487137477981)
                      ·
                        rfl

theorem cell23_7115160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_7115160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115160 prefixEnd_7115160 := by exact prefixLift 7115160
  have htrace : WordTrace (prefixWord ++ tailWord_7115160) baseStart_7115160 baseEnd_7115160 := by
    simpa [prefixWord, tailWord_7115160, baseEnd_7115160] using wordTrace_append hprefix tailTrace_7115160
  have hstable : (prefixWord ++ tailWord_7115160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115160).length < 2 ^ (prefixWord ++ tailWord_7115160).sum := by decide
  have hdescent : baseEnd_7115160 < baseStart_7115160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115193 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 3, 2, 3]
def baseStart_7115193 : Nat := 118140960795 + 7115193 * 2 ^ 59
def prefixEnd_7115193 : Nat := 4983230072969 + 3 ^ 40 * 7115193 * 2
def baseEnd_7115193 : Nat := 3653513958506085508365329

theorem tailTrace_7115193 : CollatzResearch.WordTrace tailWord_7115193 prefixEnd_7115193 3653513958506085508365329 := by
  unfold tailWord_7115193
  simp only [CollatzResearch.WordTrace]
  refine ⟨259512408511878414064230233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173008272341252276042820155 259512408511878414064230233)
  ·
    refine ⟨194634306383908810548172675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259512408511878414064230233 194634306383908810548172675)
    ·
      refine ⟨291951459575863215822259013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194634306383908810548172675 291951459575863215822259013)
      ·
        refine ⟨54740898670474352966673565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291951459575863215822259013 54740898670474352966673565)
        ·
          refine ⟨20527837001427882362502587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54740898670474352966673565 20527837001427882362502587)
          ·
            refine ⟨30791755502141823543753881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20527837001427882362502587 30791755502141823543753881)
            ·
              refine ⟨23093816626606367657815411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30791755502141823543753881 23093816626606367657815411)
              ·
                refine ⟨34640724939909551486723117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23093816626606367657815411 34640724939909551486723117)
                ·
                  refine ⟨12990271852466081807521169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34640724939909551486723117 12990271852466081807521169)
                  ·
                    refine ⟨9742703889349561355640877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12990271852466081807521169 9742703889349561355640877)
                    ·
                      refine ⟨3653513958506085508365329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9742703889349561355640877 3653513958506085508365329)
                      ·
                        rfl

theorem cell23_7115193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_7115193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115193 prefixEnd_7115193 := by exact prefixLift 7115193
  have htrace : WordTrace (prefixWord ++ tailWord_7115193) baseStart_7115193 baseEnd_7115193 := by
    simpa [prefixWord, tailWord_7115193, baseEnd_7115193] using wordTrace_append hprefix tailTrace_7115193
  have hstable : (prefixWord ++ tailWord_7115193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115193).length < 2 ^ (prefixWord ++ tailWord_7115193).sum := by decide
  have hdescent : baseEnd_7115193 < baseStart_7115193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115204 : List Nat := [2, 3, 3, 2, 3, 1, 2, 1, 1, 5]
def baseStart_7115204 : Nat := 118140960795 + 7115204 * 2 ^ 59
def prefixEnd_7115204 : Nat := 4983230072969 + 3 ^ 40 * 7115204 * 2
def baseEnd_7115204 : Nat := 1217839868931094988442593

theorem tailTrace_7115204 : CollatzResearch.WordTrace tailWord_7115204 prefixEnd_7115204 1217839868931094988442593 := by
  unfold tailWord_7115204
  simp only [CollatzResearch.WordTrace]
  refine ⟨129756404857419281471440333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173008539809892375295253777 129756404857419281471440333)
  ·
    refine ⟨48658651821532230551790125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129756404857419281471440333 48658651821532230551790125)
    ·
      refine ⟨18246994433074586456921297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48658651821532230551790125 18246994433074586456921297)
      ·
        refine ⟨13685245824805939842690973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18246994433074586456921297 13685245824805939842690973)
        ·
          refine ⟨5131967184302227441009115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13685245824805939842690973 5131967184302227441009115)
          ·
            refine ⟨7697950776453341161513673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5131967184302227441009115 7697950776453341161513673)
            ·
              refine ⟨5773463082340005871135255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7697950776453341161513673 5773463082340005871135255)
              ·
                refine ⟨8660194623510008806702883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5773463082340005871135255 8660194623510008806702883)
                ·
                  refine ⟨12990291935265013210054325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8660194623510008806702883 12990291935265013210054325)
                  ·
                    refine ⟨1217839868931094988442593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12990291935265013210054325 1217839868931094988442593)
                    ·
                      rfl

theorem cell23_7115204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_7115204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115204 prefixEnd_7115204 := by exact prefixLift 7115204
  have htrace : WordTrace (prefixWord ++ tailWord_7115204) baseStart_7115204 baseEnd_7115204 := by
    simpa [prefixWord, tailWord_7115204, baseEnd_7115204] using wordTrace_append hprefix tailTrace_7115204
  have hstable : (prefixWord ++ tailWord_7115204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115204).length < 2 ^ (prefixWord ++ tailWord_7115204).sum := by decide
  have hdescent : baseEnd_7115204 < baseStart_7115204 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115207 : List Nat := [1, 1, 4, 1, 1, 4, 1, 5, 1, 2, 2]
def baseStart_7115207 : Nat := 118140960795 + 7115207 * 2 ^ 59
def prefixEnd_7115207 : Nat := 4983230072969 + 3 ^ 40 * 7115207 * 2
def baseEnd_7115207 : Nat := 3653521147235248453590265

theorem tailTrace_7115207 : CollatzResearch.WordTrace tailWord_7115207 prefixEnd_7115207 3653521147235248453590265 := by
  unfold tailWord_7115207
  simp only [CollatzResearch.WordTrace]
  refine ⟨259512919133827694455239875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173008612755885129636826583 259512919133827694455239875)
  ·
    refine ⟨389269378700741541682859813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259512919133827694455239875 389269378700741541682859813)
    ·
      refine ⟨72988008506389039065536215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389269378700741541682859813 72988008506389039065536215)
      ·
        refine ⟨109482012759583558598304323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72988008506389039065536215 109482012759583558598304323)
        ·
          refine ⟨164223019139375337897456485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109482012759583558598304323 164223019139375337897456485)
          ·
            refine ⟨30791816088632875855773091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164223019139375337897456485 30791816088632875855773091)
            ·
              refine ⟨46187724132949313783659637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30791816088632875855773091 46187724132949313783659637)
              ·
                refine ⟨4330099137463998167218091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46187724132949313783659637 4330099137463998167218091)
                ·
                  refine ⟨6495148706195997250827137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4330099137463998167218091 6495148706195997250827137)
                  ·
                    refine ⟨4871361529646997938120353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6495148706195997250827137 4871361529646997938120353)
                    ·
                      refine ⟨3653521147235248453590265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871361529646997938120353 3653521147235248453590265)
                      ·
                        rfl

theorem cell23_7115207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_7115207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115207 prefixEnd_7115207 := by exact prefixLift 7115207
  have htrace : WordTrace (prefixWord ++ tailWord_7115207) baseStart_7115207 baseEnd_7115207 := by
    simpa [prefixWord, tailWord_7115207, baseEnd_7115207] using wordTrace_append hprefix tailTrace_7115207
  have hstable : (prefixWord ++ tailWord_7115207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115207).length < 2 ^ (prefixWord ++ tailWord_7115207).sum := by decide
  have hdescent : baseEnd_7115207 < baseStart_7115207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115234 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_7115234 : Nat := 118140960795 + 7115234 * 2 ^ 59
def prefixEnd_7115234 : Nat := 4983230072969 + 3 ^ 40 * 7115234 * 2
def baseEnd_7115234 : Nat := 1217845003737639949317547

theorem tailTrace_7115234 : CollatzResearch.WordTrace tailWord_7115234 prefixEnd_7115234 1217845003737639949317547 := by
  unfold tailWord_7115234
  simp only [CollatzResearch.WordTrace]
  refine ⟨64878475976182469516618189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173009269269819918710981837 64878475976182469516618189)
  ·
    refine ⟨24329428491068426068731821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64878475976182469516618189 24329428491068426068731821)
    ·
      refine ⟨9123535684150659775774433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24329428491068426068731821 9123535684150659775774433)
      ·
        refine ⟨6842651763112994831830825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9123535684150659775774433 6842651763112994831830825)
        ·
          refine ⟨5131988822334746123873119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6842651763112994831830825 5131988822334746123873119)
          ·
            refine ⟨7697983233502119185809679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5131988822334746123873119 7697983233502119185809679)
            ·
              refine ⟨11546974850253178778714519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7697983233502119185809679 11546974850253178778714519)
              ·
                refine ⟨17320462275379768168071779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11546974850253178778714519 17320462275379768168071779)
                ·
                  refine ⟨25980693413069652252107669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17320462275379768168071779 25980693413069652252107669)
                  ·
                    refine ⟨1217845003737639949317547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25980693413069652252107669 1217845003737639949317547)
                    ·
                      rfl

theorem cell23_7115234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_7115234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115234 prefixEnd_7115234 := by exact prefixLift 7115234
  have htrace : WordTrace (prefixWord ++ tailWord_7115234) baseStart_7115234 baseEnd_7115234 := by
    simpa [prefixWord, tailWord_7115234, baseEnd_7115234] using wordTrace_append hprefix tailTrace_7115234
  have hstable : (prefixWord ++ tailWord_7115234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115234).length < 2 ^ (prefixWord ++ tailWord_7115234).sum := by decide
  have hdescent : baseEnd_7115234 < baseStart_7115234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115237 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 1, 2, 4]
def baseStart_7115237 : Nat := 118140960795 + 7115237 * 2 ^ 59
def prefixEnd_7115237 : Nat := 4983230072969 + 3 ^ 40 * 7115237 * 2
def baseEnd_7115237 : Nat := 3653536551654883336215127

theorem tailTrace_7115237 : CollatzResearch.WordTrace tailWord_7115237 prefixEnd_7115237 3653536551654883336215127 := by
  unfold tailWord_7115237
  simp only [CollatzResearch.WordTrace]
  refine ⟨259514013323719009578831965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173009342215812673052554643 259514013323719009578831965)
  ·
    refine ⟨97317754996394628592061987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259514013323719009578831965 97317754996394628592061987)
    ·
      refine ⟨145976632494591942888092981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97317754996394628592061987 145976632494591942888092981)
      ·
        refine ⟨13685309296367994645758717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145976632494591942888092981 13685309296367994645758717)
        ·
          refine ⟨5131990986137997992159519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13685309296367994645758717 5131990986137997992159519)
          ·
            refine ⟨7697986479206996988239279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5131990986137997992159519 7697986479206996988239279)
            ·
              refine ⟨11546979718810495482358919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7697986479206996988239279 11546979718810495482358919)
              ·
                refine ⟨17320469578215743223538379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11546979718810495482358919 17320469578215743223538379)
                ·
                  refine ⟨25980704367323614835307569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17320469578215743223538379 25980704367323614835307569)
                  ·
                    refine ⟨19485528275492711126480677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25980704367323614835307569 19485528275492711126480677)
                    ·
                      refine ⟨3653536551654883336215127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19485528275492711126480677 3653536551654883336215127)
                      ·
                        rfl

theorem cell23_7115237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_7115237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115237 prefixEnd_7115237 := by exact prefixLift 7115237
  have htrace : WordTrace (prefixWord ++ tailWord_7115237) baseStart_7115237 baseEnd_7115237 := by
    simpa [prefixWord, tailWord_7115237, baseEnd_7115237] using wordTrace_append hprefix tailTrace_7115237
  have hstable : (prefixWord ++ tailWord_7115237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115237).length < 2 ^ (prefixWord ++ tailWord_7115237).sum := by decide
  have hdescent : baseEnd_7115237 < baseStart_7115237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115240 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_7115240 : Nat := 118140960795 + 7115240 * 2 ^ 59
def prefixEnd_7115240 : Nat := 4983230072969 + 3 ^ 40 * 7115240 * 2
def baseEnd_7115240 : Nat := 3653538092096846824477613

theorem tailTrace_7115240 : CollatzResearch.WordTrace tailWord_7115240 prefixEnd_7115240 3653538092096846824477613 := by
  unfold tailWord_7115240
  simp only [CollatzResearch.WordTrace]
  refine ⟨129757061371354070545595587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173009415161805427394127449 129757061371354070545595587)
  ·
    refine ⟨194635592057031105818393381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129757061371354070545595587 194635592057031105818393381)
    ·
      refine ⟨36494173510693332340948759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194635592057031105818393381 36494173510693332340948759)
      ·
        refine ⟨54741260266039998511423139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36494173510693332340948759 54741260266039998511423139)
        ·
          refine ⟨82111890399059997767134709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54741260266039998511423139 82111890399059997767134709)
          ·
            refine ⟨7697989724911874790668879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82111890399059997767134709 7697989724911874790668879)
            ·
              refine ⟨11546984587367812186003319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7697989724911874790668879 11546984587367812186003319)
              ·
                refine ⟨17320476881051718279004979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11546984587367812186003319 17320476881051718279004979)
                ·
                  refine ⟨25980715321577577418507469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17320476881051718279004979 25980715321577577418507469)
                  ·
                    refine ⟨9742768245591591531940301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25980715321577577418507469 9742768245591591531940301)
                    ·
                      refine ⟨3653538092096846824477613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9742768245591591531940301 3653538092096846824477613)
                      ·
                        rfl

theorem cell23_7115240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_7115240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115240 prefixEnd_7115240 := by exact prefixLift 7115240
  have htrace : WordTrace (prefixWord ++ tailWord_7115240) baseStart_7115240 baseEnd_7115240 := by
    simpa [prefixWord, tailWord_7115240, baseEnd_7115240] using wordTrace_append hprefix tailTrace_7115240
  have hstable : (prefixWord ++ tailWord_7115240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115240).length < 2 ^ (prefixWord ++ tailWord_7115240).sum := by decide
  have hdescent : baseEnd_7115240 < baseStart_7115240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115263 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 3, 4, 2]
def baseStart_7115263 : Nat := 118140960795 + 7115263 * 2 ^ 59
def prefixEnd_7115263 : Nat := 4983230072969 + 3 ^ 40 * 7115263 * 2
def baseEnd_7115263 : Nat := 3653549902151900234490007

theorem tailTrace_7115263 : CollatzResearch.WordTrace tailWord_7115263 prefixEnd_7115263 3653549902151900234490007 := by
  unfold tailWord_7115263
  simp only [CollatzResearch.WordTrace]
  refine ⟨259514961621624816019278443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173009974414416544012852295 259514961621624816019278443)
  ·
    refine ⟨389272442432437224028917665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259514961621624816019278443 389272442432437224028917665)
    ·
      refine ⟨291954331824327918021688249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389272442432437224028917665 291954331824327918021688249)
      ·
        refine ⟨218965748868245938516266187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291954331824327918021688249 218965748868245938516266187)
        ·
          refine ⟨328448623302368907774399281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218965748868245938516266187 328448623302368907774399281)
          ·
            refine ⟨246336467476776680830799461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328448623302368907774399281 246336467476776680830799461)
            ·
              refine ⟨46188087651895627655774899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246336467476776680830799461 46188087651895627655774899)
              ·
                refine ⟨69282131477843441483662349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46188087651895627655774899 69282131477843441483662349)
                ·
                  refine ⟨25980799304191290556373381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69282131477843441483662349 25980799304191290556373381)
                  ·
                    refine ⟨4871399869535866979320009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25980799304191290556373381 4871399869535866979320009)
                    ·
                      refine ⟨3653549902151900234490007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871399869535866979320009 3653549902151900234490007)
                      ·
                        rfl

theorem cell23_7115263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 4, 2].length) (baseStart_7115263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115263 prefixEnd_7115263 := by exact prefixLift 7115263
  have htrace : WordTrace (prefixWord ++ tailWord_7115263) baseStart_7115263 baseEnd_7115263 := by
    simpa [prefixWord, tailWord_7115263, baseEnd_7115263] using wordTrace_append hprefix tailTrace_7115263
  have hstable : (prefixWord ++ tailWord_7115263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115263).length < 2 ^ (prefixWord ++ tailWord_7115263).sum := by decide
  have hdescent : baseEnd_7115263 < baseStart_7115263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115297 : List Nat := [1, 2, 3, 2, 2, 1, 3, 3, 2, 2, 2]
def baseStart_7115297 : Nat := 118140960795 + 7115297 * 2 ^ 59
def prefixEnd_7115297 : Nat := 4983230072969 + 3 ^ 40 * 7115297 * 2
def baseEnd_7115297 : Nat := 3653567360494153101464851

theorem tailTrace_7115297 : CollatzResearch.WordTrace tailWord_7115297 prefixEnd_7115297 3653567360494153101464851 := by
  unfold tailWord_7115297
  simp only [CollatzResearch.WordTrace]
  refine ⟨259516201703501639826016145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173010801135667759884010763 259516201703501639826016145)
  ·
    refine ⟨194637151277626229869512109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259516201703501639826016145 194637151277626229869512109)
    ·
      refine ⟨72988931729109836201067041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194637151277626229869512109 72988931729109836201067041)
      ·
        refine ⟨54741698796832377150800281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72988931729109836201067041 54741698796832377150800281)
        ·
          refine ⟨41056274097624282863100211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54741698796832377150800281 41056274097624282863100211)
          ·
            refine ⟨61584411146436424294650317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41056274097624282863100211 61584411146436424294650317)
            ·
              refine ⟨23094154179913659110493869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61584411146436424294650317 23094154179913659110493869)
              ·
                refine ⟨8660307817467622166435201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23094154179913659110493869 8660307817467622166435201)
                ·
                  refine ⟨6495230863100716624826401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8660307817467622166435201 6495230863100716624826401)
                  ·
                    refine ⟨4871423147325537468619801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6495230863100716624826401 4871423147325537468619801)
                    ·
                      refine ⟨3653567360494153101464851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871423147325537468619801 3653567360494153101464851)
                      ·
                        rfl

theorem cell23_7115297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_7115297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115297 prefixEnd_7115297 := by exact prefixLift 7115297
  have htrace : WordTrace (prefixWord ++ tailWord_7115297) baseStart_7115297 baseEnd_7115297 := by
    simpa [prefixWord, tailWord_7115297, baseEnd_7115297] using wordTrace_append hprefix tailTrace_7115297
  have hstable : (prefixWord ++ tailWord_7115297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115297).length < 2 ^ (prefixWord ++ tailWord_7115297).sum := by decide
  have hdescent : baseEnd_7115297 < baseStart_7115297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115333 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 2, 5]
def baseStart_7115333 : Nat := 118140960795 + 7115333 * 2 ^ 59
def prefixEnd_7115333 : Nat := 4983230072969 + 3 ^ 40 * 7115333 * 2
def baseEnd_7115333 : Nat := 1217861948599238320204895

theorem tailTrace_7115333 : CollatzResearch.WordTrace tailWord_7115333 prefixEnd_7115333 1217861948599238320204895 := by
  unfold tailWord_7115333
  simp only [CollatzResearch.WordTrace]
  refine ⟨259517514731371217974326653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173011676487580811982884435 259517514731371217974326653)
  ·
    refine ⟨97319068024264206740372495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259517514731371217974326653 97319068024264206740372495)
    ·
      refine ⟨145978602036396310110558743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97319068024264206740372495 145978602036396310110558743)
      ·
        refine ⟨218967903054594465165838115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145978602036396310110558743 218967903054594465165838115)
        ·
          refine ⟨328451854581891697748757173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218967903054594465165838115 328451854581891697748757173)
          ·
            refine ⟨30792361367052346663945985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 328451854581891697748757173 30792361367052346663945985)
            ·
              refine ⟨23094271025289259997959489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30792361367052346663945985 23094271025289259997959489)
              ·
                refine ⟨17320703268966944998469617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23094271025289259997959489 17320703268966944998469617)
                ·
                  refine ⟨12990527451725208748852213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17320703268966944998469617 12990527451725208748852213)
                  ·
                    refine ⟨1217861948599238320204895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12990527451725208748852213 1217861948599238320204895)
                    ·
                      rfl

theorem cell23_7115333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_7115333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115333 prefixEnd_7115333 := by exact prefixLift 7115333
  have htrace : WordTrace (prefixWord ++ tailWord_7115333) baseStart_7115333 baseEnd_7115333 := by
    simpa [prefixWord, tailWord_7115333, baseEnd_7115333] using wordTrace_append hprefix tailTrace_7115333
  have hstable : (prefixWord ++ tailWord_7115333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115333).length < 2 ^ (prefixWord ++ tailWord_7115333).sum := by decide
  have hdescent : baseEnd_7115333 < baseStart_7115333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115370 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_7115370 : Nat := 118140960795 + 7115370 * 2 ^ 59
def prefixEnd_7115370 : Nat := 4983230072969 + 3 ^ 40 * 7115370 * 2
def baseEnd_7115370 : Nat := 3653604844581931315852015

theorem tailTrace_7115370 : CollatzResearch.WordTrace tailWord_7115370 prefixEnd_7115370 3653604844581931315852015 := by
  unfold tailWord_7115370
  simp only [CollatzResearch.WordTrace]
  refine ⟨64879716058059293323355891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173012576154824782195615709 64879716058059293323355891)
  ·
    refine ⟨97319574087088939985033837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64879716058059293323355891 97319574087088939985033837)
    ·
      refine ⟨36494840282658352494387689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97319574087088939985033837 36494840282658352494387689)
      ·
        refine ⟨27371130211993764370790767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36494840282658352494387689 27371130211993764370790767)
        ·
          refine ⟨41056695317990646556186151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27371130211993764370790767 41056695317990646556186151)
          ·
            refine ⟨61585042976985969834279227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41056695317990646556186151 61585042976985969834279227)
            ·
              refine ⟨92377564465478954751418841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61585042976985969834279227 92377564465478954751418841)
              ·
                refine ⟨69283173349109216063564131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92377564465478954751418841 69283173349109216063564131)
                ·
                  refine ⟨103924760023663824095346197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69283173349109216063564131 103924760023663824095346197)
                  ·
                    refine ⟨4871473126109241754469353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103924760023663824095346197 4871473126109241754469353)
                    ·
                      refine ⟨3653604844581931315852015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871473126109241754469353 3653604844581931315852015)
                      ·
                        rfl

theorem cell23_7115370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_7115370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115370 prefixEnd_7115370 := by exact prefixLift 7115370
  have htrace : WordTrace (prefixWord ++ tailWord_7115370) baseStart_7115370 baseEnd_7115370 := by
    simpa [prefixWord, tailWord_7115370, baseEnd_7115370] using wordTrace_append hprefix tailTrace_7115370
  have hstable : (prefixWord ++ tailWord_7115370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115370).length < 2 ^ (prefixWord ++ tailWord_7115370).sum := by decide
  have hdescent : baseEnd_7115370 < baseStart_7115370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115393 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 8]
def baseStart_7115393 : Nat := 118140960795 + 7115393 * 2 ^ 59
def prefixEnd_7115393 : Nat := 4983230072969 + 3 ^ 40 * 7115393 * 2
def baseEnd_7115393 : Nat := 405957406070776080651601

theorem tailTrace_7115393 : CollatzResearch.WordTrace tailWord_7115393 prefixEnd_7115393 405957406070776080651601 := by
  unfold tailWord_7115393
  simp only [CollatzResearch.WordTrace]
  refine ⟨259519703111153848221510833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173013135407435898814340555 259519703111153848221510833)
  ·
    refine ⟨194639777333365386166133125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259519703111153848221510833 194639777333365386166133125)
    ·
      refine ⟨36494958250006009906149961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194639777333365386166133125 36494958250006009906149961)
      ·
        refine ⟨27371218687504507429612471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36494958250006009906149961 27371218687504507429612471)
        ·
          refine ⟨41056828031256761144418707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27371218687504507429612471 41056828031256761144418707)
          ·
            refine ⟨61585242046885141716628061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41056828031256761144418707 61585242046885141716628061)
            ·
              refine ⟨23094465767581928143735523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61585242046885141716628061 23094465767581928143735523)
              ·
                refine ⟨34641698651372892215603285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23094465767581928143735523 34641698651372892215603285)
                ·
                  refine ⟨405957406070776080651601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34641698651372892215603285 405957406070776080651601)
                  ·
                    rfl

theorem cell23_7115393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 8].length) (baseStart_7115393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115393 prefixEnd_7115393 := by exact prefixLift 7115393
  have htrace : WordTrace (prefixWord ++ tailWord_7115393) baseStart_7115393 baseEnd_7115393 := by
    simpa [prefixWord, tailWord_7115393, baseEnd_7115393] using wordTrace_append hprefix tailTrace_7115393
  have hstable : (prefixWord ++ tailWord_7115393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115393).length < 2 ^ (prefixWord ++ tailWord_7115393).sum := by decide
  have hdescent : baseEnd_7115393 < baseStart_7115393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115397 : List Nat := [1, 3, 1, 1, 4, 2, 2, 4, 1, 4]
def baseStart_7115397 : Nat := 118140960795 + 7115397 * 2 ^ 59
def prefixEnd_7115397 : Nat := 4983230072969 + 3 ^ 40 * 7115397 * 2
def baseEnd_7115397 : Nat := 1217872902853200903404797

theorem tailTrace_7115397 : CollatzResearch.WordTrace tailWord_7115397 prefixEnd_7115397 1217872902853200903404797 := by
  unfold tailWord_7115397
  simp only [CollatzResearch.WordTrace]
  refine ⟨259519849003139356904656445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173013232668759571269770963 259519849003139356904656445)
  ·
    refine ⟨97319943376177258839246167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259519849003139356904656445 97319943376177258839246167)
    ·
      refine ⟨145979915064265888258869251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97319943376177258839246167 145979915064265888258869251)
      ·
        refine ⟨218969872596398832388303877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145979915064265888258869251 218969872596398832388303877)
        ·
          refine ⟨41056851111824781072806977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218969872596398832388303877 41056851111824781072806977)
          ·
            refine ⟨30792638333868585804605233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41056851111824781072806977 30792638333868585804605233)
            ·
              refine ⟨23094478750401439353453925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30792638333868585804605233 23094478750401439353453925)
              ·
                refine ⟨4330214765700269878772611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23094478750401439353453925 4330214765700269878772611)
                ·
                  refine ⟨6495322148550404818158917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4330214765700269878772611 6495322148550404818158917)
                  ·
                    refine ⟨1217872902853200903404797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6495322148550404818158917 1217872902853200903404797)
                    ·
                      rfl

theorem cell23_7115397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_7115397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115397 prefixEnd_7115397 := by exact prefixLift 7115397
  have htrace : WordTrace (prefixWord ++ tailWord_7115397) baseStart_7115397 baseEnd_7115397 := by
    simpa [prefixWord, tailWord_7115397, baseEnd_7115397] using wordTrace_append hprefix tailTrace_7115397
  have hstable : (prefixWord ++ tailWord_7115397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115397).length < 2 ^ (prefixWord ++ tailWord_7115397).sum := by decide
  have hdescent : baseEnd_7115397 < baseStart_7115397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115463 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_7115463 : Nat := 118140960795 + 7115463 * 2 ^ 59
def prefixEnd_7115463 : Nat := 4983230072969 + 3 ^ 40 * 7115463 * 2
def baseEnd_7115463 : Nat := 3653652598282799451989087

theorem tailTrace_7115463 : CollatzResearch.WordTrace tailWord_7115463 prefixEnd_7115463 3653652598282799451989087 := by
  unfold tailWord_7115463
  simp only [CollatzResearch.WordTrace]
  refine ⟨259522256220900250176559043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173014837480600166784372695 259522256220900250176559043)
  ·
    refine ⟨389283384331350375264838565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259522256220900250176559043 389283384331350375264838565)
    ·
      refine ⟨72990634562128195362157231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389283384331350375264838565 72990634562128195362157231)
      ·
        refine ⟨109485951843192293043235847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72990634562128195362157231 109485951843192293043235847)
        ·
          refine ⟨164228927764788439564853771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109485951843192293043235847 164228927764788439564853771)
          ·
            refine ⟨246343391647182659347280657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164228927764788439564853771 246343391647182659347280657)
            ·
              refine ⟨184757543735386994510460493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246343391647182659347280657 184757543735386994510460493)
              ·
                refine ⟨69284078900770122941422685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184757543735386994510460493 69284078900770122941422685)
                ·
                  refine ⟨25981529587788796103033507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69284078900770122941422685 25981529587788796103033507)
                  ·
                    refine ⟨38972294381683194154550261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25981529587788796103033507 38972294381683194154550261)
                    ·
                      refine ⟨3653652598282799451989087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38972294381683194154550261 3653652598282799451989087)
                      ·
                        rfl

theorem cell23_7115463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_7115463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115463 prefixEnd_7115463 := by exact prefixLift 7115463
  have htrace : WordTrace (prefixWord ++ tailWord_7115463) baseStart_7115463 baseEnd_7115463 := by
    simpa [prefixWord, tailWord_7115463, baseEnd_7115463] using wordTrace_append hprefix tailTrace_7115463
  have hstable : (prefixWord ++ tailWord_7115463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115463).length < 2 ^ (prefixWord ++ tailWord_7115463).sum := by decide
  have hdescent : baseEnd_7115463 < baseStart_7115463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115473 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_7115473 : Nat := 118140960795 + 7115473 * 2 ^ 59
def prefixEnd_7115473 : Nat := 4983230072969 + 3 ^ 40 * 7115473 * 2
def baseEnd_7115473 : Nat := 3653657733089344412864041

theorem tailTrace_7115473 : CollatzResearch.WordTrace tailWord_7115473 prefixEnd_7115473 3653657733089344412864041 := by
  unfold tailWord_7115473
  simp only [CollatzResearch.WordTrace]
  refine ⟨259522620950864021884423073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173015080633909347922948715 259522620950864021884423073)
  ·
    refine ⟨194641965713148016413317305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259522620950864021884423073 194641965713148016413317305)
    ·
      refine ⟨145981474284861012309987979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194641965713148016413317305 145981474284861012309987979)
      ·
        refine ⟨218972211427291518464981969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145981474284861012309987979 218972211427291518464981969)
        ·
          refine ⟨164229158570468638848736477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218972211427291518464981969 164229158570468638848736477)
          ·
            refine ⟨61585934463925739568276179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164229158570468638848736477 61585934463925739568276179)
            ·
              refine ⟨92378901695888609352414269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61585934463925739568276179 92378901695888609352414269)
              ·
                refine ⟨34642088135958228507155351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92378901695888609352414269 34642088135958228507155351)
                ·
                  refine ⟨51963132203937342760733027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34642088135958228507155351 51963132203937342760733027)
                  ·
                    refine ⟨77944698305906014141099541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51963132203937342760733027 77944698305906014141099541)
                    ·
                      refine ⟨3653657733089344412864041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77944698305906014141099541 3653657733089344412864041)
                      ·
                        rfl

theorem cell23_7115473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_7115473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115473 prefixEnd_7115473 := by exact prefixLift 7115473
  have htrace : WordTrace (prefixWord ++ tailWord_7115473) baseStart_7115473 baseEnd_7115473 := by
    simpa [prefixWord, tailWord_7115473, baseEnd_7115473] using wordTrace_append hprefix tailTrace_7115473
  have hstable : (prefixWord ++ tailWord_7115473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115473).length < 2 ^ (prefixWord ++ tailWord_7115473).sum := by decide
  have hdescent : baseEnd_7115473 < baseStart_7115473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115474 : List Nat := [3, 2, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_7115474 : Nat := 118140960795 + 7115474 * 2 ^ 59
def prefixEnd_7115474 : Nat := 4983230072969 + 3 ^ 40 * 7115474 * 2
def baseEnd_7115474 : Nat := 1217886082189999636317179

theorem tailTrace_7115474 : CollatzResearch.WordTrace tailWord_7115474 prefixEnd_7115474 1217886082189999636317179 := by
  unfold tailWord_7115474
  simp only [CollatzResearch.WordTrace]
  refine ⟨64880664355965099763802369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173015104949240266036806317 64880664355965099763802369)
  ·
    refine ⟨48660498266973824822851777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64880664355965099763802369 48660498266973824822851777)
    ·
      refine ⟨36495373700230368617138833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48660498266973824822851777 36495373700230368617138833)
      ·
        refine ⟨27371530275172776462854125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36495373700230368617138833 27371530275172776462854125)
        ·
          refine ⟨10264323853189791173570297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27371530275172776462854125 10264323853189791173570297)
          ·
            refine ⟨7698242889892343380177723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10264323853189791173570297 7698242889892343380177723)
            ·
              refine ⟨11547364334838515070266585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7698242889892343380177723 11547364334838515070266585)
              ·
                refine ⟨8660523251128886302699939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11547364334838515070266585 8660523251128886302699939)
                ·
                  refine ⟨12990784876693329454049909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8660523251128886302699939 12990784876693329454049909)
                  ·
                    refine ⟨1217886082189999636317179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12990784876693329454049909 1217886082189999636317179)
                    ·
                      rfl

theorem cell23_7115474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_7115474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115474 prefixEnd_7115474 := by exact prefixLift 7115474
  have htrace : WordTrace (prefixWord ++ tailWord_7115474) baseStart_7115474 baseEnd_7115474 := by
    simpa [prefixWord, tailWord_7115474, baseEnd_7115474] using wordTrace_append hprefix tailTrace_7115474
  have hstable : (prefixWord ++ tailWord_7115474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115474).length < 2 ^ (prefixWord ++ tailWord_7115474).sum := by decide
  have hdescent : baseEnd_7115474 < baseStart_7115474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115520 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 1, 9, 2]
def baseStart_7115520 : Nat := 118140960795 + 7115520 * 2 ^ 59
def prefixEnd_7115520 : Nat := 4983230072969 + 3 ^ 40 * 7115520 * 2
def baseEnd_7115520 : Nat := 3653681866680105728976325

theorem tailTrace_7115520 : CollatzResearch.WordTrace tailWord_7115520 prefixEnd_7115520 3653681866680105728976325 := by
  unfold tailWord_7115520
  simp only [CollatzResearch.WordTrace]
  refine ⟨129762167590846874455692007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173016223454462499274256009 129762167590846874455692007)
  ·
    refine ⟨194643251386270311683538011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129762167590846874455692007 194643251386270311683538011)
    ·
      refine ⟨291964877079405467525307017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194643251386270311683538011 291964877079405467525307017)
      ·
        refine ⟨218973657809554100643980263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291964877079405467525307017 218973657809554100643980263)
        ·
          refine ⟨328460486714331150965970395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218973657809554100643980263 328460486714331150965970395)
          ·
            refine ⟨492690730071496726448955593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328460486714331150965970395 492690730071496726448955593)
            ·
              refine ⟨369518047553622544836716695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492690730071496726448955593 369518047553622544836716695)
              ·
                refine ⟨554277071330433817255075043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369518047553622544836716695 554277071330433817255075043)
                ·
                  refine ⟨831415606995650725882612565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 554277071330433817255075043 831415606995650725882612565)
                  ·
                    refine ⟨4871575822240140971968433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 831415606995650725882612565 4871575822240140971968433)
                    ·
                      refine ⟨3653681866680105728976325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871575822240140971968433 3653681866680105728976325)
                      ·
                        rfl

theorem cell23_7115520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 9, 2].length) (baseStart_7115520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115520 prefixEnd_7115520 := by exact prefixLift 7115520
  have htrace : WordTrace (prefixWord ++ tailWord_7115520) baseStart_7115520 baseEnd_7115520 := by
    simpa [prefixWord, tailWord_7115520, baseEnd_7115520] using wordTrace_append hprefix tailTrace_7115520
  have hstable : (prefixWord ++ tailWord_7115520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115520).length < 2 ^ (prefixWord ++ tailWord_7115520).sum := by decide
  have hdescent : baseEnd_7115520 < baseStart_7115520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115523 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 5]
def baseStart_7115523 : Nat := 118140960795 + 7115523 * 2 ^ 59
def prefixEnd_7115523 : Nat := 4983230072969 + 3 ^ 40 * 7115523 * 2
def baseEnd_7115523 : Nat := 3653683407122069217238811

theorem tailTrace_7115523 : CollatzResearch.WordTrace tailWord_7115523 prefixEnd_7115523 3653683407122069217238811 := by
  unfold tailWord_7115523
  simp only [CollatzResearch.WordTrace]
  refine ⟨259524444600682880423743223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173016296400455253615828815 259524444600682880423743223)
  ·
    refine ⟨389286666901024320635614835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259524444600682880423743223 389286666901024320635614835)
    ·
      refine ⟨583930000351536480953422253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389286666901024320635614835 583930000351536480953422253)
      ·
        refine ⟨218973750131826180357533345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 583930000351536480953422253 218973750131826180357533345)
        ·
          refine ⟨164230312598869635268150009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218973750131826180357533345 164230312598869635268150009)
          ·
            refine ⟨123172734449152226451112507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164230312598869635268150009 123172734449152226451112507)
            ·
              refine ⟨184759101673728339676668761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123172734449152226451112507 184759101673728339676668761)
              ·
                refine ⟨138569326255296254757501571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184759101673728339676668761 138569326255296254757501571)
                ·
                  refine ⟨207853989382944382136252357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138569326255296254757501571 207853989382944382136252357)
                  ·
                    refine ⟨38972623009302071650547317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 207853989382944382136252357 38972623009302071650547317)
                    ·
                      refine ⟨3653683407122069217238811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38972623009302071650547317 3653683407122069217238811)
                      ·
                        rfl

theorem cell23_7115523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_7115523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115523 prefixEnd_7115523 := by exact prefixLift 7115523
  have htrace : WordTrace (prefixWord ++ tailWord_7115523) baseStart_7115523 baseEnd_7115523 := by
    simpa [prefixWord, tailWord_7115523, baseEnd_7115523] using wordTrace_append hprefix tailTrace_7115523
  have hstable : (prefixWord ++ tailWord_7115523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115523).length < 2 ^ (prefixWord ++ tailWord_7115523).sum := by decide
  have hdescent : baseEnd_7115523 < baseStart_7115523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115527 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_7115527 : Nat := 118140960795 + 7115527 * 2 ^ 59
def prefixEnd_7115527 : Nat := 4983230072969 + 3 ^ 40 * 7115527 * 2
def baseEnd_7115527 : Nat := 3653685461044687201588793

theorem tailTrace_7115527 : CollatzResearch.WordTrace tailWord_7115527 prefixEnd_7115527 3653685461044687201588793 := by
  unfold tailWord_7115527
  simp only [CollatzResearch.WordTrace]
  refine ⟨259524590492668389106888835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173016393661778926071259223 259524590492668389106888835)
  ·
    refine ⟨389286885739002583660333253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259524590492668389106888835 389286885739002583660333253)
    ·
      refine ⟨72991291076062984436312485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389286885739002583660333253 72991291076062984436312485)
      ·
        refine ⟨13685867076761809581808591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72991291076062984436312485 13685867076761809581808591)
        ·
          refine ⟨20528800615142714372712887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13685867076761809581808591 20528800615142714372712887)
          ·
            refine ⟨30793200922714071559069331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20528800615142714372712887 30793200922714071559069331)
            ·
              refine ⟨46189801384071107338603997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30793200922714071559069331 46189801384071107338603997)
              ·
                refine ⟨17321175519026665251976499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46189801384071107338603997 17321175519026665251976499)
                ·
                  refine ⟨25981763278539997877964749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17321175519026665251976499 25981763278539997877964749)
                  ·
                    refine ⟨9743161229452499204236781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25981763278539997877964749 9743161229452499204236781)
                    ·
                      refine ⟨3653685461044687201588793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9743161229452499204236781 3653685461044687201588793)
                      ·
                        rfl

theorem cell23_7115527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_7115527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115527 prefixEnd_7115527 := by exact prefixLift 7115527
  have htrace : WordTrace (prefixWord ++ tailWord_7115527) baseStart_7115527 baseEnd_7115527 := by
    simpa [prefixWord, tailWord_7115527, baseEnd_7115527] using wordTrace_append hprefix tailTrace_7115527
  have hstable : (prefixWord ++ tailWord_7115527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115527).length < 2 ^ (prefixWord ++ tailWord_7115527).sum := by decide
  have hdescent : baseEnd_7115527 < baseStart_7115527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115537 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 3, 3, 2]
def baseStart_7115537 : Nat := 118140960795 + 7115537 * 2 ^ 59
def prefixEnd_7115537 : Nat := 4983230072969 + 3 ^ 40 * 7115537 * 2
def baseEnd_7115537 : Nat := 3653690595851232162463747

theorem tailTrace_7115537 : CollatzResearch.WordTrace tailWord_7115537 prefixEnd_7115537 3653690595851232162463747 := by
  unfold tailWord_7115537
  simp only [CollatzResearch.WordTrace]
  refine ⟨259524955222632160814752865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173016636815088107209835243 259524955222632160814752865)
  ·
    refine ⟨194643716416974120611064649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259524955222632160814752865 194643716416974120611064649)
    ·
      refine ⟨145982787312730590458298487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194643716416974120611064649 145982787312730590458298487)
      ·
        refine ⟨218974180969095885687447731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145982787312730590458298487 218974180969095885687447731)
        ·
          refine ⟨328461271453643828531171597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218974180969095885687447731 328461271453643828531171597)
          ·
            refine ⟨123172976795116435699189349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328461271453643828531171597 123172976795116435699189349)
            ·
              refine ⟨23094933149084331693598003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123172976795116435699189349 23094933149084331693598003)
              ·
                refine ⟨34642399723626497540397005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23094933149084331693598003 34642399723626497540397005)
                ·
                  refine ⟨12990899896359936577648877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34642399723626497540397005 12990899896359936577648877)
                  ·
                    refine ⟨4871587461134976216618329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12990899896359936577648877 4871587461134976216618329)
                    ·
                      refine ⟨3653690595851232162463747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871587461134976216618329 3653690595851232162463747)
                      ·
                        rfl

theorem cell23_7115537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 3, 2].length) (baseStart_7115537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115537 prefixEnd_7115537 := by exact prefixLift 7115537
  have htrace : WordTrace (prefixWord ++ tailWord_7115537) baseStart_7115537 baseEnd_7115537 := by
    simpa [prefixWord, tailWord_7115537, baseEnd_7115537] using wordTrace_append hprefix tailTrace_7115537
  have hstable : (prefixWord ++ tailWord_7115537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115537).length < 2 ^ (prefixWord ++ tailWord_7115537).sum := by decide
  have hdescent : baseEnd_7115537 < baseStart_7115537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115560 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 4, 6]
def baseStart_7115560 : Nat := 118140960795 + 7115560 * 2 ^ 59
def prefixEnd_7115560 : Nat := 4983230072969 + 3 ^ 40 * 7115560 * 2
def baseEnd_7115560 : Nat := 1217900801968761857492047

theorem tailTrace_7115560 : CollatzResearch.WordTrace tailWord_7115560 prefixEnd_7115560 1217900801968761857492047 := by
  unfold tailWord_7115560
  simp only [CollatzResearch.WordTrace]
  refine ⟨129762897050774417871420067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173017196067699223828560089 129762897050774417871420067)
  ·
    refine ⟨194644345576161626807130101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129762897050774417871420067 194644345576161626807130101)
    ·
      refine ⟨18247907397765152513168447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194644345576161626807130101 18247907397765152513168447)
      ·
        refine ⟨27371861096647728769752671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18247907397765152513168447 27371861096647728769752671)
        ·
          refine ⟨41057791644971593154629007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27371861096647728769752671 41057791644971593154629007)
          ·
            refine ⟨61586687467457389731943511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41057791644971593154629007 61586687467457389731943511)
            ·
              refine ⟨92380031201186084597915267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61586687467457389731943511 92380031201186084597915267)
              ·
                refine ⟨138570046801779126896872901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92380031201186084597915267 138570046801779126896872901)
                ·
                  refine ⟨25981883775333586293163669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138570046801779126896872901 25981883775333586293163669)
                  ·
                    refine ⟨1217900801968761857492047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25981883775333586293163669 1217900801968761857492047)
                    ·
                      rfl

theorem cell23_7115560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_7115560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115560 prefixEnd_7115560 := by exact prefixLift 7115560
  have htrace : WordTrace (prefixWord ++ tailWord_7115560) baseStart_7115560 baseEnd_7115560 := by
    simpa [prefixWord, tailWord_7115560, baseEnd_7115560] using wordTrace_append hprefix tailTrace_7115560
  have hstable : (prefixWord ++ tailWord_7115560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115560).length < 2 ^ (prefixWord ++ tailWord_7115560).sum := by decide
  have hdescent : baseEnd_7115560 < baseStart_7115560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115563 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 6]
def baseStart_7115563 : Nat := 118140960795 + 7115563 * 2 ^ 59
def prefixEnd_7115563 : Nat := 4983230072969 + 3 ^ 40 * 7115563 * 2
def baseEnd_7115563 : Nat := 3653703946348249060738627

theorem tailTrace_7115563 : CollatzResearch.WordTrace tailWord_7115563 prefixEnd_7115563 3653703946348249060738627 := by
  unfold tailWord_7115563
  simp only [CollatzResearch.WordTrace]
  refine ⟨259525903520537967255199343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173017269013691978170132895 259525903520537967255199343)
  ·
    refine ⟨389288855280806950882799015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259525903520537967255199343 389288855280806950882799015)
    ·
      refine ⟨583933282921210426324198523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389288855280806950882799015 583933282921210426324198523)
      ·
        refine ⟨875899924381815639486297785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583933282921210426324198523 875899924381815639486297785)
        ·
          refine ⟨656924943286361729614723339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 875899924381815639486297785 656924943286361729614723339)
          ·
            refine ⟨985387414929542594422085009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656924943286361729614723339 985387414929542594422085009)
            ·
              refine ⟨739040561197156945816563757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985387414929542594422085009 739040561197156945816563757)
              ·
                refine ⟨277140210448933854681211409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 739040561197156945816563757 277140210448933854681211409)
                ·
                  refine ⟨207855157836700391010908557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277140210448933854681211409 207855157836700391010908557)
                  ·
                    refine ⟨77945684188762646629090709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207855157836700391010908557 77945684188762646629090709)
                    ·
                      refine ⟨3653703946348249060738627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77945684188762646629090709 3653703946348249060738627)
                      ·
                        rfl

theorem cell23_7115563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 6].length) (baseStart_7115563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115563 prefixEnd_7115563 := by exact prefixLift 7115563
  have htrace : WordTrace (prefixWord ++ tailWord_7115563) baseStart_7115563 baseEnd_7115563 := by
    simpa [prefixWord, tailWord_7115563, baseEnd_7115563] using wordTrace_append hprefix tailTrace_7115563
  have hstable : (prefixWord ++ tailWord_7115563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115563).length < 2 ^ (prefixWord ++ tailWord_7115563).sum := by decide
  have hdescent : baseEnd_7115563 < baseStart_7115563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115584 : List Nat := [2, 1, 1, 2, 2, 1, 1, 7, 2, 2, 2]
def baseStart_7115584 : Nat := 118140960795 + 7115584 * 2 ^ 59
def prefixEnd_7115584 : Nat := 4983230072969 + 3 ^ 40 * 7115584 * 2
def baseEnd_7115584 : Nat := 3653714729441993478576031

theorem tailTrace_7115584 : CollatzResearch.WordTrace tailWord_7115584 prefixEnd_7115584 3653714729441993478576031 := by
  unfold tailWord_7115584
  simp only [CollatzResearch.WordTrace]
  refine ⟨129763334726730943920856903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173017779635641258561142537 129763334726730943920856903)
  ·
    refine ⟨194645002090096415881285355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129763334726730943920856903 194645002090096415881285355)
    ·
      refine ⟨291967503135144623821928033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194645002090096415881285355 291967503135144623821928033)
      ·
        refine ⟨218975627351358467866446025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291967503135144623821928033 218975627351358467866446025)
        ·
          refine ⟨164231720513518850899834519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218975627351358467866446025 164231720513518850899834519)
          ·
            refine ⟨246347580770278276349751779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164231720513518850899834519 246347580770278276349751779)
            ·
              refine ⟨369521371155417414524627669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246347580770278276349751779 369521371155417414524627669)
              ·
                refine ⟨8660657136455095652920961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 369521371155417414524627669 8660657136455095652920961)
                ·
                  refine ⟨6495492852341321739690721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8660657136455095652920961 6495492852341321739690721)
                  ·
                    refine ⟨4871619639255991304768041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6495492852341321739690721 4871619639255991304768041)
                    ·
                      refine ⟨3653714729441993478576031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871619639255991304768041 3653714729441993478576031)
                      ·
                        rfl

theorem cell23_7115584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 2, 2, 2].length) (baseStart_7115584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115584 prefixEnd_7115584 := by exact prefixLift 7115584
  have htrace : WordTrace (prefixWord ++ tailWord_7115584) baseStart_7115584 baseEnd_7115584 := by
    simpa [prefixWord, tailWord_7115584, baseEnd_7115584] using wordTrace_append hprefix tailTrace_7115584
  have hstable : (prefixWord ++ tailWord_7115584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115584).length < 2 ^ (prefixWord ++ tailWord_7115584).sum := by decide
  have hdescent : baseEnd_7115584 < baseStart_7115584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115600 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 3]
def baseStart_7115600 : Nat := 118140960795 + 7115600 * 2 ^ 59
def prefixEnd_7115600 : Nat := 4983230072969 + 3 ^ 40 * 7115600 * 2
def baseEnd_7115600 : Nat := 3653722945132465415975957

theorem tailTrace_7115600 : CollatzResearch.WordTrace tailWord_7115600 prefixEnd_7115600 3653722945132465415975957 := by
  unfold tailWord_7115600
  simp only [CollatzResearch.WordTrace]
  refine ⟨129763626510701961287148127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173018168680935948382864169 129763626510701961287148127)
  ·
    refine ⟨194645439766052941930722191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129763626510701961287148127 194645439766052941930722191)
    ·
      refine ⟨291968159649079412896083287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194645439766052941930722191 291968159649079412896083287)
      ·
        refine ⟨437952239473619119344124931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291968159649079412896083287 437952239473619119344124931)
        ·
          refine ⟨656928359210428679016187397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437952239473619119344124931 656928359210428679016187397)
          ·
            refine ⟨123174067351955377315535137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 656928359210428679016187397 123174067351955377315535137)
            ·
              refine ⟨92380550513966532986651353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123174067351955377315535137 92380550513966532986651353)
              ·
                refine ⟨69285412885474899739988515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92380550513966532986651353 69285412885474899739988515)
                ·
                  refine ⟨103928119328212349609982773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69285412885474899739988515 103928119328212349609982773)
                  ·
                    refine ⟨9743261187019907775935885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103928119328212349609982773 9743261187019907775935885)
                    ·
                      refine ⟨3653722945132465415975957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9743261187019907775935885 3653722945132465415975957)
                      ·
                        rfl

theorem cell23_7115600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 3].length) (baseStart_7115600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115600 prefixEnd_7115600 := by exact prefixLift 7115600
  have htrace : WordTrace (prefixWord ++ tailWord_7115600) baseStart_7115600 baseEnd_7115600 := by
    simpa [prefixWord, tailWord_7115600, baseEnd_7115600] using wordTrace_append hprefix tailTrace_7115600
  have hstable : (prefixWord ++ tailWord_7115600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115600).length < 2 ^ (prefixWord ++ tailWord_7115600).sum := by decide
  have hdescent : baseEnd_7115600 < baseStart_7115600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115640 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_7115640 : Nat := 118140960795 + 7115640 * 2 ^ 59
def prefixEnd_7115640 : Nat := 4983230072969 + 3 ^ 40 * 7115640 * 2
def baseEnd_7115640 : Nat := 3653743484358645259475773

theorem tailTrace_7115640 : CollatzResearch.WordTrace tailWord_7115640 prefixEnd_7115640 3653743484358645259475773 := by
  unfold tailWord_7115640
  simp only [CollatzResearch.WordTrace]
  refine ⟨129764355970629504702876187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173019141294172672937168249 129764355970629504702876187)
  ·
    refine ⟨194646533955944257054314281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129764355970629504702876187 194646533955944257054314281)
    ·
      refine ⟨145984900466958192790735711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194646533955944257054314281 145984900466958192790735711)
      ·
        refine ⟨218977350700437289186103567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145984900466958192790735711 218977350700437289186103567)
        ·
          refine ⟨328466026050655933779155351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218977350700437289186103567 328466026050655933779155351)
          ·
            refine ⟨492699039075983900668733027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328466026050655933779155351 492699039075983900668733027)
            ·
              refine ⟨739048558613975851003099541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492699039075983900668733027 739048558613975851003099541)
              ·
                refine ⟨34642901185030118015770291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 739048558613975851003099541 34642901185030118015770291)
                ·
                  refine ⟨51964351777545177023655437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34642901185030118015770291 51964351777545177023655437)
                  ·
                    refine ⟨19486631916579441383870789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51964351777545177023655437 19486631916579441383870789)
                    ·
                      refine ⟨3653743484358645259475773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19486631916579441383870789 3653743484358645259475773)
                      ·
                        rfl

theorem cell23_7115640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_7115640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115640 prefixEnd_7115640 := by exact prefixLift 7115640
  have htrace : WordTrace (prefixWord ++ tailWord_7115640) baseStart_7115640 baseEnd_7115640 := by
    simpa [prefixWord, tailWord_7115640, baseEnd_7115640] using wordTrace_append hprefix tailTrace_7115640
  have hstable : (prefixWord ++ tailWord_7115640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115640).length < 2 ^ (prefixWord ++ tailWord_7115640).sum := by decide
  have hdescent : baseEnd_7115640 < baseStart_7115640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115657 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 2, 1, 4]
def baseStart_7115657 : Nat := 118140960795 + 7115657 * 2 ^ 59
def prefixEnd_7115657 : Nat := 4983230072969 + 3 ^ 40 * 7115657 * 2
def baseEnd_7115657 : Nat := 3653752213529771692963195

theorem tailTrace_7115657 : CollatzResearch.WordTrace tailWord_7115657 prefixEnd_7115657 3653752213529771692963195 := by
  unfold tailWord_7115657
  simp only [CollatzResearch.WordTrace]
  refine ⟨259529331982197421309121225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173019554654798280872747483 259529331982197421309121225)
  ·
    refine ⟨194646998986648065981840919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259529331982197421309121225 194646998986648065981840919)
    ·
      refine ⟨291970498479972098972761379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194646998986648065981840919 291970498479972098972761379)
      ·
        refine ⟨437955747719958148459142069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291970498479972098972761379 437955747719958148459142069)
        ·
          refine ⟨41058351348746076418044569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 437955747719958148459142069 41058351348746076418044569)
          ·
            refine ⟨30793763511559557313533427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41058351348746076418044569 30793763511559557313533427)
            ·
              refine ⟨46190645267339335970300141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30793763511559557313533427 46190645267339335970300141)
              ·
                refine ⟨17321491975252250988862553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46190645267339335970300141 17321491975252250988862553)
                ·
                  refine ⟨12991118981439188241646915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17321491975252250988862553 12991118981439188241646915)
                  ·
                    refine ⟨19486678472158782362470373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12991118981439188241646915 19486678472158782362470373)
                    ·
                      refine ⟨3653752213529771692963195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19486678472158782362470373 3653752213529771692963195)
                      ·
                        rfl

theorem cell23_7115657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_7115657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115657 prefixEnd_7115657 := by exact prefixLift 7115657
  have htrace : WordTrace (prefixWord ++ tailWord_7115657) baseStart_7115657 baseEnd_7115657 := by
    simpa [prefixWord, tailWord_7115657, baseEnd_7115657] using wordTrace_append hprefix tailTrace_7115657
  have hstable : (prefixWord ++ tailWord_7115657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115657).length < 2 ^ (prefixWord ++ tailWord_7115657).sum := by decide
  have hdescent : baseEnd_7115657 < baseStart_7115657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115680 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 8]
def baseStart_7115680 : Nat := 118140960795 + 7115680 * 2 ^ 59
def prefixEnd_7115680 : Nat := 4983230072969 + 3 ^ 40 * 7115680 * 2
def baseEnd_7115680 : Nat := 405973780398313900330621

theorem tailTrace_7115680 : CollatzResearch.WordTrace tailWord_7115680 prefixEnd_7115680 405973780398313900330621 := by
  unfold tailWord_7115680
  simp only [CollatzResearch.WordTrace]
  refine ⟨129765085430557048118604247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173020113907409397491472329 129765085430557048118604247)
  ·
    refine ⟨194647628145835572177906371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129765085430557048118604247 194647628145835572177906371)
    ·
      refine ⟨291971442218753358266859557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194647628145835572177906371 291971442218753358266859557)
      ·
        refine ⟨54744645416016254675036167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291971442218753358266859557 54744645416016254675036167)
        ·
          refine ⟨82116968124024382012554251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54744645416016254675036167 82116968124024382012554251)
          ·
            refine ⟨123175452186036573018831377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82116968124024382012554251 123175452186036573018831377)
            ·
              refine ⟨92381589139527429764123533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123175452186036573018831377 92381589139527429764123533)
              ·
                refine ⟨34643095927322786161546325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92381589139527429764123533 34643095927322786161546325)
                ·
                  refine ⟨405973780398313900330621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34643095927322786161546325 405973780398313900330621)
                  ·
                    rfl

theorem cell23_7115680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 8].length) (baseStart_7115680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115680 prefixEnd_7115680 := by exact prefixLift 7115680
  have htrace : WordTrace (prefixWord ++ tailWord_7115680) baseStart_7115680 baseEnd_7115680 := by
    simpa [prefixWord, tailWord_7115680, baseEnd_7115680] using wordTrace_append hprefix tailTrace_7115680
  have hstable : (prefixWord ++ tailWord_7115680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115680).length < 2 ^ (prefixWord ++ tailWord_7115680).sum := by decide
  have hdescent : baseEnd_7115680 < baseStart_7115680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115724 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 5, 1, 3]
def baseStart_7115724 : Nat := 118140960795 + 7115724 * 2 ^ 59
def prefixEnd_7115724 : Nat := 4983230072969 + 3 ^ 40 * 7115724 * 2
def baseEnd_7115724 : Nat := 3653786616733622930825387

theorem tailTrace_7115724 : CollatzResearch.WordTrace tailWord_7115724 prefixEnd_7115724 3653786616733622930825387 := by
  unfold tailWord_7115724
  simp only [CollatzResearch.WordTrace]
  refine ⟨129765887836477345875905113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173021183781969794501206817 129765887836477345875905113)
  ·
    refine ⟨97324415877358009406928835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129765887836477345875905113 97324415877358009406928835)
    ·
      refine ⟨145986623816037014110393253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97324415877358009406928835 145986623816037014110393253)
      ·
        refine ⟨27372491965506940145698735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145986623816037014110393253 27372491965506940145698735)
        ·
          refine ⟨41058737948260410218548103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27372491965506940145698735 41058737948260410218548103)
          ·
            refine ⟨61588106922390615327822155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41058737948260410218548103 61588106922390615327822155)
            ·
              refine ⟨92382160383585922991733233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61588106922390615327822155 92382160383585922991733233)
              ·
                refine ⟨69286620287689442243799925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92382160383585922991733233 69286620287689442243799925)
                ·
                  refine ⟨6495620651970885210356243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69286620287689442243799925 6495620651970885210356243)
                  ·
                    refine ⟨9743430977956327815534365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6495620651970885210356243 9743430977956327815534365)
                    ·
                      refine ⟨3653786616733622930825387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9743430977956327815534365 3653786616733622930825387)
                      ·
                        rfl

theorem cell23_7115724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_7115724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115724 prefixEnd_7115724 := by exact prefixLift 7115724
  have htrace : WordTrace (prefixWord ++ tailWord_7115724) baseStart_7115724 baseEnd_7115724 := by
    simpa [prefixWord, tailWord_7115724, baseEnd_7115724] using wordTrace_append hprefix tailTrace_7115724
  have hstable : (prefixWord ++ tailWord_7115724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115724).length < 2 ^ (prefixWord ++ tailWord_7115724).sum := by decide
  have hdescent : baseEnd_7115724 < baseStart_7115724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115734 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_7115734 : Nat := 118140960795 + 7115734 * 2 ^ 59
def prefixEnd_7115734 : Nat := 4983230072969 + 3 ^ 40 * 7115734 * 2
def baseEnd_7115734 : Nat := 3653791751540167891700341

theorem tailTrace_7115734 : CollatzResearch.WordTrace tailWord_7115734 prefixEnd_7115734 3653791751540167891700341 := by
  unfold tailWord_7115734
  simp only [CollatzResearch.WordTrace]
  refine ⟨16220758775182403966229641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173021426935278975639782837 16220758775182403966229641)
  ·
    refine ⟨12165569081386802974672231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16220758775182403966229641 12165569081386802974672231)
    ·
      refine ⟨18248353622080204462008347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12165569081386802974672231 18248353622080204462008347)
      ·
        refine ⟨27372530433120306693012521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18248353622080204462008347 27372530433120306693012521)
        ·
          refine ⟨20529397824840230019759391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27372530433120306693012521 20529397824840230019759391)
          ·
            refine ⟨30794096737260345029639087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20529397824840230019759391 30794096737260345029639087)
            ·
              refine ⟨46191145105890517544458631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30794096737260345029639087 46191145105890517544458631)
              ·
                refine ⟨69286717658835776316687947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46191145105890517544458631 69286717658835776316687947)
                ·
                  refine ⟨103930076488253664475031921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69286717658835776316687947 103930076488253664475031921)
                  ·
                    refine ⟨77947557366190248356273941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103930076488253664475031921 77947557366190248356273941)
                    ·
                      refine ⟨3653791751540167891700341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77947557366190248356273941 3653791751540167891700341)
                      ·
                        rfl

theorem cell23_7115734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_7115734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115734 prefixEnd_7115734 := by exact prefixLift 7115734
  have htrace : WordTrace (prefixWord ++ tailWord_7115734) baseStart_7115734 baseEnd_7115734 := by
    simpa [prefixWord, tailWord_7115734, baseEnd_7115734] using wordTrace_append hprefix tailTrace_7115734
  have hstable : (prefixWord ++ tailWord_7115734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115734).length < 2 ^ (prefixWord ++ tailWord_7115734).sum := by decide
  have hdescent : baseEnd_7115734 < baseStart_7115734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115741 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_7115741 : Nat := 118140960795 + 7115741 * 2 ^ 59
def prefixEnd_7115741 : Nat := 4983230072969 + 3 ^ 40 * 7115741 * 2
def baseEnd_7115741 : Nat := 3653795345904749364312809

theorem tailTrace_7115741 : CollatzResearch.WordTrace tailWord_7115741 prefixEnd_7115741 3653795345904749364312809 := by
  unfold tailWord_7115741
  simp only [CollatzResearch.WordTrace]
  refine ⟨259532395713893103655179077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173021597142595402436786051 259532395713893103655179077)
  ·
    refine ⟨48662324196354956935346077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259532395713893103655179077 48662324196354956935346077)
    ·
      refine ⟨18248371573633108850754779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48662324196354956935346077 18248371573633108850754779)
      ·
        refine ⟨27372557360449663276132169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18248371573633108850754779 27372557360449663276132169)
        ·
          refine ⟨20529418020337247457099127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27372557360449663276132169 20529418020337247457099127)
          ·
            refine ⟨30794127030505871185648691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20529418020337247457099127 30794127030505871185648691)
            ·
              refine ⟨46191190545758806778473037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30794127030505871185648691 46191190545758806778473037)
              ·
                refine ⟨17321696454659552541927389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46191190545758806778473037 17321696454659552541927389)
                ·
                  refine ⟨6495636170497332203222771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17321696454659552541927389 6495636170497332203222771)
                  ·
                    refine ⟨9743454255745998304834157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6495636170497332203222771 9743454255745998304834157)
                    ·
                      refine ⟨3653795345904749364312809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9743454255745998304834157 3653795345904749364312809)
                      ·
                        rfl

theorem cell23_7115741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_7115741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115741 prefixEnd_7115741 := by exact prefixLift 7115741
  have htrace : WordTrace (prefixWord ++ tailWord_7115741) baseStart_7115741 baseEnd_7115741 := by
    simpa [prefixWord, tailWord_7115741, baseEnd_7115741] using wordTrace_append hprefix tailTrace_7115741
  have hstable : (prefixWord ++ tailWord_7115741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115741).length < 2 ^ (prefixWord ++ tailWord_7115741).sum := by decide
  have hdescent : baseEnd_7115741 < baseStart_7115741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115784 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_7115784 : Nat := 118140960795 + 7115784 * 2 ^ 59
def prefixEnd_7115784 : Nat := 4983230072969 + 3 ^ 40 * 7115784 * 2
def baseEnd_7115784 : Nat := 3653817425572892696075111

theorem tailTrace_7115784 : CollatzResearch.WordTrace tailWord_7115784 prefixEnd_7115784 3653817425572892696075111 := by
  unfold tailWord_7115784
  simp only [CollatzResearch.WordTrace]
  refine ⟨129766982026368660999497203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173022642701824881332662937 129766982026368660999497203)
  ·
    refine ⟨194650473039552991499245805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129766982026368660999497203 194650473039552991499245805)
    ·
      refine ⟨72993927389832371812217177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194650473039552991499245805 72993927389832371812217177)
      ·
        refine ⟨54745445542374278859162883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72993927389832371812217177 54745445542374278859162883)
        ·
          refine ⟨82118168313561418288744325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54745445542374278859162883 82118168313561418288744325)
          ·
            refine ⟨15397156558792765929139561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82118168313561418288744325 15397156558792765929139561)
            ·
              refine ⟨11547867419094574446854671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15397156558792765929139561 11547867419094574446854671)
              ·
                refine ⟨17321801128641861670282007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11547867419094574446854671 17321801128641861670282007)
                ·
                  refine ⟨25982701692962792505423011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17321801128641861670282007 25982701692962792505423011)
                  ·
                    refine ⟨38974052539444188758134517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25982701692962792505423011 38974052539444188758134517)
                    ·
                      refine ⟨3653817425572892696075111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38974052539444188758134517 3653817425572892696075111)
                      ·
                        rfl

theorem cell23_7115784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_7115784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115784 prefixEnd_7115784 := by exact prefixLift 7115784
  have htrace : WordTrace (prefixWord ++ tailWord_7115784) baseStart_7115784 baseEnd_7115784 := by
    simpa [prefixWord, tailWord_7115784, baseEnd_7115784] using wordTrace_append hprefix tailTrace_7115784
  have hstable : (prefixWord ++ tailWord_7115784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115784).length < 2 ^ (prefixWord ++ tailWord_7115784).sum := by decide
  have hdescent : baseEnd_7115784 < baseStart_7115784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115787 : List Nat := [1, 1, 1, 1, 6, 4, 9]
def baseStart_7115787 : Nat := 118140960795 + 7115787 * 2 ^ 59
def prefixEnd_7115787 : Nat := 4983230072969 + 3 ^ 40 * 7115787 * 2
def baseEnd_7115787 : Nat := 45108876123640199806637

theorem tailTrace_7115787 : CollatzResearch.WordTrace tailWord_7115787 prefixEnd_7115787 45108876123640199806637 := by
  unfold tailWord_7115787
  simp only [CollatzResearch.WordTrace]
  refine ⟨259534073471726453511353615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173022715647817635674235743 259534073471726453511353615)
  ·
    refine ⟨389301110207589680267030423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259534073471726453511353615 389301110207589680267030423)
    ·
      refine ⟨583951665311384520400545635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389301110207589680267030423 583951665311384520400545635)
      ·
        refine ⟨875927497967076780600818453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583951665311384520400545635 875927497967076780600818453)
        ·
          refine ⟨41059101467206724090663365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 875927497967076780600818453 41059101467206724090663365)
          ·
            refine ⟨7698581525101260766999381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41059101467206724090663365 7698581525101260766999381)
            ·
              refine ⟨45108876123640199806637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7698581525101260766999381 45108876123640199806637)
              ·
                rfl

theorem cell23_7115787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 9].length) (baseStart_7115787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115787 prefixEnd_7115787 := by exact prefixLift 7115787
  have htrace : WordTrace (prefixWord ++ tailWord_7115787) baseStart_7115787 baseEnd_7115787 := by
    simpa [prefixWord, tailWord_7115787, baseEnd_7115787] using wordTrace_append hprefix tailTrace_7115787
  have hstable : (prefixWord ++ tailWord_7115787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115787).length < 2 ^ (prefixWord ++ tailWord_7115787).sum := by decide
  have hdescent : baseEnd_7115787 < baseStart_7115787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115804 : List Nat := [2, 2, 3, 1, 4, 1, 2, 8]
def baseStart_7115804 : Nat := 118140960795 + 7115804 * 2 ^ 59
def prefixEnd_7115804 : Nat := 4983230072969 + 3 ^ 40 * 7115804 * 2
def baseEnd_7115804 : Nat := 135326951673554911771297

theorem tailTrace_7115804 : CollatzResearch.WordTrace tailWord_7115804 prefixEnd_7115804 135326951673554911771297 := by
  unfold tailWord_7115804
  simp only [CollatzResearch.WordTrace]
  refine ⟨129767346756332432707361233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173023129008443243609814977 129767346756332432707361233)
  ·
    refine ⟨97325510067249324530520925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129767346756332432707361233 97325510067249324530520925)
    ·
      refine ⟨36497066275218496698945347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97325510067249324530520925 36497066275218496698945347)
      ·
        refine ⟨54745599412827745048418021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36497066275218496698945347 54745599412827745048418021)
        ·
          refine ⟨10264799889905202196578379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54745599412827745048418021 10264799889905202196578379)
          ·
            refine ⟨15397199834857803294867569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10264799889905202196578379 15397199834857803294867569)
            ·
              refine ⟨11547899876143352471150677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15397199834857803294867569 11547899876143352471150677)
              ·
                refine ⟨135326951673554911771297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11547899876143352471150677 135326951673554911771297)
                ·
                  rfl

theorem cell23_7115804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 8].length) (baseStart_7115804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115804 prefixEnd_7115804 := by exact prefixLift 7115804
  have htrace : WordTrace (prefixWord ++ tailWord_7115804) baseStart_7115804 baseEnd_7115804 := by
    simpa [prefixWord, tailWord_7115804, baseEnd_7115804] using wordTrace_append hprefix tailTrace_7115804
  have hstable : (prefixWord ++ tailWord_7115804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115804).length < 2 ^ (prefixWord ++ tailWord_7115804).sum := by decide
  have hdescent : baseEnd_7115804 < baseStart_7115804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115808 : List Nat := [2, 1, 1, 7, 1, 1, 1, 3, 2, 4]
def baseStart_7115808 : Nat := 118140960795 + 7115808 * 2 ^ 59
def prefixEnd_7115808 : Nat := 4983230072969 + 3 ^ 40 * 7115808 * 2
def baseEnd_7115808 : Nat := 1217943249702866867391667

theorem tailTrace_7115808 : CollatzResearch.WordTrace tailWord_7115808 prefixEnd_7115808 1217943249702866867391667 := by
  unfold tailWord_7115808
  simp only [CollatzResearch.WordTrace]
  refine ⟨129767419702325187048934039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173023226269766916065245385 129767419702325187048934039)
  ·
    refine ⟨194651129553487780573401059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129767419702325187048934039 194651129553487780573401059)
    ·
      refine ⟨291976694330231670860101589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194651129553487780573401059 291976694330231670860101589)
      ·
        refine ⟨6843203773364804785783631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 291976694330231670860101589 6843203773364804785783631)
        ·
          refine ⟨10264805660047207178675447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6843203773364804785783631 10264805660047207178675447)
          ·
            refine ⟨15397208490070810768013171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10264805660047207178675447 15397208490070810768013171)
            ·
              refine ⟨23095812735106216152019757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15397208490070810768013171 23095812735106216152019757)
              ·
                refine ⟨8660929775664831057007409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23095812735106216152019757 8660929775664831057007409)
                ·
                  refine ⟨6495697331748623292755557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8660929775664831057007409 6495697331748623292755557)
                  ·
                    refine ⟨1217943249702866867391667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6495697331748623292755557 1217943249702866867391667)
                    ·
                      rfl

theorem cell23_7115808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 2, 4].length) (baseStart_7115808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115808 prefixEnd_7115808 := by exact prefixLift 7115808
  have htrace : WordTrace (prefixWord ++ tailWord_7115808) baseStart_7115808 baseEnd_7115808 := by
    simpa [prefixWord, tailWord_7115808, baseEnd_7115808] using wordTrace_append hprefix tailTrace_7115808
  have hstable : (prefixWord ++ tailWord_7115808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115808).length < 2 ^ (prefixWord ++ tailWord_7115808).sum := by decide
  have hdescent : baseEnd_7115808 < baseStart_7115808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115857 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_7115857 : Nat := 118140960795 + 7115857 * 2 ^ 59
def prefixEnd_7115857 : Nat := 4983230072969 + 3 ^ 40 * 7115857 * 2
def baseEnd_7115857 : Nat := 3653854909660670910462275

theorem tailTrace_7115857 : CollatzResearch.WordTrace tailWord_7115857 prefixEnd_7115857 3653854909660670910462275 := by
  unfold tailWord_7115857
  simp only [CollatzResearch.WordTrace]
  refine ⟨259536626581472855466401825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173024417720981903644267883 259536626581472855466401825)
  ·
    refine ⟨194652469936104641599801369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259536626581472855466401825 194652469936104641599801369)
    ·
      refine ⟨145989352452078481199851027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194652469936104641599801369 145989352452078481199851027)
      ·
        refine ⟨218984028678117721799776541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145989352452078481199851027 218984028678117721799776541)
        ·
          refine ⟨82119010754294145674916203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218984028678117721799776541 82119010754294145674916203)
          ·
            refine ⟨123178516131441218512374305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82119010754294145674916203 123178516131441218512374305)
            ·
              refine ⟨92383887098580913884280729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123178516131441218512374305 92383887098580913884280729)
              ·
                refine ⟨69287915323935685413210547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92383887098580913884280729 69287915323935685413210547)
                ·
                  refine ⟨103931872985903528119815821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69287915323935685413210547 103931872985903528119815821)
                  ·
                    refine ⟨38974452369713823044930933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103931872985903528119815821 38974452369713823044930933)
                    ·
                      refine ⟨3653854909660670910462275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38974452369713823044930933 3653854909660670910462275)
                      ·
                        rfl

theorem cell23_7115857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_7115857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115857 prefixEnd_7115857 := by exact prefixLift 7115857
  have htrace : WordTrace (prefixWord ++ tailWord_7115857) baseStart_7115857 baseEnd_7115857 := by
    simpa [prefixWord, tailWord_7115857, baseEnd_7115857] using wordTrace_append hprefix tailTrace_7115857
  have hstable : (prefixWord ++ tailWord_7115857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115857).length < 2 ^ (prefixWord ++ tailWord_7115857).sum := by decide
  have hdescent : baseEnd_7115857 < baseStart_7115857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115871 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 1, 4, 2]
def baseStart_7115871 : Nat := 118140960795 + 7115871 * 2 ^ 59
def prefixEnd_7115871 : Nat := 4983230072969 + 3 ^ 40 * 7115871 * 2
def baseEnd_7115871 : Nat := 3653862098389833855687211

theorem tailTrace_7115871 : CollatzResearch.WordTrace tailWord_7115871 prefixEnd_7115871 3653862098389833855687211 := by
  unfold tailWord_7115871
  simp only [CollatzResearch.WordTrace]
  refine ⟨259537137203422135857411467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173024758135614757238274311 259537137203422135857411467)
  ·
    refine ⟨389305705805133203786117201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259537137203422135857411467 389305705805133203786117201)
    ·
      refine ⟨291979279353849902839587901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389305705805133203786117201 291979279353849902839587901)
      ·
        refine ⟨109492229757693713564845463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291979279353849902839587901 109492229757693713564845463)
        ·
          refine ⟨164238344636540570347268195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109492229757693713564845463 164238344636540570347268195)
          ·
            refine ⟨246357516954810855520902293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164238344636540570347268195 246357516954810855520902293)
            ·
              refine ⟨11548008607256758852542295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 246357516954810855520902293 11548008607256758852542295)
              ·
                refine ⟨17322012910885138278813443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11548008607256758852542295 17322012910885138278813443)
                ·
                  refine ⟨25983019366327707418220165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17322012910885138278813443 25983019366327707418220165)
                  ·
                    refine ⟨4871816131186445140916281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25983019366327707418220165 4871816131186445140916281)
                    ·
                      refine ⟨3653862098389833855687211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871816131186445140916281 3653862098389833855687211)
                      ·
                        rfl

theorem cell23_7115871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_7115871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115871 prefixEnd_7115871 := by exact prefixLift 7115871
  have htrace : WordTrace (prefixWord ++ tailWord_7115871) baseStart_7115871 baseEnd_7115871 := by
    simpa [prefixWord, tailWord_7115871, baseEnd_7115871] using wordTrace_append hprefix tailTrace_7115871
  have hstable : (prefixWord ++ tailWord_7115871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115871).length < 2 ^ (prefixWord ++ tailWord_7115871).sum := by decide
  have hdescent : baseEnd_7115871 < baseStart_7115871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115894 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_7115894 : Nat := 118140960795 + 7115894 * 2 ^ 59
def prefixEnd_7115894 : Nat := 4983230072969 + 3 ^ 40 * 7115894 * 2
def baseEnd_7115894 : Nat := 405985989827209696188845

theorem tailTrace_7115894 : CollatzResearch.WordTrace tailWord_7115894 prefixEnd_7115894 405985989827209696188845 := by
  unfold tailWord_7115894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16221123505146175674093671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173025317388225873856999157 16221123505146175674093671)
  ·
    refine ⟨24331685257719263511140507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16221123505146175674093671 24331685257719263511140507)
    ·
      refine ⟨36497527886578895266710761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24331685257719263511140507 36497527886578895266710761)
      ·
        refine ⟨27373145914934171450033071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36497527886578895266710761 27373145914934171450033071)
        ·
          refine ⟨41059718872401257175049607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27373145914934171450033071 41059718872401257175049607)
          ·
            refine ⟨61589578308601885762574411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41059718872401257175049607 61589578308601885762574411)
            ·
              refine ⟨92384367462902828643861617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61589578308601885762574411 92384367462902828643861617)
              ·
                refine ⟨69288275597177121482896213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92384367462902828643861617 69288275597177121482896213)
                ·
                  refine ⟨405985989827209696188845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69288275597177121482896213 405985989827209696188845)
                  ·
                    rfl

theorem cell23_7115894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_7115894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115894 prefixEnd_7115894 := by exact prefixLift 7115894
  have htrace : WordTrace (prefixWord ++ tailWord_7115894) baseStart_7115894 baseEnd_7115894 := by
    simpa [prefixWord, tailWord_7115894, baseEnd_7115894] using wordTrace_append hprefix tailTrace_7115894
  have hstable : (prefixWord ++ tailWord_7115894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115894).length < 2 ^ (prefixWord ++ tailWord_7115894).sum := by decide
  have hdescent : baseEnd_7115894 < baseStart_7115894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115904 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 3]
def baseStart_7115904 : Nat := 118140960795 + 7115904 * 2 ^ 59
def prefixEnd_7115904 : Nat := 4983230072969 + 3 ^ 40 * 7115904 * 2
def baseEnd_7115904 : Nat := 3653879043251432226574559

theorem tailTrace_7115904 : CollatzResearch.WordTrace tailWord_7115904 prefixEnd_7115904 3653879043251432226574559 := by
  unfold tailWord_7115904
  simp only [CollatzResearch.WordTrace]
  refine ⟨129769170406151291246681383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173025560541535054995575177 129769170406151291246681383)
  ·
    refine ⟨194653755609226936870022075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129769170406151291246681383 194653755609226936870022075)
    ·
      refine ⟨291980633413840405305033113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194653755609226936870022075 291980633413840405305033113)
      ·
        refine ⟨218985475060380303978774835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291980633413840405305033113 218985475060380303978774835)
        ·
          refine ⟨328478212590570455968162253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218985475060380303978774835 328478212590570455968162253)
          ·
            refine ⟨123179329721463920988060845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328478212590570455968162253 123179329721463920988060845)
            ·
              refine ⟨46192248645548970370522817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123179329721463920988060845 46192248645548970370522817)
              ·
                refine ⟨34644186484161727777892113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46192248645548970370522817 34644186484161727777892113)
                ·
                  refine ⟨25983139863121295833419085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34644186484161727777892113 25983139863121295833419085)
                  ·
                    refine ⟨9743677448670485937532157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25983139863121295833419085 9743677448670485937532157)
                    ·
                      refine ⟨3653879043251432226574559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9743677448670485937532157 3653879043251432226574559)
                      ·
                        rfl

theorem cell23_7115904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_7115904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115904 prefixEnd_7115904 := by exact prefixLift 7115904
  have htrace : WordTrace (prefixWord ++ tailWord_7115904) baseStart_7115904 baseEnd_7115904 := by
    simpa [prefixWord, tailWord_7115904, baseEnd_7115904] using wordTrace_append hprefix tailTrace_7115904
  have hstable : (prefixWord ++ tailWord_7115904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115904).length < 2 ^ (prefixWord ++ tailWord_7115904).sum := by decide
  have hdescent : baseEnd_7115904 < baseStart_7115904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115905 : List Nat := [1, 2, 4, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_7115905 : Nat := 118140960795 + 7115905 * 2 ^ 59
def prefixEnd_7115905 : Nat := 4983230072969 + 3 ^ 40 * 7115905 * 2
def baseEnd_7115905 : Nat := 3653879556732086722662055

theorem tailTrace_7115905 : CollatzResearch.WordTrace tailWord_7115905 prefixEnd_7115905 3653879556732086722662055 := by
  unfold tailWord_7115905
  simp only [CollatzResearch.WordTrace]
  refine ⟨259538377285298959664149169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173025584856865973109432779 259538377285298959664149169)
  ·
    refine ⟨194653782963974219748111877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259538377285298959664149169 194653782963974219748111877)
    ·
      refine ⟨36497584305745166202770977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194653782963974219748111877 36497584305745166202770977)
      ·
        refine ⟨27373188229308874652078233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36497584305745166202770977 27373188229308874652078233)
        ·
          refine ⟨20529891171981655989058675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27373188229308874652078233 20529891171981655989058675)
          ·
            refine ⟨30794836757972483983588013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20529891171981655989058675 30794836757972483983588013)
            ·
              refine ⟨11548063784239681493845505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30794836757972483983588013 11548063784239681493845505)
              ·
                refine ⟨8661047838179761120384129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11548063784239681493845505 8661047838179761120384129)
                ·
                  refine ⟨6495785878634820840288097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8661047838179761120384129 6495785878634820840288097)
                  ·
                    refine ⟨4871839408976115630216073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6495785878634820840288097 4871839408976115630216073)
                    ·
                      refine ⟨3653879556732086722662055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871839408976115630216073 3653879556732086722662055)
                      ·
                        rfl

theorem cell23_7115905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_7115905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115905 prefixEnd_7115905 := by exact prefixLift 7115905
  have htrace : WordTrace (prefixWord ++ tailWord_7115905) baseStart_7115905 baseEnd_7115905 := by
    simpa [prefixWord, tailWord_7115905, baseEnd_7115905] using wordTrace_append hprefix tailTrace_7115905
  have hstable : (prefixWord ++ tailWord_7115905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115905).length < 2 ^ (prefixWord ++ tailWord_7115905).sum := by decide
  have hdescent : baseEnd_7115905 < baseStart_7115905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115922 : List Nat := [3, 2, 3, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_7115922 : Nat := 118140960795 + 7115922 * 2 ^ 59
def prefixEnd_7115922 : Nat := 4983230072969 + 3 ^ 40 * 7115922 * 2
def baseEnd_7115922 : Nat := 3653888285903213156149477

theorem tailTrace_7115922 : CollatzResearch.WordTrace tailWord_7115922 prefixEnd_7115922 3653888285903213156149477 := by
  unfold tailWord_7115922
  simp only [CollatzResearch.WordTrace]
  refine ⟨64884749331559342891879505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173025998217491581045012013 64884749331559342891879505)
  ·
    refine ⟨48663561998669507168909629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64884749331559342891879505 48663561998669507168909629)
    ·
      refine ⟨18248835749501065188341111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48663561998669507168909629 18248835749501065188341111)
      ·
        refine ⟨27373253624251597782511667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18248835749501065188341111 27373253624251597782511667)
        ·
          refine ⟨41059880436377396673767501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27373253624251597782511667 41059880436377396673767501)
          ·
            refine ⟨15397455163641523752662813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41059880436377396673767501 15397455163641523752662813)
            ·
              refine ⟨5774045686365571407248555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15397455163641523752662813 5774045686365571407248555)
              ·
                refine ⟨8661068529548357110872833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5774045686365571407248555 8661068529548357110872833)
                ·
                  refine ⟨6495801397161267833154625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8661068529548357110872833 6495801397161267833154625)
                  ·
                    refine ⟨4871851047870950874865969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6495801397161267833154625 4871851047870950874865969)
                    ·
                      refine ⟨3653888285903213156149477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871851047870950874865969 3653888285903213156149477)
                      ·
                        rfl

theorem cell23_7115922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_7115922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115922 prefixEnd_7115922 := by exact prefixLift 7115922
  have htrace : WordTrace (prefixWord ++ tailWord_7115922) baseStart_7115922 baseEnd_7115922 := by
    simpa [prefixWord, tailWord_7115922, baseEnd_7115922] using wordTrace_append hprefix tailTrace_7115922
  have hstable : (prefixWord ++ tailWord_7115922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115922).length < 2 ^ (prefixWord ++ tailWord_7115922).sum := by decide
  have hdescent : baseEnd_7115922 < baseStart_7115922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7115961 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 2, 1, 4]
def baseStart_7115961 : Nat := 118140960795 + 7115961 * 2 ^ 59
def prefixEnd_7115961 : Nat := 4983230072969 + 3 ^ 40 * 7115961 * 2
def baseEnd_7115961 : Nat := 3653908311648738503561797

theorem tailTrace_7115961 : CollatzResearch.WordTrace tailWord_7115961 prefixEnd_7115961 3653908311648738503561797 := by
  unfold tailWord_7115961
  simp only [CollatzResearch.WordTrace]
  refine ⟨259540419773096081228187737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173026946515397387485458491 259540419773096081228187737)
  ·
    refine ⟨194655314829822060921140803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259540419773096081228187737 194655314829822060921140803)
    ·
      refine ⟨291982972244733091381711205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194655314829822060921140803 291982972244733091381711205)
      ·
        refine ⟨54746807295887454634070851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291982972244733091381711205 54746807295887454634070851)
        ·
          refine ⟨82120210943831181951106277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54746807295887454634070851 82120210943831181951106277)
          ·
            refine ⟨15397539551968346615832427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82120210943831181951106277 15397539551968346615832427)
            ·
              refine ⟨23096309327952519923748641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15397539551968346615832427 23096309327952519923748641)
              ·
                refine ⟨17322231995964389942811481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23096309327952519923748641 17322231995964389942811481)
                ·
                  refine ⟨12991673996973292457108611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17322231995964389942811481 12991673996973292457108611)
                  ·
                    refine ⟨19487510995459938685662917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12991673996973292457108611 19487510995459938685662917)
                    ·
                      refine ⟨3653908311648738503561797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19487510995459938685662917 3653908311648738503561797)
                      ·
                        rfl

theorem cell23_7115961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_7115961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7115961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7115961 prefixEnd_7115961 := by exact prefixLift 7115961
  have htrace : WordTrace (prefixWord ++ tailWord_7115961) baseStart_7115961 baseEnd_7115961 := by
    simpa [prefixWord, tailWord_7115961, baseEnd_7115961] using wordTrace_append hprefix tailTrace_7115961
  have hstable : (prefixWord ++ tailWord_7115961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7115961).length < 2 ^ (prefixWord ++ tailWord_7115961).sum := by decide
  have hdescent : baseEnd_7115961 < baseStart_7115961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7115961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116018 : List Nat := [3, 2, 1, 3, 3, 1, 2, 2, 6]
def baseStart_7116018 : Nat := 118140960795 + 7116018 * 2 ^ 59
def prefixEnd_7116018 : Nat := 4983230072969 + 3 ^ 40 * 7116018 * 2
def baseEnd_7116018 : Nat := 405993064449560531172115

theorem tailTrace_7116018 : CollatzResearch.WordTrace tailWord_7116018 prefixEnd_7116018 405993064449560531172115 := by
  unfold tailWord_7116018
  simp only [CollatzResearch.WordTrace]
  refine ⟨64885624683472394990753177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173028332489259719975341805 64885624683472394990753177)
  ·
    refine ⟨48664218512604296243064883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64885624683472394990753177 48664218512604296243064883)
    ·
      refine ⟨72996327768906444364597325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48664218512604296243064883 72996327768906444364597325)
      ·
        refine ⟨27373622913339916636723997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72996327768906444364597325 27373622913339916636723997)
        ·
          refine ⟨10265108592502468738771499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27373622913339916636723997 10265108592502468738771499)
          ·
            refine ⟨15397662888753703108157249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10265108592502468738771499 15397662888753703108157249)
            ·
              refine ⟨11548247166565277331117937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15397662888753703108157249 11548247166565277331117937)
              ·
                refine ⟨8661185374923957998338453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11548247166565277331117937 8661185374923957998338453)
                ·
                  refine ⟨405993064449560531172115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8661185374923957998338453 405993064449560531172115)
                  ·
                    rfl

theorem cell23_7116018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_7116018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116018 prefixEnd_7116018 := by exact prefixLift 7116018
  have htrace : WordTrace (prefixWord ++ tailWord_7116018) baseStart_7116018 baseEnd_7116018 := by
    simpa [prefixWord, tailWord_7116018, baseEnd_7116018] using wordTrace_append hprefix tailTrace_7116018
  have hstable : (prefixWord ++ tailWord_7116018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116018).length < 2 ^ (prefixWord ++ tailWord_7116018).sum := by decide
  have hdescent : baseEnd_7116018 < baseStart_7116018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116068 : List Nat := [2, 3, 1, 3, 1, 1, 3, 3, 1, 1, 4]
def baseStart_7116068 : Nat := 118140960795 + 7116068 * 2 ^ 59
def prefixEnd_7116068 : Nat := 4983230072969 + 3 ^ 40 * 7116068 * 2
def baseEnd_7116068 : Nat := 3653963254078769584923805

theorem tailTrace_7116068 : CollatzResearch.WordTrace tailWord_7116068 prefixEnd_7116068 3653963254078769584923805 := by
  unfold tailWord_7116068
  simp only [CollatzResearch.WordTrace]
  refine ⟨129772161191854219251166429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173029548255805625668221905 129772161191854219251166429)
  ·
    refine ⟨48664560446945332219187411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129772161191854219251166429 48664560446945332219187411)
    ·
      refine ⟨72996840670417998328781117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48664560446945332219187411 72996840670417998328781117)
      ·
        refine ⟨27373815251406749373292919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72996840670417998328781117 27373815251406749373292919)
        ·
          refine ⟨41060722877110124059939379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27373815251406749373292919 41060722877110124059939379)
          ·
            refine ⟨61591084315665186089909069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41060722877110124059939379 61591084315665186089909069)
            ·
              refine ⟨23096656618374444783715901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61591084315665186089909069 23096656618374444783715901)
              ·
                refine ⟨8661246231890416793893463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23096656618374444783715901 8661246231890416793893463)
                ·
                  refine ⟨12991869347835625190840195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8661246231890416793893463 12991869347835625190840195)
                  ·
                    refine ⟨19487804021753437786260293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12991869347835625190840195 19487804021753437786260293)
                    ·
                      refine ⟨3653963254078769584923805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19487804021753437786260293 3653963254078769584923805)
                      ·
                        rfl

theorem cell23_7116068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_7116068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116068 prefixEnd_7116068 := by exact prefixLift 7116068
  have htrace : WordTrace (prefixWord ++ tailWord_7116068) baseStart_7116068 baseEnd_7116068 := by
    simpa [prefixWord, tailWord_7116068, baseEnd_7116068] using wordTrace_append hprefix tailTrace_7116068
  have hstable : (prefixWord ++ tailWord_7116068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116068).length < 2 ^ (prefixWord ++ tailWord_7116068).sum := by decide
  have hdescent : baseEnd_7116068 < baseStart_7116068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116085 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_7116085 : Nat := 118140960795 + 7116085 * 2 ^ 59
def prefixEnd_7116085 : Nat := 4983230072969 + 3 ^ 40 * 7116085 * 2
def baseEnd_7116085 : Nat := 3653971983249896018411227

theorem tailTrace_7116085 : CollatzResearch.WordTrace tailWord_7116085 prefixEnd_7116085 3653971983249896018411227 := by
  unfold tailWord_7116085
  simp only [CollatzResearch.WordTrace]
  refine ⟨259544942424646850405701709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173029961616431233603801139 259544942424646850405701709)
  ·
    refine ⟨97329353409242568902138141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259544942424646850405701709 97329353409242568902138141)
    ·
      refine ⟨36498507528465963338301803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97329353409242568902138141 36498507528465963338301803)
      ·
        refine ⟨54747761292698945007452705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36498507528465963338301803 54747761292698945007452705)
        ·
          refine ⟨41060820969524208755589529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54747761292698945007452705 41060820969524208755589529)
          ·
            refine ⟨30795615727143156566692147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41060820969524208755589529 30795615727143156566692147)
            ·
              refine ⟨46193423590714734850038221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30795615727143156566692147 46193423590714734850038221)
              ·
                refine ⟨17322533846518025568764333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46193423590714734850038221 17322533846518025568764333)
                ·
                  refine ⟨6495950192444259588286625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17322533846518025568764333 6495950192444259588286625)
                  ·
                    refine ⟨4871962644333194691214969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6495950192444259588286625 4871962644333194691214969)
                    ·
                      refine ⟨3653971983249896018411227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871962644333194691214969 3653971983249896018411227)
                      ·
                        rfl

theorem cell23_7116085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_7116085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116085 prefixEnd_7116085 := by exact prefixLift 7116085
  have htrace : WordTrace (prefixWord ++ tailWord_7116085) baseStart_7116085 baseEnd_7116085 := by
    simpa [prefixWord, tailWord_7116085, baseEnd_7116085] using wordTrace_append hprefix tailTrace_7116085
  have hstable : (prefixWord ++ tailWord_7116085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116085).length < 2 ^ (prefixWord ++ tailWord_7116085).sum := by decide
  have hdescent : baseEnd_7116085 < baseStart_7116085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116095 : List Nat := [1, 1, 2, 2, 4, 3, 3, 1, 2, 4]
def baseStart_7116095 : Nat := 118140960795 + 7116095 * 2 ^ 59
def prefixEnd_7116095 : Nat := 4983230072969 + 3 ^ 40 * 7116095 * 2
def baseEnd_7116095 : Nat := 1217992372685480326428727

theorem tailTrace_7116095 : CollatzResearch.WordTrace tailWord_7116095 prefixEnd_7116095 1217992372685480326428727 := by
  unfold tailWord_7116095
  simp only [CollatzResearch.WordTrace]
  refine ⟨259545307154610622113565739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173030204769740414742377159 259545307154610622113565739)
  ·
    refine ⟨389317960731915933170348609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259545307154610622113565739 389317960731915933170348609)
    ·
      refine ⟨291988470548936949877761457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389317960731915933170348609 291988470548936949877761457)
      ·
        refine ⟨218991352911702712408321093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291988470548936949877761457 218991352911702712408321093)
        ·
          refine ⟨41060878670944258576560205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218991352911702712408321093 41060878670944258576560205)
          ·
            refine ⟨15397829501604096966210077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41060878670944258576560205 15397829501604096966210077)
            ·
              refine ⟨5774186063101536362328779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15397829501604096966210077 5774186063101536362328779)
              ·
                refine ⟨8661279094652304543493169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5774186063101536362328779 8661279094652304543493169)
                ·
                  refine ⟨6495959320989228407619877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8661279094652304543493169 6495959320989228407619877)
                  ·
                    refine ⟨1217992372685480326428727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6495959320989228407619877 1217992372685480326428727)
                    ·
                      rfl

theorem cell23_7116095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 2, 4].length) (baseStart_7116095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116095 prefixEnd_7116095 := by exact prefixLift 7116095
  have htrace : WordTrace (prefixWord ++ tailWord_7116095) baseStart_7116095 baseEnd_7116095 := by
    simpa [prefixWord, tailWord_7116095, baseEnd_7116095] using wordTrace_append hprefix tailTrace_7116095
  have hstable : (prefixWord ++ tailWord_7116095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116095).length < 2 ^ (prefixWord ++ tailWord_7116095).sum := by decide
  have hdescent : baseEnd_7116095 < baseStart_7116095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116108 : List Nat := [2, 2, 1, 3, 2, 4, 2, 7]
def baseStart_7116108 : Nat := 118140960795 + 7116108 * 2 ^ 59
def prefixEnd_7116108 : Nat := 4983230072969 + 3 ^ 40 * 7116108 * 2
def baseEnd_7116108 : Nat := 135332733085368497349023

theorem tailTrace_7116108 : CollatzResearch.WordTrace tailWord_7116108 prefixEnd_7116108 135332733085368497349023 := by
  unfold tailWord_7116108
  simp only [CollatzResearch.WordTrace]
  refine ⟨129772890651781762666894489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173030520869042350222525985 129772890651781762666894489)
  ·
    refine ⟨97329667988836322000170867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129772890651781762666894489 97329667988836322000170867)
    ·
      refine ⟨145994501983254483000256301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97329667988836322000170867 145994501983254483000256301)
      ·
        refine ⟨54747938243720431125096113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145994501983254483000256301 54747938243720431125096113)
        ·
          refine ⟨41060953682790323343822085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54747938243720431125096113 41060953682790323343822085)
          ·
            refine ⟨7698928815523185626966641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41060953682790323343822085 7698928815523185626966641)
            ·
              refine ⟨5774196611642389220224981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7698928815523185626966641 5774196611642389220224981)
              ·
                refine ⟨135332733085368497349023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5774196611642389220224981 135332733085368497349023)
                ·
                  rfl

theorem cell23_7116108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 7].length) (baseStart_7116108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116108 prefixEnd_7116108 := by exact prefixLift 7116108
  have htrace : WordTrace (prefixWord ++ tailWord_7116108) baseStart_7116108 baseEnd_7116108 := by
    simpa [prefixWord, tailWord_7116108, baseEnd_7116108] using wordTrace_append hprefix tailTrace_7116108
  have hstable : (prefixWord ++ tailWord_7116108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116108).length < 2 ^ (prefixWord ++ tailWord_7116108).sum := by decide
  have hdescent : baseEnd_7116108 < baseStart_7116108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116119 : List Nat := [1, 1, 3, 2, 3, 4, 1, 3, 1, 2, 2]
def baseStart_7116119 : Nat := 118140960795 + 7116119 * 2 ^ 59
def prefixEnd_7116119 : Nat := 4983230072969 + 3 ^ 40 * 7116119 * 2
def baseEnd_7116119 : Nat := 3653989441592148885386071

theorem tailTrace_7116119 : CollatzResearch.WordTrace tailWord_7116119 prefixEnd_7116119 3653989441592148885386071 := by
  unfold tailWord_7116119
  simp only [CollatzResearch.WordTrace]
  refine ⟨259546182506523674212439411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173030788337682449474959607 259546182506523674212439411)
  ·
    refine ⟨389319273759785511318659117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259546182506523674212439411 389319273759785511318659117)
    ·
      refine ⟨145994727659919566744497169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389319273759785511318659117 145994727659919566744497169)
      ·
        refine ⟨109496045744939675058372877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145994727659919566744497169 109496045744939675058372877)
        ·
          refine ⟨41061017154352378146889829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109496045744939675058372877 41061017154352378146889829)
          ·
            refine ⟨7698940716441070902541843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41061017154352378146889829 7698940716441070902541843)
            ·
              refine ⟨11548411074661606353812765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7698940716441070902541843 11548411074661606353812765)
              ·
                refine ⟨4330654152998102382679787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11548411074661606353812765 4330654152998102382679787)
                ·
                  refine ⟨6495981229497153574019681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4330654152998102382679787 6495981229497153574019681)
                  ·
                    refine ⟨4871985922122865180514761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6495981229497153574019681 4871985922122865180514761)
                    ·
                      refine ⟨3653989441592148885386071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871985922122865180514761 3653989441592148885386071)
                      ·
                        rfl

theorem cell23_7116119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_7116119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116119 prefixEnd_7116119 := by exact prefixLift 7116119
  have htrace : WordTrace (prefixWord ++ tailWord_7116119) baseStart_7116119 baseEnd_7116119 := by
    simpa [prefixWord, tailWord_7116119, baseEnd_7116119] using wordTrace_append hprefix tailTrace_7116119
  have hstable : (prefixWord ++ tailWord_7116119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116119).length < 2 ^ (prefixWord ++ tailWord_7116119).sum := by decide
  have hdescent : baseEnd_7116119 < baseStart_7116119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116136 : List Nat := [2, 1, 4, 2, 3, 1, 3, 2, 1, 2, 2]
def baseStart_7116136 : Nat := 118140960795 + 7116136 * 2 ^ 59
def prefixEnd_7116136 : Nat := 4983230072969 + 3 ^ 40 * 7116136 * 2
def baseEnd_7116136 : Nat := 3653998170763275318873493

theorem tailTrace_7116136 : CollatzResearch.WordTrace tailWord_7116136 prefixEnd_7116136 3653998170763275318873493 := by
  unfold tailWord_7116136
  simp only [CollatzResearch.WordTrace]
  refine ⟨129773401273731043057904131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173031201698308057410538841 129773401273731043057904131)
  ·
    refine ⟨194660101910596564586856197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129773401273731043057904131 194660101910596564586856197)
    ·
      refine ⟨36498769108236855860035537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194660101910596564586856197 36498769108236855860035537)
      ·
        refine ⟨27374076831177641895026653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36498769108236855860035537 27374076831177641895026653)
        ·
          refine ⟨10265278811691615710634995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27374076831177641895026653 10265278811691615710634995)
          ·
            refine ⟨15397918217537423565952493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10265278811691615710634995 15397918217537423565952493)
            ·
              refine ⟨5774219331576533837232185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15397918217537423565952493 5774219331576533837232185)
              ·
                refine ⟨4330664498682400377924139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5774219331576533837232185 4330664498682400377924139)
                ·
                  refine ⟨6495996748023600566886209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4330664498682400377924139 6495996748023600566886209)
                  ·
                    refine ⟨4871997561017700425164657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6495996748023600566886209 4871997561017700425164657)
                    ·
                      refine ⟨3653998170763275318873493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4871997561017700425164657 3653998170763275318873493)
                      ·
                        rfl

theorem cell23_7116136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_7116136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116136 prefixEnd_7116136 := by exact prefixLift 7116136
  have htrace : WordTrace (prefixWord ++ tailWord_7116136) baseStart_7116136 baseEnd_7116136 := by
    simpa [prefixWord, tailWord_7116136, baseEnd_7116136] using wordTrace_append hprefix tailTrace_7116136
  have hstable : (prefixWord ++ tailWord_7116136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116136).length < 2 ^ (prefixWord ++ tailWord_7116136).sum := by decide
  have hdescent : baseEnd_7116136 < baseStart_7116136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116192 : List Nat := [2, 1, 1, 4, 1, 2, 4, 2, 2, 2, 2]
def baseStart_7116192 : Nat := 118140960795 + 7116192 * 2 ^ 59
def prefixEnd_7116192 : Nat := 4983230072969 + 3 ^ 40 * 7116192 * 2
def baseEnd_7116192 : Nat := 3654026925679927099773235

theorem tailTrace_7116192 : CollatzResearch.WordTrace tailWord_7116192 prefixEnd_7116192 3654026925679927099773235 := by
  unfold tailWord_7116192
  simp only [CollatzResearch.WordTrace]
  refine ⟨129774422517629603839923415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173032563356839471786564553 129774422517629603839923415)
  ·
    refine ⟨194661633776444405759885123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129774422517629603839923415 194661633776444405759885123)
    ·
      refine ⟨291992450664666608639827685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194661633776444405759885123 291992450664666608639827685)
      ·
        refine ⟨54748584499624989119967691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291992450664666608639827685 54748584499624989119967691)
        ·
          refine ⟨82122876749437483679951537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54748584499624989119967691 82122876749437483679951537)
          ·
            refine ⟨61592157562078112759963653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82122876749437483679951537 61592157562078112759963653)
            ·
              refine ⟨11548529542889646142493185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61592157562078112759963653 11548529542889646142493185)
              ·
                refine ⟨8661397157167234606869889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11548529542889646142493185 8661397157167234606869889)
                ·
                  refine ⟨6496047867875425955152417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8661397157167234606869889 6496047867875425955152417)
                  ·
                    refine ⟨4872035900906569466364313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6496047867875425955152417 4872035900906569466364313)
                    ·
                      refine ⟨3654026925679927099773235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872035900906569466364313 3654026925679927099773235)
                      ·
                        rfl

theorem cell23_7116192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_7116192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116192 prefixEnd_7116192 := by exact prefixLift 7116192
  have htrace : WordTrace (prefixWord ++ tailWord_7116192) baseStart_7116192 baseEnd_7116192 := by
    simpa [prefixWord, tailWord_7116192, baseEnd_7116192] using wordTrace_append hprefix tailTrace_7116192
  have hstable : (prefixWord ++ tailWord_7116192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116192).length < 2 ^ (prefixWord ++ tailWord_7116192).sum := by decide
  have hdescent : baseEnd_7116192 < baseStart_7116192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116205 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_7116205 : Nat := 118140960795 + 7116205 * 2 ^ 59
def prefixEnd_7116205 : Nat := 4983230072969 + 3 ^ 40 * 7116205 * 2
def baseEnd_7116205 : Nat := 3654033600928435548910675

theorem tailTrace_7116205 : CollatzResearch.WordTrace tailWord_7116205 prefixEnd_7116205 3654033600928435548910675 := by
  unfold tailWord_7116205
  simp only [CollatzResearch.WordTrace]
  refine ⟨259549319184212110900070069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173032879456141407266713379 259549319184212110900070069)
  ·
    refine ⟨24332748673519885396881569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259549319184212110900070069 24332748673519885396881569)
    ·
      refine ⟨18249561505139914047661177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24332748673519885396881569 18249561505139914047661177)
      ·
        refine ⟨13687171128854935535745883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18249561505139914047661177 13687171128854935535745883)
        ·
          refine ⟨20530756693282403303618825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13687171128854935535745883 20530756693282403303618825)
          ·
            refine ⟨15398067519961802477714119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20530756693282403303618825 15398067519961802477714119)
            ·
              refine ⟨23097101279942703716571179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15398067519961802477714119 23097101279942703716571179)
              ·
                refine ⟨34645651919914055574856769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23097101279942703716571179 34645651919914055574856769)
                ·
                  refine ⟨25984238939935541681142577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34645651919914055574856769 25984238939935541681142577)
                  ·
                    refine ⟨19488179204951656260856933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25984238939935541681142577 19488179204951656260856933)
                    ·
                      refine ⟨3654033600928435548910675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19488179204951656260856933 3654033600928435548910675)
                      ·
                        rfl

theorem cell23_7116205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_7116205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116205 prefixEnd_7116205 := by exact prefixLift 7116205
  have htrace : WordTrace (prefixWord ++ tailWord_7116205) baseStart_7116205 baseEnd_7116205 := by
    simpa [prefixWord, tailWord_7116205, baseEnd_7116205] using wordTrace_append hprefix tailTrace_7116205
  have hstable : (prefixWord ++ tailWord_7116205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116205).length < 2 ^ (prefixWord ++ tailWord_7116205).sum := by decide
  have hdescent : baseEnd_7116205 < baseStart_7116205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116211 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 4, 5]
def baseStart_7116211 : Nat := 118140960795 + 7116211 * 2 ^ 59
def prefixEnd_7116211 : Nat := 4983230072969 + 3 ^ 40 * 7116211 * 2
def baseEnd_7116211 : Nat := 1218012227270787508478549

theorem tailTrace_7116211 : CollatzResearch.WordTrace tailWord_7116211 prefixEnd_7116211 1218012227270787508478549 := by
  unfold tailWord_7116211
  simp only [CollatzResearch.WordTrace]
  refine ⟨259549538022190373924788487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173033025348126915949858991 259549538022190373924788487)
  ·
    refine ⟨389324307033285560887182731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259549538022190373924788487 389324307033285560887182731)
    ·
      refine ⟨583986460549928341330774097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389324307033285560887182731 583986460549928341330774097)
      ·
        refine ⟨437989845412446255998080573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583986460549928341330774097 437989845412446255998080573)
        ·
          refine ⟨164246192029667345999280215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437989845412446255998080573 164246192029667345999280215)
          ·
            refine ⟨246369288044501018998920323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164246192029667345999280215 246369288044501018998920323)
            ·
              refine ⟨369553932066751528498380485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246369288044501018998920323 369553932066751528498380485)
              ·
                refine ⟨69291362262515911593446341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369553932066751528498380485 69291362262515911593446341)
                ·
                  refine ⟨12992130424221733423771189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69291362262515911593446341 12992130424221733423771189)
                  ·
                    refine ⟨1218012227270787508478549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12992130424221733423771189 1218012227270787508478549)
                    ·
                      rfl

theorem cell23_7116211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 5].length) (baseStart_7116211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116211 prefixEnd_7116211 := by exact prefixLift 7116211
  have htrace : WordTrace (prefixWord ++ tailWord_7116211) baseStart_7116211 baseEnd_7116211 := by
    simpa [prefixWord, tailWord_7116211, baseEnd_7116211] using wordTrace_append hprefix tailTrace_7116211
  have hstable : (prefixWord ++ tailWord_7116211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116211).length < 2 ^ (prefixWord ++ tailWord_7116211).sum := by decide
  have hdescent : baseEnd_7116211 < baseStart_7116211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116248 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 2, 1, 4]
def baseStart_7116248 : Nat := 118140960795 + 7116248 * 2 ^ 59
def prefixEnd_7116248 : Nat := 4983230072969 + 3 ^ 40 * 7116248 * 2
def baseEnd_7116248 : Nat := 3654055680596578880672977

theorem tailTrace_7116248 : CollatzResearch.WordTrace tailWord_7116248 prefixEnd_7116248 3654055680596578880672977 := by
  unfold tailWord_7116248
  simp only [CollatzResearch.WordTrace]
  refine ⟨129775443761528164621942699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173033925015370886162590265 129775443761528164621942699)
  ·
    refine ⟨194663165642292246932914049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129775443761528164621942699 194663165642292246932914049)
    ·
      refine ⟨145997374231719185199685537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194663165642292246932914049 145997374231719185199685537)
      ·
        refine ⟨109498030673789388899764153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145997374231719185199685537 109498030673789388899764153)
        ·
          refine ⟨82123523005342041674823115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109498030673789388899764153 82123523005342041674823115)
          ·
            refine ⟨123185284508013062512234673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82123523005342041674823115 123185284508013062512234673)
            ·
              refine ⟨92388963381009796884176005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123185284508013062512234673 92388963381009796884176005)
              ·
                refine ⟨17322930633939336915783001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92388963381009796884176005 17322930633939336915783001)
                ·
                  refine ⟨12992197975454502686837251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17322930633939336915783001 12992197975454502686837251)
                  ·
                    refine ⟨19488296963181754030255877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12992197975454502686837251 19488296963181754030255877)
                    ·
                      refine ⟨3654055680596578880672977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19488296963181754030255877 3654055680596578880672977)
                      ·
                        rfl

theorem cell23_7116248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_7116248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116248 prefixEnd_7116248 := by exact prefixLift 7116248
  have htrace : WordTrace (prefixWord ++ tailWord_7116248) baseStart_7116248 baseEnd_7116248 := by
    simpa [prefixWord, tailWord_7116248, baseEnd_7116248] using wordTrace_append hprefix tailTrace_7116248
  have hstable : (prefixWord ++ tailWord_7116248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116248).length < 2 ^ (prefixWord ++ tailWord_7116248).sum := by decide
  have hdescent : baseEnd_7116248 < baseStart_7116248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116268 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 3]
def baseStart_7116268 : Nat := 118140960795 + 7116268 * 2 ^ 59
def prefixEnd_7116268 : Nat := 4983230072969 + 3 ^ 40 * 7116268 * 2
def baseEnd_7116268 : Nat := 3654065950209668802422885

theorem tailTrace_7116268 : CollatzResearch.WordTrace tailWord_7116268 prefixEnd_7116268 3654065950209668802422885 := by
  unfold tailWord_7116268
  simp only [CollatzResearch.WordTrace]
  refine ⟨129775808491491936329806729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173034411321989248439742305 129775808491491936329806729)
  ·
    refine ⟨97331856368618952247355047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129775808491491936329806729 97331856368618952247355047)
    ·
      refine ⟨145997784552928428371032571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97331856368618952247355047 145997784552928428371032571)
      ·
        refine ⟨218996676829392642556548857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145997784552928428371032571 218996676829392642556548857)
        ·
          refine ⟨164247507622044481917411643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218996676829392642556548857 164247507622044481917411643)
          ·
            refine ⟨246371261433066722876117465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164247507622044481917411643 246371261433066722876117465)
            ·
              refine ⟨184778446074800042157088099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246371261433066722876117465 184778446074800042157088099)
              ·
                refine ⟨277167669112200063235632149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184778446074800042157088099 277167669112200063235632149)
                ·
                  refine ⟨12992234489634377964170257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 277167669112200063235632149 12992234489634377964170257)
                  ·
                    refine ⟨9744175867225783473127693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12992234489634377964170257 9744175867225783473127693)
                    ·
                      refine ⟨3654065950209668802422885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9744175867225783473127693 3654065950209668802422885)
                      ·
                        rfl

theorem cell23_7116268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_7116268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116268 prefixEnd_7116268 := by exact prefixLift 7116268
  have htrace : WordTrace (prefixWord ++ tailWord_7116268) baseStart_7116268 baseEnd_7116268 := by
    simpa [prefixWord, tailWord_7116268, baseEnd_7116268] using wordTrace_append hprefix tailTrace_7116268
  have hstable : (prefixWord ++ tailWord_7116268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116268).length < 2 ^ (prefixWord ++ tailWord_7116268).sum := by decide
  have hdescent : baseEnd_7116268 < baseStart_7116268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116291 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 8]
def baseStart_7116291 : Nat := 118140960795 + 7116291 * 2 ^ 59
def prefixEnd_7116291 : Nat := 4983230072969 + 3 ^ 40 * 7116291 * 2
def baseEnd_7116291 : Nat := 3654077760264722212435279

theorem tailTrace_7116291 : CollatzResearch.WordTrace tailWord_7116291 prefixEnd_7116291 3654077760264722212435279 := by
  unfold tailWord_7116291
  simp only [CollatzResearch.WordTrace]
  refine ⟨259552455861900547587700727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173034970574600365058467151 259552455861900547587700727)
  ·
    refine ⟨389328683792850821381551091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259552455861900547587700727 389328683792850821381551091)
    ·
      refine ⟨583993025689276232072326637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389328683792850821381551091 583993025689276232072326637)
      ·
        refine ⟨218997384633478587027122489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 583993025689276232072326637 218997384633478587027122489)
        ·
          refine ⟨164248038475108940270341867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218997384633478587027122489 164248038475108940270341867)
          ·
            refine ⟨246372057712663410405512801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164248038475108940270341867 246372057712663410405512801)
            ·
              refine ⟨184779043284497557804134601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246372057712663410405512801 184779043284497557804134601)
              ·
                refine ⟨138584282463373168353100951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184779043284497557804134601 138584282463373168353100951)
                ·
                  refine ⟨207876423695059752529651427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138584282463373168353100951 207876423695059752529651427)
                  ·
                    refine ⟨311814635542589628794477141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207876423695059752529651427 311814635542589628794477141)
                    ·
                      refine ⟨3654077760264722212435279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 311814635542589628794477141 3654077760264722212435279)
                      ·
                        rfl

theorem cell23_7116291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_7116291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116291 prefixEnd_7116291 := by exact prefixLift 7116291
  have htrace : WordTrace (prefixWord ++ tailWord_7116291) baseStart_7116291 baseEnd_7116291 := by
    simpa [prefixWord, tailWord_7116291, baseEnd_7116291] using wordTrace_append hprefix tailTrace_7116291
  have hstable : (prefixWord ++ tailWord_7116291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116291).length < 2 ^ (prefixWord ++ tailWord_7116291).sum := by decide
  have hdescent : baseEnd_7116291 < baseStart_7116291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116302 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_7116302 : Nat := 118140960795 + 7116302 * 2 ^ 59
def prefixEnd_7116302 : Nat := 4983230072969 + 3 ^ 40 * 7116302 * 2
def baseEnd_7116302 : Nat := 3654083408551921669397729

theorem tailTrace_7116302 : CollatzResearch.WordTrace tailWord_7116302 prefixEnd_7116302 3654083408551921669397729 := by
  unfold tailWord_7116302
  simp only [CollatzResearch.WordTrace]
  refine ⟨32444107133107587058293895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173035238043240464310900773 32444107133107587058293895)
  ·
    refine ⟨48666160699661380587440843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32444107133107587058293895 48666160699661380587440843)
    ·
      refine ⟨72999241049492070881161265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48666160699661380587440843 72999241049492070881161265)
      ·
        refine ⟨54749430787119053160870949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72999241049492070881161265 54749430787119053160870949)
        ·
          refine ⟨10265518272584822467663303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54749430787119053160870949 10265518272584822467663303)
          ·
            refine ⟨15398277408877233701494955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10265518272584822467663303 15398277408877233701494955)
            ·
              refine ⟨23097416113315850552242433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15398277408877233701494955 23097416113315850552242433)
              ·
                refine ⟨17323062084986887914181825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23097416113315850552242433 17323062084986887914181825)
                ·
                  refine ⟨12992296563740165935636369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17323062084986887914181825 12992296563740165935636369)
                  ·
                    refine ⟨9744222422805124451727277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12992296563740165935636369 9744222422805124451727277)
                    ·
                      refine ⟨3654083408551921669397729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9744222422805124451727277 3654083408551921669397729)
                      ·
                        rfl

theorem cell23_7116302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_7116302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116302 prefixEnd_7116302 := by exact prefixLift 7116302
  have htrace : WordTrace (prefixWord ++ tailWord_7116302) baseStart_7116302 baseEnd_7116302 := by
    simpa [prefixWord, tailWord_7116302, baseEnd_7116302] using wordTrace_append hprefix tailTrace_7116302
  have hstable : (prefixWord ++ tailWord_7116302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116302).length < 2 ^ (prefixWord ++ tailWord_7116302).sum := by decide
  have hdescent : baseEnd_7116302 < baseStart_7116302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116309 : List Nat := [1, 3, 2, 1, 3, 3, 3, 2, 1, 4]
def baseStart_7116309 : Nat := 118140960795 + 7116309 * 2 ^ 59
def prefixEnd_7116309 : Nat := 4983230072969 + 3 ^ 40 * 7116309 * 2
def baseEnd_7116309 : Nat := 1218029000972167714003399

theorem tailTrace_7116309 : CollatzResearch.WordTrace tailWord_7116309 prefixEnd_7116309 1218029000972167714003399 := by
  unfold tailWord_7116309
  simp only [CollatzResearch.WordTrace]
  refine ⟨259553112375835336661855981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173035408250556891107903987 259553112375835336661855981)
  ·
    refine ⟨97332417140938251248195993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259553112375835336661855981 97332417140938251248195993)
    ·
      refine ⟨72999312855703688436146995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97332417140938251248195993 72999312855703688436146995)
      ·
        refine ⟨109498969283555532654220493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72999312855703688436146995 109498969283555532654220493)
        ·
          refine ⟨41062113481333324745332685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109498969283555532654220493 41062113481333324745332685)
          ·
            refine ⟨15398292555499996779499757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41062113481333324745332685 15398292555499996779499757)
            ·
              refine ⟨5774359708312498792312409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15398292555499996779499757 5774359708312498792312409)
              ·
                refine ⟨4330769781234374094234307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5774359708312498792312409 4330769781234374094234307)
                ·
                  refine ⟨6496154671851561141351461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4330769781234374094234307 6496154671851561141351461)
                  ·
                    refine ⟨1218029000972167714003399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6496154671851561141351461 1218029000972167714003399)
                    ·
                      rfl

theorem cell23_7116309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_7116309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116309 prefixEnd_7116309 := by exact prefixLift 7116309
  have htrace : WordTrace (prefixWord ++ tailWord_7116309) baseStart_7116309 baseEnd_7116309 := by
    simpa [prefixWord, tailWord_7116309, baseEnd_7116309] using wordTrace_append hprefix tailTrace_7116309
  have hstable : (prefixWord ++ tailWord_7116309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116309).length < 2 ^ (prefixWord ++ tailWord_7116309).sum := by decide
  have hdescent : baseEnd_7116309 < baseStart_7116309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116325 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 6, 3, 2]
def baseStart_7116325 : Nat := 118140960795 + 7116325 * 2 ^ 59
def prefixEnd_7116325 : Nat := 4983230072969 + 3 ^ 40 * 7116325 * 2
def baseEnd_7116325 : Nat := 3654095218606975079410123

theorem tailTrace_7116325 : CollatzResearch.WordTrace tailWord_7116325 prefixEnd_7116325 3654095218606975079410123 := by
  unfold tailWord_7116325
  simp only [CollatzResearch.WordTrace]
  refine ⟨259553695943777371394438429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173035797295851580929625619 259553695943777371394438429)
  ·
    refine ⟨97332635978916514272914411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259553695943777371394438429 97332635978916514272914411)
    ·
      refine ⟨145998953968374771409371617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97332635978916514272914411 145998953968374771409371617)
      ·
        refine ⟨109499215476281078557028713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145998953968374771409371617 109499215476281078557028713)
        ·
          refine ⟨82124411607210808917771535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109499215476281078557028713 82124411607210808917771535)
          ·
            refine ⟨123186617410816213376657303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82124411607210808917771535 123186617410816213376657303)
            ·
              refine ⟨184779926116224320064985955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123186617410816213376657303 184779926116224320064985955)
              ·
                refine ⟨277169889174336480097478933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184779926116224320064985955 277169889174336480097478933)
                ·
                  refine ⟨12992338555047022504569325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 277169889174336480097478933 12992338555047022504569325)
                  ·
                    refine ⟨4872126958142633439213497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12992338555047022504569325 4872126958142633439213497)
                    ·
                      refine ⟨3654095218606975079410123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872126958142633439213497 3654095218606975079410123)
                      ·
                        rfl

theorem cell23_7116325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_7116325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116325 prefixEnd_7116325 := by exact prefixLift 7116325
  have htrace : WordTrace (prefixWord ++ tailWord_7116325) baseStart_7116325 baseEnd_7116325 := by
    simpa [prefixWord, tailWord_7116325, baseEnd_7116325] using wordTrace_append hprefix tailTrace_7116325
  have hstable : (prefixWord ++ tailWord_7116325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116325).length < 2 ^ (prefixWord ++ tailWord_7116325).sum := by decide
  have hdescent : baseEnd_7116325 < baseStart_7116325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116368 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 4]
def baseStart_7116368 : Nat := 118140960795 + 7116368 * 2 ^ 59
def prefixEnd_7116368 : Nat := 4983230072969 + 3 ^ 40 * 7116368 * 2
def baseEnd_7116368 : Nat := 3654117298275118411172425

theorem tailTrace_7116368 : CollatzResearch.WordTrace tailWord_7116368 prefixEnd_7116368 3654117298275118411172425 := by
  unfold tailWord_7116368
  simp only [CollatzResearch.WordTrace]
  refine ⟨129777632141310794869126879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173036842855081059825502505 129777632141310794869126879)
  ·
    refine ⟨194666448211966192303690319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129777632141310794869126879 194666448211966192303690319)
    ·
      refine ⟨291999672317949288455535479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194666448211966192303690319 291999672317949288455535479)
      ·
        refine ⟨437999508476923932683303219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291999672317949288455535479 437999508476923932683303219)
        ·
          refine ⟨656999262715385899024954829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437999508476923932683303219 656999262715385899024954829)
          ·
            refine ⟨246374723518269712134358061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 656999262715385899024954829 246374723518269712134358061)
            ·
              refine ⟨92390521319351142050384273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246374723518269712134358061 92390521319351142050384273)
              ·
                refine ⟨69292890989513356537788205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92390521319351142050384273 69292890989513356537788205)
                ·
                  refine ⟨25984834121067508701670577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69292890989513356537788205 25984834121067508701670577)
                  ·
                    refine ⟨19488625590800631526252933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25984834121067508701670577 19488625590800631526252933)
                    ·
                      refine ⟨3654117298275118411172425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19488625590800631526252933 3654117298275118411172425)
                      ·
                        rfl

theorem cell23_7116368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_7116368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116368 prefixEnd_7116368 := by exact prefixLift 7116368
  have htrace : WordTrace (prefixWord ++ tailWord_7116368) baseStart_7116368 baseEnd_7116368 := by
    simpa [prefixWord, tailWord_7116368, baseEnd_7116368] using wordTrace_append hprefix tailTrace_7116368
  have hstable : (prefixWord ++ tailWord_7116368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116368).length < 2 ^ (prefixWord ++ tailWord_7116368).sum := by decide
  have hdescent : baseEnd_7116368 < baseStart_7116368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116375 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 3]
def baseStart_7116375 : Nat := 118140960795 + 7116375 * 2 ^ 59
def prefixEnd_7116375 : Nat := 4983230072969 + 3 ^ 40 * 7116375 * 2
def baseEnd_7116375 : Nat := 3654120892639699883784893

theorem tailTrace_7116375 : CollatzResearch.WordTrace tailWord_7116375 prefixEnd_7116375 3654120892639699883784893 := by
  unfold tailWord_7116375
  simp only [CollatzResearch.WordTrace]
  refine ⟨259555519593596229933758579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173037013062397486622505719 259555519593596229933758579)
  ·
    refine ⟨389333279390394344900637869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259555519593596229933758579 389333279390394344900637869)
    ·
      refine ⟨145999979771397879337739201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389333279390394344900637869 145999979771397879337739201)
      ·
        refine ⟨109499984828548409503304401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145999979771397879337739201 109499984828548409503304401)
        ·
          refine ⟨82124988621411307127478301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109499984828548409503304401 82124988621411307127478301)
          ·
            refine ⟨30796870733029240172804363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82124988621411307127478301 30796870733029240172804363)
            ·
              refine ⟨46195306099543860259206545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30796870733029240172804363 46195306099543860259206545)
              ·
                refine ⟨34646479574657895194404909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46195306099543860259206545 34646479574657895194404909)
                ·
                  refine ⟨12992429840496710697901841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34646479574657895194404909 12992429840496710697901841)
                  ·
                    refine ⟨9744322380372533023426381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12992429840496710697901841 9744322380372533023426381)
                    ·
                      refine ⟨3654120892639699883784893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9744322380372533023426381 3654120892639699883784893)
                      ·
                        rfl

theorem cell23_7116375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_7116375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116375 prefixEnd_7116375 := by exact prefixLift 7116375
  have htrace : WordTrace (prefixWord ++ tailWord_7116375) baseStart_7116375 baseEnd_7116375 := by
    simpa [prefixWord, tailWord_7116375, baseEnd_7116375] using wordTrace_append hprefix tailTrace_7116375
  have hstable : (prefixWord ++ tailWord_7116375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116375).length < 2 ^ (prefixWord ++ tailWord_7116375).sum := by decide
  have hdescent : baseEnd_7116375 < baseStart_7116375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116385 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_7116385 : Nat := 118140960795 + 7116385 * 2 ^ 59
def prefixEnd_7116385 : Nat := 4983230072969 + 3 ^ 40 * 7116385 * 2
def baseEnd_7116385 : Nat := 3654126027446244844659847

theorem tailTrace_7116385 : CollatzResearch.WordTrace tailWord_7116385 prefixEnd_7116385 3654126027446244844659847 := by
  unfold tailWord_7116385
  simp only [CollatzResearch.WordTrace]
  refine ⟨259555884323560001641622609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173037256215706667761081739 259555884323560001641622609)
  ·
    refine ⟨194666913242670001231216957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259555884323560001641622609 194666913242670001231216957)
    ·
      refine ⟨73000092466001250461706359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194666913242670001231216957 73000092466001250461706359)
      ·
        refine ⟨109500138699001875692559539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73000092466001250461706359 109500138699001875692559539)
        ·
          refine ⟨164250208048502813538839309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109500138699001875692559539 164250208048502813538839309)
          ·
            refine ⟨61593828018188555077064741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164250208048502813538839309 61593828018188555077064741)
            ·
              refine ⟨11548842753410354076949639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61593828018188555077064741 11548842753410354076949639)
              ·
                refine ⟨17323264130115531115424459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11548842753410354076949639 17323264130115531115424459)
                ·
                  refine ⟨25984896195173296673136689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17323264130115531115424459 25984896195173296673136689)
                  ·
                    refine ⟨19488672146379972504852517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25984896195173296673136689 19488672146379972504852517)
                    ·
                      refine ⟨3654126027446244844659847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19488672146379972504852517 3654126027446244844659847)
                      ·
                        rfl

theorem cell23_7116385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_7116385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116385 prefixEnd_7116385 := by exact prefixLift 7116385
  have htrace : WordTrace (prefixWord ++ tailWord_7116385) baseStart_7116385 baseEnd_7116385 := by
    simpa [prefixWord, tailWord_7116385, baseEnd_7116385] using wordTrace_append hprefix tailTrace_7116385
  have hstable : (prefixWord ++ tailWord_7116385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116385).length < 2 ^ (prefixWord ++ tailWord_7116385).sum := by decide
  have hdescent : baseEnd_7116385 < baseStart_7116385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116389 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 3, 2, 2]
def baseStart_7116389 : Nat := 118140960795 + 7116389 * 2 ^ 59
def prefixEnd_7116389 : Nat := 4983230072969 + 3 ^ 40 * 7116389 * 2
def baseEnd_7116389 : Nat := 3654128081368862829009829

theorem tailTrace_7116389 : CollatzResearch.WordTrace tailWord_7116389 prefixEnd_7116389 3654128081368862829009829 := by
  unfold tailWord_7116389
  simp only [CollatzResearch.WordTrace]
  refine ⟨259556030215545510324768221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173037353477030340216512147 259556030215545510324768221)
  ·
    refine ⟨97333511330829566371788083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259556030215545510324768221 97333511330829566371788083)
    ·
      refine ⟨146000266996244349557682125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97333511330829566371788083 146000266996244349557682125)
      ·
        refine ⟨54750100123591631084130797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146000266996244349557682125 54750100123591631084130797)
        ·
          refine ⟨20531287546346861656549049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54750100123591631084130797 20531287546346861656549049)
          ·
            refine ⟨15398465659760146242411787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20531287546346861656549049 15398465659760146242411787)
            ·
              refine ⟨23097698489640219363617681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15398465659760146242411787 23097698489640219363617681)
              ·
                refine ⟨17323273867230164522713261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23097698489640219363617681 17323273867230164522713261)
                ·
                  refine ⟨6496227700211311696017473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17323273867230164522713261 6496227700211311696017473)
                  ·
                    refine ⟨4872170775158483772013105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6496227700211311696017473 4872170775158483772013105)
                    ·
                      refine ⟨3654128081368862829009829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872170775158483772013105 3654128081368862829009829)
                      ·
                        rfl

theorem cell23_7116389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_7116389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116389 prefixEnd_7116389 := by exact prefixLift 7116389
  have htrace : WordTrace (prefixWord ++ tailWord_7116389) baseStart_7116389 baseEnd_7116389 := by
    simpa [prefixWord, tailWord_7116389, baseEnd_7116389] using wordTrace_append hprefix tailTrace_7116389
  have hstable : (prefixWord ++ tailWord_7116389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116389).length < 2 ^ (prefixWord ++ tailWord_7116389).sum := by decide
  have hdescent : baseEnd_7116389 < baseStart_7116389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116392 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_7116392 : Nat := 118140960795 + 7116392 * 2 ^ 59
def prefixEnd_7116392 : Nat := 4983230072969 + 3 ^ 40 * 7116392 * 2
def baseEnd_7116392 : Nat := 3654129621810826317272315

theorem tailTrace_7116392 : CollatzResearch.WordTrace tailWord_7116392 prefixEnd_7116392 3654129621810826317272315 := by
  unfold tailWord_7116392
  simp only [CollatzResearch.WordTrace]
  refine ⟨129778069817267320918563715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173037426423023094558084953 129778069817267320918563715)
  ·
    refine ⟨194667104725900981377845573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129778069817267320918563715 194667104725900981377845573)
    ·
      refine ⟨36500082136106434008346045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194667104725900981377845573 36500082136106434008346045)
      ·
        refine ⟨13687530801039912753129767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36500082136106434008346045 13687530801039912753129767)
        ·
          refine ⟨20531296201559869129694651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13687530801039912753129767 20531296201559869129694651)
          ·
            refine ⟨30796944302339803694541977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20531296201559869129694651 30796944302339803694541977)
            ·
              refine ⟨23097708226754852770906483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30796944302339803694541977 23097708226754852770906483)
              ·
                refine ⟨34646562340132279156359725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23097708226754852770906483 34646562340132279156359725)
                ·
                  refine ⟨12992460877549604683634897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34646562340132279156359725 12992460877549604683634897)
                  ·
                    refine ⟨9744345658162203512726173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12992460877549604683634897 9744345658162203512726173)
                    ·
                      refine ⟨3654129621810826317272315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9744345658162203512726173 3654129621810826317272315)
                      ·
                        rfl

theorem cell23_7116392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_7116392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116392 prefixEnd_7116392 := by exact prefixLift 7116392
  have htrace : WordTrace (prefixWord ++ tailWord_7116392) baseStart_7116392 baseEnd_7116392 := by
    simpa [prefixWord, tailWord_7116392, baseEnd_7116392] using wordTrace_append hprefix tailTrace_7116392
  have hstable : (prefixWord ++ tailWord_7116392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116392).length < 2 ^ (prefixWord ++ tailWord_7116392).sum := by decide
  have hdescent : baseEnd_7116392 < baseStart_7116392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116406 : List Nat := [5, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_7116406 : Nat := 118140960795 + 7116406 * 2 ^ 59
def prefixEnd_7116406 : Nat := 4983230072969 + 3 ^ 40 * 7116406 * 2
def baseEnd_7116406 : Nat := 3654136810539989262497251

theorem tailTrace_7116406 : CollatzResearch.WordTrace tailWord_7116406 prefixEnd_7116406 3654136810539989262497251 := by
  unfold tailWord_7116406
  simp only [CollatzResearch.WordTrace]
  refine ⟨16222290641030245139258567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173037766837655948152091381 16222290641030245139258567)
  ·
    refine ⟨24333435961545367708887851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16222290641030245139258567 24333435961545367708887851)
    ·
      refine ⟨36500153942318051563331777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24333435961545367708887851 36500153942318051563331777)
      ·
        refine ⟨27375115456738538672498833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36500153942318051563331777 27375115456738538672498833)
        ·
          refine ⟨20531336592553904004374125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27375115456738538672498833 20531336592553904004374125)
          ·
            refine ⟨7699251222207714001640297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20531336592553904004374125 7699251222207714001640297)
            ·
              refine ⟨5774438416655785501230223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7699251222207714001640297 5774438416655785501230223)
              ·
                refine ⟨8661657624983678251845335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5774438416655785501230223 8661657624983678251845335)
                ·
                  refine ⟨12992486437475517377768003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8661657624983678251845335 12992486437475517377768003)
                  ·
                    refine ⟨19488729656213276066652005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12992486437475517377768003 19488729656213276066652005)
                    ·
                      refine ⟨3654136810539989262497251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19488729656213276066652005 3654136810539989262497251)
                      ·
                        rfl

theorem cell23_7116406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_7116406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116406 prefixEnd_7116406 := by exact prefixLift 7116406
  have htrace : WordTrace (prefixWord ++ tailWord_7116406) baseStart_7116406 baseEnd_7116406 := by
    simpa [prefixWord, tailWord_7116406, baseEnd_7116406] using wordTrace_append hprefix tailTrace_7116406
  have hstable : (prefixWord ++ tailWord_7116406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116406).length < 2 ^ (prefixWord ++ tailWord_7116406).sum := by decide
  have hdescent : baseEnd_7116406 < baseStart_7116406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116436 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_7116436 : Nat := 118140960795 + 7116436 * 2 ^ 59
def prefixEnd_7116436 : Nat := 4983230072969 + 3 ^ 40 * 7116436 * 2
def baseEnd_7116436 : Nat := 3654152214959624145122113

theorem tailTrace_7116436 : CollatzResearch.WordTrace tailWord_7116436 prefixEnd_7116436 3654152214959624145122113 := by
  unfold tailWord_7116436
  simp only [CollatzResearch.WordTrace]
  refine ⟨129778872223187618675864581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173038496297583491567819441 129778872223187618675864581)
  ·
    refine ⟨24333538541847678501724609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129778872223187618675864581 24333538541847678501724609)
    ·
      refine ⟨18250153906385758876293457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24333538541847678501724609 18250153906385758876293457)
      ·
        refine ⟨13687615429789319157220093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18250153906385758876293457 13687615429789319157220093)
        ·
          refine ⟨5132855786170994683957535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13687615429789319157220093 5132855786170994683957535)
          ·
            refine ⟨7699283679256492025936303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5132855786170994683957535 7699283679256492025936303)
            ·
              refine ⟨11548925518884738038904455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7699283679256492025936303 11548925518884738038904455)
              ·
                refine ⟨17323388278327107058356683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11548925518884738038904455 17323388278327107058356683)
                ·
                  refine ⟨25985082417490660587535025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17323388278327107058356683 25985082417490660587535025)
                  ·
                    refine ⟨19488811813117995440651269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25985082417490660587535025 19488811813117995440651269)
                    ·
                      refine ⟨3654152214959624145122113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19488811813117995440651269 3654152214959624145122113)
                      ·
                        rfl

theorem cell23_7116436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_7116436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116436 prefixEnd_7116436 := by exact prefixLift 7116436
  have htrace : WordTrace (prefixWord ++ tailWord_7116436) baseStart_7116436 baseEnd_7116436 := by
    simpa [prefixWord, tailWord_7116436, baseEnd_7116436] using wordTrace_append hprefix tailTrace_7116436
  have hstable : (prefixWord ++ tailWord_7116436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116436).length < 2 ^ (prefixWord ++ tailWord_7116436).sum := by decide
  have hdescent : baseEnd_7116436 < baseStart_7116436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116449 : List Nat := [1, 2, 3, 3, 2, 1, 1, 4, 1, 3, 2]
def baseStart_7116449 : Nat := 118140960795 + 7116449 * 2 ^ 59
def prefixEnd_7116449 : Nat := 4983230072969 + 3 ^ 40 * 7116449 * 2
def baseEnd_7116449 : Nat := 3654158890208132594259553

theorem tailTrace_7116449 : CollatzResearch.WordTrace tailWord_7116449 prefixEnd_7116449 3654158890208132594259553 := by
  unfold tailWord_7116449
  simp only [CollatzResearch.WordTrace]
  refine ⟨259558218595328140571952401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173038812396885427047968267 259558218595328140571952401)
  ·
    refine ⟨194668663946496105428964301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259558218595328140571952401 194668663946496105428964301)
    ·
      refine ⟨73000748979936039535861613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194668663946496105428964301 73000748979936039535861613)
      ·
        refine ⟨27375280867476014825948105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73000748979936039535861613 27375280867476014825948105)
        ·
          refine ⟨20531460650607011119461079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27375280867476014825948105 20531460650607011119461079)
          ·
            refine ⟨30797190975910516679191619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20531460650607011119461079 30797190975910516679191619)
            ·
              refine ⟨46195786463865775018787429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30797190975910516679191619 46195786463865775018787429)
              ·
                refine ⟨8661709961974832816022643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46195786463865775018787429 8661709961974832816022643)
                ·
                  refine ⟨12992564942962249224033965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8661709961974832816022643 12992564942962249224033965)
                  ·
                    refine ⟨4872211853610843459012737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12992564942962249224033965 4872211853610843459012737)
                    ·
                      refine ⟨3654158890208132594259553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872211853610843459012737 3654158890208132594259553)
                      ·
                        rfl

theorem cell23_7116449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_7116449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116449 prefixEnd_7116449 := by exact prefixLift 7116449
  have htrace : WordTrace (prefixWord ++ tailWord_7116449) baseStart_7116449 baseEnd_7116449 := by
    simpa [prefixWord, tailWord_7116449, baseEnd_7116449] using wordTrace_append hprefix tailTrace_7116449
  have hstable : (prefixWord ++ tailWord_7116449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116449).length < 2 ^ (prefixWord ++ tailWord_7116449).sum := by decide
  have hdescent : baseEnd_7116449 < baseStart_7116449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116479 : List Nat := [1, 1, 2, 2, 2, 3, 2, 4, 2, 2, 2]
def baseStart_7116479 : Nat := 118140960795 + 7116479 * 2 ^ 59
def prefixEnd_7116479 : Nat := 4983230072969 + 3 ^ 40 * 7116479 * 2
def baseEnd_7116479 : Nat := 3654174294627767476884415

theorem tailTrace_7116479 : CollatzResearch.WordTrace tailWord_7116479 prefixEnd_7116479 3654174294627767476884415 := by
  unfold tailWord_7116479
  simp only [CollatzResearch.WordTrace]
  refine ⟨259559312785219455695544491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173039541856812970463696327 259559312785219455695544491)
  ·
    refine ⟨389338969177829183543316737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259559312785219455695544491 389338969177829183543316737)
    ·
      refine ⟨292004226883371887657487553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389338969177829183543316737 292004226883371887657487553)
      ·
        refine ⟨219003170162528915743115665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292004226883371887657487553 219003170162528915743115665)
        ·
          refine ⟨164252377621896686807336749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219003170162528915743115665 164252377621896686807336749)
          ·
            refine ⟨61594641608211257552751281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164252377621896686807336749 61594641608211257552751281)
            ·
              refine ⟨46195981206158443164563461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61594641608211257552751281 46195981206158443164563461)
              ·
                refine ⟨8661746476154708093355649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46195981206158443164563461 8661746476154708093355649)
                ·
                  refine ⟨6496309857116031070016737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8661746476154708093355649 6496309857116031070016737)
                  ·
                    refine ⟨4872232392837023302512553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6496309857116031070016737 4872232392837023302512553)
                    ·
                      refine ⟨3654174294627767476884415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872232392837023302512553 3654174294627767476884415)
                      ·
                        rfl

theorem cell23_7116479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 2, 2].length) (baseStart_7116479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116479 prefixEnd_7116479 := by exact prefixLift 7116479
  have htrace : WordTrace (prefixWord ++ tailWord_7116479) baseStart_7116479 baseEnd_7116479 := by
    simpa [prefixWord, tailWord_7116479, baseEnd_7116479] using wordTrace_append hprefix tailTrace_7116479
  have hstable : (prefixWord ++ tailWord_7116479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116479).length < 2 ^ (prefixWord ++ tailWord_7116479).sum := by decide
  have hdescent : baseEnd_7116479 < baseStart_7116479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116495 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 3]
def baseStart_7116495 : Nat := 118140960795 + 7116495 * 2 ^ 59
def prefixEnd_7116495 : Nat := 4983230072969 + 3 ^ 40 * 7116495 * 2
def baseEnd_7116495 : Nat := 3654182510318239414284341

theorem tailTrace_7116495 : CollatzResearch.WordTrace tailWord_7116495 prefixEnd_7116495 3654182510318239414284341 := by
  unfold tailWord_7116495
  simp only [CollatzResearch.WordTrace]
  refine ⟨259559896353161490428126939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173039930902107660285417959 259559896353161490428126939)
  ·
    refine ⟨389339844529742235642190409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259559896353161490428126939 389339844529742235642190409)
    ·
      refine ⟨292004883397306676731642807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389339844529742235642190409 292004883397306676731642807)
      ·
        refine ⟨438007325095960015097464211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292004883397306676731642807 438007325095960015097464211)
        ·
          refine ⟨657010987643940022646196317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438007325095960015097464211 657010987643940022646196317)
          ·
            refine ⟨246379120366477508492323619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 657010987643940022646196317 246379120366477508492323619)
            ·
              refine ⟨369568680549716262738485429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246379120366477508492323619 369568680549716262738485429)
              ·
                refine ⟨34647063801535899631733009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 369568680549716262738485429 34647063801535899631733009)
                ·
                  refine ⟨25985297851151924723799757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34647063801535899631733009 25985297851151924723799757)
                  ·
                    refine ⟨9744486694181971771424909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25985297851151924723799757 9744486694181971771424909)
                    ·
                      refine ⟨3654182510318239414284341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9744486694181971771424909 3654182510318239414284341)
                      ·
                        rfl

theorem cell23_7116495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 3].length) (baseStart_7116495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116495 prefixEnd_7116495 := by exact prefixLift 7116495
  have htrace : WordTrace (prefixWord ++ tailWord_7116495) baseStart_7116495 baseEnd_7116495 := by
    simpa [prefixWord, tailWord_7116495, baseEnd_7116495] using wordTrace_append hprefix tailTrace_7116495
  have hstable : (prefixWord ++ tailWord_7116495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116495).length < 2 ^ (prefixWord ++ tailWord_7116495).sum := by decide
  have hdescent : baseEnd_7116495 < baseStart_7116495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116572 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_7116572 : Nat := 118140960795 + 7116572 * 2 ^ 59
def prefixEnd_7116572 : Nat := 4983230072969 + 3 ^ 40 * 7116572 * 2
def baseEnd_7116572 : Nat := 3654222048328635613021487

theorem tailTrace_7116572 : CollatzResearch.WordTrace tailWord_7116572 prefixEnd_7116572 3654222048328635613021487 := by
  unfold tailWord_7116572
  simp only [CollatzResearch.WordTrace]
  refine ⟨129781352386941266289339985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173041803182588355052453313 129781352386941266289339985)
  ·
    refine ⟨97336014290205949717004989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129781352386941266289339985 97336014290205949717004989)
    ·
      refine ⟨36501005358827231143876871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97336014290205949717004989 36501005358827231143876871)
      ·
        refine ⟨54751508038240846715815307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36501005358827231143876871 54751508038240846715815307)
        ·
          refine ⟨82127262057361270073722961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54751508038240846715815307 82127262057361270073722961)
          ·
            refine ⟨61595446543020952555292221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82127262057361270073722961 61595446543020952555292221)
            ·
              refine ⟨23098292453632857208234583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61595446543020952555292221 23098292453632857208234583)
              ·
                refine ⟨34647438680449285812351875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23098292453632857208234583 34647438680449285812351875)
                ·
                  refine ⟨51971158020673928718527813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34647438680449285812351875 51971158020673928718527813)
                  ·
                    refine ⟨9744592128876361634723965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51971158020673928718527813 9744592128876361634723965)
                    ·
                      refine ⟨3654222048328635613021487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9744592128876361634723965 3654222048328635613021487)
                      ·
                        rfl

theorem cell23_7116572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_7116572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116572 prefixEnd_7116572 := by exact prefixLift 7116572
  have htrace : WordTrace (prefixWord ++ tailWord_7116572) baseStart_7116572 baseEnd_7116572 := by
    simpa [prefixWord, tailWord_7116572, baseEnd_7116572] using wordTrace_append hprefix tailTrace_7116572
  have hstable : (prefixWord ++ tailWord_7116572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116572).length < 2 ^ (prefixWord ++ tailWord_7116572).sum := by decide
  have hdescent : baseEnd_7116572 < baseStart_7116572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116575 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 8]
def baseStart_7116575 : Nat := 118140960795 + 7116575 * 2 ^ 59
def prefixEnd_7116575 : Nat := 4983230072969 + 3 ^ 40 * 7116575 * 2
def baseEnd_7116575 : Nat := 406024843196733233475997

theorem tailTrace_7116575 : CollatzResearch.WordTrace tailWord_7116575 prefixEnd_7116575 406024843196733233475997 := by
  unfold tailWord_7116575
  simp only [CollatzResearch.WordTrace]
  refine ⟨259562814192871664091039179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173041876128581109394026119 259562814192871664091039179)
  ·
    refine ⟨389344221289307496136558769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259562814192871664091039179 389344221289307496136558769)
    ·
      refine ⟨292008165966980622102419077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389344221289307496136558769 292008165966980622102419077)
      ·
        refine ⟨54751531118808866644203577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292008165966980622102419077 54751531118808866644203577)
        ·
          refine ⟨41063648339106649983152683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54751531118808866644203577 41063648339106649983152683)
          ·
            refine ⟨61595472508659974974729025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41063648339106649983152683 61595472508659974974729025)
            ·
              refine ⟨46196604381494981231046769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61595472508659974974729025 46196604381494981231046769)
              ·
                refine ⟨34647453286121235923285077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46196604381494981231046769 34647453286121235923285077)
                ·
                  refine ⟨406024843196733233475997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34647453286121235923285077 406024843196733233475997)
                  ·
                    rfl

theorem cell23_7116575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 8].length) (baseStart_7116575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116575 prefixEnd_7116575 := by exact prefixLift 7116575
  have htrace : WordTrace (prefixWord ++ tailWord_7116575) baseStart_7116575 baseEnd_7116575 := by
    simpa [prefixWord, tailWord_7116575, baseEnd_7116575] using wordTrace_append hprefix tailTrace_7116575
  have hstable : (prefixWord ++ tailWord_7116575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116575).length < 2 ^ (prefixWord ++ tailWord_7116575).sum := by decide
  have hdescent : baseEnd_7116575 < baseStart_7116575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116579 : List Nat := [1, 1, 1, 4, 2, 1, 3, 5, 1, 4]
def baseStart_7116579 : Nat := 118140960795 + 7116579 * 2 ^ 59
def prefixEnd_7116579 : Nat := 4983230072969 + 3 ^ 40 * 7116579 * 2
def baseEnd_7116579 : Nat := 1218075214231072361877985

theorem tailTrace_7116579 : CollatzResearch.WordTrace tailWord_7116579 prefixEnd_7116579 1218075214231072361877985 := by
  unfold tailWord_7116579
  simp only [CollatzResearch.WordTrace]
  refine ⟨259562960084857172774184791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173041973389904781849456527 259562960084857172774184791)
  ·
    refine ⟨389344440127285759161277187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259562960084857172774184791 389344440127285759161277187)
    ·
      refine ⟨584016660190928638741915781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389344440127285759161277187 584016660190928638741915781)
      ·
        refine ⟨109503123785799119764109209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 584016660190928638741915781 109503123785799119764109209)
        ·
          refine ⟨82127342839349339823081907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109503123785799119764109209 82127342839349339823081907)
          ·
            refine ⟨123191014259024009734622861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82127342839349339823081907 123191014259024009734622861)
            ·
              refine ⟨46196630347134003650483573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123191014259024009734622861 46196630347134003650483573)
              ·
                refine ⟨4330934095043812842232835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46196630347134003650483573 4330934095043812842232835)
                ·
                  refine ⟨6496401142565719263349253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4330934095043812842232835 6496401142565719263349253)
                  ·
                    refine ⟨1218075214231072361877985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6496401142565719263349253 1218075214231072361877985)
                    ·
                      rfl

theorem cell23_7116579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 1, 4].length) (baseStart_7116579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116579 prefixEnd_7116579 := by exact prefixLift 7116579
  have htrace : WordTrace (prefixWord ++ tailWord_7116579) baseStart_7116579 baseEnd_7116579 := by
    simpa [prefixWord, tailWord_7116579, baseEnd_7116579] using wordTrace_append hprefix tailTrace_7116579
  have hstable : (prefixWord ++ tailWord_7116579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116579).length < 2 ^ (prefixWord ++ tailWord_7116579).sum := by decide
  have hdescent : baseEnd_7116579 < baseStart_7116579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116596 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_7116596 : Nat := 118140960795 + 7116596 * 2 ^ 59
def prefixEnd_7116596 : Nat := 4983230072969 + 3 ^ 40 * 7116596 * 2
def baseEnd_7116596 : Nat := 1218078123954781173040459

theorem tailTrace_7116596 : CollatzResearch.WordTrace tailWord_7116596 prefixEnd_7116596 1218078123954781173040459 := by
  unfold tailWord_7116596
  simp only [CollatzResearch.WordTrace]
  refine ⟨129781790062897792338776821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173042386750530389785035761 129781790062897792338776821)
  ·
    refine ⟨12167042818396668031760327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129781790062897792338776821 12167042818396668031760327)
    ·
      refine ⟨18250564227595002047640491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12167042818396668031760327 18250564227595002047640491)
      ·
        refine ⟨27375846341392503071460737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18250564227595002047640491 27375846341392503071460737)
        ·
          refine ⟨20531884756044377303595553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27375846341392503071460737 20531884756044377303595553)
          ·
            refine ⟨15398913567033282977696665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20531884756044377303595553 15398913567033282977696665)
            ·
              refine ⟨11549185175274962233272499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15398913567033282977696665 11549185175274962233272499)
              ·
                refine ⟨17323777762912443349908749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11549185175274962233272499 17323777762912443349908749)
                ·
                  refine ⟨6496416661092166256215781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17323777762912443349908749 6496416661092166256215781)
                  ·
                    refine ⟨1218078123954781173040459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6496416661092166256215781 1218078123954781173040459)
                    ·
                      rfl

theorem cell23_7116596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_7116596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116596 prefixEnd_7116596 := by exact prefixLift 7116596
  have htrace : WordTrace (prefixWord ++ tailWord_7116596) baseStart_7116596 baseEnd_7116596 := by
    simpa [prefixWord, tailWord_7116596, baseEnd_7116596] using wordTrace_append hprefix tailTrace_7116596
  have hstable : (prefixWord ++ tailWord_7116596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116596).length < 2 ^ (prefixWord ++ tailWord_7116596).sum := by decide
  have hdescent : baseEnd_7116596 < baseStart_7116596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116615 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_7116615 : Nat := 118140960795 + 7116615 * 2 ^ 59
def prefixEnd_7116615 : Nat := 4983230072969 + 3 ^ 40 * 7116615 * 2
def baseEnd_7116615 : Nat := 3654244127996778944783789

theorem tailTrace_7116615 : CollatzResearch.WordTrace tailWord_7116615 prefixEnd_7116615 3654244127996778944783789 := by
  unfold tailWord_7116615
  simp only [CollatzResearch.WordTrace]
  refine ⟨259564273112726750922495299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173042848741817833948330199 259564273112726750922495299)
  ·
    refine ⟨389346409669090126383742949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259564273112726750922495299 389346409669090126383742949)
    ·
      refine ⟨73002451812954398696951803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389346409669090126383742949 73002451812954398696951803)
      ·
        refine ⟨109503677719431598045427705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73002451812954398696951803 109503677719431598045427705)
        ·
          refine ⟨82127758289573698534070779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109503677719431598045427705 82127758289573698534070779)
          ·
            refine ⟨123191637434360547801106169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82127758289573698534070779 123191637434360547801106169)
            ·
              refine ⟨92393728075770410850829627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123191637434360547801106169 92393728075770410850829627)
              ·
                refine ⟨138590592113655616276244441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92393728075770410850829627 138590592113655616276244441)
                ·
                  refine ⟨103942944085241712207183331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138590592113655616276244441 103942944085241712207183331)
                  ·
                    refine ⟨155914416127862568310774997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103942944085241712207183331 155914416127862568310774997)
                    ·
                      refine ⟨3654244127996778944783789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155914416127862568310774997 3654244127996778944783789)
                      ·
                        rfl

theorem cell23_7116615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_7116615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116615 prefixEnd_7116615 := by exact prefixLift 7116615
  have htrace : WordTrace (prefixWord ++ tailWord_7116615) baseStart_7116615 baseEnd_7116615 := by
    simpa [prefixWord, tailWord_7116615, baseEnd_7116615] using wordTrace_append hprefix tailTrace_7116615
  have hstable : (prefixWord ++ tailWord_7116615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116615).length < 2 ^ (prefixWord ++ tailWord_7116615).sum := by decide
  have hdescent : baseEnd_7116615 < baseStart_7116615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116629 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 1, 5, 2]
def baseStart_7116629 : Nat := 118140960795 + 7116629 * 2 ^ 59
def prefixEnd_7116629 : Nat := 4983230072969 + 3 ^ 40 * 7116629 * 2
def baseEnd_7116629 : Nat := 3654251316725941890008725

theorem tailTrace_7116629 : CollatzResearch.WordTrace tailWord_7116629 prefixEnd_7116629 3654251316725941890008725 := by
  unfold tailWord_7116629
  simp only [CollatzResearch.WordTrace]
  refine ⟨259564783734676031313504941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173043189156450687542336627 259564783734676031313504941)
  ·
    refine ⟨97336793900503511742564353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259564783734676031313504941 97336793900503511742564353)
    ·
      refine ⟨73002595425377633806923265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97336793900503511742564353 73002595425377633806923265)
      ·
        refine ⟨54751946569033225355192449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73002595425377633806923265 54751946569033225355192449)
        ·
          refine ⟨41063959926774919016394337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54751946569033225355192449 41063959926774919016394337)
          ·
            refine ⟨30797969945081189262295753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41063959926774919016394337 30797969945081189262295753)
            ·
              refine ⟨23098477458810891946721815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30797969945081189262295753 23098477458810891946721815)
              ·
                refine ⟨34647716188216337920082723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23098477458810891946721815 34647716188216337920082723)
                ·
                  refine ⟨51971574282324506880124085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34647716188216337920082723 51971574282324506880124085)
                  ·
                    refine ⟨4872335088967922520011633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51971574282324506880124085 4872335088967922520011633)
                    ·
                      refine ⟨3654251316725941890008725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872335088967922520011633 3654251316725941890008725)
                      ·
                        rfl

theorem cell23_7116629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_7116629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116629 prefixEnd_7116629 := by exact prefixLift 7116629
  have htrace : WordTrace (prefixWord ++ tailWord_7116629) baseStart_7116629 baseEnd_7116629 := by
    simpa [prefixWord, tailWord_7116629, baseEnd_7116629] using wordTrace_append hprefix tailTrace_7116629
  have hstable : (prefixWord ++ tailWord_7116629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116629).length < 2 ^ (prefixWord ++ tailWord_7116629).sum := by decide
  have hdescent : baseEnd_7116629 < baseStart_7116629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116672 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 4]
def baseStart_7116672 : Nat := 118140960795 + 7116672 * 2 ^ 59
def prefixEnd_7116672 : Nat := 4983230072969 + 3 ^ 40 * 7116672 * 2
def baseEnd_7116672 : Nat := 3654273396394085221771027

theorem tailTrace_7116672 : CollatzResearch.WordTrace tailWord_7116672 prefixEnd_7116672 3654273396394085221771027 := by
  unfold tailWord_7116672
  simp only [CollatzResearch.WordTrace]
  refine ⟨129783176036760124828660135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173044234715680166438213513 129783176036760124828660135)
  ·
    refine ⟨194674764055140187242990203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129783176036760124828660135 194674764055140187242990203)
    ·
      refine ⟨292012146082710280864485305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194674764055140187242990203 292012146082710280864485305)
      ·
        refine ⟨219009109562032710648363979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292012146082710280864485305 219009109562032710648363979)
        ·
          refine ⟨328513664343049065972545969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219009109562032710648363979 328513664343049065972545969)
          ·
            refine ⟨246385248257286799479409477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328513664343049065972545969 246385248257286799479409477)
            ·
              refine ⟨46197234048241274902389277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246385248257286799479409477 46197234048241274902389277)
              ·
                refine ⟨17323962768090478088395979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46197234048241274902389277 17323962768090478088395979)
                ·
                  refine ⟨25985944152135717132593969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17323962768090478088395979 25985944152135717132593969)
                  ·
                    refine ⟨19489458114101787849445477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25985944152135717132593969 19489458114101787849445477)
                    ·
                      refine ⟨3654273396394085221771027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19489458114101787849445477 3654273396394085221771027)
                      ·
                        rfl

theorem cell23_7116672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_7116672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116672 prefixEnd_7116672 := by exact prefixLift 7116672
  have htrace : WordTrace (prefixWord ++ tailWord_7116672) baseStart_7116672 baseEnd_7116672 := by
    simpa [prefixWord, tailWord_7116672, baseEnd_7116672] using wordTrace_append hprefix tailTrace_7116672
  have hstable : (prefixWord ++ tailWord_7116672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116672).length < 2 ^ (prefixWord ++ tailWord_7116672).sum := by decide
  have hdescent : baseEnd_7116672 < baseStart_7116672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116673 : List Nat := [1, 2, 4, 4, 1, 2, 1, 2, 1, 5]
def baseStart_7116673 : Nat := 118140960795 + 7116673 * 2 ^ 59
def prefixEnd_7116673 : Nat := 4983230072969 + 3 ^ 40 * 7116673 * 2
def baseEnd_7116673 : Nat := 1218091303291579905952841

theorem tailTrace_7116673 : CollatzResearch.WordTrace tailWord_7116673 prefixEnd_7116673 1218091303291579905952841 := by
  unfold tailWord_7116673
  simp only [CollatzResearch.WordTrace]
  refine ⟨259566388546516626828106673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173044259031011084552071115 259566388546516626828106673)
  ·
    refine ⟨194674791409887470121080005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259566388546516626828106673 194674791409887470121080005)
    ·
      refine ⟨36501523389353900647702501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194674791409887470121080005 36501523389353900647702501)
      ·
        refine ⟨6844035635503856371444219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36501523389353900647702501 6844035635503856371444219)
        ·
          refine ⟨10266053453255784557166329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6844035635503856371444219 10266053453255784557166329)
          ·
            refine ⟨7699540089941838417874747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10266053453255784557166329 7699540089941838417874747)
            ·
              refine ⟨11549310134912757626812121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7699540089941838417874747 11549310134912757626812121)
              ·
                refine ⟨8661982601184568220109091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11549310134912757626812121 8661982601184568220109091)
                ·
                  refine ⟨12992973901776852330163637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8661982601184568220109091 12992973901776852330163637)
                  ·
                    refine ⟨1218091303291579905952841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12992973901776852330163637 1218091303291579905952841)
                    ·
                      rfl

theorem cell23_7116673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_7116673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116673 prefixEnd_7116673 := by exact prefixLift 7116673
  have htrace : WordTrace (prefixWord ++ tailWord_7116673) baseStart_7116673 baseEnd_7116673 := by
    simpa [prefixWord, tailWord_7116673, baseEnd_7116673] using wordTrace_append hprefix tailTrace_7116673
  have hstable : (prefixWord ++ tailWord_7116673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116673).length < 2 ^ (prefixWord ++ tailWord_7116673).sum := by decide
  have hdescent : baseEnd_7116673 < baseStart_7116673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116676 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_7116676 : Nat := 118140960795 + 7116676 * 2 ^ 59
def prefixEnd_7116676 : Nat := 4983230072969 + 3 ^ 40 * 7116676 * 2
def baseEnd_7116676 : Nat := 3654275450316703206121009

theorem tailTrace_7116676 : CollatzResearch.WordTrace tailWord_7116676 prefixEnd_7116676 3654275450316703206121009 := by
  unfold tailWord_7116676
  simp only [CollatzResearch.WordTrace]
  refine ⟨129783248982752879170232941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173044331977003838893643921 129783248982752879170232941)
  ·
    refine ⟨48668718368532329688837353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129783248982752879170232941 48668718368532329688837353)
    ·
      refine ⟨36501538776399247266628015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48668718368532329688837353 36501538776399247266628015)
      ·
        refine ⟨54752308164598870899942023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36501538776399247266628015 54752308164598870899942023)
        ·
          refine ⟨82128462246898306349913035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54752308164598870899942023 82128462246898306349913035)
          ·
            refine ⟨123192693370347459524869553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82128462246898306349913035 123192693370347459524869553)
            ·
              refine ⟨92394520027760594643652165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123192693370347459524869553 92394520027760594643652165)
              ·
                refine ⟨17323972505205111495684781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92394520027760594643652165 17323972505205111495684781)
                ·
                  refine ⟨6496489689451916810881793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17323972505205111495684781 6496489689451916810881793)
                  ·
                    refine ⟨4872367267088937608161345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6496489689451916810881793 4872367267088937608161345)
                    ·
                      refine ⟨3654275450316703206121009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872367267088937608161345 3654275450316703206121009)
                      ·
                        rfl

theorem cell23_7116676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_7116676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116676 prefixEnd_7116676 := by exact prefixLift 7116676
  have htrace : WordTrace (prefixWord ++ tailWord_7116676) baseStart_7116676 baseEnd_7116676 := by
    simpa [prefixWord, tailWord_7116676, baseEnd_7116676] using wordTrace_append hprefix tailTrace_7116676
  have hstable : (prefixWord ++ tailWord_7116676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116676).length < 2 ^ (prefixWord ++ tailWord_7116676).sum := by decide
  have hdescent : baseEnd_7116676 < baseStart_7116676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116686 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_7116686 : Nat := 118140960795 + 7116686 * 2 ^ 59
def prefixEnd_7116686 : Nat := 4983230072969 + 3 ^ 40 * 7116686 * 2
def baseEnd_7116686 : Nat := 1218093528374416055665321

theorem tailTrace_7116686 : CollatzResearch.WordTrace tailWord_7116686 prefixEnd_7116686 1218093528374416055665321 := by
  unfold tailWord_7116686
  simp only [CollatzResearch.WordTrace]
  refine ⟨32445857836933691256041239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173044575130313020032219941 32445857836933691256041239)
  ·
    refine ⟨48668786755400536884061859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32445857836933691256041239 48668786755400536884061859)
    ·
      refine ⟨73003180133100805326092789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48668786755400536884061859 73003180133100805326092789)
      ·
        refine ⟨6844048137478200499321199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73003180133100805326092789 6844048137478200499321199)
        ·
          refine ⟨10266072206217300748981799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6844048137478200499321199 10266072206217300748981799)
          ·
            refine ⟨15399108309325951123472699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10266072206217300748981799 15399108309325951123472699)
            ·
              refine ⟨23098662463988926685209049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15399108309325951123472699 23098662463988926685209049)
              ·
                refine ⟨17323996847991695013906787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23098662463988926685209049 17323996847991695013906787)
                ·
                  refine ⟨25985995271987542520860181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17323996847991695013906787 25985995271987542520860181)
                  ·
                    refine ⟨1218093528374416055665321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25985995271987542520860181 1218093528374416055665321)
                    ·
                      rfl

theorem cell23_7116686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_7116686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116686 prefixEnd_7116686 := by exact prefixLift 7116686
  have htrace : WordTrace (prefixWord ++ tailWord_7116686) baseStart_7116686 baseEnd_7116686 := by
    simpa [prefixWord, tailWord_7116686, baseEnd_7116686] using wordTrace_append hprefix tailTrace_7116686
  have hstable : (prefixWord ++ tailWord_7116686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116686).length < 2 ^ (prefixWord ++ tailWord_7116686).sum := by decide
  have hdescent : baseEnd_7116686 < baseStart_7116686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116693 : List Nat := [1, 3, 2, 1, 1, 3, 2, 5, 1, 2, 2]
def baseStart_7116693 : Nat := 118140960795 + 7116693 * 2 ^ 59
def prefixEnd_7116693 : Nat := 4983230072969 + 3 ^ 40 * 7116693 * 2
def baseEnd_7116693 : Nat := 3654284179487829639608431

theorem tailTrace_7116693 : CollatzResearch.WordTrace tailWord_7116693 prefixEnd_7116693 3654284179487829639608431 := by
  unfold tailWord_7116693
  simp only [CollatzResearch.WordTrace]
  refine ⟨259567118006444170243834733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173044745337629446829223155 259567118006444170243834733)
  ·
    refine ⟨97337669252416563841438025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259567118006444170243834733 97337669252416563841438025)
    ·
      refine ⟨73003251939312422881078519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97337669252416563841438025 73003251939312422881078519)
      ·
        refine ⟨109504877908968634321617779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73003251939312422881078519 109504877908968634321617779)
        ·
          refine ⟨164257316863452951482426669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109504877908968634321617779 164257316863452951482426669)
          ·
            refine ⟨61596493823794856805910001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164257316863452951482426669 61596493823794856805910001)
            ·
              refine ⟨46197370367846142604432501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61596493823794856805910001 46197370367846142604432501)
              ·
                refine ⟨4331003471985575869165547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46197370367846142604432501 4331003471985575869165547)
                ·
                  refine ⟨6496505207978363803748321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4331003471985575869165547 6496505207978363803748321)
                  ·
                    refine ⟨4872378905983772852811241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6496505207978363803748321 4872378905983772852811241)
                    ·
                      refine ⟨3654284179487829639608431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872378905983772852811241 3654284179487829639608431)
                      ·
                        rfl

theorem cell23_7116693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_7116693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116693 prefixEnd_7116693 := by exact prefixLift 7116693
  have htrace : WordTrace (prefixWord ++ tailWord_7116693) baseStart_7116693 baseEnd_7116693 := by
    simpa [prefixWord, tailWord_7116693, baseEnd_7116693] using wordTrace_append hprefix tailTrace_7116693
  have hstable : (prefixWord ++ tailWord_7116693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116693).length < 2 ^ (prefixWord ++ tailWord_7116693).sum := by decide
  have hdescent : baseEnd_7116693 < baseStart_7116693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116709 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 4, 1, 3]
def baseStart_7116709 : Nat := 118140960795 + 7116709 * 2 ^ 59
def prefixEnd_7116709 : Nat := 4983230072969 + 3 ^ 40 * 7116709 * 2
def baseEnd_7116709 : Nat := 3654292395178301577008357

theorem tailTrace_7116709 : CollatzResearch.WordTrace tailWord_7116709 prefixEnd_7116709 3654292395178301577008357 := by
  unfold tailWord_7116709
  simp only [CollatzResearch.WordTrace]
  refine ⟨259567701574386204976417181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173045134382924136650944787 259567701574386204976417181)
  ·
    refine ⟨97337888090394826866156443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259567701574386204976417181 97337888090394826866156443)
    ·
      refine ⟨146006832135592240299234665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97337888090394826866156443 146006832135592240299234665)
      ·
        refine ⟨109505124101694180224425999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146006832135592240299234665 109505124101694180224425999)
        ·
          refine ⟨164257686152541270336638999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109505124101694180224425999 164257686152541270336638999)
          ·
            refine ⟨246386529228811905504958499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164257686152541270336638999 246386529228811905504958499)
            ·
              refine ⟨369579793843217858257437749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246386529228811905504958499 369579793843217858257437749)
              ·
                refine ⟨34648105672801674211634789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 369579793843217858257437749 34648105672801674211634789)
                ·
                  refine ⟨6496519813650313914681523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34648105672801674211634789 6496519813650313914681523)
                  ·
                    refine ⟨9744779720475470872022285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6496519813650313914681523 9744779720475470872022285)
                    ·
                      refine ⟨3654292395178301577008357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9744779720475470872022285 3654292395178301577008357)
                      ·
                        rfl

theorem cell23_7116709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_7116709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116709 prefixEnd_7116709 := by exact prefixLift 7116709
  have htrace : WordTrace (prefixWord ++ tailWord_7116709) baseStart_7116709 baseEnd_7116709 := by
    simpa [prefixWord, tailWord_7116709, baseEnd_7116709] using wordTrace_append hprefix tailTrace_7116709
  have hstable : (prefixWord ++ tailWord_7116709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116709).length < 2 ^ (prefixWord ++ tailWord_7116709).sum := by decide
  have hdescent : baseEnd_7116709 < baseStart_7116709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116719 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 5, 3, 2]
def baseStart_7116719 : Nat := 118140960795 + 7116719 * 2 ^ 59
def prefixEnd_7116719 : Nat := 4983230072969 + 3 ^ 40 * 7116719 * 2
def baseEnd_7116719 : Nat := 3654297529984846537883311

theorem tailTrace_7116719 : CollatzResearch.WordTrace tailWord_7116719 prefixEnd_7116719 3654297529984846537883311 := by
  unfold tailWord_7116719
  simp only [CollatzResearch.WordTrace]
  refine ⟨259568066304349976684281211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173045377536233317789520807 259568066304349976684281211)
  ·
    refine ⟨389352099456524965026421817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259568066304349976684281211 389352099456524965026421817)
    ·
      refine ⟨292014074592393723769816363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389352099456524965026421817 292014074592393723769816363)
      ·
        refine ⟨438021111888590585654724545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292014074592393723769816363 438021111888590585654724545)
        ·
          refine ⟨328515833916442939241043409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438021111888590585654724545 328515833916442939241043409)
          ·
            refine ⟨246386875437332204430782557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328515833916442939241043409 246386875437332204430782557)
            ·
              refine ⟨92395078288999576661543459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246386875437332204430782557 92395078288999576661543459)
              ·
                refine ⟨138592617433499364992315189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92395078288999576661543459 138592617433499364992315189)
                ·
                  refine ⟨12993057884390565468029549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138592617433499364992315189 12993057884390565468029549)
                  ·
                    refine ⟨4872396706646462050511081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12993057884390565468029549 4872396706646462050511081)
                    ·
                      refine ⟨3654297529984846537883311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872396706646462050511081 3654297529984846537883311)
                      ·
                        rfl

theorem cell23_7116719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 3, 2].length) (baseStart_7116719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116719 prefixEnd_7116719 := by exact prefixLift 7116719
  have htrace : WordTrace (prefixWord ++ tailWord_7116719) baseStart_7116719 baseEnd_7116719 := by
    simpa [prefixWord, tailWord_7116719, baseEnd_7116719] using wordTrace_append hprefix tailTrace_7116719
  have hstable : (prefixWord ++ tailWord_7116719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116719).length < 2 ^ (prefixWord ++ tailWord_7116719).sum := by decide
  have hdescent : baseEnd_7116719 < baseStart_7116719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116736 : List Nat := [2, 1, 1, 2, 3, 2, 2, 4, 1, 3, 2]
def baseStart_7116736 : Nat := 118140960795 + 7116736 * 2 ^ 59
def prefixEnd_7116736 : Nat := 4983230072969 + 3 ^ 40 * 7116736 * 2
def baseEnd_7116736 : Nat := 3654306259155972971370733

theorem tailTrace_7116736 : CollatzResearch.WordTrace tailWord_7116736 prefixEnd_7116736 3654306259155972971370733 := by
  unfold tailWord_7116736
  simp only [CollatzResearch.WordTrace]
  refine ⟨129784343172644194293825031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173045790896858925725100041 129784343172644194293825031)
  ·
    refine ⟨194676514758966291440737547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129784343172644194293825031 194676514758966291440737547)
    ·
      refine ⟨292014772138449437161106321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194676514758966291440737547 292014772138449437161106321)
      ·
        refine ⟨219011079103837077870829741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292014772138449437161106321 219011079103837077870829741)
        ·
          refine ⟨82129154663938904201561153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219011079103837077870829741 82129154663938904201561153)
          ·
            refine ⟨61596865997954178151170865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82129154663938904201561153 61596865997954178151170865)
            ·
              refine ⟨46197649498465633613378149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61596865997954178151170865 46197649498465633613378149)
              ·
                refine ⟨8662059280962306302508403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46197649498465633613378149 8662059280962306302508403)
                ·
                  refine ⟨12993088921443459453762605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8662059280962306302508403 12993088921443459453762605)
                  ·
                    refine ⟨4872408345541297295160977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12993088921443459453762605 4872408345541297295160977)
                    ·
                      refine ⟨3654306259155972971370733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872408345541297295160977 3654306259155972971370733)
                      ·
                        rfl

theorem cell23_7116736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 1, 3, 2].length) (baseStart_7116736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116736 prefixEnd_7116736 := by exact prefixLift 7116736
  have htrace : WordTrace (prefixWord ++ tailWord_7116736) baseStart_7116736 baseEnd_7116736 := by
    simpa [prefixWord, tailWord_7116736, baseEnd_7116736] using wordTrace_append hprefix tailTrace_7116736
  have hstable : (prefixWord ++ tailWord_7116736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116736).length < 2 ^ (prefixWord ++ tailWord_7116736).sum := by decide
  have hdescent : baseEnd_7116736 < baseStart_7116736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116752 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 5]
def baseStart_7116752 : Nat := 118140960795 + 7116752 * 2 ^ 59
def prefixEnd_7116752 : Nat := 4983230072969 + 3 ^ 40 * 7116752 * 2
def baseEnd_7116752 : Nat := 3654314474846444908770659

theorem tailTrace_7116752 : CollatzResearch.WordTrace tailWord_7116752 prefixEnd_7116752 3654314474846444908770659 := by
  unfold tailWord_7116752
  simp only [CollatzResearch.WordTrace]
  refine ⟨129784634956615211660116255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173046179942153615546821673 129784634956615211660116255)
  ·
    refine ⟨194676952434922817490174383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129784634956615211660116255 194676952434922817490174383)
    ·
      refine ⟨292015428652384226235261575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194676952434922817490174383 292015428652384226235261575)
      ·
        refine ⟨438023142978576339352892363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292015428652384226235261575 438023142978576339352892363)
        ·
          refine ⟨657034714467864509029338545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438023142978576339352892363 657034714467864509029338545)
          ·
            refine ⟨492776035850898381772003909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657034714467864509029338545 492776035850898381772003909)
            ·
              refine ⟨92395506722043446582250733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 492776035850898381772003909 92395506722043446582250733)
              ·
                refine ⟨34648315020766292468344025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92395506722043446582250733 34648315020766292468344025)
                ·
                  refine ⟨25986236265574719351258019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34648315020766292468344025 25986236265574719351258019)
                  ·
                    refine ⟨38979354398362079026887029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25986236265574719351258019 38979354398362079026887029)
                    ·
                      refine ⟨3654314474846444908770659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38979354398362079026887029 3654314474846444908770659)
                      ·
                        rfl

theorem cell23_7116752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_7116752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116752 prefixEnd_7116752 := by exact prefixLift 7116752
  have htrace : WordTrace (prefixWord ++ tailWord_7116752) baseStart_7116752 baseEnd_7116752 := by
    simpa [prefixWord, tailWord_7116752, baseEnd_7116752] using wordTrace_append hprefix tailTrace_7116752
  have hstable : (prefixWord ++ tailWord_7116752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116752).length < 2 ^ (prefixWord ++ tailWord_7116752).sum := by decide
  have hdescent : baseEnd_7116752 < baseStart_7116752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116809 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 3, 7, 2]
def baseStart_7116809 : Nat := 118140960795 + 7116809 * 2 ^ 59
def prefixEnd_7116809 : Nat := 4983230072969 + 3 ^ 40 * 7116809 * 2
def baseEnd_7116809 : Nat := 3654343743243751185757897

theorem tailTrace_7116809 : CollatzResearch.WordTrace tailWord_7116809 prefixEnd_7116809 3654343743243751185757897 := by
  unfold tailWord_7116809
  simp only [CollatzResearch.WordTrace]
  refine ⟨259571348874023922055057481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173047565916015948036704987 259571348874023922055057481)
  ·
    refine ⟨194678511655517941541293111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259571348874023922055057481 194678511655517941541293111)
    ·
      refine ⟨292017767483276912311939667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194678511655517941541293111 292017767483276912311939667)
      ·
        refine ⟨438026651224915368467909501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292017767483276912311939667 438026651224915368467909501)
        ·
          refine ⟨164259994209343263175466063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438026651224915368467909501 164259994209343263175466063)
          ·
            refine ⟨246389991314014894763199095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164259994209343263175466063 246389991314014894763199095)
            ·
              refine ⟨369584986971022342144798643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246389991314014894763199095 369584986971022342144798643)
              ·
                refine ⟨554377480456533513217197965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369584986971022342144798643 554377480456533513217197965)
                ·
                  refine ⟨207891555171200067456449237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 554377480456533513217197965 207891555171200067456449237)
                  ·
                    refine ⟨4872458324325001581010529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 207891555171200067456449237 4872458324325001581010529)
                    ·
                      refine ⟨3654343743243751185757897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872458324325001581010529 3654343743243751185757897)
                      ·
                        rfl

theorem cell23_7116809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 7, 2].length) (baseStart_7116809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116809 prefixEnd_7116809 := by exact prefixLift 7116809
  have htrace : WordTrace (prefixWord ++ tailWord_7116809) baseStart_7116809 baseEnd_7116809 := by
    simpa [prefixWord, tailWord_7116809, baseEnd_7116809] using wordTrace_append hprefix tailTrace_7116809
  have hstable : (prefixWord ++ tailWord_7116809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116809).length < 2 ^ (prefixWord ++ tailWord_7116809).sum := by decide
  have hdescent : baseEnd_7116809 < baseStart_7116809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116823 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 7]
def baseStart_7116823 : Nat := 118140960795 + 7116823 * 2 ^ 59
def prefixEnd_7116823 : Nat := 4983230072969 + 3 ^ 40 * 7116823 * 2
def baseEnd_7116823 : Nat := 406038992441434903442537

theorem tailTrace_7116823 : CollatzResearch.WordTrace tailWord_7116823 prefixEnd_7116823 406038992441434903442537 := by
  unfold tailWord_7116823
  simp only [CollatzResearch.WordTrace]
  refine ⟨259571859495973202446067123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173047906330648801630711415 259571859495973202446067123)
  ·
    refine ⟨389357789243959803669100685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259571859495973202446067123 389357789243959803669100685)
    ·
      refine ⟨146009170966484926375912757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389357789243959803669100685 146009170966484926375912757)
      ·
        refine ⟨13688359778107961847741821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146009170966484926375912757 13688359778107961847741821)
        ·
          refine ⟨5133134916790485692903183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13688359778107961847741821 5133134916790485692903183)
          ·
            refine ⟨7699702375185728539354775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5133134916790485692903183 7699702375185728539354775)
            ·
              refine ⟨11549553562778592809032163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7699702375185728539354775 11549553562778592809032163)
              ·
                refine ⟨17324330344167889213548245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11549553562778592809032163 17324330344167889213548245)
                ·
                  refine ⟨406038992441434903442537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17324330344167889213548245 406038992441434903442537)
                  ·
                    rfl

theorem cell23_7116823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 7].length) (baseStart_7116823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116823 prefixEnd_7116823 := by exact prefixLift 7116823
  have htrace : WordTrace (prefixWord ++ tailWord_7116823) baseStart_7116823 baseEnd_7116823 := by
    simpa [prefixWord, tailWord_7116823, baseEnd_7116823] using wordTrace_append hprefix tailTrace_7116823
  have hstable : (prefixWord ++ tailWord_7116823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116823).length < 2 ^ (prefixWord ++ tailWord_7116823).sum := by decide
  have hdescent : baseEnd_7116823 < baseStart_7116823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116829 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_7116829 : Nat := 118140960795 + 7116829 * 2 ^ 59
def prefixEnd_7116829 : Nat := 4983230072969 + 3 ^ 40 * 7116829 * 2
def baseEnd_7116829 : Nat := 3654354012856841107507805

theorem tailTrace_7116829 : CollatzResearch.WordTrace tailWord_7116829 prefixEnd_7116829 3654354012856841107507805 := by
  unfold tailWord_7116829
  simp only [CollatzResearch.WordTrace]
  refine ⟨259572078333951465470785541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173048052222634310313857027 259572078333951465470785541)
  ·
    refine ⟨48669764687615899775772289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259572078333951465470785541 48669764687615899775772289)
    ·
      refine ⟨36502323515711924831829217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48669764687615899775772289 36502323515711924831829217)
      ·
        refine ⟨27376742636783943623871913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36502323515711924831829217 27376742636783943623871913)
        ·
          refine ⟨20532556977587957717903935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27376742636783943623871913 20532556977587957717903935)
          ·
            refine ⟨30798835466381936576855903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20532556977587957717903935 30798835466381936576855903)
            ·
              refine ⟨46198253199572904865283855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30798835466381936576855903 46198253199572904865283855)
              ·
                refine ⟨69297379799359357297925783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46198253199572904865283855 69297379799359357297925783)
                ·
                  refine ⟨103946069699039035946888675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69297379799359357297925783 103946069699039035946888675)
                  ·
                    refine ⟨155919104548558553920333013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103946069699039035946888675 155919104548558553920333013)
                    ·
                      refine ⟨3654354012856841107507805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155919104548558553920333013 3654354012856841107507805)
                      ·
                        rfl

theorem cell23_7116829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_7116829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116829 prefixEnd_7116829 := by exact prefixLift 7116829
  have htrace : WordTrace (prefixWord ++ tailWord_7116829) baseStart_7116829 baseEnd_7116829 := by
    simpa [prefixWord, tailWord_7116829, baseEnd_7116829] using wordTrace_append hprefix tailTrace_7116829
  have hstable : (prefixWord ++ tailWord_7116829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116829).length < 2 ^ (prefixWord ++ tailWord_7116829).sum := by decide
  have hdescent : baseEnd_7116829 < baseStart_7116829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116859 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 3]
def baseStart_7116859 : Nat := 118140960795 + 7116859 * 2 ^ 59
def prefixEnd_7116859 : Nat := 4983230072969 + 3 ^ 40 * 7116859 * 2
def baseEnd_7116859 : Nat := 3654369417276475990132667

theorem tailTrace_7116859 : CollatzResearch.WordTrace tailWord_7116859 prefixEnd_7116859 3654369417276475990132667 := by
  unfold tailWord_7116859
  simp only [CollatzResearch.WordTrace]
  refine ⟨259573172523842780594377631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173048781682561853729585087 259573172523842780594377631)
  ·
    refine ⟨389359758785764170891566447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259573172523842780594377631 389359758785764170891566447)
    ·
      refine ⟨584039638178646256337349671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389359758785764170891566447 584039638178646256337349671)
      ·
        refine ⟨876059457267969384506024507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584039638178646256337349671 876059457267969384506024507)
        ·
          refine ⟨1314089185901954076759036761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876059457267969384506024507 1314089185901954076759036761)
          ·
            refine ⟨985566889426465557569277571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314089185901954076759036761 985566889426465557569277571)
            ·
              refine ⟨1478350334139698336353916357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985566889426465557569277571 1478350334139698336353916357)
              ·
                refine ⟨277190687651193438066359317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1478350334139698336353916357 277190687651193438066359317)
                ·
                  refine ⟨12993313483649692409360593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 277190687651193438066359317 12993313483649692409360593)
                  ·
                    refine ⟨9744985112737269307020445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12993313483649692409360593 9744985112737269307020445)
                    ·
                      refine ⟨3654369417276475990132667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9744985112737269307020445 3654369417276475990132667)
                      ·
                        rfl

theorem cell23_7116859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 3].length) (baseStart_7116859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116859 prefixEnd_7116859 := by exact prefixLift 7116859
  have htrace : WordTrace (prefixWord ++ tailWord_7116859) baseStart_7116859 baseEnd_7116859 := by
    simpa [prefixWord, tailWord_7116859, baseEnd_7116859] using wordTrace_append hprefix tailTrace_7116859
  have hstable : (prefixWord ++ tailWord_7116859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116859).length < 2 ^ (prefixWord ++ tailWord_7116859).sum := by decide
  have hdescent : baseEnd_7116859 < baseStart_7116859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116876 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 2, 2, 3]
def baseStart_7116876 : Nat := 118140960795 + 7116876 * 2 ^ 59
def prefixEnd_7116876 : Nat := 4983230072969 + 3 ^ 40 * 7116876 * 2
def baseEnd_7116876 : Nat := 3654378146447602423620089

theorem tailTrace_7116876 : CollatzResearch.WordTrace tailWord_7116876 prefixEnd_7116876 3654378146447602423620089 := by
  unfold tailWord_7116876
  simp only [CollatzResearch.WordTrace]
  refine ⟨129786896282390596248873241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173049195043187461665164321 129786896282390596248873241)
  ·
    refine ⟨97340172211792947186654931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129786896282390596248873241 97340172211792947186654931)
    ·
      refine ⟨146010258317689420779982397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97340172211792947186654931 146010258317689420779982397)
      ·
        refine ⟨54753846869133532792493399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146010258317689420779982397 54753846869133532792493399)
        ·
          refine ⟨82130770303700299188740099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54753846869133532792493399 82130770303700299188740099)
          ·
            refine ⟨123196155455550448783110149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82130770303700299188740099 123196155455550448783110149)
            ·
              refine ⟨23099279147915709146833153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123196155455550448783110149 23099279147915709146833153)
              ·
                refine ⟨17324459360936781860124865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23099279147915709146833153 17324459360936781860124865)
                ·
                  refine ⟨12993344520702586395093649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17324459360936781860124865 12993344520702586395093649)
                  ·
                    refine ⟨9745008390526939796320237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12993344520702586395093649 9745008390526939796320237)
                    ·
                      refine ⟨3654378146447602423620089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9745008390526939796320237 3654378146447602423620089)
                      ·
                        rfl

theorem cell23_7116876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_7116876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116876 prefixEnd_7116876 := by exact prefixLift 7116876
  have htrace : WordTrace (prefixWord ++ tailWord_7116876) baseStart_7116876 baseEnd_7116876 := by
    simpa [prefixWord, tailWord_7116876, baseEnd_7116876] using wordTrace_append hprefix tailTrace_7116876
  have hstable : (prefixWord ++ tailWord_7116876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116876).length < 2 ^ (prefixWord ++ tailWord_7116876).sum := by decide
  have hdescent : baseEnd_7116876 < baseStart_7116876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116973 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_7116973 : Nat := 118140960795 + 7116973 * 2 ^ 59
def prefixEnd_7116973 : Nat := 4983230072969 + 3 ^ 40 * 7116973 * 2
def baseEnd_7116973 : Nat := 1218142651357029514702381

theorem tailTrace_7116973 : CollatzResearch.WordTrace tailWord_7116973 prefixEnd_7116973 1218142651357029514702381 := by
  unfold tailWord_7116973
  simp only [CollatzResearch.WordTrace]
  refine ⟨259577330445429778064027573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173051553630286518709351715 259577330445429778064027573)
  ·
    refine ⟨24335374729259041693502585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259577330445429778064027573 24335374729259041693502585)
    ·
      refine ⟨18251531046944281270126939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24335374729259041693502585 18251531046944281270126939)
      ·
        refine ⟨27377296570416421905190409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18251531046944281270126939 27377296570416421905190409)
        ·
          refine ⟨20532972427812316428892807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27377296570416421905190409 20532972427812316428892807)
          ·
            refine ⟨30799458641718474643339211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20532972427812316428892807 30799458641718474643339211)
            ·
              refine ⟨46199187962577711965008817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30799458641718474643339211 46199187962577711965008817)
              ·
                refine ⟨34649390971933283973756613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46199187962577711965008817 34649390971933283973756613)
                ·
                  refine ⟨6496760807237490745079365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34649390971933283973756613 6496760807237490745079365)
                  ·
                    refine ⟨1218142651357029514702381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6496760807237490745079365 1218142651357029514702381)
                    ·
                      rfl

theorem cell23_7116973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_7116973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116973 prefixEnd_7116973 := by exact prefixLift 7116973
  have htrace : WordTrace (prefixWord ++ tailWord_7116973) baseStart_7116973 baseEnd_7116973 := by
    simpa [prefixWord, tailWord_7116973, baseEnd_7116973] using wordTrace_append hprefix tailTrace_7116973
  have hstable : (prefixWord ++ tailWord_7116973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116973).length < 2 ^ (prefixWord ++ tailWord_7116973).sum := by decide
  have hdescent : baseEnd_7116973 < baseStart_7116973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7116983 : List Nat := [1, 1, 3, 1, 4, 2, 2, 3, 1, 2, 3]
def baseStart_7116983 : Nat := 118140960795 + 7116983 * 2 ^ 59
def prefixEnd_7116983 : Nat := 4983230072969 + 3 ^ 40 * 7116983 * 2
def baseEnd_7116983 : Nat := 3654433088877633504982097

theorem tailTrace_7116983 : CollatzResearch.WordTrace tailWord_7116983 prefixEnd_7116983 3654433088877633504982097 := by
  unfold tailWord_7116983
  simp only [CollatzResearch.WordTrace]
  refine ⟨259577695175393549771891603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173051796783595699847927735 259577695175393549771891603)
  ·
    refine ⟨389366542763090324657837405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259577695175393549771891603 389366542763090324657837405)
    ·
      refine ⟨146012453536158871746689027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389366542763090324657837405 146012453536158871746689027)
      ·
        refine ⟨219018680304238307620033541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146012453536158871746689027 219018680304238307620033541)
        ·
          refine ⟨41066002557044682678756289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219018680304238307620033541 41066002557044682678756289)
          ·
            refine ⟨30799501917783512009067217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41066002557044682678756289 30799501917783512009067217)
            ·
              refine ⟨23099626438337634006800413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30799501917783512009067217 23099626438337634006800413)
              ·
                refine ⟨8662359914376612752550155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23099626438337634006800413 8662359914376612752550155)
                ·
                  refine ⟨12993539871564919128825233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8662359914376612752550155 12993539871564919128825233)
                  ·
                    refine ⟨9745154903673689346618925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12993539871564919128825233 9745154903673689346618925)
                    ·
                      refine ⟨3654433088877633504982097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9745154903673689346618925 3654433088877633504982097)
                      ·
                        rfl

theorem cell23_7116983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_7116983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7116983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7116983 prefixEnd_7116983 := by exact prefixLift 7116983
  have htrace : WordTrace (prefixWord ++ tailWord_7116983) baseStart_7116983 baseEnd_7116983 := by
    simpa [prefixWord, tailWord_7116983, baseEnd_7116983] using wordTrace_append hprefix tailTrace_7116983
  have hstable : (prefixWord ++ tailWord_7116983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7116983).length < 2 ^ (prefixWord ++ tailWord_7116983).sum := by decide
  have hdescent : baseEnd_7116983 < baseStart_7116983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7116983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117056 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 3]
def baseStart_7117056 : Nat := 118140960795 + 7117056 * 2 ^ 59
def prefixEnd_7117056 : Nat := 4983230072969 + 3 ^ 40 * 7117056 * 2
def baseEnd_7117056 : Nat := 3654470572965411719369261

theorem tailTrace_7117056 : CollatzResearch.WordTrace tailWord_7117056 prefixEnd_7117056 3654470572965411719369261 := by
  unfold tailWord_7117056
  simp only [CollatzResearch.WordTrace]
  refine ⟨129790178852064541619649511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173053571802752722159532681 129790178852064541619649511)
  ·
    refine ⟨194685268278096812429474267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129790178852064541619649511 194685268278096812429474267)
    ·
      refine ⟨292027902417145218644211401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194685268278096812429474267 292027902417145218644211401)
      ·
        refine ⟨219020926812858913983158551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292027902417145218644211401 219020926812858913983158551)
        ·
          refine ⟨328531390219288370974737827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219020926812858913983158551 328531390219288370974737827)
          ·
            refine ⟨492797085328932556462106741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328531390219288370974737827 492797085328932556462106741)
            ·
              refine ⟨46199726749587427168322507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 492797085328932556462106741 46199726749587427168322507)
              ·
                refine ⟨69299590124381140752483761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46199726749587427168322507 69299590124381140752483761)
                ·
                  refine ⟨51974692593285855564362821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69299590124381140752483761 51974692593285855564362821)
                  ·
                    refine ⟨9745254861241097918318029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51974692593285855564362821 9745254861241097918318029)
                    ·
                      refine ⟨3654470572965411719369261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9745254861241097918318029 3654470572965411719369261)
                      ·
                        rfl

theorem cell23_7117056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_7117056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117056 prefixEnd_7117056 := by exact prefixLift 7117056
  have htrace : WordTrace (prefixWord ++ tailWord_7117056) baseStart_7117056 baseEnd_7117056 := by
    simpa [prefixWord, tailWord_7117056, baseEnd_7117056] using wordTrace_append hprefix tailTrace_7117056
  have hstable : (prefixWord ++ tailWord_7117056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117056).length < 2 ^ (prefixWord ++ tailWord_7117056).sum := by decide
  have hdescent : baseEnd_7117056 < baseStart_7117056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117066 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_7117066 : Nat := 118140960795 + 7117066 * 2 ^ 59
def prefixEnd_7117066 : Nat := 4983230072969 + 3 ^ 40 * 7117066 * 2
def baseEnd_7117066 : Nat := 3654475707771956680244215

theorem tailTrace_7117066 : CollatzResearch.WordTrace tailWord_7117066 prefixEnd_7117066 3654475707771956680244215 := by
  unfold tailWord_7117066
  simp only [CollatzResearch.WordTrace]
  refine ⟨64895180608523213736790763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173053814956061903298108701 64895180608523213736790763)
  ·
    refine ⟨97342770912784820605186145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64895180608523213736790763 97342770912784820605186145)
    ·
      refine ⟨73007078184588615453889609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97342770912784820605186145 73007078184588615453889609)
      ·
        refine ⟨54755308638441461590417207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73007078184588615453889609 54755308638441461590417207)
        ·
          refine ⟨82132962957662192385625811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54755308638441461590417207 82132962957662192385625811)
          ·
            refine ⟨123199444436493288578438717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82132962957662192385625811 123199444436493288578438717)
            ·
              refine ⟨46199791663684983216914519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123199444436493288578438717 46199791663684983216914519)
              ·
                refine ⟨69299687495527474825371779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46199791663684983216914519 69299687495527474825371779)
                ·
                  refine ⟨103949531243291212238057669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69299687495527474825371779 103949531243291212238057669)
                  ·
                    refine ⟨19490537108117102294635813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103949531243291212238057669 19490537108117102294635813)
                    ·
                      refine ⟨3654475707771956680244215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19490537108117102294635813 3654475707771956680244215)
                      ·
                        rfl

theorem cell23_7117066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_7117066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117066 prefixEnd_7117066 := by exact prefixLift 7117066
  have htrace : WordTrace (prefixWord ++ tailWord_7117066) baseStart_7117066 baseEnd_7117066 := by
    simpa [prefixWord, tailWord_7117066, baseEnd_7117066] using wordTrace_append hprefix tailTrace_7117066
  have hstable : (prefixWord ++ tailWord_7117066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117066).length < 2 ^ (prefixWord ++ tailWord_7117066).sum := by decide
  have hdescent : baseEnd_7117066 < baseStart_7117066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117070 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2]
def baseStart_7117070 : Nat := 118140960795 + 7117070 * 2 ^ 59
def prefixEnd_7117070 : Nat := 4983230072969 + 3 ^ 40 * 7117070 * 2
def baseEnd_7117070 : Nat := 3654477761694574664594197

theorem tailTrace_7117070 : CollatzResearch.WordTrace tailWord_7117070 prefixEnd_7117070 3654477761694574664594197 := by
  unfold tailWord_7117070
  simp only [CollatzResearch.WordTrace]
  refine ⟨32447608540759795453788583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173053912217385575753539109 32447608540759795453788583)
  ·
    refine ⟨48671412811139693180682875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32447608540759795453788583 48671412811139693180682875)
    ·
      refine ⟨73007119216709539771024313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48671412811139693180682875 73007119216709539771024313)
      ·
        refine ⟨54755339412532154828268235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73007119216709539771024313 54755339412532154828268235)
        ·
          refine ⟨82133009118798232242402353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54755339412532154828268235 82133009118798232242402353)
          ·
            refine ⟨61599756839098674181801765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82133009118798232242402353 61599756839098674181801765)
            ·
              refine ⟨11549954407331001409087831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61599756839098674181801765 11549954407331001409087831)
              ·
                refine ⟨17324931610996502113631747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11549954407331001409087831 17324931610996502113631747)
                ·
                  refine ⟨25987397416494753170447621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17324931610996502113631747 25987397416494753170447621)
                  ·
                    refine ⟨4872637015592766219458929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25987397416494753170447621 4872637015592766219458929)
                    ·
                      refine ⟨3654477761694574664594197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872637015592766219458929 3654477761694574664594197)
                      ·
                        rfl

theorem cell23_7117070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_7117070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117070 prefixEnd_7117070 := by exact prefixLift 7117070
  have htrace : WordTrace (prefixWord ++ tailWord_7117070) baseStart_7117070 baseEnd_7117070 := by
    simpa [prefixWord, tailWord_7117070, baseEnd_7117070] using wordTrace_append hprefix tailTrace_7117070
  have hstable : (prefixWord ++ tailWord_7117070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117070).length < 2 ^ (prefixWord ++ tailWord_7117070).sum := by decide
  have hdescent : baseEnd_7117070 < baseStart_7117070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117116 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_7117116 : Nat := 118140960795 + 7117116 * 2 ^ 59
def prefixEnd_7117116 : Nat := 4983230072969 + 3 ^ 40 * 7117116 * 2
def baseEnd_7117116 : Nat := 3654501381804681484618985

theorem tailTrace_7117116 : CollatzResearch.WordTrace tailWord_7117116 prefixEnd_7117116 3654501381804681484618985 := by
  unfold tailWord_7117116
  simp only [CollatzResearch.WordTrace]
  refine ⟨129791273041955856743241601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173055030722607808990988801 129791273041955856743241601)
  ·
    refine ⟨97343454781466892557431201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129791273041955856743241601 97343454781466892557431201)
    ·
      refine ⟨73007591086100169418073401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97343454781466892557431201 73007591086100169418073401)
      ·
        refine ⟨54755693314575127063555051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73007591086100169418073401 54755693314575127063555051)
        ·
          refine ⟨82133539971862690595332577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54755693314575127063555051 82133539971862690595332577)
          ·
            refine ⟨61600154978897017946499433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82133539971862690595332577 61600154978897017946499433)
            ·
              refine ⟨46200116234172763459874575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61600154978897017946499433 46200116234172763459874575)
              ·
                refine ⟨69300174351259145189811863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46200116234172763459874575 69300174351259145189811863)
                ·
                  refine ⟨103950261526888717784717795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69300174351259145189811863 103950261526888717784717795)
                  ·
                    refine ⟨155925392290333076677076693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103950261526888717784717795 155925392290333076677076693)
                    ·
                      refine ⟨3654501381804681484618985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155925392290333076677076693 3654501381804681484618985)
                      ·
                        rfl

theorem cell23_7117116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_7117116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117116 prefixEnd_7117116 := by exact prefixLift 7117116
  have htrace : WordTrace (prefixWord ++ tailWord_7117116) baseStart_7117116 baseEnd_7117116 := by
    simpa [prefixWord, tailWord_7117116, baseEnd_7117116] using wordTrace_append hprefix tailTrace_7117116
  have hstable : (prefixWord ++ tailWord_7117116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117116).length < 2 ^ (prefixWord ++ tailWord_7117116).sum := by decide
  have hdescent : baseEnd_7117116 < baseStart_7117116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117121 : List Nat := [1, 2, 5, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_7117121 : Nat := 118140960795 + 7117121 * 2 ^ 59
def prefixEnd_7117121 : Nat := 4983230072969 + 3 ^ 40 * 7117121 * 2
def baseEnd_7117121 : Nat := 3654503949207953965056463

theorem tailTrace_7117121 : CollatzResearch.WordTrace tailWord_7117121 prefixEnd_7117121 3654503949207953965056463 := by
  unfold tailWord_7117121
  simp only [CollatzResearch.WordTrace]
  refine ⟨259582728448893599340415217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173055152299262399560276811 259582728448893599340415217)
  ·
    refine ⟨194687046336670199505311413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259582728448893599340415217 194687046336670199505311413)
    ·
      refine ⟨18251910594062831203622945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194687046336670199505311413 18251910594062831203622945)
      ·
        refine ⟨13688932945547123402717209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18251910594062831203622945 13688932945547123402717209)
        ·
          refine ⟨10266699709160342552037907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13688932945547123402717209 10266699709160342552037907)
          ·
            refine ⟨15400049563740513828056861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10266699709160342552037907 15400049563740513828056861)
            ·
              refine ⟨5775018586402692685521323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15400049563740513828056861 5775018586402692685521323)
              ·
                refine ⟨8662527879604039028281985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5775018586402692685521323 8662527879604039028281985)
                ·
                  refine ⟨6496895909703029271211489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8662527879604039028281985 6496895909703029271211489)
                  ·
                    refine ⟨4872671932277271953408617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6496895909703029271211489 4872671932277271953408617)
                    ·
                      refine ⟨3654503949207953965056463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872671932277271953408617 3654503949207953965056463)
                      ·
                        rfl

theorem cell23_7117121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_7117121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117121 prefixEnd_7117121 := by exact prefixLift 7117121
  have htrace : WordTrace (prefixWord ++ tailWord_7117121) baseStart_7117121 baseEnd_7117121 := by
    simpa [prefixWord, tailWord_7117121, baseEnd_7117121] using wordTrace_append hprefix tailTrace_7117121
  have hstable : (prefixWord ++ tailWord_7117121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117121).length < 2 ^ (prefixWord ++ tailWord_7117121).sum := by decide
  have hdescent : baseEnd_7117121 < baseStart_7117121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117143 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 4]
def baseStart_7117143 : Nat := 118140960795 + 7117143 * 2 ^ 59
def prefixEnd_7117143 : Nat := 4983230072969 + 3 ^ 40 * 7117143 * 2
def baseEnd_7117143 : Nat := 3654515245782352878981361

theorem tailTrace_7117143 : CollatzResearch.WordTrace tailWord_7117143 prefixEnd_7117143 3654515245782352878981361 := by
  unfold tailWord_7117143
  simp only [CollatzResearch.WordTrace]
  refine ⟨259583530854813897097716083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173055687236542598065144055 259583530854813897097716083)
  ·
    refine ⟨389375296282220845646574125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259583530854813897097716083 389375296282220845646574125)
    ·
      refine ⟨146015736105832817117465297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389375296282220845646574125 146015736105832817117465297)
      ·
        refine ⟨109511802079374612838098973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146015736105832817117465297 109511802079374612838098973)
        ·
          refine ⟨41066925779765479814287115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109511802079374612838098973 41066925779765479814287115)
          ·
            refine ⟨61600388669648219721430673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41066925779765479814287115 61600388669648219721430673)
            ·
              refine ⟨46200291502236164791073005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61600388669648219721430673 46200291502236164791073005)
              ·
                refine ⟨17325109313338561796652377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46200291502236164791073005 17325109313338561796652377)
                ·
                  refine ⟨12993831985003921347489283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17325109313338561796652377 12993831985003921347489283)
                  ·
                    refine ⟨19490747977505882021233925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12993831985003921347489283 19490747977505882021233925)
                    ·
                      refine ⟨3654515245782352878981361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19490747977505882021233925 3654515245782352878981361)
                      ·
                        rfl

theorem cell23_7117143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_7117143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117143 prefixEnd_7117143 := by exact prefixLift 7117143
  have htrace : WordTrace (prefixWord ++ tailWord_7117143) baseStart_7117143 baseEnd_7117143 := by
    simpa [prefixWord, tailWord_7117143, baseEnd_7117143] using wordTrace_append hprefix tailTrace_7117143
  have hstable : (prefixWord ++ tailWord_7117143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117143).length < 2 ^ (prefixWord ++ tailWord_7117143).sum := by decide
  have hdescent : baseEnd_7117143 < baseStart_7117143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117146 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_7117146 : Nat := 118140960795 + 7117146 * 2 ^ 59
def prefixEnd_7117146 : Nat := 4983230072969 + 3 ^ 40 * 7117146 * 2
def baseEnd_7117146 : Nat := 3654516786224316367243847

theorem tailTrace_7117146 : CollatzResearch.WordTrace tailWord_7117146 prefixEnd_7117146 3654516786224316367243847 := by
  unfold tailWord_7117146
  simp only [CollatzResearch.WordTrace]
  refine ⟨64895910068450757152518823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173055760182535352406716861 64895910068450757152518823)
  ·
    refine ⟨97343865102676135728778235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64895910068450757152518823 97343865102676135728778235)
    ·
      refine ⟨146015797654014203593167353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97343865102676135728778235 146015797654014203593167353)
      ·
        refine ⟨109511848240510652694875515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146015797654014203593167353 109511848240510652694875515)
        ·
          refine ⟨164267772360765979042313273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109511848240510652694875515 164267772360765979042313273)
          ·
            refine ⟨123200829270574484281734955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164267772360765979042313273 123200829270574484281734955)
            ·
              refine ⟨184801243905861726422602433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123200829270574484281734955 184801243905861726422602433)
              ·
                refine ⟨138600932929396294816951825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184801243905861726422602433 138600932929396294816951825)
                ·
                  refine ⟨103950699697047221112713869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138600932929396294816951825 103950699697047221112713869)
                  ·
                    refine ⟨38981512386392707917267701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103950699697047221112713869 38981512386392707917267701)
                    ·
                      refine ⟨3654516786224316367243847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38981512386392707917267701 3654516786224316367243847)
                      ·
                        rfl

theorem cell23_7117146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_7117146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117146 prefixEnd_7117146 := by exact prefixLift 7117146
  have htrace : WordTrace (prefixWord ++ tailWord_7117146) baseStart_7117146 baseEnd_7117146 := by
    simpa [prefixWord, tailWord_7117146, baseEnd_7117146] using wordTrace_append hprefix tailTrace_7117146
  have hstable : (prefixWord ++ tailWord_7117146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117146).length < 2 ^ (prefixWord ++ tailWord_7117146).sum := by decide
  have hdescent : baseEnd_7117146 < baseStart_7117146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117160 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_7117160 : Nat := 118140960795 + 7117160 * 2 ^ 59
def prefixEnd_7117160 : Nat := 4983230072969 + 3 ^ 40 * 7117160 * 2
def baseEnd_7117160 : Nat := 3654523974953479312468783

theorem tailTrace_7117160 : CollatzResearch.WordTrace tailWord_7117160 prefixEnd_7117160 3654523974953479312468783 := by
  unfold tailWord_7117160
  simp only [CollatzResearch.WordTrace]
  refine ⟨129792075447876154500542467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173056100597168206000723289 129792075447876154500542467)
  ·
    refine ⟨194688113171814231750813701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129792075447876154500542467 194688113171814231750813701)
    ·
      refine ⟨36504021219715168453277569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194688113171814231750813701 36504021219715168453277569)
      ·
        refine ⟨27378015914786376339958177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36504021219715168453277569 27378015914786376339958177)
        ·
          refine ⟨20533511936089782254968633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27378015914786376339958177 20533511936089782254968633)
          ·
            refine ⟨15400133952067336691226475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20533511936089782254968633 15400133952067336691226475)
            ·
              refine ⟨23100200928101005036839713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15400133952067336691226475 23100200928101005036839713)
              ·
                refine ⟨17325150696075753777629785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23100200928101005036839713 17325150696075753777629785)
                ·
                  refine ⟨12993863022056815333222339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17325150696075753777629785 12993863022056815333222339)
                  ·
                    refine ⟨19490794533085222999833509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12993863022056815333222339 19490794533085222999833509)
                    ·
                      refine ⟨3654523974953479312468783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19490794533085222999833509 3654523974953479312468783)
                      ·
                        rfl

theorem cell23_7117160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_7117160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117160 prefixEnd_7117160 := by exact prefixLift 7117160
  have htrace : WordTrace (prefixWord ++ tailWord_7117160) baseStart_7117160 baseEnd_7117160 := by
    simpa [prefixWord, tailWord_7117160, baseEnd_7117160] using wordTrace_append hprefix tailTrace_7117160
  have hstable : (prefixWord ++ tailWord_7117160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117160).length < 2 ^ (prefixWord ++ tailWord_7117160).sum := by decide
  have hdescent : baseEnd_7117160 < baseStart_7117160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117163 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 3]
def baseStart_7117163 : Nat := 118140960795 + 7117163 * 2 ^ 59
def prefixEnd_7117163 : Nat := 4983230072969 + 3 ^ 40 * 7117163 * 2
def baseEnd_7117163 : Nat := 3654525515395442800731269

theorem tailTrace_7117163 : CollatzResearch.WordTrace tailWord_7117163 prefixEnd_7117163 3654525515395442800731269 := by
  unfold tailWord_7117163
  simp only [CollatzResearch.WordTrace]
  refine ⟨259584260314741440513444143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173056173543160960342296095 259584260314741440513444143)
  ·
    refine ⟨389376390472112160770166215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259584260314741440513444143 389376390472112160770166215)
    ·
      refine ⟨584064585708168241155249323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389376390472112160770166215 584064585708168241155249323)
      ·
        refine ⟨876096878562252361732873985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584064585708168241155249323 876096878562252361732873985)
        ·
          refine ⟨657072658921689271299655489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 876096878562252361732873985 657072658921689271299655489)
          ·
            refine ⟨492804494191266953474741617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657072658921689271299655489 492804494191266953474741617)
            ·
              refine ⟨369603370643450215106056213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492804494191266953474741617 369603370643450215106056213)
              ·
                refine ⟨17325157998911728833096385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 369603370643450215106056213 17325157998911728833096385)
                ·
                  refine ⟨12993868499183796624822289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17325157998911728833096385 12993868499183796624822289)
                  ·
                    refine ⟨9745401374387847468616717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12993868499183796624822289 9745401374387847468616717)
                    ·
                      refine ⟨3654525515395442800731269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9745401374387847468616717 3654525515395442800731269)
                      ·
                        rfl

theorem cell23_7117163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 3].length) (baseStart_7117163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117163 prefixEnd_7117163 := by exact prefixLift 7117163
  have htrace : WordTrace (prefixWord ++ tailWord_7117163) baseStart_7117163 baseEnd_7117163 := by
    simpa [prefixWord, tailWord_7117163, baseEnd_7117163] using wordTrace_append hprefix tailTrace_7117163
  have hstable : (prefixWord ++ tailWord_7117163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117163).length < 2 ^ (prefixWord ++ tailWord_7117163).sum := by decide
  have hdescent : baseEnd_7117163 < baseStart_7117163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117170 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_7117170 : Nat := 118140960795 + 7117170 * 2 ^ 59
def prefixEnd_7117170 : Nat := 4983230072969 + 3 ^ 40 * 7117170 * 2
def baseEnd_7117170 : Nat := 1218176369920008091114579

theorem tailTrace_7117170 : CollatzResearch.WordTrace tailWord_7117170 prefixEnd_7117170 1218176369920008091114579 := by
  unfold tailWord_7117170
  simp only [CollatzResearch.WordTrace]
  refine ⟨64896128906429020177237241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173056343750477387139299309 64896128906429020177237241)
  ·
    refine ⟨48672096679821765132927931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64896128906429020177237241 48672096679821765132927931)
    ·
      refine ⟨73008145019732647699391897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48672096679821765132927931 73008145019732647699391897)
      ·
        refine ⟨54756108764799485774543923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73008145019732647699391897 54756108764799485774543923)
        ·
          refine ⟨82134163147199228661815885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54756108764799485774543923 82134163147199228661815885)
          ·
            refine ⟨30800311180199710748180957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82134163147199228661815885 30800311180199710748180957)
            ·
              refine ⟨11550116692574891530567859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30800311180199710748180957 11550116692574891530567859)
              ·
                refine ⟨17325175038862337295851789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11550116692574891530567859 17325175038862337295851789)
                ·
                  refine ⟨6496940639573376485944421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17325175038862337295851789 6496940639573376485944421)
                  ·
                    refine ⟨1218176369920008091114579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6496940639573376485944421 1218176369920008091114579)
                    ·
                      rfl

theorem cell23_7117170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_7117170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117170 prefixEnd_7117170 := by exact prefixLift 7117170
  have htrace : WordTrace (prefixWord ++ tailWord_7117170) baseStart_7117170 baseEnd_7117170 := by
    simpa [prefixWord, tailWord_7117170, baseEnd_7117170] using wordTrace_append hprefix tailTrace_7117170
  have hstable : (prefixWord ++ tailWord_7117170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117170).length < 2 ^ (prefixWord ++ tailWord_7117170).sum := by decide
  have hdescent : baseEnd_7117170 < baseStart_7117170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117217 : List Nat := [1, 2, 3, 5, 1, 1, 2, 2, 6]
def baseStart_7117217 : Nat := 118140960795 + 7117217 * 2 ^ 59
def prefixEnd_7117217 : Nat := 4983230072969 + 3 ^ 40 * 7117217 * 2
def baseEnd_7117217 : Nat := 406061471483420621050669

theorem tailTrace_7117217 : CollatzResearch.WordTrace tailWord_7117217 prefixEnd_7117217 406061471483420621050669 := by
  unfold tailWord_7117217
  simp only [CollatzResearch.WordTrace]
  refine ⟨259586229856545807735909905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173057486571030538490606603 259586229856545807735909905)
  ·
    refine ⟨194689672392409355801932429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259586229856545807735909905 194689672392409355801932429)
    ·
      refine ⟨73008627147153508425724661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194689672392409355801932429 73008627147153508425724661)
      ·
        refine ⟨6844558795045641414911687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73008627147153508425724661 6844558795045641414911687)
        ·
          refine ⟨10266838192568462122367531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6844558795045641414911687 10266838192568462122367531)
          ·
            refine ⟨15400257288852693183551297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10266838192568462122367531 15400257288852693183551297)
            ·
              refine ⟨11550192966639519887663473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15400257288852693183551297 11550192966639519887663473)
              ·
                refine ⟨8662644724979639915747605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11550192966639519887663473 8662644724979639915747605)
                ·
                  refine ⟨406061471483420621050669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8662644724979639915747605 406061471483420621050669)
                  ·
                    rfl

theorem cell23_7117217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 6].length) (baseStart_7117217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117217 prefixEnd_7117217 := by exact prefixLift 7117217
  have htrace : WordTrace (prefixWord ++ tailWord_7117217) baseStart_7117217 baseEnd_7117217 := by
    simpa [prefixWord, tailWord_7117217, baseEnd_7117217] using wordTrace_append hprefix tailTrace_7117217
  have hstable : (prefixWord ++ tailWord_7117217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117217).length < 2 ^ (prefixWord ++ tailWord_7117217).sum := by decide
  have hdescent : baseEnd_7117217 < baseStart_7117217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117294 : List Nat := [4, 1, 2, 1, 2, 3, 3, 1, 2, 4]
def baseStart_7117294 : Nat := 118140960795 + 7117294 * 2 ^ 59
def prefixEnd_7117294 : Nat := 4983230072969 + 3 ^ 40 * 7117294 * 2
def baseEnd_7117294 : Nat := 1218197593787060596064389

theorem tailTrace_7117294 : CollatzResearch.WordTrace tailWord_7117294 prefixEnd_7117294 1218197593787060596064389 := by
  unfold tailWord_7117294
  simp only [CollatzResearch.WordTrace]
  refine ⟨32448629784658356235807867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173059358851511233257641957 32448629784658356235807867)
  ·
    refine ⟨48672944676987534353711801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32448629784658356235807867 48672944676987534353711801)
    ·
      refine ⟨36504708507740650765283851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48672944676987534353711801 36504708507740650765283851)
      ·
        refine ⟨54757062761610976147925777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36504708507740650765283851 54757062761610976147925777)
        ·
          refine ⟨41067797071208232110944333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54757062761610976147925777 41067797071208232110944333)
          ·
            refine ⟨15400423901703087041604125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41067797071208232110944333 15400423901703087041604125)
            ·
              refine ⟨5775158963138657640601547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15400423901703087041604125 5775158963138657640601547)
              ·
                refine ⟨8662738444707986460902321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5775158963138657640601547 8662738444707986460902321)
                ·
                  refine ⟨6497053833530989845676741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8662738444707986460902321 6497053833530989845676741)
                  ·
                    refine ⟨1218197593787060596064389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6497053833530989845676741 1218197593787060596064389)
                    ·
                      rfl

theorem cell23_7117294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_7117294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117294 prefixEnd_7117294 := by exact prefixLift 7117294
  have htrace : WordTrace (prefixWord ++ tailWord_7117294) baseStart_7117294 baseEnd_7117294 := by
    simpa [prefixWord, tailWord_7117294, baseEnd_7117294] using wordTrace_append hprefix tailTrace_7117294
  have hstable : (prefixWord ++ tailWord_7117294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117294).length < 2 ^ (prefixWord ++ tailWord_7117294).sum := by decide
  have hdescent : baseEnd_7117294 < baseStart_7117294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117335 : List Nat := [1, 1, 3, 6, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7117335 : Nat := 118140960795 + 7117335 * 2 ^ 59
def prefixEnd_7117335 : Nat := 4983230072969 + 3 ^ 40 * 7117335 * 2
def baseEnd_7117335 : Nat := 3654613834068016127780479

theorem tailTrace_7117335 : CollatzResearch.WordTrace tailWord_7117335 prefixEnd_7117335 3654613834068016127780479 := by
  unfold tailWord_7117335
  simp only [CollatzResearch.WordTrace]
  refine ⟨259590533670118313888705459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173060355780078875925803639 259590533670118313888705459)
  ·
    refine ⟨389385800505177470833058189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259590533670118313888705459 389385800505177470833058189)
    ·
      refine ⟨146019675189441551562396821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389385800505177470833058189 146019675189441551562396821)
      ·
        refine ⟨6844672274505072729487351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146019675189441551562396821 6844672274505072729487351)
        ·
          refine ⟨10267008411757609094231027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6844672274505072729487351 10267008411757609094231027)
          ·
            refine ⟨15400512617636413641346541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10267008411757609094231027 15400512617636413641346541)
            ·
              refine ⟨5775192231613655115504953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15400512617636413641346541 5775192231613655115504953)
              ·
                refine ⟨4331394173710241336628715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5775192231613655115504953 4331394173710241336628715)
                ·
                  refine ⟨6497091260565362004943073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4331394173710241336628715 6497091260565362004943073)
                  ·
                    refine ⟨4872818445424021503707305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6497091260565362004943073 4872818445424021503707305)
                    ·
                      refine ⟨3654613834068016127780479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872818445424021503707305 3654613834068016127780479)
                      ·
                        rfl

theorem cell23_7117335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7117335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117335 prefixEnd_7117335 := by exact prefixLift 7117335
  have htrace : WordTrace (prefixWord ++ tailWord_7117335) baseStart_7117335 baseEnd_7117335 := by
    simpa [prefixWord, tailWord_7117335, baseEnd_7117335] using wordTrace_append hprefix tailTrace_7117335
  have hstable : (prefixWord ++ tailWord_7117335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117335).length < 2 ^ (prefixWord ++ tailWord_7117335).sum := by decide
  have hdescent : baseEnd_7117335 < baseStart_7117335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117343 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 5]
def baseStart_7117343 : Nat := 118140960795 + 7117343 * 2 ^ 59
def prefixEnd_7117343 : Nat := 4983230072969 + 3 ^ 40 * 7117343 * 2
def baseEnd_7117343 : Nat := 3654617941913252096480441

theorem tailTrace_7117343 : CollatzResearch.WordTrace tailWord_7117343 prefixEnd_7117343 3654617941913252096480441 := by
  unfold tailWord_7117343
  simp only [CollatzResearch.WordTrace]
  refine ⟨259590825454089331254996683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173060550302726220836664455 259590825454089331254996683)
  ·
    refine ⟨389386238181133996882495025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259590825454089331254996683 389386238181133996882495025)
    ·
      refine ⟨292039678635850497661871269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389386238181133996882495025 292039678635850497661871269)
      ·
        refine ⟨54757439744221968311600863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292039678635850497661871269 54757439744221968311600863)
        ·
          refine ⟨82136159616332952467401295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54757439744221968311600863 82136159616332952467401295)
          ·
            refine ⟨123204239424499428701101943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82136159616332952467401295 123204239424499428701101943)
            ·
              refine ⟨184806359136749143051652915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123204239424499428701101943 184806359136749143051652915)
              ·
                refine ⟨277209538705123714577479373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184806359136749143051652915 277209538705123714577479373)
                ·
                  refine ⟨103953577014421392966554765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277209538705123714577479373 103953577014421392966554765)
                  ·
                    refine ⟨38982591380408022362458037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103953577014421392966554765 38982591380408022362458037)
                    ·
                      refine ⟨3654617941913252096480441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38982591380408022362458037 3654617941913252096480441)
                      ·
                        rfl

theorem cell23_7117343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_7117343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117343 prefixEnd_7117343 := by exact prefixLift 7117343
  have htrace : WordTrace (prefixWord ++ tailWord_7117343) baseStart_7117343 baseEnd_7117343 := by
    simpa [prefixWord, tailWord_7117343, baseEnd_7117343] using wordTrace_append hprefix tailTrace_7117343
  have hstable : (prefixWord ++ tailWord_7117343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117343).length < 2 ^ (prefixWord ++ tailWord_7117343).sum := by decide
  have hdescent : baseEnd_7117343 < baseStart_7117343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117363 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 9]
def baseStart_7117363 : Nat := 118140960795 + 7117363 * 2 ^ 59
def prefixEnd_7117363 : Nat := 4983230072969 + 3 ^ 40 * 7117363 * 2
def baseEnd_7117363 : Nat := 406069801280704668692261

theorem tailTrace_7117363 : CollatzResearch.WordTrace tailWord_7117363 prefixEnd_7117363 406069801280704668692261 := by
  unfold tailWord_7117363
  simp only [CollatzResearch.WordTrace]
  refine ⟨259591554914016874670724743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173061036609344583113816495 259591554914016874670724743)
  ·
    refine ⟨389387332371025312006087115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259591554914016874670724743 389387332371025312006087115)
    ·
      refine ⟨584080998556537968009130673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389387332371025312006087115 584080998556537968009130673)
      ·
        refine ⟨438060748917403476006848005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 584080998556537968009130673 438060748917403476006848005)
        ·
          refine ⟨82136390422013151751284001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 438060748917403476006848005 82136390422013151751284001)
          ·
            refine ⟨61602292816509863813463001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82136390422013151751284001 61602292816509863813463001)
            ·
              refine ⟨46201719612382397860097251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61602292816509863813463001 46201719612382397860097251)
              ·
                refine ⟨69302579418573596790145877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46201719612382397860097251 69302579418573596790145877)
                ·
                  refine ⟨406069801280704668692261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69302579418573596790145877 406069801280704668692261)
                  ·
                    rfl

theorem cell23_7117363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 9].length) (baseStart_7117363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117363 prefixEnd_7117363 := by exact prefixLift 7117363
  have htrace : WordTrace (prefixWord ++ tailWord_7117363) baseStart_7117363 baseEnd_7117363 := by
    simpa [prefixWord, tailWord_7117363, baseEnd_7117363] using wordTrace_append hprefix tailTrace_7117363
  have hstable : (prefixWord ++ tailWord_7117363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117363).length < 2 ^ (prefixWord ++ tailWord_7117363).sum := by decide
  have hdescent : baseEnd_7117363 < baseStart_7117363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117447 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 4, 4, 2]
def baseStart_7117447 : Nat := 118140960795 + 7117447 * 2 ^ 59
def prefixEnd_7117447 : Nat := 4983230072969 + 3 ^ 40 * 7117447 * 2
def baseEnd_7117447 : Nat := 3654671343901319689579963

theorem tailTrace_7117447 : CollatzResearch.WordTrace tailWord_7117447 prefixEnd_7117447 3654671343901319689579963 := by
  unfold tailWord_7117447
  simp only [CollatzResearch.WordTrace]
  refine ⟨259594618645712557016782595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173063079097141704677855063 259594618645712557016782595)
  ·
    refine ⟨389391927968568835525173893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259594618645712557016782595 389391927968568835525173893)
    ·
      refine ⟨73010986494106656660970105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389391927968568835525173893 73010986494106656660970105)
      ·
        refine ⟨54758239870579992495727579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73010986494106656660970105 54758239870579992495727579)
        ·
          refine ⟨82137359805869988743591369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54758239870579992495727579 82137359805869988743591369)
          ·
            refine ⟨61603019854402491557693527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82137359805869988743591369 61603019854402491557693527)
            ·
              refine ⟨92404529781603737336540291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61603019854402491557693527 92404529781603737336540291)
              ·
                refine ⟨138606794672405606004810437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92404529781603737336540291 138606794672405606004810437)
                ·
                  refine ⟨25988774001076051125901957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138606794672405606004810437 25988774001076051125901957)
                  ·
                    refine ⟨4872895125201759586106617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25988774001076051125901957 4872895125201759586106617)
                    ·
                      refine ⟨3654671343901319689579963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872895125201759586106617 3654671343901319689579963)
                      ·
                        rfl

theorem cell23_7117447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_7117447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117447 prefixEnd_7117447 := by exact prefixLift 7117447
  have htrace : WordTrace (prefixWord ++ tailWord_7117447) baseStart_7117447 baseEnd_7117447 := by
    simpa [prefixWord, tailWord_7117447, baseEnd_7117447] using wordTrace_append hprefix tailTrace_7117447
  have hstable : (prefixWord ++ tailWord_7117447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117447).length < 2 ^ (prefixWord ++ tailWord_7117447).sum := by decide
  have hdescent : baseEnd_7117447 < baseStart_7117447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117491 : List Nat := [1, 1, 1, 2, 3, 6, 1, 3, 1, 4]
def baseStart_7117491 : Nat := 118140960795 + 7117491 * 2 ^ 59
def prefixEnd_7117491 : Nat := 4983230072969 + 3 ^ 40 * 7117491 * 2
def baseEnd_7117491 : Nat := 1218231312350039172476587

theorem tailTrace_7117491 : CollatzResearch.WordTrace tailWord_7117491 prefixEnd_7117491 1218231312350039172476587 := by
  unfold tailWord_7117491
  simp only [CollatzResearch.WordTrace]
  refine ⟨259596223457553152531384327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173064148971702101687589551 259596223457553152531384327)
  ·
    refine ⟨389394335186329728797076491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259596223457553152531384327 389394335186329728797076491)
    ·
      refine ⟨584091502779494593195614737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389394335186329728797076491 584091502779494593195614737)
      ·
        refine ⟨438068627084620944896711053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 584091502779494593195614737 438068627084620944896711053)
        ·
          refine ⟨164275735156732854336266645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438068627084620944896711053 164275735156732854336266645)
          ·
            refine ⟨7700425085471852547012499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 164275735156732854336266645 7700425085471852547012499)
            ·
              refine ⟨11550637628207778820518749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7700425085471852547012499 11550637628207778820518749)
              ·
                refine ⟨4331489110577917057694531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11550637628207778820518749 4331489110577917057694531)
                ·
                  refine ⟨6497233665866875586541797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4331489110577917057694531 6497233665866875586541797)
                  ·
                    refine ⟨1218231312350039172476587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6497233665866875586541797 1218231312350039172476587)
                    ·
                      rfl

theorem cell23_7117491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 1, 4].length) (baseStart_7117491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117491 prefixEnd_7117491 := by exact prefixLift 7117491
  have htrace : WordTrace (prefixWord ++ tailWord_7117491) baseStart_7117491 baseEnd_7117491 := by
    simpa [prefixWord, tailWord_7117491, baseEnd_7117491] using wordTrace_append hprefix tailTrace_7117491
  have hstable : (prefixWord ++ tailWord_7117491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117491).length < 2 ^ (prefixWord ++ tailWord_7117491).sum := by decide
  have hdescent : baseEnd_7117491 < baseStart_7117491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117508 : List Nat := [2, 3, 3, 1, 1, 3, 3, 2, 1, 4]
def baseStart_7117508 : Nat := 118140960795 + 7117508 * 2 ^ 59
def prefixEnd_7117508 : Nat := 4983230072969 + 3 ^ 40 * 7117508 * 2
def baseEnd_7117508 : Nat := 1218234222073747983639061

theorem tailTrace_7117508 : CollatzResearch.WordTrace tailWord_7117508 prefixEnd_7117508 1218234222073747983639061 := by
  unfold tailWord_7117508
  simp only [CollatzResearch.WordTrace]
  refine ⟨129798421749245782217376589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173064562332327709623168785 129798421749245782217376589)
  ·
    refine ⟨48674408155967168331516221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129798421749245782217376589 48674408155967168331516221)
    ·
      refine ⟨18252903058487688124318583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48674408155967168331516221 18252903058487688124318583)
      ·
        refine ⟨27379354587731532186477875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18252903058487688124318583 27379354587731532186477875)
        ·
          refine ⟨41069031881597298279716813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27379354587731532186477875 41069031881597298279716813)
          ·
            refine ⟨15400886955598986854893805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41069031881597298279716813 15400886955598986854893805)
            ·
              refine ⟨5775332608349620070585177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15400886955598986854893805 5775332608349620070585177)
              ·
                refine ⟨4331499456262215052938883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5775332608349620070585177 4331499456262215052938883)
                ·
                  refine ⟨6497249184393322579408325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4331499456262215052938883 6497249184393322579408325)
                  ·
                    refine ⟨1218234222073747983639061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6497249184393322579408325 1218234222073747983639061)
                    ·
                      rfl

theorem cell23_7117508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_7117508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117508 prefixEnd_7117508 := by exact prefixLift 7117508
  have htrace : WordTrace (prefixWord ++ tailWord_7117508) baseStart_7117508 baseEnd_7117508 := by
    simpa [prefixWord, tailWord_7117508, baseEnd_7117508] using wordTrace_append hprefix tailTrace_7117508
  have hstable : (prefixWord ++ tailWord_7117508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117508).length < 2 ^ (prefixWord ++ tailWord_7117508).sum := by decide
  have hdescent : baseEnd_7117508 < baseStart_7117508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117541 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 2, 3, 2]
def baseStart_7117541 : Nat := 118140960795 + 7117541 * 2 ^ 59
def prefixEnd_7117541 : Nat := 4983230072969 + 3 ^ 40 * 7117541 * 2
def baseEnd_7117541 : Nat := 3654719611082842321804531

theorem tailTrace_7117541 : CollatzResearch.WordTrace tailWord_7117541 prefixEnd_7117541 3654719611082842321804531 := by
  unfold tailWord_7117541
  simp only [CollatzResearch.WordTrace]
  refine ⟨259598047107372011070704477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173065364738248007380469651 259598047107372011070704477)
  ·
    refine ⟨97349267665264504151514179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259598047107372011070704477 97349267665264504151514179)
    ·
      refine ⟨146023901497896756227271269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97349267665264504151514179 146023901497896756227271269)
      ·
        refine ⟨27379481530855641792613363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146023901497896756227271269 27379481530855641792613363)
        ·
          refine ⟨41069222296283462688920045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27379481530855641792613363 41069222296283462688920045)
          ·
            refine ⟨15400958361106298508345017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41069222296283462688920045 15400958361106298508345017)
            ·
              refine ⟨11550718770829723881258763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15400958361106298508345017 11550718770829723881258763)
              ·
                refine ⟨17326078156244585821888145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11550718770829723881258763 17326078156244585821888145)
                ·
                  refine ⟨12994558617183439366416109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17326078156244585821888145 12994558617183439366416109)
                  ·
                    refine ⟨4872959481443789762406041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12994558617183439366416109 4872959481443789762406041)
                    ·
                      refine ⟨3654719611082842321804531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4872959481443789762406041 3654719611082842321804531)
                      ·
                        rfl

theorem cell23_7117541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_7117541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117541 prefixEnd_7117541 := by exact prefixLift 7117541
  have htrace : WordTrace (prefixWord ++ tailWord_7117541) baseStart_7117541 baseEnd_7117541 := by
    simpa [prefixWord, tailWord_7117541, baseEnd_7117541] using wordTrace_append hprefix tailTrace_7117541
  have hstable : (prefixWord ++ tailWord_7117541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117541).length < 2 ^ (prefixWord ++ tailWord_7117541).sum := by decide
  have hdescent : baseEnd_7117541 < baseStart_7117541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117564 : List Nat := [2, 2, 2, 1, 3, 2, 1, 4, 2, 4]
def baseStart_7117564 : Nat := 118140960795 + 7117564 * 2 ^ 59
def prefixEnd_7117564 : Nat := 4983230072969 + 3 ^ 40 * 7117564 * 2
def baseEnd_7117564 : Nat := 1218243807045965243938975

theorem tailTrace_7117564 : CollatzResearch.WordTrace tailWord_7117564 prefixEnd_7117564 1218243807045965243938975 := by
  unfold tailWord_7117564
  simp only [CollatzResearch.WordTrace]
  refine ⟨129799442993144342999395873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173065923990859123999194497 129799442993144342999395873)
  ·
    refine ⟨97349582244858257249546905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129799442993144342999395873 97349582244858257249546905)
    ·
      refine ⟨73012186683643692937160179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97349582244858257249546905 73012186683643692937160179)
      ·
        refine ⟨109518280025465539405740269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73012186683643692937160179 109518280025465539405740269)
        ·
          refine ⟨41069355009549577277152601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109518280025465539405740269 41069355009549577277152601)
          ·
            refine ⟨30802016257162182957864451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41069355009549577277152601 30802016257162182957864451)
            ·
              refine ⟨46203024385743274436796677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30802016257162182957864451 46203024385743274436796677)
              ·
                refine ⟨8663067072326863956899377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46203024385743274436796677 8663067072326863956899377)
                ·
                  refine ⟨6497300304245147967674533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8663067072326863956899377 6497300304245147967674533)
                  ·
                    refine ⟨1218243807045965243938975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6497300304245147967674533 1218243807045965243938975)
                    ·
                      rfl

theorem cell23_7117564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_7117564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117564 prefixEnd_7117564 := by exact prefixLift 7117564
  have htrace : WordTrace (prefixWord ++ tailWord_7117564) baseStart_7117564 baseEnd_7117564 := by
    simpa [prefixWord, tailWord_7117564, baseEnd_7117564] using wordTrace_append hprefix tailTrace_7117564
  have hstable : (prefixWord ++ tailWord_7117564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117564).length < 2 ^ (prefixWord ++ tailWord_7117564).sum := by decide
  have hdescent : baseEnd_7117564 < baseStart_7117564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117621 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_7117621 : Nat := 118140960795 + 7117621 * 2 ^ 59
def prefixEnd_7117621 : Nat := 4983230072969 + 3 ^ 40 * 7117621 * 2
def baseEnd_7117621 : Nat := 3654760689535202008804163

theorem tailTrace_7117621 : CollatzResearch.WordTrace tailWord_7117621 prefixEnd_7117621 3654760689535202008804163 := by
  unfold tailWord_7117621
  simp only [CollatzResearch.WordTrace]
  refine ⟨259600964947082184733616717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173067309964721456489077811 259600964947082184733616717)
  ·
    refine ⟨97350361855155819275106269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259600964947082184733616717 97350361855155819275106269)
    ·
      refine ⟨36506385695683432228164851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97350361855155819275106269 36506385695683432228164851)
      ·
        refine ⟨54759578543525148342247277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36506385695683432228164851 54759578543525148342247277)
        ·
          refine ⟨20534841953821930628342729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54759578543525148342247277 20534841953821930628342729)
          ·
            refine ⟨15401131465366447971257047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20534841953821930628342729 15401131465366447971257047)
            ·
              refine ⟨23101697198049671956885571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15401131465366447971257047 23101697198049671956885571)
              ·
                refine ⟨34652545797074507935328357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23101697198049671956885571 34652545797074507935328357)
                ·
                  refine ⟨6497352336951470237874067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34652545797074507935328357 6497352336951470237874067)
                  ·
                    refine ⟨9746028505427205356811101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6497352336951470237874067 9746028505427205356811101)
                    ·
                      refine ⟨3654760689535202008804163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9746028505427205356811101 3654760689535202008804163)
                      ·
                        rfl

theorem cell23_7117621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_7117621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117621 prefixEnd_7117621 := by exact prefixLift 7117621
  have htrace : WordTrace (prefixWord ++ tailWord_7117621) baseStart_7117621 baseEnd_7117621 := by
    simpa [prefixWord, tailWord_7117621, baseEnd_7117621] using wordTrace_append hprefix tailTrace_7117621
  have hstable : (prefixWord ++ tailWord_7117621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117621).length < 2 ^ (prefixWord ++ tailWord_7117621).sum := by decide
  have hdescent : baseEnd_7117621 < baseStart_7117621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117677 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_7117677 : Nat := 118140960795 + 7117677 * 2 ^ 59
def prefixEnd_7117677 : Nat := 4983230072969 + 3 ^ 40 * 7117677 * 2
def baseEnd_7117677 : Nat := 3654789444451853789703905

theorem tailTrace_7117677 : CollatzResearch.WordTrace tailWord_7117677 prefixEnd_7117677 3654789444451853789703905 := by
  unfold tailWord_7117677
  simp only [CollatzResearch.WordTrace]
  refine ⟨259603007434879306297655285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173068671623252870865103523 259603007434879306297655285)
  ·
    refine ⟨24337781947019934965405183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259603007434879306297655285 24337781947019934965405183)
    ·
      refine ⟨36506672920529902448107775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24337781947019934965405183 36506672920529902448107775)
      ·
        refine ⟨54760009380794853672161663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36506672920529902448107775 54760009380794853672161663)
        ·
          refine ⟨82140014071192280508242495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54760009380794853672161663 82140014071192280508242495)
          ·
            refine ⟨123210021106788420762363743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82140014071192280508242495 123210021106788420762363743)
            ·
              refine ⟨184815031660182631143545615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123210021106788420762363743 184815031660182631143545615)
              ·
                refine ⟨277222547490273946715318423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184815031660182631143545615 277222547490273946715318423)
                ·
                  refine ⟨415833821235410920072977635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277222547490273946715318423 415833821235410920072977635)
                  ·
                    refine ⟨623750731853116380109466453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 415833821235410920072977635 623750731853116380109466453)
                    ·
                      refine ⟨3654789444451853789703905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 623750731853116380109466453 3654789444451853789703905)
                      ·
                        rfl

theorem cell23_7117677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_7117677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117677 prefixEnd_7117677 := by exact prefixLift 7117677
  have htrace : WordTrace (prefixWord ++ tailWord_7117677) baseStart_7117677 baseEnd_7117677 := by
    simpa [prefixWord, tailWord_7117677, baseEnd_7117677] using wordTrace_append hprefix tailTrace_7117677
  have hstable : (prefixWord ++ tailWord_7117677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117677).length < 2 ^ (prefixWord ++ tailWord_7117677).sum := by decide
  have hdescent : baseEnd_7117677 < baseStart_7117677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117735 : List Nat := [1, 1, 6, 1, 3, 2, 2, 2, 5]
def baseStart_7117735 : Nat := 118140960795 + 7117735 * 2 ^ 59
def prefixEnd_7117735 : Nat := 4983230072969 + 3 ^ 40 * 7117735 * 2
def baseEnd_7117735 : Nat := 406091025147757173642071

theorem tailTrace_7117735 : CollatzResearch.WordTrace tailWord_7117735 prefixEnd_7117735 406091025147757173642071 := by
  unfold tailWord_7117735
  simp only [CollatzResearch.WordTrace]
  refine ⟨259605122868669182203266659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173070081912446121468844439 259605122868669182203266659)
  ·
    refine ⟨389407684303003773304899989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259605122868669182203266659 389407684303003773304899989)
    ·
      refine ⟨18253485201703301873667187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 389407684303003773304899989 18253485201703301873667187)
      ·
        refine ⟨27380227802554952810500781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18253485201703301873667187 27380227802554952810500781)
        ·
          refine ⟨10267585425958107303937793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27380227802554952810500781 10267585425958107303937793)
          ·
            refine ⟨7700689069468580477953345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10267585425958107303937793 7700689069468580477953345)
            ·
              refine ⟨5775516802101435358465009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7700689069468580477953345 5775516802101435358465009)
              ·
                refine ⟨4331637601576076518848757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5775516802101435358465009 4331637601576076518848757)
                ·
                  refine ⟨406091025147757173642071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4331637601576076518848757 406091025147757173642071)
                  ·
                    rfl

theorem cell23_7117735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 5].length) (baseStart_7117735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117735 prefixEnd_7117735 := by exact prefixLift 7117735
  have htrace : WordTrace (prefixWord ++ tailWord_7117735) baseStart_7117735 baseEnd_7117735 := by
    simpa [prefixWord, tailWord_7117735, baseEnd_7117735] using wordTrace_append hprefix tailTrace_7117735
  have hstable : (prefixWord ++ tailWord_7117735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117735).length < 2 ^ (prefixWord ++ tailWord_7117735).sum := by decide
  have hdescent : baseEnd_7117735 < baseStart_7117735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117737 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 2, 3, 5]
def baseStart_7117737 : Nat := 118140960795 + 7117737 * 2 ^ 59
def prefixEnd_7117737 : Nat := 4983230072969 + 3 ^ 40 * 7117737 * 2
def baseEnd_7117737 : Nat := 3654820253291123554953629

theorem tailTrace_7117737 : CollatzResearch.WordTrace tailWord_7117737 prefixEnd_7117737 3654820253291123554953629 := by
  unfold tailWord_7117737
  simp only [CollatzResearch.WordTrace]
  refine ⟨259605195814661936544839465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173070130543107957696559643 259605195814661936544839465)
  ·
    refine ⟨194703896860996452408629599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259605195814661936544839465 194703896860996452408629599)
    ·
      refine ⟨292055845291494678612944399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194703896860996452408629599 292055845291494678612944399)
      ·
        refine ⟨438083767937242017919416599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292055845291494678612944399 438083767937242017919416599)
        ·
          refine ⟨657125651905863026879124899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438083767937242017919416599 657125651905863026879124899)
          ·
            refine ⟨985688477858794540318687349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657125651905863026879124899 985688477858794540318687349)
            ·
              refine ⟨92408294799261988154876939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 985688477858794540318687349 92408294799261988154876939)
              ·
                refine ⟨138612442198892982232315409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92408294799261988154876939 138612442198892982232315409)
                ·
                  refine ⟨103959331649169736674236557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138612442198892982232315409 103959331649169736674236557)
                  ·
                    refine ⟨38984749368438651252838709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103959331649169736674236557 38984749368438651252838709)
                    ·
                      refine ⟨3654820253291123554953629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38984749368438651252838709 3654820253291123554953629)
                      ·
                        rfl

theorem cell23_7117737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_7117737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117737 prefixEnd_7117737 := by exact prefixLift 7117737
  have htrace : WordTrace (prefixWord ++ tailWord_7117737) baseStart_7117737 baseEnd_7117737 := by
    simpa [prefixWord, tailWord_7117737, baseEnd_7117737] using wordTrace_append hprefix tailTrace_7117737
  have hstable : (prefixWord ++ tailWord_7117737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117737).length < 2 ^ (prefixWord ++ tailWord_7117737).sum := by decide
  have hdescent : baseEnd_7117737 < baseStart_7117737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117747 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 6]
def baseStart_7117747 : Nat := 118140960795 + 7117747 * 2 ^ 59
def prefixEnd_7117747 : Nat := 4983230072969 + 3 ^ 40 * 7117747 * 2
def baseEnd_7117747 : Nat := 3654825388097668515828583

theorem tailTrace_7117747 : CollatzResearch.WordTrace tailWord_7117747 prefixEnd_7117747 3654825388097668515828583 := by
  unfold tailWord_7117747
  simp only [CollatzResearch.WordTrace]
  refine ⟨259605560544625708252703495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173070373696417138835135663 259605560544625708252703495)
  ·
    refine ⟨389408340816938562379055243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259605560544625708252703495 389408340816938562379055243)
    ·
      refine ⟨584112511225407843568582865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389408340816938562379055243 584112511225407843568582865)
      ·
        refine ⟨438084383419055882676437149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 584112511225407843568582865 438084383419055882676437149)
        ·
          refine ⟨164281643782145956003663931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438084383419055882676437149 164281643782145956003663931)
          ·
            refine ⟨246422465673218934005495897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164281643782145956003663931 246422465673218934005495897)
            ·
              refine ⟨184816849254914200504121923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246422465673218934005495897 184816849254914200504121923)
              ·
                refine ⟨277225273882371300756182885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184816849254914200504121923 277225273882371300756182885)
                ·
                  refine ⟨51979738852944618891784291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277225273882371300756182885 51979738852944618891784291)
                  ·
                    refine ⟨77969608279416928337676437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51979738852944618891784291 77969608279416928337676437)
                    ·
                      refine ⟨3654825388097668515828583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77969608279416928337676437 3654825388097668515828583)
                      ·
                        rfl

theorem cell23_7117747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_7117747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117747 prefixEnd_7117747 := by exact prefixLift 7117747
  have htrace : WordTrace (prefixWord ++ tailWord_7117747) baseStart_7117747 baseEnd_7117747 := by
    simpa [prefixWord, tailWord_7117747, baseEnd_7117747] using wordTrace_append hprefix tailTrace_7117747
  have hstable : (prefixWord ++ tailWord_7117747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117747).length < 2 ^ (prefixWord ++ tailWord_7117747).sum := by decide
  have hdescent : baseEnd_7117747 < baseStart_7117747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117754 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3]
def baseStart_7117754 : Nat := 118140960795 + 7117754 * 2 ^ 59
def prefixEnd_7117754 : Nat := 4983230072969 + 3 ^ 40 * 7117754 * 2
def baseEnd_7117754 : Nat := 3654828982462249988441051

theorem tailTrace_7117754 : CollatzResearch.WordTrace tailWord_7117754 prefixEnd_7117754 3654828982462249988441051 := by
  unfold tailWord_7117754
  simp only [CollatzResearch.WordTrace]
  refine ⟨64901453963900087112052079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173070543903733565632138877 64901453963900087112052079)
  ·
    refine ⟨97352180945850130668078119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64901453963900087112052079 97352180945850130668078119)
    ·
      refine ⟨146028271418775196002117179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97352180945850130668078119 146028271418775196002117179)
      ·
        refine ⟨219042407128162794003175769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146028271418775196002117179 219042407128162794003175769)
        ·
          refine ⟨164281805346122095502381827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219042407128162794003175769 164281805346122095502381827)
          ·
            refine ⟨246422708019183143253572741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164281805346122095502381827 246422708019183143253572741)
            ·
              refine ⟨46204257753596839360044889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246422708019183143253572741 46204257753596839360044889)
              ·
                refine ⟨34653193315197629520033667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46204257753596839360044889 34653193315197629520033667)
                ·
                  refine ⟨51979789972796444280050501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34653193315197629520033667 51979789972796444280050501)
                  ·
                    refine ⟨9746210619899333302509469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51979789972796444280050501 9746210619899333302509469)
                    ·
                      refine ⟨3654828982462249988441051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9746210619899333302509469 3654828982462249988441051)
                      ·
                        rfl

theorem cell23_7117754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_7117754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117754 prefixEnd_7117754 := by exact prefixLift 7117754
  have htrace : WordTrace (prefixWord ++ tailWord_7117754) baseStart_7117754 baseEnd_7117754 := by
    simpa [prefixWord, tailWord_7117754, baseEnd_7117754] using wordTrace_append hprefix tailTrace_7117754
  have hstable : (prefixWord ++ tailWord_7117754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117754).length < 2 ^ (prefixWord ++ tailWord_7117754).sum := by decide
  have hdescent : baseEnd_7117754 < baseStart_7117754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117768 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 2, 1, 4]
def baseStart_7117768 : Nat := 118140960795 + 7117768 * 2 ^ 59
def prefixEnd_7117768 : Nat := 4983230072969 + 3 ^ 40 * 7117768 * 2
def baseEnd_7117768 : Nat := 3654836171191412933665987

theorem tailTrace_7117768 : CollatzResearch.WordTrace tailWord_7117768 prefixEnd_7117768 3654836171191412933665987 := by
  unfold tailWord_7117768
  simp only [CollatzResearch.WordTrace]
  refine ⟨129803163238774814419608979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173070884318366419226145305 129803163238774814419608979)
  ·
    refine ⟨194704744858162221629413469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129803163238774814419608979 194704744858162221629413469)
    ·
      refine ⟨73014279321810833111030051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194704744858162221629413469 73014279321810833111030051)
      ·
        refine ⟨109521418982716249666545077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73014279321810833111030051 109521418982716249666545077)
        ·
          refine ⟨10267633029629648406238601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109521418982716249666545077 10267633029629648406238601)
          ·
            refine ⟨7700724772222236304678951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10267633029629648406238601 7700724772222236304678951)
            ·
              refine ⟨11551087158333354457018427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7700724772222236304678951 11551087158333354457018427)
              ·
                refine ⟨17326630737500031685527641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11551087158333354457018427 17326630737500031685527641)
                ·
                  refine ⟨12994973053125023764145731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17326630737500031685527641 12994973053125023764145731)
                  ·
                    refine ⟨19492459579687535646218597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12994973053125023764145731 19492459579687535646218597)
                    ·
                      refine ⟨3654836171191412933665987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19492459579687535646218597 3654836171191412933665987)
                      ·
                        rfl

theorem cell23_7117768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_7117768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117768 prefixEnd_7117768 := by exact prefixLift 7117768
  have htrace : WordTrace (prefixWord ++ tailWord_7117768) baseStart_7117768 baseEnd_7117768 := by
    simpa [prefixWord, tailWord_7117768, baseEnd_7117768] using wordTrace_append hprefix tailTrace_7117768
  have hstable : (prefixWord ++ tailWord_7117768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117768).length < 2 ^ (prefixWord ++ tailWord_7117768).sum := by decide
  have hdescent : baseEnd_7117768 < baseStart_7117768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117771 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 3]
def baseStart_7117771 : Nat := 118140960795 + 7117771 * 2 ^ 59
def prefixEnd_7117771 : Nat := 4983230072969 + 3 ^ 40 * 7117771 * 2
def baseEnd_7117771 : Nat := 3654837711633376421928473

theorem tailTrace_7117771 : CollatzResearch.WordTrace tailWord_7117771 prefixEnd_7117771 3654837711633376421928473 := by
  unfold tailWord_7117771
  simp only [CollatzResearch.WordTrace]
  refine ⟨259606435896538760351577167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173070957264359173567718111 259606435896538760351577167)
  ·
    refine ⟨389409653844808140527365751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259606435896538760351577167 389409653844808140527365751)
    ·
      refine ⟨584114480767212210791048627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389409653844808140527365751 584114480767212210791048627)
      ·
        refine ⟨876171721150818316186572941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584114480767212210791048627 876171721150818316186572941)
        ·
          refine ⟨328564395431556868569964853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 876171721150818316186572941 328564395431556868569964853)
          ·
            refine ⟨30802912071708456428434205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 328564395431556868569964853 30802912071708456428434205)
            ·
              refine ⟨11551092026890671160662827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30802912071708456428434205 11551092026890671160662827)
              ·
                refine ⟨17326638040336006740994241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11551092026890671160662827 17326638040336006740994241)
                ·
                  refine ⟨12994978530252005055745681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17326638040336006740994241 12994978530252005055745681)
                  ·
                    refine ⟨9746233897689003791809261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12994978530252005055745681 9746233897689003791809261)
                    ·
                      refine ⟨3654837711633376421928473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9746233897689003791809261 3654837711633376421928473)
                      ·
                        rfl

theorem cell23_7117771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 3].length) (baseStart_7117771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117771 prefixEnd_7117771 := by exact prefixLift 7117771
  have htrace : WordTrace (prefixWord ++ tailWord_7117771) baseStart_7117771 baseEnd_7117771 := by
    simpa [prefixWord, tailWord_7117771, baseEnd_7117771] using wordTrace_append hprefix tailTrace_7117771
  have hstable : (prefixWord ++ tailWord_7117771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117771).length < 2 ^ (prefixWord ++ tailWord_7117771).sum := by decide
  have hdescent : baseEnd_7117771 < baseStart_7117771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117824 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 4]
def baseStart_7117824 : Nat := 118140960795 + 7117824 * 2 ^ 59
def prefixEnd_7117824 : Nat := 4983230072969 + 3 ^ 40 * 7117824 * 2
def baseEnd_7117824 : Nat := 3654864926108064714565729

theorem tailTrace_7117824 : CollatzResearch.WordTrace tailWord_7117824 prefixEnd_7117824 3654864926108064714565729 := by
  unfold tailWord_7117824
  simp only [CollatzResearch.WordTrace]
  refine ⟨129804184482673375201628263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173072245976897833602171017 129804184482673375201628263)
  ·
    refine ⟨194706276724010062802442395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129804184482673375201628263 194706276724010062802442395)
    ·
      refine ⟨292059415086015094203663593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194706276724010062802442395 292059415086015094203663593)
      ·
        refine ⟨219044561314511320652747695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292059415086015094203663593 219044561314511320652747695)
        ·
          refine ⟨328566841971766980979121543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219044561314511320652747695 328566841971766980979121543)
          ·
            refine ⟨492850262957650471468682315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328566841971766980979121543 492850262957650471468682315)
            ·
              refine ⟨739275394436475707203023473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492850262957650471468682315 739275394436475707203023473)
              ·
                refine ⟨554456545827356780402267605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739275394436475707203023473 554456545827356780402267605)
                ·
                  refine ⟨12995075292828674540678147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 554456545827356780402267605 12995075292828674540678147)
                  ·
                    refine ⟨19492612939243011811017221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12995075292828674540678147 19492612939243011811017221)
                    ·
                      refine ⟨3654864926108064714565729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19492612939243011811017221 3654864926108064714565729)
                      ·
                        rfl

theorem cell23_7117824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_7117824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117824 prefixEnd_7117824 := by exact prefixLift 7117824
  have htrace : WordTrace (prefixWord ++ tailWord_7117824) baseStart_7117824 baseEnd_7117824 := by
    simpa [prefixWord, tailWord_7117824, baseEnd_7117824] using wordTrace_append hprefix tailTrace_7117824
  have hstable : (prefixWord ++ tailWord_7117824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117824).length < 2 ^ (prefixWord ++ tailWord_7117824).sum := by decide
  have hdescent : baseEnd_7117824 < baseStart_7117824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117835 : List Nat := [1, 1, 1, 1, 6, 2, 3, 3, 1, 1, 3]
def baseStart_7117835 : Nat := 118140960795 + 7117835 * 2 ^ 59
def prefixEnd_7117835 : Nat := 4983230072969 + 3 ^ 40 * 7117835 * 2
def baseEnd_7117835 : Nat := 3654870574395264171528179

theorem tailTrace_7117835 : CollatzResearch.WordTrace tailWord_7117835 prefixEnd_7117835 3654870574395264171528179 := by
  unfold tailWord_7117835
  simp only [CollatzResearch.WordTrace]
  refine ⟨259608770168306899281906959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173072513445537932854604639 259608770168306899281906959)
  ·
    refine ⟨389413155252460348922860439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259608770168306899281906959 389413155252460348922860439)
    ·
      refine ⟨584119732878690523384290659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389413155252460348922860439 584119732878690523384290659)
      ·
        refine ⟨876179599318035785076435989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584119732878690523384290659 876179599318035785076435989)
        ·
          refine ⟨41070918718032927425457937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 876179599318035785076435989 41070918718032927425457937)
          ·
            refine ⟨30803189038524695569093453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41070918718032927425457937 30803189038524695569093453)
            ·
              refine ⟨11551195889446760838410045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30803189038524695569093453 11551195889446760838410045)
              ·
                refine ⟨4331698458542535314403767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11551195889446760838410045 4331698458542535314403767)
                ·
                  refine ⟨6497547687813802971605651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4331698458542535314403767 6497547687813802971605651)
                  ·
                    refine ⟨9746321531720704457408477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6497547687813802971605651 9746321531720704457408477)
                    ·
                      refine ⟨3654870574395264171528179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9746321531720704457408477 3654870574395264171528179)
                      ·
                        rfl

theorem cell23_7117835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 3, 1, 1, 3].length) (baseStart_7117835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117835 prefixEnd_7117835 := by exact prefixLift 7117835
  have htrace : WordTrace (prefixWord ++ tailWord_7117835) baseStart_7117835 baseEnd_7117835 := by
    simpa [prefixWord, tailWord_7117835, baseEnd_7117835] using wordTrace_append hprefix tailTrace_7117835
  have hstable : (prefixWord ++ tailWord_7117835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117835).length < 2 ^ (prefixWord ++ tailWord_7117835).sum := by decide
  have hdescent : baseEnd_7117835 < baseStart_7117835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117852 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_7117852 : Nat := 118140960795 + 7117852 * 2 ^ 59
def prefixEnd_7117852 : Nat := 4983230072969 + 3 ^ 40 * 7117852 * 2
def baseEnd_7117852 : Nat := 3654879303566390605015601

theorem tailTrace_7117852 : CollatzResearch.WordTrace tailWord_7117852 prefixEnd_7117852 3654879303566390605015601 := by
  unfold tailWord_7117852
  simp only [CollatzResearch.WordTrace]
  refine ⟨129804695104622655592637905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173072926806163540790183873 129804695104622655592637905)
  ·
    refine ⟨97353521328466991694478429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129804695104622655592637905 97353521328466991694478429)
    ·
      refine ⟨36507570498175121885429411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97353521328466991694478429 36507570498175121885429411)
      ·
        refine ⟨54761355747262682828144117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36507570498175121885429411 54761355747262682828144117)
        ·
          refine ⟨5133877101305876515138511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54761355747262682828144117 5133877101305876515138511)
          ·
            refine ⟨7700815651958814772707767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5133877101305876515138511 7700815651958814772707767)
            ·
              refine ⟨11551223477938222159061651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7700815651958814772707767 11551223477938222159061651)
              ·
                refine ⟨17326835216907333238592477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11551223477938222159061651 17326835216907333238592477)
                ·
                  refine ⟨6497563206340249964472179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17326835216907333238592477 6497563206340249964472179)
                  ·
                    refine ⟨9746344809510374946708269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6497563206340249964472179 9746344809510374946708269)
                    ·
                      refine ⟨3654879303566390605015601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9746344809510374946708269 3654879303566390605015601)
                      ·
                        rfl

theorem cell23_7117852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_7117852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117852 prefixEnd_7117852 := by exact prefixLift 7117852
  have htrace : WordTrace (prefixWord ++ tailWord_7117852) baseStart_7117852 baseEnd_7117852 := by
    simpa [prefixWord, tailWord_7117852, baseEnd_7117852] using wordTrace_append hprefix tailTrace_7117852
  have hstable : (prefixWord ++ tailWord_7117852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117852).length < 2 ^ (prefixWord ++ tailWord_7117852).sum := by decide
  have hdescent : baseEnd_7117852 < baseStart_7117852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117861 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 3, 2, 3]
def baseStart_7117861 : Nat := 118140960795 + 7117861 * 2 ^ 59
def prefixEnd_7117861 : Nat := 4983230072969 + 3 ^ 40 * 7117861 * 2
def baseEnd_7117861 : Nat := 3654883924892281069803059

theorem tailTrace_7117861 : CollatzResearch.WordTrace tailWord_7117861 prefixEnd_7117861 3654883924892281069803059 := by
  unfold tailWord_7117861
  simp only [CollatzResearch.WordTrace]
  refine ⟨259609718466212705722353437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173073145644141803814902291 259609718466212705722353437)
  ·
    refine ⟨97353644424829764645882539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259609718466212705722353437 97353644424829764645882539)
    ·
      refine ⟨146030466637244646968823809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97353644424829764645882539 146030466637244646968823809)
      ·
        refine ⟨109522849977933485226617857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146030466637244646968823809 109522849977933485226617857)
        ·
          refine ⟨82142137483450113919963393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109522849977933485226617857 82142137483450113919963393)
          ·
            refine ⟨61606603112587585439972545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82142137483450113919963393 61606603112587585439972545)
            ·
              refine ⟨46204952334440689079979409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61606603112587585439972545 46204952334440689079979409)
              ·
                refine ⟨34653714250830516809984557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46204952334440689079979409 34653714250830516809984557)
                ·
                  refine ⟨12995142844061443803744209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34653714250830516809984557 12995142844061443803744209)
                  ·
                    refine ⟨9746357133046082852808157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12995142844061443803744209 9746357133046082852808157)
                    ·
                      refine ⟨3654883924892281069803059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9746357133046082852808157 3654883924892281069803059)
                      ·
                        rfl

theorem cell23_7117861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_7117861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117861 prefixEnd_7117861 := by exact prefixLift 7117861
  have htrace : WordTrace (prefixWord ++ tailWord_7117861) baseStart_7117861 baseEnd_7117861 := by
    simpa [prefixWord, tailWord_7117861, baseEnd_7117861] using wordTrace_append hprefix tailTrace_7117861
  have hstable : (prefixWord ++ tailWord_7117861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117861).length < 2 ^ (prefixWord ++ tailWord_7117861).sum := by decide
  have hdescent : baseEnd_7117861 < baseStart_7117861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117891 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 3]
def baseStart_7117891 : Nat := 118140960795 + 7117891 * 2 ^ 59
def prefixEnd_7117891 : Nat := 4983230072969 + 3 ^ 40 * 7117891 * 2
def baseEnd_7117891 : Nat := 3654899329311915952427921

theorem tailTrace_7117891 : CollatzResearch.WordTrace tailWord_7117891 prefixEnd_7117891 3654899329311915952427921 := by
  unfold tailWord_7117891
  simp only [CollatzResearch.WordTrace]
  refine ⟨259610812656104020845945527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173073875104069347230630351 259610812656104020845945527)
  ·
    refine ⟨389416218984156031268918291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259610812656104020845945527 389416218984156031268918291)
    ·
      refine ⟨584124328476234046903377437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389416218984156031268918291 584124328476234046903377437)
      ·
        refine ⟨219046623178587767588766539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 584124328476234046903377437 219046623178587767588766539)
        ·
          refine ⟨328569934767881651383149809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219046623178587767588766539 328569934767881651383149809)
          ·
            refine ⟨246427451075911238537362357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328569934767881651383149809 246427451075911238537362357)
            ·
              refine ⟨23102573538366678612877721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 246427451075911238537362357 23102573538366678612877721)
              ·
                refine ⟨17326930153775008959658291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23102573538366678612877721 17326930153775008959658291)
                ·
                  refine ⟨25990395230662513439487437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17326930153775008959658291 25990395230662513439487437)
                  ·
                    refine ⟨9746398211498442539807789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25990395230662513439487437 9746398211498442539807789)
                    ·
                      refine ⟨3654899329311915952427921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9746398211498442539807789 3654899329311915952427921)
                      ·
                        rfl

theorem cell23_7117891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_7117891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117891 prefixEnd_7117891 := by exact prefixLift 7117891
  have htrace : WordTrace (prefixWord ++ tailWord_7117891) baseStart_7117891 baseEnd_7117891 := by
    simpa [prefixWord, tailWord_7117891, baseEnd_7117891] using wordTrace_append hprefix tailTrace_7117891
  have hstable : (prefixWord ++ tailWord_7117891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117891).length < 2 ^ (prefixWord ++ tailWord_7117891).sum := by decide
  have hdescent : baseEnd_7117891 < baseStart_7117891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117895 : List Nat := [1, 1, 4, 1, 3, 3, 3, 1, 1, 2, 3]
def baseStart_7117895 : Nat := 118140960795 + 7117895 * 2 ^ 59
def prefixEnd_7117895 : Nat := 4983230072969 + 3 ^ 40 * 7117895 * 2
def baseEnd_7117895 : Nat := 3654901383234533936777903

theorem tailTrace_7117895 : CollatzResearch.WordTrace tailWord_7117895 prefixEnd_7117895 3654901383234533936777903 := by
  unfold tailWord_7117895
  simp only [CollatzResearch.WordTrace]
  refine ⟨259610958548089529529091139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173073972365393019686060759 259610958548089529529091139)
  ·
    refine ⟨389416437822134294293636709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259610958548089529529091139 389416437822134294293636709)
    ·
      refine ⟨73015582091650180180056883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389416437822134294293636709 73015582091650180180056883)
      ·
        refine ⟨109523373137475270270085325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73015582091650180180056883 109523373137475270270085325)
        ·
          refine ⟨41071264926553226351281997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109523373137475270270085325 41071264926553226351281997)
          ·
            refine ⟨15401724347457459881730749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41071264926553226351281997 15401724347457459881730749)
            ·
              refine ⟨5775646630296547455649031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15401724347457459881730749 5775646630296547455649031)
              ·
                refine ⟨8663469945444821183473547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5775646630296547455649031 8663469945444821183473547)
                ·
                  refine ⟨12995204918167231775210321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8663469945444821183473547 12995204918167231775210321)
                  ·
                    refine ⟨9746403688625423831407741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12995204918167231775210321 9746403688625423831407741)
                    ·
                      refine ⟨3654901383234533936777903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9746403688625423831407741 3654901383234533936777903)
                      ·
                        rfl

theorem cell23_7117895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_7117895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117895 prefixEnd_7117895 := by exact prefixLift 7117895
  have htrace : WordTrace (prefixWord ++ tailWord_7117895) baseStart_7117895 baseEnd_7117895 := by
    simpa [prefixWord, tailWord_7117895, baseEnd_7117895] using wordTrace_append hprefix tailTrace_7117895
  have hstable : (prefixWord ++ tailWord_7117895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117895).length < 2 ^ (prefixWord ++ tailWord_7117895).sum := by decide
  have hdescent : baseEnd_7117895 < baseStart_7117895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117904 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 5]
def baseStart_7117904 : Nat := 118140960795 + 7117904 * 2 ^ 59
def prefixEnd_7117904 : Nat := 4983230072969 + 3 ^ 40 * 7117904 * 2
def baseEnd_7117904 : Nat := 3654906004560424401565361

theorem tailTrace_7117904 : CollatzResearch.WordTrace tailWord_7117904 prefixEnd_7117904 3654906004560424401565361 := by
  unfold tailWord_7117904
  simp only [CollatzResearch.WordTrace]
  refine ⟨129805643402528462033084383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173074191203371282710779177 129805643402528462033084383)
  ·
    refine ⟨194708465103792693049626575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129805643402528462033084383 194708465103792693049626575)
    ·
      refine ⟨292062697655689039574439863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194708465103792693049626575 292062697655689039574439863)
      ·
        refine ⟨438094046483533559361659795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292062697655689039574439863 438094046483533559361659795)
        ·
          refine ⟨657141069725300339042489693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438094046483533559361659795 657141069725300339042489693)
          ·
            refine ⟨246427901146987627140933635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 657141069725300339042489693 246427901146987627140933635)
            ·
              refine ⟨369641851720481440711400453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246427901146987627140933635 369641851720481440711400453)
              ·
                refine ⟨69307847197590270133387585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369641851720481440711400453 69307847197590270133387585)
                ·
                  refine ⟨51980885398192702600040689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69307847197590270133387585 51980885398192702600040689)
                  ·
                    refine ⟨38985664048644526950030517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51980885398192702600040689 38985664048644526950030517)
                    ·
                      refine ⟨3654906004560424401565361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38985664048644526950030517 3654906004560424401565361)
                      ·
                        rfl

theorem cell23_7117904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_7117904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117904 prefixEnd_7117904 := by exact prefixLift 7117904
  have htrace : WordTrace (prefixWord ++ tailWord_7117904) baseStart_7117904 baseEnd_7117904 := by
    simpa [prefixWord, tailWord_7117904, baseEnd_7117904] using wordTrace_append hprefix tailTrace_7117904
  have hstable : (prefixWord ++ tailWord_7117904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117904).length < 2 ^ (prefixWord ++ tailWord_7117904).sum := by decide
  have hdescent : baseEnd_7117904 < baseStart_7117904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117908 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_7117908 : Nat := 118140960795 + 7117908 * 2 ^ 59
def prefixEnd_7117908 : Nat := 4983230072969 + 3 ^ 40 * 7117908 * 2
def baseEnd_7117908 : Nat := 3654908058483042385915343

theorem tailTrace_7117908 : CollatzResearch.WordTrace tailWord_7117908 prefixEnd_7117908 3654908058483042385915343 := by
  unfold tailWord_7117908
  simp only [CollatzResearch.WordTrace]
  refine ⟨129805716348521216374657189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173074288464694955166209585 129805716348521216374657189)
  ·
    refine ⟨24338571815347728070248223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129805716348521216374657189 24338571815347728070248223)
    ·
      refine ⟨36507857723021592105372335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24338571815347728070248223 36507857723021592105372335)
      ·
        refine ⟨54761786584532388158058503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36507857723021592105372335 54761786584532388158058503)
        ·
          refine ⟨82142679876798582237087755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54761786584532388158058503 82142679876798582237087755)
          ·
            refine ⟨123214019815197873355631633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82142679876798582237087755 123214019815197873355631633)
            ·
              refine ⟨92410514861398405016723725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123214019815197873355631633 92410514861398405016723725)
              ·
                refine ⟨34653943073024401881271397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92410514861398405016723725 34653943073024401881271397)
                ·
                  refine ⟨6497614326192075352738387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34653943073024401881271397 6497614326192075352738387)
                  ·
                    refine ⟨9746421489288113029107581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6497614326192075352738387 9746421489288113029107581)
                    ·
                      refine ⟨3654908058483042385915343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9746421489288113029107581 3654908058483042385915343)
                      ·
                        rfl

theorem cell23_7117908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_7117908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117908 prefixEnd_7117908 := by exact prefixLift 7117908
  have htrace : WordTrace (prefixWord ++ tailWord_7117908) baseStart_7117908 baseEnd_7117908 := by
    simpa [prefixWord, tailWord_7117908, baseEnd_7117908] using wordTrace_append hprefix tailTrace_7117908
  have hstable : (prefixWord ++ tailWord_7117908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117908).length < 2 ^ (prefixWord ++ tailWord_7117908).sum := by decide
  have hdescent : baseEnd_7117908 < baseStart_7117908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117948 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 1, 4, 2]
def baseStart_7117948 : Nat := 118140960795 + 7117948 * 2 ^ 59
def prefixEnd_7117948 : Nat := 4983230072969 + 3 ^ 40 * 7117948 * 2
def baseEnd_7117948 : Nat := 3654928597709222229415159

theorem tailTrace_7117948 : CollatzResearch.WordTrace tailWord_7117948 prefixEnd_7117948 3654928597709222229415159 := by
  unfold tailWord_7117948
  simp only [CollatzResearch.WordTrace]
  refine ⟨129806445808448759790385249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173075261077931679720513665 129806445808448759790385249)
  ·
    refine ⟨97354834356336569842788937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129806445808448759790385249 97354834356336569842788937)
    ·
      refine ⟨73016125767252427382091703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97354834356336569842788937 73016125767252427382091703)
      ·
        refine ⟨109524188650878641073137555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73016125767252427382091703 109524188650878641073137555)
        ·
          refine ⟨164286282976317961609706333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109524188650878641073137555 164286282976317961609706333)
          ·
            refine ⟨61607356116119235603639875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164286282976317961609706333 61607356116119235603639875)
            ·
              refine ⟨92411034174178853405459813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61607356116119235603639875 92411034174178853405459813)
              ·
                refine ⟨17327068907658535013523715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92411034174178853405459813 17327068907658535013523715)
                ·
                  refine ⟨25990603361487802520285573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17327068907658535013523715 25990603361487802520285573)
                  ·
                    refine ⟨4873238130278962972553545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25990603361487802520285573 4873238130278962972553545)
                    ·
                      refine ⟨3654928597709222229415159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4873238130278962972553545 3654928597709222229415159)
                      ·
                        rfl

theorem cell23_7117948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_7117948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117948 prefixEnd_7117948 := by exact prefixLift 7117948
  have htrace : WordTrace (prefixWord ++ tailWord_7117948) baseStart_7117948 baseEnd_7117948 := by
    simpa [prefixWord, tailWord_7117948, baseEnd_7117948] using wordTrace_append hprefix tailTrace_7117948
  have hstable : (prefixWord ++ tailWord_7117948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117948).length < 2 ^ (prefixWord ++ tailWord_7117948).sum := by decide
  have hdescent : baseEnd_7117948 < baseStart_7117948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117961 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 2, 2, 4]
def baseStart_7117961 : Nat := 118140960795 + 7117961 * 2 ^ 59
def prefixEnd_7117961 : Nat := 4983230072969 + 3 ^ 40 * 7117961 * 2
def baseEnd_7117961 : Nat := 3654935272957730678552599

theorem tailTrace_7117961 : CollatzResearch.WordTrace tailWord_7117961 prefixEnd_7117961 3654935272957730678552599 := by
  unfold tailWord_7117961
  simp only [CollatzResearch.WordTrace]
  refine ⟨259613365765850422800993737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173075577177233615200662491 259613365765850422800993737)
  ·
    refine ⟨194710024324387817100745303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259613365765850422800993737 194710024324387817100745303)
    ·
      refine ⟨292065036486581725651117955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194710024324387817100745303 292065036486581725651117955)
      ·
        refine ⟨438097554729872588476676933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292065036486581725651117955 438097554729872588476676933)
        ·
          refine ⟨82143291511851110339376925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 438097554729872588476676933 82143291511851110339376925)
          ·
            refine ⟨30803734316944166377266347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82143291511851110339376925 30803734316944166377266347)
            ·
              refine ⟨46205601475416249565899521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30803734316944166377266347 46205601475416249565899521)
              ·
                refine ⟨34654201106562187174424641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46205601475416249565899521 34654201106562187174424641)
                ·
                  refine ⟨25990650829921640380818481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34654201106562187174424641 25990650829921640380818481)
                  ·
                    refine ⟨19492988122441230285613861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25990650829921640380818481 19492988122441230285613861)
                    ·
                      refine ⟨3654935272957730678552599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19492988122441230285613861 3654935272957730678552599)
                      ·
                        rfl

theorem cell23_7117961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_7117961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117961 prefixEnd_7117961 := by exact prefixLift 7117961
  have htrace : WordTrace (prefixWord ++ tailWord_7117961) baseStart_7117961 baseEnd_7117961 := by
    simpa [prefixWord, tailWord_7117961, baseEnd_7117961] using wordTrace_append hprefix tailTrace_7117961
  have hstable : (prefixWord ++ tailWord_7117961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117961).length < 2 ^ (prefixWord ++ tailWord_7117961).sum := by decide
  have hdescent : baseEnd_7117961 < baseStart_7117961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117978 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4]
def baseStart_7117978 : Nat := 118140960795 + 7117978 * 2 ^ 59
def prefixEnd_7117978 : Nat := 4983230072969 + 3 ^ 40 * 7117978 * 2
def baseEnd_7117978 : Nat := 3654944002128857112040021

theorem tailTrace_7117978 : CollatzResearch.WordTrace tailWord_7117978 prefixEnd_7117978 3654944002128857112040021 := by
  unfold tailWord_7117978
  simp only [CollatzResearch.WordTrace]
  refine ⟨64903496451697208676090647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173075990537859223136241725 64903496451697208676090647)
  ·
    refine ⟨97355244677545813014135971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64903496451697208676090647 97355244677545813014135971)
    ·
      refine ⟨146032867016318719521203957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97355244677545813014135971 146032867016318719521203957)
      ·
        refine ⟨13690581282779879955112871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146032867016318719521203957 13690581282779879955112871)
        ·
          refine ⟨20535871924169819932669307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13690581282779879955112871 20535871924169819932669307)
          ·
            refine ⟨30803807886254729899003961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20535871924169819932669307 30803807886254729899003961)
            ·
              refine ⟨23102855914691047424252971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30803807886254729899003961 23102855914691047424252971)
              ·
                refine ⟨34654283872036571136379457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23102855914691047424252971 34654283872036571136379457)
                ·
                  refine ⟨25990712904027428352284593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34654283872036571136379457 25990712904027428352284593)
                  ·
                    refine ⟨19493034678020571264213445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25990712904027428352284593 19493034678020571264213445)
                    ·
                      refine ⟨3654944002128857112040021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19493034678020571264213445 3654944002128857112040021)
                      ·
                        rfl

theorem cell23_7117978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_7117978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117978 prefixEnd_7117978 := by exact prefixLift 7117978
  have htrace : WordTrace (prefixWord ++ tailWord_7117978) baseStart_7117978 baseEnd_7117978 := by
    simpa [prefixWord, tailWord_7117978, baseEnd_7117978] using wordTrace_append hprefix tailTrace_7117978
  have hstable : (prefixWord ++ tailWord_7117978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117978).length < 2 ^ (prefixWord ++ tailWord_7117978).sum := by decide
  have hdescent : baseEnd_7117978 < baseStart_7117978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7117982 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_7117982 : Nat := 118140960795 + 7117982 * 2 ^ 59
def prefixEnd_7117982 : Nat := 4983230072969 + 3 ^ 40 * 7117982 * 2
def baseEnd_7117982 : Nat := 3654946056051475096390003

theorem tailTrace_7117982 : CollatzResearch.WordTrace tailWord_7117982 prefixEnd_7117982 3654946056051475096390003 := by
  unfold tailWord_7117982
  simp only [CollatzResearch.WordTrace]
  refine ⟨32451766462346792923438525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173076087799182895591672133 32451766462346792923438525)
  ·
    refine ⟨12169412423380047346289447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32451766462346792923438525 12169412423380047346289447)
    ·
      refine ⟨18254118635070071019434171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12169412423380047346289447 18254118635070071019434171)
      ·
        refine ⟨27381177952605106529151257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18254118635070071019434171 27381177952605106529151257)
        ·
          refine ⟨20535883464453829896863443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27381177952605106529151257 20535883464453829896863443)
          ·
            refine ⟨30803825196680744845295165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20535883464453829896863443 30803825196680744845295165)
            ·
              refine ⟨11551434448755279316985687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30803825196680744845295165 11551434448755279316985687)
              ·
                refine ⟨17327151673132918975478531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11551434448755279316985687 17327151673132918975478531)
                ·
                  refine ⟨25990727509699378463217797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17327151673132918975478531 25990727509699378463217797)
                  ·
                    refine ⟨4873261408068633461853337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25990727509699378463217797 4873261408068633461853337)
                    ·
                      refine ⟨3654946056051475096390003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4873261408068633461853337 3654946056051475096390003)
                      ·
                        rfl

theorem cell23_7117982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_7117982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7117982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7117982 prefixEnd_7117982 := by exact prefixLift 7117982
  have htrace : WordTrace (prefixWord ++ tailWord_7117982) baseStart_7117982 baseEnd_7117982 := by
    simpa [prefixWord, tailWord_7117982, baseEnd_7117982] using wordTrace_append hprefix tailTrace_7117982
  have hstable : (prefixWord ++ tailWord_7117982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7117982).length < 2 ^ (prefixWord ++ tailWord_7117982).sum := by decide
  have hdescent : baseEnd_7117982 < baseStart_7117982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7117982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118065 : List Nat := [1, 2, 2, 2, 2, 1, 1, 7, 1, 4]
def baseStart_7118065 : Nat := 118140960795 + 7118065 * 2 ^ 59
def prefixEnd_7118065 : Nat := 4983230072969 + 3 ^ 40 * 7118065 * 2
def baseEnd_7118065 : Nat := 1218329558315266090550707

theorem tailTrace_7118065 : CollatzResearch.WordTrace tailWord_7118065 prefixEnd_7118065 1218329558315266090550707 := by
  unfold tailWord_7118065
  simp only [CollatzResearch.WordTrace]
  refine ⟨259617158957473648562779649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173078105971649099041853099 259617158957473648562779649)
  ·
    refine ⟨194712869218105236422084737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259617158957473648562779649 194712869218105236422084737)
    ·
      refine ⟨146034651913578927316563553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194712869218105236422084737 146034651913578927316563553)
      ·
        refine ⟨109525988935184195487422665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146034651913578927316563553 109525988935184195487422665)
        ·
          refine ⟨82144491701388146615566999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109525988935184195487422665 82144491701388146615566999)
          ·
            refine ⟨123216737552082219923350499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82144491701388146615566999 123216737552082219923350499)
            ·
              refine ⟨184825106328123329885025749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123216737552082219923350499 184825106328123329885025749)
              ·
                refine ⟨4331838429565390544180291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 184825106328123329885025749 4331838429565390544180291)
                ·
                  refine ⟨6497757644348085816270437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4331838429565390544180291 6497757644348085816270437)
                  ·
                    refine ⟨1218329558315266090550707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6497757644348085816270437 1218329558315266090550707)
                    ·
                      rfl

theorem cell23_7118065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_7118065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118065 prefixEnd_7118065 := by exact prefixLift 7118065
  have htrace : WordTrace (prefixWord ++ tailWord_7118065) baseStart_7118065 baseEnd_7118065 := by
    simpa [prefixWord, tailWord_7118065, baseEnd_7118065] using wordTrace_append hprefix tailTrace_7118065
  have hstable : (prefixWord ++ tailWord_7118065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118065).length < 2 ^ (prefixWord ++ tailWord_7118065).sum := by decide
  have hdescent : baseEnd_7118065 < baseStart_7118065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118101 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_7118101 : Nat := 118140960795 + 7118101 * 2 ^ 59
def prefixEnd_7118101 : Nat := 4983230072969 + 3 ^ 40 * 7118101 * 2
def baseEnd_7118101 : Nat := 3655007160249360130801955

theorem tailTrace_7118101 : CollatzResearch.WordTrace tailWord_7118101 prefixEnd_7118101 3655007160249360130801955 := by
  unfold tailWord_7118101
  simp only [CollatzResearch.WordTrace]
  refine ⟨259618471985343226711090157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173078981323562151140726771 259618471985343226711090157)
  ·
    refine ⟨97356926994503710016658809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259618471985343226711090157 97356926994503710016658809)
    ·
      refine ⟨73017695245877782512494107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97356926994503710016658809 73017695245877782512494107)
      ·
        refine ⟨109526542868816673768741161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73017695245877782512494107 109526542868816673768741161)
        ·
          refine ⟨82144907151612505326555871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109526542868816673768741161 82144907151612505326555871)
          ·
            refine ⟨123217360727418757989833807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82144907151612505326555871 123217360727418757989833807)
            ·
              refine ⟨184826041091128136984750711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123217360727418757989833807 184826041091128136984750711)
              ·
                refine ⟨277239061636692205477126067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184826041091128136984750711 277239061636692205477126067)
                ·
                  refine ⟨415858592455038308215689101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277239061636692205477126067 415858592455038308215689101)
                  ·
                    refine ⟨155946972170639365580883413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 415858592455038308215689101 155946972170639365580883413)
                    ·
                      refine ⟨3655007160249360130801955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 155946972170639365580883413 3655007160249360130801955)
                      ·
                        rfl

theorem cell23_7118101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_7118101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118101 prefixEnd_7118101 := by exact prefixLift 7118101
  have htrace : WordTrace (prefixWord ++ tailWord_7118101) baseStart_7118101 baseEnd_7118101 := by
    simpa [prefixWord, tailWord_7118101, baseEnd_7118101] using wordTrace_append hprefix tailTrace_7118101
  have hstable : (prefixWord ++ tailWord_7118101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118101).length < 2 ^ (prefixWord ++ tailWord_7118101).sum := by decide
  have hdescent : baseEnd_7118101 < baseStart_7118101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118108 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 3, 5]
def baseStart_7118108 : Nat := 118140960795 + 7118108 * 2 ^ 59
def prefixEnd_7118108 : Nat := 4983230072969 + 3 ^ 40 * 7118108 * 2
def baseEnd_7118108 : Nat := 1218336918204647201138141

theorem tailTrace_7118108 : CollatzResearch.WordTrace tailWord_7118108 prefixEnd_7118108 1218336918204647201138141 := by
  unfold tailWord_7118108
  simp only [CollatzResearch.WordTrace]
  refine ⟨129809363648158933453297489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173079151530878577937729985 129809363648158933453297489)
  ·
    refine ⟨97357022736119200089973117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129809363648158933453297489 97357022736119200089973117)
    ·
      refine ⟨36508883526044700033739919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97357022736119200089973117 36508883526044700033739919)
      ·
        refine ⟨54763325289067050050609879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36508883526044700033739919 54763325289067050050609879)
        ·
          refine ⟨82144987933600575075914819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54763325289067050050609879 82144987933600575075914819)
          ·
            refine ⟨123217481900400862613872229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82144987933600575075914819 123217481900400862613872229)
            ·
              refine ⟨23103277856325161740101043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123217481900400862613872229 23103277856325161740101043)
              ·
                refine ⟨34654916784487742610151565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23103277856325161740101043 34654916784487742610151565)
                ·
                  refine ⟨12995593794182903478806837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34654916784487742610151565 12995593794182903478806837)
                  ·
                    refine ⟨1218336918204647201138141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12995593794182903478806837 1218336918204647201138141)
                    ·
                      rfl

theorem cell23_7118108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_7118108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118108 prefixEnd_7118108 := by exact prefixLift 7118108
  have htrace : WordTrace (prefixWord ++ tailWord_7118108) baseStart_7118108 baseEnd_7118108 := by
    simpa [prefixWord, tailWord_7118108, baseEnd_7118108] using wordTrace_append hprefix tailTrace_7118108
  have hstable : (prefixWord ++ tailWord_7118108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118108).length < 2 ^ (prefixWord ++ tailWord_7118108).sum := by decide
  have hdescent : baseEnd_7118108 < baseStart_7118108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118115 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 1, 5, 2]
def baseStart_7118115 : Nat := 118140960795 + 7118115 * 2 ^ 59
def prefixEnd_7118115 : Nat := 4983230072969 + 3 ^ 40 * 7118115 * 2
def baseEnd_7118115 : Nat := 3655014348978523076026891

theorem tailTrace_7118115 : CollatzResearch.WordTrace tailWord_7118115 prefixEnd_7118115 3655014348978523076026891 := by
  unfold tailWord_7118115
  simp only [CollatzResearch.WordTrace]
  refine ⟨259618982607292507102099799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173079321738195004734733199 259618982607292507102099799)
  ·
    refine ⟨389428473910938760653149699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259618982607292507102099799 389428473910938760653149699)
    ·
      refine ⟨584142710866408140979724549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389428473910938760653149699 584142710866408140979724549)
      ·
        refine ⟨109526758287451526433698353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 584142710866408140979724549 109526758287451526433698353)
        ·
          refine ⟨82145068715588644825273765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109526758287451526433698353 82145068715588644825273765)
          ·
            refine ⟨15402200384172870904738831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82145068715588644825273765 15402200384172870904738831)
            ·
              refine ⟨23103300576259306357108247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15402200384172870904738831 23103300576259306357108247)
              ·
                refine ⟨34654950864388959535662371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23103300576259306357108247 34654950864388959535662371)
                ·
                  refine ⟨51982426296583439303493557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34654950864388959535662371 51982426296583439303493557)
                  ·
                    refine ⟨4873352465304697434702521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51982426296583439303493557 4873352465304697434702521)
                    ·
                      refine ⟨3655014348978523076026891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4873352465304697434702521 3655014348978523076026891)
                      ·
                        rfl

theorem cell23_7118115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_7118115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118115 prefixEnd_7118115 := by exact prefixLift 7118115
  have htrace : WordTrace (prefixWord ++ tailWord_7118115) baseStart_7118115 baseEnd_7118115 := by
    simpa [prefixWord, tailWord_7118115, baseEnd_7118115] using wordTrace_append hprefix tailTrace_7118115
  have hstable : (prefixWord ++ tailWord_7118115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118115).length < 2 ^ (prefixWord ++ tailWord_7118115).sum := by decide
  have hdescent : baseEnd_7118115 < baseStart_7118115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118121 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 7, 6]
def baseStart_7118121 : Nat := 118140960795 + 7118121 * 2 ^ 59
def prefixEnd_7118121 : Nat := 4983230072969 + 3 ^ 40 * 7118121 * 2
def baseEnd_7118121 : Nat := 1218339143287483350850621

theorem tailTrace_7118121 : CollatzResearch.WordTrace tailWord_7118121 prefixEnd_7118121 1218339143287483350850621 := by
  unfold tailWord_7118121
  simp only [CollatzResearch.WordTrace]
  refine ⟨259619201445270770126818217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173079467630180513417878811 259619201445270770126818217)
  ·
    refine ⟨194714401083953077595113663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259619201445270770126818217 194714401083953077595113663)
    ·
      refine ⟨292071601625929616392670495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194714401083953077595113663 292071601625929616392670495)
      ·
        refine ⟨438107402438894424589005743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292071601625929616392670495 438107402438894424589005743)
        ·
          refine ⟨657161103658341636883508615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438107402438894424589005743 657161103658341636883508615)
          ·
            refine ⟨985741655487512455325262923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657161103658341636883508615 985741655487512455325262923)
            ·
              refine ⟨1478612483231268682987894385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985741655487512455325262923 1478612483231268682987894385)
              ·
                refine ⟨1108959362423451512240920789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1478612483231268682987894385 1108959362423451512240920789)
                ·
                  refine ⟨25991235056799644818146581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1108959362423451512240920789 25991235056799644818146581)
                  ·
                    refine ⟨1218339143287483350850621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25991235056799644818146581 1218339143287483350850621)
                    ·
                      rfl

theorem cell23_7118121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 6].length) (baseStart_7118121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118121 prefixEnd_7118121 := by exact prefixLift 7118121
  have htrace : WordTrace (prefixWord ++ tailWord_7118121) baseStart_7118121 baseEnd_7118121 := by
    simpa [prefixWord, tailWord_7118121, baseEnd_7118121] using wordTrace_append hprefix tailTrace_7118121
  have hstable : (prefixWord ++ tailWord_7118121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118121).length < 2 ^ (prefixWord ++ tailWord_7118121).sum := by decide
  have hdescent : baseEnd_7118121 < baseStart_7118121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118132 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_7118132 : Nat := 118140960795 + 7118132 * 2 ^ 59
def prefixEnd_7118132 : Nat := 4983230072969 + 3 ^ 40 * 7118132 * 2
def baseEnd_7118132 : Nat := 3655023078149649509514313

theorem tailTrace_7118132 : CollatzResearch.WordTrace tailWord_7118132 prefixEnd_7118132 3655023078149649509514313 := by
  unfold tailWord_7118132
  simp only [CollatzResearch.WordTrace]
  refine ⟨129809801324115459502734325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173079735098820612670312433 129809801324115459502734325)
  ·
    refine ⟨12169668874135824328381343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129809801324115459502734325 12169668874135824328381343)
    ·
      refine ⟨18254503311203736492572015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12169668874135824328381343 18254503311203736492572015)
      ·
        refine ⟨27381754966805604738858023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18254503311203736492572015 27381754966805604738858023)
        ·
          refine ⟨41072632450208407108287035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27381754966805604738858023 41072632450208407108287035)
          ·
            refine ⟨61608948675312610662430553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41072632450208407108287035 61608948675312610662430553)
            ·
              refine ⟨46206711506484457996822915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61608948675312610662430553 46206711506484457996822915)
              ·
                refine ⟨69310067259726686995234373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46206711506484457996822915 69310067259726686995234373)
                ·
                  refine ⟨12995637611198753811606445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69310067259726686995234373 12995637611198753811606445)
                  ·
                    refine ⟨4873364104199532679352417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12995637611198753811606445 4873364104199532679352417)
                    ·
                      refine ⟨3655023078149649509514313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4873364104199532679352417 3655023078149649509514313)
                      ·
                        rfl

theorem cell23_7118132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_7118132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118132 prefixEnd_7118132 := by exact prefixLift 7118132
  have htrace : WordTrace (prefixWord ++ tailWord_7118132) baseStart_7118132 baseEnd_7118132 := by
    simpa [prefixWord, tailWord_7118132, baseEnd_7118132] using wordTrace_append hprefix tailTrace_7118132
  have hstable : (prefixWord ++ tailWord_7118132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118132).length < 2 ^ (prefixWord ++ tailWord_7118132).sum := by decide
  have hdescent : baseEnd_7118132 < baseStart_7118132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118158 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_7118158 : Nat := 118140960795 + 7118158 * 2 ^ 59
def prefixEnd_7118158 : Nat := 4983230072969 + 3 ^ 40 * 7118158 * 2
def baseEnd_7118158 : Nat := 3655036428646666407789193

theorem tailTrace_7118158 : CollatzResearch.WordTrace tailWord_7118158 prefixEnd_7118158 3655036428646666407789193 := by
  unfold tailWord_7118158
  simp only [CollatzResearch.WordTrace]
  refine ⟨32452568868267090680739391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173080367297424483630610085 32452568868267090680739391)
  ·
    refine ⟨48678853302400636021109087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32452568868267090680739391 48678853302400636021109087)
    ·
      refine ⟨73018279953600954031663631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48678853302400636021109087 73018279953600954031663631)
      ·
        refine ⟨109527419930401431047495447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73018279953600954031663631 109527419930401431047495447)
        ·
          refine ⟨164291129895602146571243171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109527419930401431047495447 164291129895602146571243171)
          ·
            refine ⟨246436694843403219856864757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164291129895602146571243171 246436694843403219856864757)
            ·
              refine ⟨23103440141569051861581071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 246436694843403219856864757 23103440141569051861581071)
              ·
                refine ⟨34655160212353577792371607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23103440141569051861581071 34655160212353577792371607)
                ·
                  refine ⟨51982740318530366688557411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34655160212353577792371607 51982740318530366688557411)
                  ·
                    refine ⟨77974110477795550032836117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51982740318530366688557411 77974110477795550032836117)
                    ·
                      refine ⟨3655036428646666407789193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77974110477795550032836117 3655036428646666407789193)
                      ·
                        rfl

theorem cell23_7118158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_7118158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118158 prefixEnd_7118158 := by exact prefixLift 7118158
  have htrace : WordTrace (prefixWord ++ tailWord_7118158) baseStart_7118158 baseEnd_7118158 := by
    simpa [prefixWord, tailWord_7118158, baseEnd_7118158] using wordTrace_append hprefix tailTrace_7118158
  have hstable : (prefixWord ++ tailWord_7118158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118158).length < 2 ^ (prefixWord ++ tailWord_7118158).sum := by decide
  have hdescent : baseEnd_7118158 < baseStart_7118158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118206 : List Nat := [4, 2, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_7118206 : Nat := 118140960795 + 7118206 * 2 ^ 59
def prefixEnd_7118206 : Nat := 4983230072969 + 3 ^ 40 * 7118206 * 2
def baseEnd_7118206 : Nat := 1218353691906027406662991

theorem tailTrace_7118206 : CollatzResearch.WordTrace tailWord_7118206 prefixEnd_7118206 1218353691906027406662991 := by
  unfold tailWord_7118206
  simp only [CollatzResearch.WordTrace]
  refine ⟨32452787706245353705457809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173081534433308553095774981 32452787706245353705457809)
  ·
    refine ⟨24339590779684015279093357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32452787706245353705457809 24339590779684015279093357)
    ·
      refine ⟨9127346542381505729660009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24339590779684015279093357 9127346542381505729660009)
      ·
        refine ⟨6845509906786129297245007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9127346542381505729660009 6845509906786129297245007)
        ·
          refine ⟨10268264860179193945867511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6845509906786129297245007 10268264860179193945867511)
          ·
            refine ⟨15402397290268790918801267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10268264860179193945867511 15402397290268790918801267)
            ·
              refine ⟨23103595935403186378201901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15402397290268790918801267 23103595935403186378201901)
              ·
                refine ⟨8663848475776194891825713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23103595935403186378201901 8663848475776194891825713)
                ·
                  refine ⟨6497886356832146168869285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8663848475776194891825713 6497886356832146168869285)
                  ·
                    refine ⟨1218353691906027406662991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6497886356832146168869285 1218353691906027406662991)
                    ·
                      rfl

theorem cell23_7118206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_7118206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118206 prefixEnd_7118206 := by exact prefixLift 7118206
  have htrace : WordTrace (prefixWord ++ tailWord_7118206) baseStart_7118206 baseEnd_7118206 := by
    simpa [prefixWord, tailWord_7118206, baseEnd_7118206] using wordTrace_append hprefix tailTrace_7118206
  have hstable : (prefixWord ++ tailWord_7118206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118206).length < 2 ^ (prefixWord ++ tailWord_7118206).sum := by decide
  have hdescent : baseEnd_7118206 < baseStart_7118206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118252 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 4, 2, 2]
def baseStart_7118252 : Nat := 118140960795 + 7118252 * 2 ^ 59
def prefixEnd_7118252 : Nat := 4983230072969 + 3 ^ 40 * 7118252 * 2
def baseEnd_7118252 : Nat := 3655084695828189040013761

theorem tailTrace_7118252 : CollatzResearch.WordTrace tailWord_7118252 prefixEnd_7118252 3655084695828189040013761 := by
  unfold tailWord_7118252
  simp only [CollatzResearch.WordTrace]
  refine ⟨129811989703898089749918505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173082652938530786333224673 129811989703898089749918505)
  ·
    refine ⟨97358992277923567312438879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129811989703898089749918505 97358992277923567312438879)
    ·
      refine ⟨146038488416885350968658319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97358992277923567312438879 146038488416885350968658319)
      ·
        refine ⟨219057732625328026452987479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146038488416885350968658319 219057732625328026452987479)
        ·
          refine ⟨328586598937992039679481219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219057732625328026452987479 328586598937992039679481219)
          ·
            refine ⟨492879898406988059519221829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328586598937992039679481219 492879898406988059519221829)
            ·
              refine ⟨92414980951310261159854093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 492879898406988059519221829 92414980951310261159854093)
              ·
                refine ⟨34655617856741347934945285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92414980951310261159854093 34655617856741347934945285)
                ·
                  refine ⟨6497928348139002737802241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34655617856741347934945285 6497928348139002737802241)
                  ·
                    refine ⟨4873446261104252053351681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6497928348139002737802241 4873446261104252053351681)
                    ·
                      refine ⟨3655084695828189040013761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4873446261104252053351681 3655084695828189040013761)
                      ·
                        rfl

theorem cell23_7118252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 2, 2].length) (baseStart_7118252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118252 prefixEnd_7118252 := by exact prefixLift 7118252
  have htrace : WordTrace (prefixWord ++ tailWord_7118252) baseStart_7118252 baseEnd_7118252 := by
    simpa [prefixWord, tailWord_7118252, baseEnd_7118252] using wordTrace_append hprefix tailTrace_7118252
  have hstable : (prefixWord ++ tailWord_7118252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118252).length < 2 ^ (prefixWord ++ tailWord_7118252).sum := by decide
  have hdescent : baseEnd_7118252 < baseStart_7118252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118269 : List Nat := [1, 4, 1, 2, 2, 1, 1, 5, 2, 2, 2]
def baseStart_7118269 : Nat := 118140960795 + 7118269 * 2 ^ 59
def prefixEnd_7118269 : Nat := 4983230072969 + 3 ^ 40 * 7118269 * 2
def baseEnd_7118269 : Nat := 3655093424999315473501183

theorem tailTrace_7118269 : CollatzResearch.WordTrace tailWord_7118269 prefixEnd_7118269 3655093424999315473501183 := by
  unfold tailWord_7118269
  simp only [CollatzResearch.WordTrace]
  refine ⟨259624599448734591403205861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173083066299156394268803907 259624599448734591403205861)
  ·
    refine ⟨48679612396637735888101099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259624599448734591403205861 48679612396637735888101099)
    ·
      refine ⟨73019418594956603832151649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48679612396637735888101099 73019418594956603832151649)
      ·
        refine ⟨54764563946217452874113737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73019418594956603832151649 54764563946217452874113737)
        ·
          refine ⟨41073422959663089655585303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54764563946217452874113737 41073422959663089655585303)
          ·
            refine ⟨61610134439494634483377955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41073422959663089655585303 61610134439494634483377955)
            ·
              refine ⟨92415201659241951725066933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61610134439494634483377955 92415201659241951725066933)
              ·
                refine ⟨8663925155553932974225025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92415201659241951725066933 8663925155553932974225025)
                ·
                  refine ⟨6497943866665449730668769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8663925155553932974225025 6497943866665449730668769)
                  ·
                    refine ⟨4873457899999087298001577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6497943866665449730668769 4873457899999087298001577)
                    ·
                      refine ⟨3655093424999315473501183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4873457899999087298001577 3655093424999315473501183)
                      ·
                        rfl

theorem cell23_7118269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_7118269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118269 prefixEnd_7118269 := by exact prefixLift 7118269
  have htrace : WordTrace (prefixWord ++ tailWord_7118269) baseStart_7118269 baseEnd_7118269 := by
    simpa [prefixWord, tailWord_7118269, baseEnd_7118269] using wordTrace_append hprefix tailTrace_7118269
  have hstable : (prefixWord ++ tailWord_7118269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118269).length < 2 ^ (prefixWord ++ tailWord_7118269).sum := by decide
  have hdescent : baseEnd_7118269 < baseStart_7118269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118288 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 1, 7]
def baseStart_7118288 : Nat := 118140960795 + 7118288 * 2 ^ 59
def prefixEnd_7118288 : Nat := 4983230072969 + 3 ^ 40 * 7118288 * 2
def baseEnd_7118288 : Nat := 1218367727043916966387865

theorem tailTrace_7118288 : CollatzResearch.WordTrace tailWord_7118288 prefixEnd_7118288 1218367727043916966387865 := by
  unfold tailWord_7118288
  simp only [CollatzResearch.WordTrace]
  refine ⟨129812646217832878824073759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173083528290443838432098345 129812646217832878824073759)
  ·
    refine ⟨194718969326749318236110639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129812646217832878824073759 194718969326749318236110639)
    ·
      refine ⟨292078453990123977354165959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194718969326749318236110639 292078453990123977354165959)
      ·
        refine ⟨438117680985185966031248939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292078453990123977354165959 438117680985185966031248939)
        ·
          refine ⟨657176521477778949046873409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438117680985185966031248939 657176521477778949046873409)
          ·
            refine ⟨492882391108334211785155057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657176521477778949046873409 492882391108334211785155057)
            ·
              refine ⟨369661793331250658838866293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492882391108334211785155057 369661793331250658838866293)
              ·
                refine ⟨34655793124804749266143715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 369661793331250658838866293 34655793124804749266143715)
                ·
                  refine ⟨51983689687207123899215573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34655793124804749266143715 51983689687207123899215573)
                  ·
                    refine ⟨1218367727043916966387865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51983689687207123899215573 1218367727043916966387865)
                    ·
                      rfl

theorem cell23_7118288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 7].length) (baseStart_7118288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118288 prefixEnd_7118288 := by exact prefixLift 7118288
  have htrace : WordTrace (prefixWord ++ tailWord_7118288) baseStart_7118288 baseEnd_7118288 := by
    simpa [prefixWord, tailWord_7118288, baseEnd_7118288] using wordTrace_append hprefix tailTrace_7118288
  have hstable : (prefixWord ++ tailWord_7118288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118288).length < 2 ^ (prefixWord ++ tailWord_7118288).sum := by decide
  have hdescent : baseEnd_7118288 < baseStart_7118288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118335 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 5, 4]
def baseStart_7118335 : Nat := 118140960795 + 7118335 * 2 ^ 59
def prefixEnd_7118335 : Nat := 4983230072969 + 3 ^ 40 * 7118335 * 2
def baseEnd_7118335 : Nat := 1218375771574170738425293

theorem tailTrace_7118335 : CollatzResearch.WordTrace tailWord_7118335 prefixEnd_7118335 1218375771574170738425293 := by
  unfold tailWord_7118335
  simp only [CollatzResearch.WordTrace]
  refine ⟨259627006666495484675108459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173084671110996989783405639 259627006666495484675108459)
  ·
    refine ⟨389440509999743227012662689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259627006666495484675108459 389440509999743227012662689)
    ·
      refine ⟨292080382499807420259497017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389440509999743227012662689 292080382499807420259497017)
      ·
        refine ⟨219060286874855565194622763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292080382499807420259497017 219060286874855565194622763)
        ·
          refine ⟨328590430312283347791934145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219060286874855565194622763 328590430312283347791934145)
          ·
            refine ⟨246442822734212510843950609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328590430312283347791934145 246442822734212510843950609)
            ·
              refine ⟨184832117050659383132962957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246442822734212510843950609 184832117050659383132962957)
              ·
                refine ⟨69312043893997268674861109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184832117050659383132962957 69312043893997268674861109)
                ·
                  refine ⟨6498004115062243938268229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69312043893997268674861109 6498004115062243938268229)
                  ·
                    refine ⟨1218375771574170738425293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6498004115062243938268229 1218375771574170738425293)
                    ·
                      rfl

theorem cell23_7118335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 4].length) (baseStart_7118335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118335 prefixEnd_7118335 := by exact prefixLift 7118335
  have htrace : WordTrace (prefixWord ++ tailWord_7118335) baseStart_7118335 baseEnd_7118335 := by
    simpa [prefixWord, tailWord_7118335, baseEnd_7118335] using wordTrace_append hprefix tailTrace_7118335
  have hstable : (prefixWord ++ tailWord_7118335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118335).length < 2 ^ (prefixWord ++ tailWord_7118335).sum := by decide
  have hdescent : baseEnd_7118335 < baseStart_7118335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118345 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 1, 4, 3]
def baseStart_7118345 : Nat := 118140960795 + 7118345 * 2 ^ 59
def prefixEnd_7118345 : Nat := 4983230072969 + 3 ^ 40 * 7118345 * 2
def baseEnd_7118345 : Nat := 3655132449529057176150833

theorem tailTrace_7118345 : CollatzResearch.WordTrace tailWord_7118345 prefixEnd_7118345 3655132449529057176150833 := by
  unfold tailWord_7118345
  simp only [CollatzResearch.WordTrace]
  refine ⟨259627371396459256382972489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173084914264306170921981659 259627371396459256382972489)
  ·
    refine ⟨194720528547344442287229367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259627371396459256382972489 194720528547344442287229367)
    ·
      refine ⟨292080792821016663430844051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194720528547344442287229367 292080792821016663430844051)
      ·
        refine ⟨438121189231524995146266077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292080792821016663430844051 438121189231524995146266077)
        ·
          refine ⟨164295445961821873179849779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438121189231524995146266077 164295445961821873179849779)
          ·
            refine ⟨246443168942732809769774669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164295445961821873179849779 246443168942732809769774669)
            ·
              refine ⟨92416188353524803663665501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246443168942732809769774669 92416188353524803663665501)
              ·
                refine ⟨34656070632571801373874563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92416188353524803663665501 34656070632571801373874563)
                ·
                  refine ⟨51984105948857702060811845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34656070632571801373874563 51984105948857702060811845)
                  ·
                    refine ⟨9747019865410819136402221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51984105948857702060811845 9747019865410819136402221)
                    ·
                      refine ⟨3655132449529057176150833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9747019865410819136402221 3655132449529057176150833)
                      ·
                        rfl

theorem cell23_7118345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 4, 3].length) (baseStart_7118345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118345 prefixEnd_7118345 := by exact prefixLift 7118345
  have htrace : WordTrace (prefixWord ++ tailWord_7118345) baseStart_7118345 baseEnd_7118345 := by
    simpa [prefixWord, tailWord_7118345, baseEnd_7118345] using wordTrace_append hprefix tailTrace_7118345
  have hstable : (prefixWord ++ tailWord_7118345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118345).length < 2 ^ (prefixWord ++ tailWord_7118345).sum := by decide
  have hdescent : baseEnd_7118345 < baseStart_7118345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118365 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 8]
def baseStart_7118365 : Nat := 118140960795 + 7118365 * 2 ^ 59
def prefixEnd_7118365 : Nat := 4983230072969 + 3 ^ 40 * 7118365 * 2
def baseEnd_7118365 : Nat := 406126968793571899766749

theorem tailTrace_7118365 : CollatzResearch.WordTrace tailWord_7118365 prefixEnd_7118365 406126968793571899766749 := by
  unfold tailWord_7118365
  simp only [CollatzResearch.WordTrace]
  refine ⟨259628100856386799798700549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173085400570924533199133699 259628100856386799798700549)
  ·
    refine ⟨48680268910572524962256353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259628100856386799798700549 48680268910572524962256353)
    ·
      refine ⟨36510201682929393721692265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48680268910572524962256353 36510201682929393721692265)
      ·
        refine ⟨27382651262197045291269199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36510201682929393721692265 27382651262197045291269199)
        ·
          refine ⟨41073976893295567936903799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27382651262197045291269199 41073976893295567936903799)
          ·
            refine ⟨61610965339943351905355699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41073976893295567936903799 61610965339943351905355699)
            ·
              refine ⟨92416448009915027858033549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61610965339943351905355699 92416448009915027858033549)
              ·
                refine ⟨34656168003718135446762581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92416448009915027858033549 34656168003718135446762581)
                ·
                  refine ⟨406126968793571899766749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34656168003718135446762581 406126968793571899766749)
                  ·
                    rfl

theorem cell23_7118365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_7118365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118365 prefixEnd_7118365 := by exact prefixLift 7118365
  have htrace : WordTrace (prefixWord ++ tailWord_7118365) baseStart_7118365 baseEnd_7118365 := by
    simpa [prefixWord, tailWord_7118365, baseEnd_7118365] using wordTrace_append hprefix tailTrace_7118365
  have hstable : (prefixWord ++ tailWord_7118365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118365).length < 2 ^ (prefixWord ++ tailWord_7118365).sum := by decide
  have hdescent : baseEnd_7118365 < baseStart_7118365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118369 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 3, 4]
def baseStart_7118369 : Nat := 118140960795 + 7118369 * 2 ^ 59
def prefixEnd_7118369 : Nat := 4983230072969 + 3 ^ 40 * 7118369 * 2
def baseEnd_7118369 : Nat := 1218381591021588360750241

theorem tailTrace_7118369 : CollatzResearch.WordTrace tailWord_7118369 prefixEnd_7118369 1218381591021588360750241 := by
  unfold tailWord_7118369
  simp only [CollatzResearch.WordTrace]
  refine ⟨259628246748372308481846161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173085497832248205654564107 259628246748372308481846161)
  ·
    refine ⟨194721185061279231361384621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259628246748372308481846161 194721185061279231361384621)
    ·
      refine ⟨73020444397979711760519233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194721185061279231361384621 73020444397979711760519233)
      ·
        refine ⟨54765333298484783820389425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73020444397979711760519233 54765333298484783820389425)
        ·
          refine ⟨41073999973863587865292069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54765333298484783820389425 41073999973863587865292069)
          ·
            refine ⟨7701374995099422724742263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41073999973863587865292069 7701374995099422724742263)
            ·
              refine ⟨11552062492649134087113395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7701374995099422724742263 11552062492649134087113395)
              ·
                refine ⟨17328093738973701130670093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11552062492649134087113395 17328093738973701130670093)
                ·
                  refine ⟨6498035152115137924001285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17328093738973701130670093 6498035152115137924001285)
                  ·
                    refine ⟨1218381591021588360750241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6498035152115137924001285 1218381591021588360750241)
                    ·
                      rfl

theorem cell23_7118369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_7118369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118369 prefixEnd_7118369 := by exact prefixLift 7118369
  have htrace : WordTrace (prefixWord ++ tailWord_7118369) baseStart_7118369 baseEnd_7118369 := by
    simpa [prefixWord, tailWord_7118369, baseEnd_7118369] using wordTrace_append hprefix tailTrace_7118369
  have hstable : (prefixWord ++ tailWord_7118369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118369).length < 2 ^ (prefixWord ++ tailWord_7118369).sum := by decide
  have hdescent : baseEnd_7118369 < baseStart_7118369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118432 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 2, 6, 2]
def baseStart_7118432 : Nat := 118140960795 + 7118432 * 2 ^ 59
def prefixEnd_7118432 : Nat := 4983230072969 + 3 ^ 40 * 7118432 * 2
def baseEnd_7118432 : Nat := 3655177122345998335762933

theorem tailTrace_7118432 : CollatzResearch.WordTrace tailWord_7118432 prefixEnd_7118432 3655177122345998335762933 := by
  unfold tailWord_7118432
  simp only [CollatzResearch.WordTrace]
  refine ⟨129815272273572035120694775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173087029698096046827593033 129815272273572035120694775)
  ·
    refine ⟨194722908410358052681042163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129815272273572035120694775 194722908410358052681042163)
    ·
      refine ⟨292084362615537079021563245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194722908410358052681042163 292084362615537079021563245)
      ·
        refine ⟨109531635980826404633086217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292084362615537079021563245 109531635980826404633086217)
        ·
          refine ⟨82148726985619803474814663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109531635980826404633086217 82148726985619803474814663)
          ·
            refine ⟨123223090478429705212221995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82148726985619803474814663 123223090478429705212221995)
            ·
              refine ⟨184834635717644557818332993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123223090478429705212221995 184834635717644557818332993)
              ·
                refine ⟨138625976788233418363749745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184834635717644557818332993 138625976788233418363749745)
                ·
                  refine ⟨103969482591175063772812309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138625976788233418363749745 103969482591175063772812309)
                  ·
                    refine ⟨4873569496461331114350577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103969482591175063772812309 4873569496461331114350577)
                    ·
                      refine ⟨3655177122345998335762933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4873569496461331114350577 3655177122345998335762933)
                      ·
                        rfl

theorem cell23_7118432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_7118432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118432 prefixEnd_7118432 := by exact prefixLift 7118432
  have htrace : WordTrace (prefixWord ++ tailWord_7118432) baseStart_7118432 baseEnd_7118432 := by
    simpa [prefixWord, tailWord_7118432, baseEnd_7118432] using wordTrace_append hprefix tailTrace_7118432
  have hstable : (prefixWord ++ tailWord_7118432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118432).length < 2 ^ (prefixWord ++ tailWord_7118432).sum := by decide
  have hdescent : baseEnd_7118432 < baseStart_7118432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118442 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 1, 6]
def baseStart_7118442 : Nat := 118140960795 + 7118442 * 2 ^ 59
def prefixEnd_7118442 : Nat := 4983230072969 + 3 ^ 40 * 7118442 * 2
def baseEnd_7118442 : Nat := 1218394085717514432212629

theorem tailTrace_7118442 : CollatzResearch.WordTrace tailWord_7118442 prefixEnd_7118442 1218394085717514432212629 := by
  unfold tailWord_7118442
  simp only [CollatzResearch.WordTrace]
  refine ⟨64907727319276960487313395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173087272851405227966169053 64907727319276960487313395)
  ·
    refine ⟨97361590978915440730970093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64907727319276960487313395 97361590978915440730970093)
    ·
      refine ⟨36510596617093290274113785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97361590978915440730970093 36510596617093290274113785)
      ·
        refine ⟨27382947462819967705585339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36510596617093290274113785 27382947462819967705585339)
        ·
          refine ⟨41074421194229951558378009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27382947462819967705585339 41074421194229951558378009)
          ·
            refine ⟨30805815895672463668783507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41074421194229951558378009 30805815895672463668783507)
            ·
              refine ⟨46208723843508695503175261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30805815895672463668783507 46208723843508695503175261)
              ·
                refine ⟨17328271441315760813690723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46208723843508695503175261 17328271441315760813690723)
                ·
                  refine ⟨25992407161973641220536085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17328271441315760813690723 25992407161973641220536085)
                  ·
                    refine ⟨1218394085717514432212629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25992407161973641220536085 1218394085717514432212629)
                    ·
                      rfl

theorem cell23_7118442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_7118442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118442 prefixEnd_7118442 := by exact prefixLift 7118442
  have htrace : WordTrace (prefixWord ++ tailWord_7118442) baseStart_7118442 baseEnd_7118442 := by
    simpa [prefixWord, tailWord_7118442, baseEnd_7118442] using wordTrace_append hprefix tailTrace_7118442
  have hstable : (prefixWord ++ tailWord_7118442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118442).length < 2 ^ (prefixWord ++ tailWord_7118442).sum := by decide
  have hdescent : baseEnd_7118442 < baseStart_7118442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118453 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_7118453 : Nat := 118140960795 + 7118453 * 2 ^ 59
def prefixEnd_7118453 : Nat := 4983230072969 + 3 ^ 40 * 7118453 * 2
def baseEnd_7118453 : Nat := 3655187905439742753600337

theorem tailTrace_7118453 : CollatzResearch.WordTrace tailWord_7118453 prefixEnd_7118453 3655187905439742753600337 := by
  unfold tailWord_7118453
  simp only [CollatzResearch.WordTrace]
  refine ⟨259631310480067990827904013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173087540320045327218602675 259631310480067990827904013)
  ·
    refine ⟨97361741430025496560464005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259631310480067990827904013 97361741430025496560464005)
    ·
      refine ⟨18255326518129780605087001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97361741430025496560464005 18255326518129780605087001)
      ·
        refine ⟨13691494888597335453815251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18255326518129780605087001 13691494888597335453815251)
        ·
          refine ⟨20537242332896003180722877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13691494888597335453815251 20537242332896003180722877)
          ·
            refine ⟨7701465874836001192771079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20537242332896003180722877 7701465874836001192771079)
            ·
              refine ⟨11552198812254001789156619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7701465874836001192771079 11552198812254001789156619)
              ·
                refine ⟨17328298218381002683734929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11552198812254001789156619 17328298218381002683734929)
                ·
                  refine ⟨12996223663785752012801197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17328298218381002683734929 12996223663785752012801197)
                  ·
                    refine ⟨4873583873919657004800449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12996223663785752012801197 4873583873919657004800449)
                    ·
                      refine ⟨3655187905439742753600337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4873583873919657004800449 3655187905439742753600337)
                      ·
                        rfl

theorem cell23_7118453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_7118453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118453 prefixEnd_7118453 := by exact prefixLift 7118453
  have htrace : WordTrace (prefixWord ++ tailWord_7118453) baseStart_7118453 baseEnd_7118453 := by
    simpa [prefixWord, tailWord_7118453, baseEnd_7118453] using wordTrace_append hprefix tailTrace_7118453
  have hstable : (prefixWord ++ tailWord_7118453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118453).length < 2 ^ (prefixWord ++ tailWord_7118453).sum := by decide
  have hdescent : baseEnd_7118453 < baseStart_7118453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118469 : List Nat := [1, 3, 1, 1, 4, 1, 3, 3, 1, 2, 3]
def baseStart_7118469 : Nat := 118140960795 + 7118469 * 2 ^ 59
def prefixEnd_7118469 : Nat := 4983230072969 + 3 ^ 40 * 7118469 * 2
def baseEnd_7118469 : Nat := 3655196121130214691000263

theorem tailTrace_7118469 : CollatzResearch.WordTrace tailWord_7118469 prefixEnd_7118469 3655196121130214691000263 := by
  unfold tailWord_7118469
  simp only [CollatzResearch.WordTrace]
  refine ⟨259631894048010025560486461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173087929365340017040324307 259631894048010025560486461)
  ·
    refine ⟨97361960268003759585182423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259631894048010025560486461 97361960268003759585182423)
    ·
      refine ⟨146042940402005639377773635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97361960268003759585182423 146042940402005639377773635)
      ·
        refine ⟨219064410603008459066660453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146042940402005639377773635 219064410603008459066660453)
        ·
          refine ⟨41074576988064086074998835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219064410603008459066660453 41074576988064086074998835)
          ·
            refine ⟨61611865482096129112498253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41074576988064086074998835 61611865482096129112498253)
            ·
              refine ⟨23104449555786048417186845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61611865482096129112498253 23104449555786048417186845)
              ·
                refine ⟨8664168583419768156445067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23104449555786048417186845 8664168583419768156445067)
                ·
                  refine ⟨12996252875129652234667601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8664168583419768156445067 12996252875129652234667601)
                  ·
                    refine ⟨9747189656347239176000701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12996252875129652234667601 9747189656347239176000701)
                    ·
                      refine ⟨3655196121130214691000263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9747189656347239176000701 3655196121130214691000263)
                      ·
                        rfl

theorem cell23_7118469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_7118469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118469 prefixEnd_7118469 := by exact prefixLift 7118469
  have htrace : WordTrace (prefixWord ++ tailWord_7118469) baseStart_7118469 baseEnd_7118469 := by
    simpa [prefixWord, tailWord_7118469, baseEnd_7118469] using wordTrace_append hprefix tailTrace_7118469
  have hstable : (prefixWord ++ tailWord_7118469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118469).length < 2 ^ (prefixWord ++ tailWord_7118469).sum := by decide
  have hdescent : baseEnd_7118469 < baseStart_7118469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118485 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 1, 9]
def baseStart_7118485 : Nat := 118140960795 + 7118485 * 2 ^ 59
def prefixEnd_7118485 : Nat := 4983230072969 + 3 ^ 40 * 7118485 * 2
def baseEnd_7118485 : Nat := 1218401445606895542800063

theorem tailTrace_7118485 : CollatzResearch.WordTrace tailWord_7118485 prefixEnd_7118485 1218401445606895542800063 := by
  unfold tailWord_7118485
  simp only [CollatzResearch.WordTrace]
  refine ⟨259632477615952060293068909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173088318410634706862045939 259632477615952060293068909)
  ·
    refine ⟨97362179105982022609900841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259632477615952060293068909 97362179105982022609900841)
    ·
      refine ⟨73021634329486516957425631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97362179105982022609900841 73021634329486516957425631)
      ·
        refine ⟨109532451494229775436138447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73021634329486516957425631 109532451494229775436138447)
        ·
          refine ⟨164298677241344663154207671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109532451494229775436138447 164298677241344663154207671)
          ·
            refine ⟨246448015862016994731311507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164298677241344663154207671 246448015862016994731311507)
            ·
              refine ⟨369672023793025492096967261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246448015862016994731311507 369672023793025492096967261)
              ·
                refine ⟨138627008922384559536362723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369672023793025492096967261 138627008922384559536362723)
                ·
                  refine ⟨207940513383576839304544085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138627008922384559536362723 207940513383576839304544085)
                  ·
                    refine ⟨1218401445606895542800063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 207940513383576839304544085 1218401445606895542800063)
                    ·
                      rfl

theorem cell23_7118485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_7118485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118485 prefixEnd_7118485 := by exact prefixLift 7118485
  have htrace : WordTrace (prefixWord ++ tailWord_7118485) baseStart_7118485 baseEnd_7118485 := by
    simpa [prefixWord, tailWord_7118485, baseEnd_7118485] using wordTrace_append hprefix tailTrace_7118485
  have hstable : (prefixWord ++ tailWord_7118485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118485).length < 2 ^ (prefixWord ++ tailWord_7118485).sum := by decide
  have hdescent : baseEnd_7118485 < baseStart_7118485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118517 : List Nat := [1, 3, 3, 3, 2, 2, 1, 3, 1, 2, 2]
def baseStart_7118517 : Nat := 118140960795 + 7118517 * 2 ^ 59
def prefixEnd_7118517 : Nat := 4983230072969 + 3 ^ 40 * 7118517 * 2
def baseEnd_7118517 : Nat := 3655220768201630503200043

theorem tailTrace_7118517 : CollatzResearch.WordTrace tailWord_7118517 prefixEnd_7118517 3655220768201630503200043 := by
  unfold tailWord_7118517
  simp only [CollatzResearch.WordTrace]
  refine ⟨259633644751836129758233805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173089096501224086505489203 259633644751836129758233805)
  ·
    refine ⟨97362616781938548659337677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259633644751836129758233805 97362616781938548659337677)
    ·
      refine ⟨36510981293226955747251629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97362616781938548659337677 36510981293226955747251629)
      ·
        refine ⟨13691617984960108405219361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36510981293226955747251629 13691617984960108405219361)
        ·
          refine ⟨10268713488720081303914521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13691617984960108405219361 10268713488720081303914521)
          ·
            refine ⟨7701535116540060977935891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10268713488720081303914521 7701535116540060977935891)
            ·
              refine ⟨11552302674810091466903837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7701535116540060977935891 11552302674810091466903837)
              ·
                refine ⟨4332113503053784300088939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11552302674810091466903837 4332113503053784300088939)
                ·
                  refine ⟨6498170254580676450133409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4332113503053784300088939 6498170254580676450133409)
                  ·
                    refine ⟨4873627690935507337600057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6498170254580676450133409 4873627690935507337600057)
                    ·
                      refine ⟨3655220768201630503200043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4873627690935507337600057 3655220768201630503200043)
                      ·
                        rfl

theorem cell23_7118517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_7118517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118517 prefixEnd_7118517 := by exact prefixLift 7118517
  have htrace : WordTrace (prefixWord ++ tailWord_7118517) baseStart_7118517 baseEnd_7118517 := by
    simpa [prefixWord, tailWord_7118517, baseEnd_7118517] using wordTrace_append hprefix tailTrace_7118517
  have hstable : (prefixWord ++ tailWord_7118517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118517).length < 2 ^ (prefixWord ++ tailWord_7118517).sum := by decide
  have hdescent : baseEnd_7118517 < baseStart_7118517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118542 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_7118542 : Nat := 118140960795 + 7118542 * 2 ^ 59
def prefixEnd_7118542 : Nat := 4983230072969 + 3 ^ 40 * 7118542 * 2
def baseEnd_7118542 : Nat := 3655233605217992905387427

theorem tailTrace_7118542 : CollatzResearch.WordTrace tailWord_7118542 prefixEnd_7118542 3655233605217992905387427 := by
  unfold tailWord_7118542
  simp only [CollatzResearch.WordTrace]
  refine ⟨32454319572093194878486735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173089704384497039351929253 32454319572093194878486735)
  ·
    refine ⟨48681479358139792317730103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32454319572093194878486735 48681479358139792317730103)
    ·
      refine ⟨73022219037209688476595155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48681479358139792317730103 73022219037209688476595155)
      ·
        refine ⟨109533328555814532714892733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73022219037209688476595155 109533328555814532714892733)
        ·
          refine ⟨41074998208430449768084775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109533328555814532714892733 41074998208430449768084775)
          ·
            refine ⟨61612497312645674652127163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41074998208430449768084775 61612497312645674652127163)
            ·
              refine ⟨92418745968968511978190745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61612497312645674652127163 92418745968968511978190745)
              ·
                refine ⟨69314059476726383983643059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92418745968968511978190745 69314059476726383983643059)
                ·
                  refine ⟨103971089215089575975464589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69314059476726383983643059 103971089215089575975464589)
                  ·
                    refine ⟨38989158455658590990799221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103971089215089575975464589 38989158455658590990799221)
                    ·
                      refine ⟨3655233605217992905387427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38989158455658590990799221 3655233605217992905387427)
                      ·
                        rfl

theorem cell23_7118542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_7118542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118542 prefixEnd_7118542 := by exact prefixLift 7118542
  have htrace : WordTrace (prefixWord ++ tailWord_7118542) baseStart_7118542 baseEnd_7118542 := by
    simpa [prefixWord, tailWord_7118542, baseEnd_7118542] using wordTrace_append hprefix tailTrace_7118542
  have hstable : (prefixWord ++ tailWord_7118542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118542).length < 2 ^ (prefixWord ++ tailWord_7118542).sum := by decide
  have hdescent : baseEnd_7118542 < baseStart_7118542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118552 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_7118552 : Nat := 118140960795 + 7118552 * 2 ^ 59
def prefixEnd_7118552 : Nat := 4983230072969 + 3 ^ 40 * 7118552 * 2
def baseEnd_7118552 : Nat := 3655238740024537866262381

theorem tailTrace_7118552 : CollatzResearch.WordTrace tailWord_7118552 prefixEnd_7118552 3655238740024537866262381 := by
  unfold tailWord_7118552
  simp only [CollatzResearch.WordTrace]
  refine ⟨129817460653354665367878955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173089947537806220490505273 129817460653354665367878955)
  ·
    refine ⟨194726190980031998051818433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129817460653354665367878955 194726190980031998051818433)
    ·
      refine ⟨146044643235023998538863825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194726190980031998051818433 146044643235023998538863825)
      ·
        refine ⟨109533482426267998904147869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146044643235023998538863825 109533482426267998904147869)
        ·
          refine ⟨41075055909850499589055451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109533482426267998904147869 41075055909850499589055451)
          ·
            refine ⟨61612583864775749383583177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41075055909850499589055451 61612583864775749383583177)
            ·
              refine ⟨46209437898581812037687383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61612583864775749383583177 46209437898581812037687383)
              ·
                refine ⟨69314156847872718056531075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46209437898581812037687383 69314156847872718056531075)
                ·
                  refine ⟨103971235271809077084796613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69314156847872718056531075 103971235271809077084796613)
                  ·
                    refine ⟨19494606613464201953399365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103971235271809077084796613 19494606613464201953399365)
                    ·
                      refine ⟨3655238740024537866262381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19494606613464201953399365 3655238740024537866262381)
                      ·
                        rfl

theorem cell23_7118552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_7118552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118552 prefixEnd_7118552 := by exact prefixLift 7118552
  have htrace : WordTrace (prefixWord ++ tailWord_7118552) baseStart_7118552 baseEnd_7118552 := by
    simpa [prefixWord, tailWord_7118552, baseEnd_7118552] using wordTrace_append hprefix tailTrace_7118552
  have hstable : (prefixWord ++ tailWord_7118552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118552).length < 2 ^ (prefixWord ++ tailWord_7118552).sum := by decide
  have hdescent : baseEnd_7118552 < baseStart_7118552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118596 : List Nat := [2, 3, 2, 2, 1, 3, 1, 4, 5]
def baseStart_7118596 : Nat := 118140960795 + 7118596 * 2 ^ 59
def prefixEnd_7118596 : Nat := 4983230072969 + 3 ^ 40 * 7118596 * 2
def baseEnd_7118596 : Nat := 406140148130370632679131

theorem tailTrace_7118596 : CollatzResearch.WordTrace tailWord_7118596 prefixEnd_7118596 406140148130370632679131 := by
  unfold tailWord_7118596
  simp only [CollatzResearch.WordTrace]
  refine ⟨129818263059274963125179821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173091017412366617500239761 129818263059274963125179821)
  ·
    refine ⟨48681848647228111171942433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129818263059274963125179821 48681848647228111171942433)
    ·
      refine ⟨36511386485421083378956825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48681848647228111171942433 36511386485421083378956825)
      ·
        refine ⟨27383539864065812534217619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36511386485421083378956825 27383539864065812534217619)
        ·
          refine ⟨41075309796098718801326429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27383539864065812534217619 41075309796098718801326429)
          ·
            refine ⟨15403241173537019550497411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41075309796098718801326429 15403241173537019550497411)
            ·
              refine ⟨23104861760305529325746117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15403241173537019550497411 23104861760305529325746117)
              ·
                refine ⟨4332161580057286748577397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23104861760305529325746117 4332161580057286748577397)
                ·
                  refine ⟨406140148130370632679131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4332161580057286748577397 406140148130370632679131)
                  ·
                    rfl

theorem cell23_7118596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_7118596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118596 prefixEnd_7118596 := by exact prefixLift 7118596
  have htrace : WordTrace (prefixWord ++ tailWord_7118596) baseStart_7118596 baseEnd_7118596 := by
    simpa [prefixWord, tailWord_7118596, baseEnd_7118596] using wordTrace_append hprefix tailTrace_7118596
  have hstable : (prefixWord ++ tailWord_7118596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118596).length < 2 ^ (prefixWord ++ tailWord_7118596).sum := by decide
  have hdescent : baseEnd_7118596 < baseStart_7118596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118629 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 1, 3, 4]
def baseStart_7118629 : Nat := 118140960795 + 7118629 * 2 ^ 59
def prefixEnd_7118629 : Nat := 4983230072969 + 3 ^ 40 * 7118629 * 2
def baseEnd_7118629 : Nat := 3655278278034934064999527

theorem tailTrace_7118629 : CollatzResearch.WordTrace tailWord_7118629 prefixEnd_7118629 3655278278034934064999527 := by
  unfold tailWord_7118629
  simp only [CollatzResearch.WordTrace]
  refine ⟨259637729727430372886310941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173091819818286915257540627 259637729727430372886310941)
  ·
    refine ⟨97364148647786389832366603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259637729727430372886310941 97364148647786389832366603)
    ·
      refine ⟨146046222971679584748549905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97364148647786389832366603 146046222971679584748549905)
      ·
        refine ⟨109534667228759688561412429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146046222971679584748549905 109534667228759688561412429)
        ·
          refine ⟨41075500210784883210529661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109534667228759688561412429 41075500210784883210529661)
          ·
            refine ⟨15403312579044331203948623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41075500210784883210529661 15403312579044331203948623)
            ·
              refine ⟨23104968868566496805922935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15403312579044331203948623 23104968868566496805922935)
              ·
                refine ⟨34657453302849745208884403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23104968868566496805922935 34657453302849745208884403)
                ·
                  refine ⟨51986179954274617813326605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34657453302849745208884403 51986179954274617813326605)
                  ·
                    refine ⟨19494817482852981679997477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51986179954274617813326605 19494817482852981679997477)
                    ·
                      refine ⟨3655278278034934064999527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19494817482852981679997477 3655278278034934064999527)
                      ·
                        rfl

theorem cell23_7118629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_7118629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118629 prefixEnd_7118629 := by exact prefixLift 7118629
  have htrace : WordTrace (prefixWord ++ tailWord_7118629) baseStart_7118629 baseEnd_7118629 := by
    simpa [prefixWord, tailWord_7118629, baseEnd_7118629] using wordTrace_append hprefix tailTrace_7118629
  have hstable : (prefixWord ++ tailWord_7118629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118629).length < 2 ^ (prefixWord ++ tailWord_7118629).sum := by decide
  have hdescent : baseEnd_7118629 < baseStart_7118629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118672 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 6]
def baseStart_7118672 : Nat := 118140960795 + 7118672 * 2 ^ 59
def prefixEnd_7118672 : Nat := 4983230072969 + 3 ^ 40 * 7118672 * 2
def baseEnd_7118672 : Nat := 3655300357703077396761829

theorem tailTrace_7118672 : CollatzResearch.WordTrace tailWord_7118672 prefixEnd_7118672 3655300357703077396761829 := by
  unfold tailWord_7118672
  simp only [CollatzResearch.WordTrace]
  refine ⟨129819649033137295615063135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173092865377516394153417513 129819649033137295615063135)
  ·
    refine ⟨194729473549705943422594703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129819649033137295615063135 194729473549705943422594703)
    ·
      refine ⟨292094210324558915133892055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194729473549705943422594703 292094210324558915133892055)
      ·
        refine ⟨438141315486838372700838083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292094210324558915133892055 438141315486838372700838083)
        ·
          refine ⟨657211973230257559051257125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438141315486838372700838083 657211973230257559051257125)
          ·
            refine ⟨123227244980673292322110711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 657211973230257559051257125 123227244980673292322110711)
            ·
              refine ⟨184840867471009938483166067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123227244980673292322110711 184840867471009938483166067)
              ·
                refine ⟨277261301206514907724749101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184840867471009938483166067 277261301206514907724749101)
                ·
                  refine ⟨103972987952443090396780913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 277261301206514907724749101 103972987952443090396780913)
                  ·
                    refine ⟨77979740964332317797585685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103972987952443090396780913 77979740964332317797585685)
                    ·
                      refine ⟨3655300357703077396761829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77979740964332317797585685 3655300357703077396761829)
                      ·
                        rfl

theorem cell23_7118672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_7118672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118672 prefixEnd_7118672 := by exact prefixLift 7118672
  have htrace : WordTrace (prefixWord ++ tailWord_7118672) baseStart_7118672 baseEnd_7118672 := by
    simpa [prefixWord, tailWord_7118672, baseEnd_7118672] using wordTrace_append hprefix tailTrace_7118672
  have hstable : (prefixWord ++ tailWord_7118672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118672).length < 2 ^ (prefixWord ++ tailWord_7118672).sum := by decide
  have hdescent : baseEnd_7118672 < baseStart_7118672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118690 : List Nat := [3, 3, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_7118690 : Nat := 118140960795 + 7118690 * 2 ^ 59
def prefixEnd_7118690 : Nat := 4983230072969 + 3 ^ 40 * 7118690 * 2
def baseEnd_7118690 : Nat := 1218436533451619442112249

theorem tailTrace_7118690 : CollatzResearch.WordTrace tailWord_7118690 prefixEnd_7118690 1218436533451619442112249 := by
  unfold tailWord_7118690
  simp only [CollatzResearch.WordTrace]
  refine ⟨64909988645052345076070381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173093303053472920202854349 64909988645052345076070381)
  ·
    refine ⟨24341245741894629403526393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64909988645052345076070381 24341245741894629403526393)
    ·
      refine ⟨18255934306420972052644795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24341245741894629403526393 18255934306420972052644795)
      ·
        refine ⟨27383901459631458078967193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18255934306420972052644795 27383901459631458078967193)
        ·
          refine ⟨20537926094723593559225395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27383901459631458078967193 20537926094723593559225395)
          ·
            refine ⟨30806889142085390338838093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20537926094723593559225395 30806889142085390338838093)
            ·
              refine ⟨11552583428282021377064285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30806889142085390338838093 11552583428282021377064285)
              ·
                refine ⟨4332218785605758016399107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11552583428282021377064285 4332218785605758016399107)
                ·
                  refine ⟨6498328178408637024598661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4332218785605758016399107 6498328178408637024598661)
                  ·
                    refine ⟨1218436533451619442112249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6498328178408637024598661 1218436533451619442112249)
                    ·
                      rfl

theorem cell23_7118690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_7118690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118690 prefixEnd_7118690 := by exact prefixLift 7118690
  have htrace : WordTrace (prefixWord ++ tailWord_7118690) baseStart_7118690 baseEnd_7118690 := by
    simpa [prefixWord, tailWord_7118690, baseEnd_7118690] using wordTrace_append hprefix tailTrace_7118690
  have hstable : (prefixWord ++ tailWord_7118690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118690).length < 2 ^ (prefixWord ++ tailWord_7118690).sum := by decide
  have hdescent : baseEnd_7118690 < baseStart_7118690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118719 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 4]
def baseStart_7118719 : Nat := 118140960795 + 7118719 * 2 ^ 59
def prefixEnd_7118719 : Nat := 4983230072969 + 3 ^ 40 * 7118719 * 2
def baseEnd_7118719 : Nat := 3655324491293838712874113

theorem tailTrace_7118719 : CollatzResearch.WordTrace tailWord_7118719 prefixEnd_7118719 3655324491293838712874113 := by
  unfold tailWord_7118719
  simp only [CollatzResearch.WordTrace]
  refine ⟨259641012297104318257087211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173094008198069545504724807 259641012297104318257087211)
  ·
    refine ⟨389461518445656477385630817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259641012297104318257087211 389461518445656477385630817)
    ·
      refine ⟨292096138834242358039223113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389461518445656477385630817 292096138834242358039223113)
      ·
        refine ⟨219072104125681768529417335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292096138834242358039223113 219072104125681768529417335)
        ·
          refine ⟨328608156188522652794126003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219072104125681768529417335 328608156188522652794126003)
          ·
            refine ⟨492912234282783979191189005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328608156188522652794126003 492912234282783979191189005)
            ·
              refine ⟨184842087856043992196695877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 492912234282783979191189005 184842087856043992196695877)
              ·
                refine ⟨34657891473008248536880477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184842087856043992196695877 34657891473008248536880477)
                ·
                  refine ⟨12996709302378093201330179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34657891473008248536880477 12996709302378093201330179)
                  ·
                    refine ⟨19495063953567139801995269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12996709302378093201330179 19495063953567139801995269)
                    ·
                      refine ⟨3655324491293838712874113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19495063953567139801995269 3655324491293838712874113)
                      ·
                        rfl

theorem cell23_7118719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_7118719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118719 prefixEnd_7118719 := by exact prefixLift 7118719
  have htrace : WordTrace (prefixWord ++ tailWord_7118719) baseStart_7118719 baseEnd_7118719 := by
    simpa [prefixWord, tailWord_7118719, baseEnd_7118719] using wordTrace_append hprefix tailTrace_7118719
  have hstable : (prefixWord ++ tailWord_7118719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118719).length < 2 ^ (prefixWord ++ tailWord_7118719).sum := by decide
  have hdescent : baseEnd_7118719 < baseStart_7118719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118729 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 1, 6]
def baseStart_7118729 : Nat := 118140960795 + 7118729 * 2 ^ 59
def prefixEnd_7118729 : Nat := 4983230072969 + 3 ^ 40 * 7118729 * 2
def baseEnd_7118729 : Nat := 1218443208700127891249689

theorem tailTrace_7118729 : CollatzResearch.WordTrace tailWord_7118729 prefixEnd_7118729 1218443208700127891249689 := by
  unfold tailWord_7118729
  simp only [CollatzResearch.WordTrace]
  refine ⟨259641377027068089964951241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173094251351378726643300827 259641377027068089964951241)
  ·
    refine ⟨194731032770301067473713431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259641377027068089964951241 194731032770301067473713431)
    ·
      refine ⟨292096549155451601210570147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194731032770301067473713431 292096549155451601210570147)
      ·
        refine ⟨438144823733177401815855221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292096549155451601210570147 438144823733177401815855221)
        ·
          refine ⟨41076077224985381420236427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 438144823733177401815855221 41076077224985381420236427)
          ·
            refine ⟨61614115837478072130354641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41076077224985381420236427 61614115837478072130354641)
            ·
              refine ⟨46210586878108554097765981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61614115837478072130354641 46210586878108554097765981)
              ·
                refine ⟨17328970079290707786662243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46210586878108554097765981 17328970079290707786662243)
                ·
                  refine ⟨25993455118936061679993365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17328970079290707786662243 25993455118936061679993365)
                  ·
                    refine ⟨1218443208700127891249689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25993455118936061679993365 1218443208700127891249689)
                    ·
                      rfl

theorem cell23_7118729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 6].length) (baseStart_7118729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118729 prefixEnd_7118729 := by exact prefixLift 7118729
  have htrace : WordTrace (prefixWord ++ tailWord_7118729) baseStart_7118729 baseEnd_7118729 := by
    simpa [prefixWord, tailWord_7118729, baseEnd_7118729] using wordTrace_append hprefix tailTrace_7118729
  have hstable : (prefixWord ++ tailWord_7118729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118729).length < 2 ^ (prefixWord ++ tailWord_7118729).sum := by decide
  have hdescent : baseEnd_7118729 < baseStart_7118729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118740 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_7118740 : Nat := 118140960795 + 7118740 * 2 ^ 59
def prefixEnd_7118740 : Nat := 4983230072969 + 3 ^ 40 * 7118740 * 2
def baseEnd_7118740 : Nat := 3655335274387583130711517

theorem tailTrace_7118740 : CollatzResearch.WordTrace tailWord_7118740 prefixEnd_7118740 3655335274387583130711517 := by
  unfold tailWord_7118740
  simp only [CollatzResearch.WordTrace]
  refine ⟨129820889115014119421800837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173094518820018825895734449 129820889115014119421800837)
  ·
    refine ⟨24341416709065147391587657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129820889115014119421800837 24341416709065147391587657)
    ·
      refine ⟨18256062531798860543690743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24341416709065147391587657 18256062531798860543690743)
      ·
        refine ⟨27384093797698290815536115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18256062531798860543690743 27384093797698290815536115)
        ·
          refine ⟨41076140696547436223304173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27384093797698290815536115 41076140696547436223304173)
          ·
            refine ⟨15403552761205288583739065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41076140696547436223304173 15403552761205288583739065)
            ·
              refine ⟨11552664570903966437804299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15403552761205288583739065 11552664570903966437804299)
              ·
                refine ⟨17328996856355949656706449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11552664570903966437804299 17328996856355949656706449)
                ·
                  refine ⟨12996747642266962242529837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17328996856355949656706449 12996747642266962242529837)
                  ·
                    refine ⟨4873780365850110840948689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12996747642266962242529837 4873780365850110840948689)
                    ·
                      refine ⟨3655335274387583130711517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4873780365850110840948689 3655335274387583130711517)
                      ·
                        rfl

theorem cell23_7118740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_7118740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118740 prefixEnd_7118740 := by exact prefixLift 7118740
  have htrace : WordTrace (prefixWord ++ tailWord_7118740) baseStart_7118740 baseEnd_7118740 := by
    simpa [prefixWord, tailWord_7118740, baseEnd_7118740] using wordTrace_append hprefix tailTrace_7118740
  have hstable : (prefixWord ++ tailWord_7118740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118740).length < 2 ^ (prefixWord ++ tailWord_7118740).sum := by decide
  have hdescent : baseEnd_7118740 < baseStart_7118740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118746 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 1, 6]
def baseStart_7118746 : Nat := 118140960795 + 7118746 * 2 ^ 59
def prefixEnd_7118746 : Nat := 4983230072969 + 3 ^ 40 * 7118746 * 2
def baseEnd_7118746 : Nat := 1218446118423836702412163

theorem tailTrace_7118746 : CollatzResearch.WordTrace tailWord_7118746 prefixEnd_7118746 1218446118423836702412163 := by
  unfold tailWord_7118746
  simp only [CollatzResearch.WordTrace]
  refine ⟨64910499267001625467080023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173094664712004334578880061 64910499267001625467080023)
  ·
    refine ⟨97365748900502438200620035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64910499267001625467080023 97365748900502438200620035)
    ·
      refine ⟨146048623350753657300930053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97365748900502438200620035 146048623350753657300930053)
      ·
        refine ⟨27384116878266310743924385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146048623350753657300930053 27384116878266310743924385)
        ·
          refine ⟨20538087658699733057943289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27384116878266310743924385 20538087658699733057943289)
          ·
            refine ⟨15403565744024799793457467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20538087658699733057943289 15403565744024799793457467)
            ·
              refine ⟨23105348616037199690186201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15403565744024799793457467 23105348616037199690186201)
              ·
                refine ⟨17329011462027899767639651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23105348616037199690186201 17329011462027899767639651)
                ·
                  refine ⟨25993517193041849651459477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17329011462027899767639651 25993517193041849651459477)
                  ·
                    refine ⟨1218446118423836702412163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25993517193041849651459477 1218446118423836702412163)
                    ·
                      rfl

theorem cell23_7118746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_7118746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118746 prefixEnd_7118746 := by exact prefixLift 7118746
  have htrace : WordTrace (prefixWord ++ tailWord_7118746) baseStart_7118746 baseEnd_7118746 := by
    simpa [prefixWord, tailWord_7118746, baseEnd_7118746] using wordTrace_append hprefix tailTrace_7118746
  have hstable : (prefixWord ++ tailWord_7118746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118746).length < 2 ^ (prefixWord ++ tailWord_7118746).sum := by decide
  have hdescent : baseEnd_7118746 < baseStart_7118746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118756 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_7118756 : Nat := 118140960795 + 7118756 * 2 ^ 59
def prefixEnd_7118756 : Nat := 4983230072969 + 3 ^ 40 * 7118756 * 2
def baseEnd_7118756 : Nat := 3655343490078055068111443

theorem tailTrace_7118756 : CollatzResearch.WordTrace tailWord_7118756 prefixEnd_7118756 3655343490078055068111443 := by
  unfold tailWord_7118756
  simp only [CollatzResearch.WordTrace]
  refine ⟨129821180898985136788092061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173094907865313515717456081 129821180898985136788092061)
  ·
    refine ⟨48682942837119426295534523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129821180898985136788092061 48682942837119426295534523)
    ·
      refine ⟨73024414255679139443301785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48682942837119426295534523 73024414255679139443301785)
      ·
        refine ⟨54768310691759354582476339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73024414255679139443301785 54768310691759354582476339)
        ·
          refine ⟨82152466037639031873714509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54768310691759354582476339 82152466037639031873714509)
          ·
            refine ⟨30807174764114636952642941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82152466037639031873714509 30807174764114636952642941)
            ·
              refine ⟨11552690536542988857241103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30807174764114636952642941 11552690536542988857241103)
              ·
                refine ⟨17329035804814483285861655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11552690536542988857241103 17329035804814483285861655)
                ·
                  refine ⟨25993553707221724928792483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17329035804814483285861655 25993553707221724928792483)
                  ·
                    refine ⟨38990330560832587393188725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25993553707221724928792483 38990330560832587393188725)
                    ·
                      refine ⟨3655343490078055068111443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38990330560832587393188725 3655343490078055068111443)
                      ·
                        rfl

theorem cell23_7118756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_7118756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118756 prefixEnd_7118756 := by exact prefixLift 7118756
  have htrace : WordTrace (prefixWord ++ tailWord_7118756) baseStart_7118756 baseEnd_7118756 := by
    simpa [prefixWord, tailWord_7118756, baseEnd_7118756] using wordTrace_append hprefix tailTrace_7118756
  have hstable : (prefixWord ++ tailWord_7118756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118756).length < 2 ^ (prefixWord ++ tailWord_7118756).sum := by decide
  have hdescent : baseEnd_7118756 < baseStart_7118756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118759 : List Nat := [1, 1, 6, 1, 2, 12]
def baseStart_7118759 : Nat := 118140960795 + 7118759 * 2 ^ 59
def prefixEnd_7118759 : Nat := 4983230072969 + 3 ^ 40 * 7118759 * 2
def baseEnd_7118759 : Nat := 15042572142057689532403

theorem tailTrace_7118759 : CollatzResearch.WordTrace tailWord_7118759 prefixEnd_7118759 15042572142057689532403 := by
  unfold tailWord_7118759
  simp only [CollatzResearch.WordTrace]
  refine ⟨259642471216959405088543331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173094980811306270059028887 259642471216959405088543331)
  ·
    refine ⟨389463706825439107632814997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259642471216959405088543331 389463706825439107632814997)
    ·
      refine ⟨18256111257442458170288203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 389463706825439107632814997 18256111257442458170288203)
      ·
        refine ⟨27384166886163687255432305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18256111257442458170288203 27384166886163687255432305)
        ·
          refine ⟨20538125164622765441574229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27384166886163687255432305 20538125164622765441574229)
          ·
            refine ⟨15042572142057689532403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 20538125164622765441574229 15042572142057689532403)
            ·
              rfl

theorem cell23_7118759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 12].length) (baseStart_7118759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118759 prefixEnd_7118759 := by exact prefixLift 7118759
  have htrace : WordTrace (prefixWord ++ tailWord_7118759) baseStart_7118759 baseEnd_7118759 := by
    simpa [prefixWord, tailWord_7118759, baseEnd_7118759] using wordTrace_append hprefix tailTrace_7118759
  have hstable : (prefixWord ++ tailWord_7118759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118759).length < 2 ^ (prefixWord ++ tailWord_7118759).sum := by decide
  have hdescent : baseEnd_7118759 < baseStart_7118759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118799 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 5]
def baseStart_7118799 : Nat := 118140960795 + 7118799 * 2 ^ 59
def prefixEnd_7118799 : Nat := 4983230072969 + 3 ^ 40 * 7118799 * 2
def baseEnd_7118799 : Nat := 3655365569746198399873745

theorem tailTrace_7118799 : CollatzResearch.WordTrace tailWord_7118799 prefixEnd_7118799 3655365569746198399873745 := by
  unfold tailWord_7118799
  simp only [CollatzResearch.WordTrace]
  refine ⟨259643930136814491919999451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173095953424542994613332967 259643930136814491919999451)
  ·
    refine ⟨389465895205221737879999177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259643930136814491919999451 389465895205221737879999177)
    ·
      refine ⟨292099421403916303409999383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389465895205221737879999177 292099421403916303409999383)
      ·
        refine ⟨438149132105874455114999075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292099421403916303409999383 438149132105874455114999075)
        ·
          refine ⟨657223698158811682672498613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438149132105874455114999075 657223698158811682672498613)
          ·
            refine ⟨61614721702388595250546745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 657223698158811682672498613 61614721702388595250546745)
            ·
              refine ⟨46211041276791446437910059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61614721702388595250546745 46211041276791446437910059)
              ·
                refine ⟨69316561915187169656865089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46211041276791446437910059 69316561915187169656865089)
                ·
                  refine ⟨51987421436390377242648817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69316561915187169656865089 51987421436390377242648817)
                  ·
                    refine ⟨38990566077292782931986613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51987421436390377242648817 38990566077292782931986613)
                    ·
                      refine ⟨3655365569746198399873745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38990566077292782931986613 3655365569746198399873745)
                      ·
                        rfl

theorem cell23_7118799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_7118799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118799 prefixEnd_7118799 := by exact prefixLift 7118799
  have htrace : WordTrace (prefixWord ++ tailWord_7118799) baseStart_7118799 baseEnd_7118799 := by
    simpa [prefixWord, tailWord_7118799, baseEnd_7118799] using wordTrace_append hprefix tailTrace_7118799
  have hstable : (prefixWord ++ tailWord_7118799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118799).length < 2 ^ (prefixWord ++ tailWord_7118799).sum := by decide
  have hdescent : baseEnd_7118799 < baseStart_7118799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118843 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 1, 4, 2]
def baseStart_7118843 : Nat := 118140960795 + 7118843 * 2 ^ 59
def prefixEnd_7118843 : Nat := 4983230072969 + 3 ^ 40 * 7118843 * 2
def baseEnd_7118843 : Nat := 3655388162894996227723543

theorem tailTrace_7118843 : CollatzResearch.WordTrace tailWord_7118843 prefixEnd_7118843 3655388162894996227723543 := by
  unfold tailWord_7118843
  simp only [CollatzResearch.WordTrace]
  refine ⟨259645534948655087434601183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173097023299103391623067455 259645534948655087434601183)
  ·
    refine ⟨389468302422982631151901775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259645534948655087434601183 389468302422982631151901775)
    ·
      refine ⟨584202453634473946727852663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389468302422982631151901775 584202453634473946727852663)
      ·
        refine ⟨876303680451710920091778995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584202453634473946727852663 876303680451710920091778995)
        ·
          refine ⟨1314455520677566380137668493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876303680451710920091778995 1314455520677566380137668493)
          ·
            refine ⟨492920820254087392551625685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1314455520677566380137668493 492920820254087392551625685)
            ·
              refine ⟨11552831724705173262928727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 492920820254087392551625685 11552831724705173262928727)
              ·
                refine ⟨17329247587057759894393091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11552831724705173262928727 17329247587057759894393091)
                ·
                  refine ⟨25993871380586639841589637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17329247587057759894393091 25993871380586639841589637)
                  ·
                    refine ⟨4873850883859994970298057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25993871380586639841589637 4873850883859994970298057)
                    ·
                      refine ⟨3655388162894996227723543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4873850883859994970298057 3655388162894996227723543)
                      ·
                        rfl

theorem cell23_7118843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 4, 2].length) (baseStart_7118843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118843 prefixEnd_7118843 := by exact prefixLift 7118843
  have htrace : WordTrace (prefixWord ++ tailWord_7118843) baseStart_7118843 baseEnd_7118843 := by
    simpa [prefixWord, tailWord_7118843, baseEnd_7118843] using wordTrace_append hprefix tailTrace_7118843
  have hstable : (prefixWord ++ tailWord_7118843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118843).length < 2 ^ (prefixWord ++ tailWord_7118843).sum := by decide
  have hdescent : baseEnd_7118843 < baseStart_7118843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118894 : List Nat := [4, 1, 3, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_7118894 : Nat := 118140960795 + 7118894 * 2 ^ 59
def prefixEnd_7118894 : Nat := 4983230072969 + 3 ^ 40 * 7118894 * 2
def baseEnd_7118894 : Nat := 3655414350408375528185809

theorem tailTrace_7118894 : CollatzResearch.WordTrace tailWord_7118894 prefixEnd_7118894 3655414350408375528185809 := by
  unfold tailWord_7118894
  simp only [CollatzResearch.WordTrace]
  refine ⟨32455924383933790393088467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173098263380980215429805157 32455924383933790393088467)
  ·
    refine ⟨48683886575900685589632701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32455924383933790393088467 48683886575900685589632701)
    ·
      refine ⟨18256457465962757096112263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48683886575900685589632701 18256457465962757096112263)
      ·
        refine ⟨27384686198944135644168395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18256457465962757096112263 27384686198944135644168395)
        ·
          refine ⟨41077029298416203466252593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27384686198944135644168395 41077029298416203466252593)
          ·
            refine ⟨30807771973812152599689445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41077029298416203466252593 30807771973812152599689445)
            ·
              refine ⟨5776457245089778612441771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30807771973812152599689445 5776457245089778612441771)
              ·
                refine ⟨8664685867634667918662657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5776457245089778612441771 8664685867634667918662657)
                ·
                  refine ⟨6498514400726000938996993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8664685867634667918662657 6498514400726000938996993)
                  ·
                    refine ⟨4873885800544500704247745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6498514400726000938996993 4873885800544500704247745)
                    ·
                      refine ⟨3655414350408375528185809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4873885800544500704247745 3655414350408375528185809)
                      ·
                        rfl

theorem cell23_7118894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_7118894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118894 prefixEnd_7118894 := by exact prefixLift 7118894
  have htrace : WordTrace (prefixWord ++ tailWord_7118894) baseStart_7118894 baseEnd_7118894 := by
    simpa [prefixWord, tailWord_7118894, baseEnd_7118894] using wordTrace_append hprefix tailTrace_7118894
  have hstable : (prefixWord ++ tailWord_7118894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118894).length < 2 ^ (prefixWord ++ tailWord_7118894).sum := by decide
  have hdescent : baseEnd_7118894 < baseStart_7118894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118913 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 2, 5]
def baseStart_7118913 : Nat := 118140960795 + 7118913 * 2 ^ 59
def prefixEnd_7118913 : Nat := 4983230072969 + 3 ^ 40 * 7118913 * 2
def baseEnd_7118913 : Nat := 1218474702180270317949407

theorem tailTrace_7118913 : CollatzResearch.WordTrace tailWord_7118913 prefixEnd_7118913 1218474702180270317949407 := by
  unfold tailWord_7118913
  simp only [CollatzResearch.WordTrace]
  refine ⟨259648088058401489389649393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173098725372267659593099595 259648088058401489389649393)
  ·
    refine ⟨194736066043801117042237045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259648088058401489389649393 194736066043801117042237045)
    ·
      refine ⟨18256506191606354722709723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194736066043801117042237045 18256506191606354722709723)
      ·
        refine ⟨27384759287409532084064585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18256506191606354722709723 27384759287409532084064585)
        ·
          refine ⟨20538569465557149063048439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27384759287409532084064585 20538569465557149063048439)
          ·
            refine ⟨30807854198335723594572659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20538569465557149063048439 30807854198335723594572659)
            ·
              refine ⟨46211781297503585391858989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30807854198335723594572659 46211781297503585391858989)
              ·
                refine ⟨17329417986563844521947121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46211781297503585391858989 17329417986563844521947121)
                ·
                  refine ⟨12997063489922883391460341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17329417986563844521947121 12997063489922883391460341)
                  ·
                    refine ⟨1218474702180270317949407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12997063489922883391460341 1218474702180270317949407)
                    ·
                      rfl

theorem cell23_7118913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_7118913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118913 prefixEnd_7118913 := by exact prefixLift 7118913
  have htrace : WordTrace (prefixWord ++ tailWord_7118913) baseStart_7118913 baseEnd_7118913 := by
    simpa [prefixWord, tailWord_7118913, baseEnd_7118913] using wordTrace_append hprefix tailTrace_7118913
  have hstable : (prefixWord ++ tailWord_7118913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118913).length < 2 ^ (prefixWord ++ tailWord_7118913).sum := by decide
  have hdescent : baseEnd_7118913 < baseStart_7118913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118933 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_7118933 : Nat := 118140960795 + 7118933 * 2 ^ 59
def prefixEnd_7118933 : Nat := 4983230072969 + 3 ^ 40 * 7118933 * 2
def baseEnd_7118933 : Nat := 3655434376153900875598129

theorem tailTrace_7118933 : CollatzResearch.WordTrace tailWord_7118933 prefixEnd_7118933 3655434376153900875598129 := by
  unfold tailWord_7118933
  simp only [CollatzResearch.WordTrace]
  refine ⟨259648817518329032805377453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173099211678886021870251635 259648817518329032805377453)
  ·
    refine ⟨97368306569373387302016545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259648817518329032805377453 97368306569373387302016545)
    ·
      refine ⟨73026229927030040476512409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97368306569373387302016545 73026229927030040476512409)
      ·
        refine ⟨54769672445272530357384307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73026229927030040476512409 54769672445272530357384307)
        ·
          refine ⟨82154508667908795536076461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54769672445272530357384307 82154508667908795536076461)
          ·
            refine ⟨30807940750465798326028673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82154508667908795536076461 30807940750465798326028673)
            ·
              refine ⟨23105955562849348744521505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30807940750465798326028673 23105955562849348744521505)
              ·
                refine ⟨17329466672137011558391129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23105955562849348744521505 17329466672137011558391129)
                ·
                  refine ⟨12997100004102758668793347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17329466672137011558391129 12997100004102758668793347)
                  ·
                    refine ⟨19495650006154138003190021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12997100004102758668793347 19495650006154138003190021)
                    ·
                      refine ⟨3655434376153900875598129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19495650006154138003190021 3655434376153900875598129)
                      ·
                        rfl

theorem cell23_7118933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_7118933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118933 prefixEnd_7118933 := by exact prefixLift 7118933
  have htrace : WordTrace (prefixWord ++ tailWord_7118933) baseStart_7118933 baseEnd_7118933 := by
    simpa [prefixWord, tailWord_7118933, baseEnd_7118933] using wordTrace_append hprefix tailTrace_7118933
  have hstable : (prefixWord ++ tailWord_7118933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118933).length < 2 ^ (prefixWord ++ tailWord_7118933).sum := by decide
  have hdescent : baseEnd_7118933 < baseStart_7118933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7118934 : List Nat := [5, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_7118934 : Nat := 118140960795 + 7118934 * 2 ^ 59
def prefixEnd_7118934 : Nat := 4983230072969 + 3 ^ 40 * 7118934 * 2
def baseEnd_7118934 : Nat := 406159432181617263520625

theorem tailTrace_7118934 : CollatzResearch.WordTrace tailWord_7118934 prefixEnd_7118934 406159432181617263520625 := by
  unfold tailWord_7118934
  simp only [CollatzResearch.WordTrace]
  refine ⟨16228053374457838123510241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173099235994216939984109237 16228053374457838123510241)
  ·
    refine ⟨12171040030843378592632681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16228053374457838123510241 12171040030843378592632681)
    ·
      refine ⟨9128280023132533944474511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12171040030843378592632681 9128280023132533944474511)
      ·
        refine ⟨13692420034698800916711767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9128280023132533944474511 13692420034698800916711767)
        ·
          refine ⟨20538630052048201375067651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13692420034698800916711767 20538630052048201375067651)
          ·
            refine ⟨30807945078072302062601477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20538630052048201375067651 30807945078072302062601477)
            ·
              refine ⟨5776489702138556636737777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30807945078072302062601477 5776489702138556636737777)
              ·
                refine ⟨4332367276603917477553333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5776489702138556636737777 4332367276603917477553333)
                ·
                  refine ⟨406159432181617263520625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4332367276603917477553333 406159432181617263520625)
                  ·
                    rfl

theorem cell23_7118934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_7118934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7118934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7118934 prefixEnd_7118934 := by exact prefixLift 7118934
  have htrace : WordTrace (prefixWord ++ tailWord_7118934) baseStart_7118934 baseEnd_7118934 := by
    simpa [prefixWord, tailWord_7118934, baseEnd_7118934] using wordTrace_append hprefix tailTrace_7118934
  have hstable : (prefixWord ++ tailWord_7118934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7118934).length < 2 ^ (prefixWord ++ tailWord_7118934).sum := by decide
  have hdescent : baseEnd_7118934 < baseStart_7118934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7118934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119023 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 1, 8, 2]
def baseStart_7119023 : Nat := 118140960795 + 7119023 * 2 ^ 59
def prefixEnd_7119023 : Nat := 4983230072969 + 3 ^ 40 * 7119023 * 2
def baseEnd_7119023 : Nat := 3655480589412805523472715

theorem tailTrace_7119023 : CollatzResearch.WordTrace tailWord_7119023 prefixEnd_7119023 3655480589412805523472715 := by
  unfold tailWord_7119023
  simp only [CollatzResearch.WordTrace]
  refine ⟨259652100088002978176153723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173101400058668652117435815 259652100088002978176153723)
  ·
    refine ⟨389478150132004467264230585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259652100088002978176153723 389478150132004467264230585)
    ·
      refine ⟨292108612599003350448172939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389478150132004467264230585 292108612599003350448172939)
      ·
        refine ⟨438162918898505025672259409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292108612599003350448172939 438162918898505025672259409)
        ·
          refine ⟨328622189173878769254194557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438162918898505025672259409 328622189173878769254194557)
          ·
            refine ⟨123233320940204538470322959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328622189173878769254194557 123233320940204538470322959)
            ·
              refine ⟨184849981410306807705484439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123233320940204538470322959 184849981410306807705484439)
              ·
                refine ⟨277274972115460211558226659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184849981410306807705484439 277274972115460211558226659)
                ·
                  refine ⟨415912458173190317337339989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277274972115460211558226659 415912458173190317337339989)
                  ·
                    refine ⟨4873974119217074031296953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 415912458173190317337339989 4873974119217074031296953)
                    ·
                      refine ⟨3655480589412805523472715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4873974119217074031296953 3655480589412805523472715)
                      ·
                        rfl

theorem cell23_7119023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 8, 2].length) (baseStart_7119023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119023 prefixEnd_7119023 := by exact prefixLift 7119023
  have htrace : WordTrace (prefixWord ++ tailWord_7119023) baseStart_7119023 baseEnd_7119023 := by
    simpa [prefixWord, tailWord_7119023, baseEnd_7119023] using wordTrace_append hprefix tailTrace_7119023
  have hstable : (prefixWord ++ tailWord_7119023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119023).length < 2 ^ (prefixWord ++ tailWord_7119023).sum := by decide
  have hdescent : baseEnd_7119023 < baseStart_7119023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119033 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 6, 4]
def baseStart_7119033 : Nat := 118140960795 + 7119033 * 2 ^ 59
def prefixEnd_7119033 : Nat := 4983230072969 + 3 ^ 40 * 7119033 * 2
def baseEnd_7119033 : Nat := 1218495241406450161449223

theorem tailTrace_7119033 : CollatzResearch.WordTrace tailWord_7119033 prefixEnd_7119033 1218495241406450161449223 := by
  unfold tailWord_7119033
  simp only [CollatzResearch.WordTrace]
  refine ⟨259652464817966749884017753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173101643211977833256011835 259652464817966749884017753)
  ·
    refine ⟨194739348613475062413013315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259652464817966749884017753 194739348613475062413013315)
    ·
      refine ⟨292109022920212593619519973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194739348613475062413013315 292109022920212593619519973)
      ·
        refine ⟨54770441797539861303659995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292109022920212593619519973 54770441797539861303659995)
        ·
          refine ⟨82155662696309791955489993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54770441797539861303659995 82155662696309791955489993)
          ·
            refine ⟨61616747022232343966617495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82155662696309791955489993 61616747022232343966617495)
            ·
              refine ⟨92425120533348515949926243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61616747022232343966617495 92425120533348515949926243)
              ·
                refine ⟨138637680800022773924889365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92425120533348515949926243 138637680800022773924889365)
                ·
                  refine ⟨6498641287501067527729189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138637680800022773924889365 6498641287501067527729189)
                  ·
                    refine ⟨1218495241406450161449223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6498641287501067527729189 1218495241406450161449223)
                    ·
                      rfl

theorem cell23_7119033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 4].length) (baseStart_7119033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119033 prefixEnd_7119033 := by exact prefixLift 7119033
  have htrace : WordTrace (prefixWord ++ tailWord_7119033) baseStart_7119033 baseEnd_7119033 := by
    simpa [prefixWord, tailWord_7119033, baseEnd_7119033] using wordTrace_append hprefix tailTrace_7119033
  have hstable : (prefixWord ++ tailWord_7119033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119033).length < 2 ^ (prefixWord ++ tailWord_7119033).sum := by decide
  have hdescent : baseEnd_7119033 < baseStart_7119033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119040 : List Nat := [2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 4]
def baseStart_7119040 : Nat := 118140960795 + 7119040 * 2 ^ 59
def prefixEnd_7119040 : Nat := 4983230072969 + 3 ^ 40 * 7119040 * 2
def baseEnd_7119040 : Nat := 3655489318583931956960137

theorem tailTrace_7119040 : CollatzResearch.WordTrace tailWord_7119040 prefixEnd_7119040 3655489318583931956960137 := by
  unfold tailWord_7119040
  simp only [CollatzResearch.WordTrace]
  refine ⟨129826360064470695039761287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173101813419294260053015049 129826360064470695039761287)
  ·
    refine ⟨194739540096706042559641931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129826360064470695039761287 194739540096706042559641931)
    ·
      refine ⟨292109310145059063839462897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194739540096706042559641931 292109310145059063839462897)
      ·
        refine ⟨219081982608794297879597173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292109310145059063839462897 219081982608794297879597173)
        ·
          refine ⟨20538935869574465426212235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 219081982608794297879597173 20538935869574465426212235)
          ·
            refine ⟨30808403804361698139318353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20538935869574465426212235 30808403804361698139318353)
            ·
              refine ⟨23106302853271273604488765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30808403804361698139318353 23106302853271273604488765)
              ·
                refine ⟨8664863569976727601683287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23106302853271273604488765 8664863569976727601683287)
                ·
                  refine ⟨12997295354965091402524931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8664863569976727601683287 12997295354965091402524931)
                  ·
                    refine ⟨19495943032447637103787397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12997295354965091402524931 19495943032447637103787397)
                    ·
                      refine ⟨3655489318583931956960137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19495943032447637103787397 3655489318583931956960137)
                      ·
                        rfl

theorem cell23_7119040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_7119040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119040 prefixEnd_7119040 := by exact prefixLift 7119040
  have htrace : WordTrace (prefixWord ++ tailWord_7119040) baseStart_7119040 baseEnd_7119040 := by
    simpa [prefixWord, tailWord_7119040, baseEnd_7119040] using wordTrace_append hprefix tailTrace_7119040
  have hstable : (prefixWord ++ tailWord_7119040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119040).length < 2 ^ (prefixWord ++ tailWord_7119040).sum := by decide
  have hdescent : baseEnd_7119040 < baseStart_7119040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119050 : List Nat := [3, 1, 2, 1, 3, 1, 2, 4, 2, 4]
def baseStart_7119050 : Nat := 118140960795 + 7119050 * 2 ^ 59
def prefixEnd_7119050 : Nat := 4983230072969 + 3 ^ 40 * 7119050 * 2
def baseEnd_7119050 : Nat := 1218498151130158972611697

theorem tailTrace_7119050 : CollatzResearch.WordTrace tailWord_7119050 prefixEnd_7119050 1218498151130158972611697 := by
  unfold tailWord_7119050
  simp only [CollatzResearch.WordTrace]
  refine ⟨64913271214726290446846651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173102056572603441191591069 64913271214726290446846651)
  ·
    refine ⟨97369906822089435670269977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64913271214726290446846651 97369906822089435670269977)
    ·
      refine ⟨73027430116567076752702483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97369906822089435670269977 73027430116567076752702483)
      ·
        refine ⟨109541145174850615129053725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73027430116567076752702483 109541145174850615129053725)
        ·
          refine ⟨41077929440568980673395147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109541145174850615129053725 41077929440568980673395147)
          ·
            refine ⟨61616894160853471010092721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41077929440568980673395147 61616894160853471010092721)
            ·
              refine ⟨46212670620640103257569541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61616894160853471010092721 46212670620640103257569541)
              ·
                refine ⟨8664875741370019360794289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46212670620640103257569541 8664875741370019360794289)
                ·
                  refine ⟨6498656806027514520595717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8664875741370019360794289 6498656806027514520595717)
                  ·
                    refine ⟨1218498151130158972611697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6498656806027514520595717 1218498151130158972611697)
                    ·
                      rfl

theorem cell23_7119050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_7119050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119050 prefixEnd_7119050 := by exact prefixLift 7119050
  have htrace : WordTrace (prefixWord ++ tailWord_7119050) baseStart_7119050 baseEnd_7119050 := by
    simpa [prefixWord, tailWord_7119050, baseEnd_7119050] using wordTrace_append hprefix tailTrace_7119050
  have hstable : (prefixWord ++ tailWord_7119050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119050).length < 2 ^ (prefixWord ++ tailWord_7119050).sum := by decide
  have hdescent : baseEnd_7119050 < baseStart_7119050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119057 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 3, 2, 2]
def baseStart_7119057 : Nat := 118140960795 + 7119057 * 2 ^ 59
def prefixEnd_7119057 : Nat := 4983230072969 + 3 ^ 40 * 7119057 * 2
def baseEnd_7119057 : Nat := 3655498047755058390447559

theorem tailTrace_7119057 : CollatzResearch.WordTrace tailWord_7119057 prefixEnd_7119057 3655498047755058390447559 := by
  unfold tailWord_7119057
  simp only [CollatzResearch.WordTrace]
  refine ⟨259653340169879801982891425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173102226779919867988594283 259653340169879801982891425)
  ·
    refine ⟨194740005127409851487168569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259653340169879801982891425 194740005127409851487168569)
    ·
      refine ⟨146055003845557388615376427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194740005127409851487168569 146055003845557388615376427)
      ·
        refine ⟨219082505768336082923064641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146055003845557388615376427 219082505768336082923064641)
        ·
          refine ⟨164311879326252062192298481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219082505768336082923064641 164311879326252062192298481)
          ·
            refine ⟨123233909494689046644223861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164311879326252062192298481 123233909494689046644223861)
            ·
              refine ⟨11553179015127098122895987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123233909494689046644223861 11553179015127098122895987)
              ·
                refine ⟨17329768522690647184343981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11553179015127098122895987 17329768522690647184343981)
                ·
                  refine ⟨6498663196008992694128993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17329768522690647184343981 6498663196008992694128993)
                  ·
                    refine ⟨4873997397006744520596745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6498663196008992694128993 4873997397006744520596745)
                    ·
                      refine ⟨3655498047755058390447559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4873997397006744520596745 3655498047755058390447559)
                      ·
                        rfl

theorem cell23_7119057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 2, 2].length) (baseStart_7119057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119057 prefixEnd_7119057 := by exact prefixLift 7119057
  have htrace : WordTrace (prefixWord ++ tailWord_7119057) baseStart_7119057 baseEnd_7119057 := by
    simpa [prefixWord, tailWord_7119057, baseEnd_7119057] using wordTrace_append hprefix tailTrace_7119057
  have hstable : (prefixWord ++ tailWord_7119057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119057).length < 2 ^ (prefixWord ++ tailWord_7119057).sum := by decide
  have hdescent : baseEnd_7119057 < baseStart_7119057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119077 : List Nat := [1, 3, 1, 4, 2, 1, 3, 2, 1, 2, 3]
def baseStart_7119077 : Nat := 118140960795 + 7119077 * 2 ^ 59
def prefixEnd_7119077 : Nat := 4983230072969 + 3 ^ 40 * 7119077 * 2
def baseEnd_7119077 : Nat := 3655508317368148312197467

theorem tailTrace_7119077 : CollatzResearch.WordTrace tailWord_7119077 prefixEnd_7119077 3655508317368148312197467 := by
  unfold tailWord_7119077
  simp only [CollatzResearch.WordTrace]
  refine ⟨259654069629807345398619485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173102713086538230265746323 259654069629807345398619485)
  ·
    refine ⟨97370276111177754524482307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259654069629807345398619485 97370276111177754524482307)
    ·
      refine ⟨146055414166766631786723461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97370276111177754524482307 146055414166766631786723461)
      ·
        refine ⟨27385390156268743460010649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146055414166766631786723461 27385390156268743460010649)
        ·
          refine ⟨20539042617201557595007987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27385390156268743460010649 20539042617201557595007987)
          ·
            refine ⟨30808563925802336392511981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20539042617201557595007987 30808563925802336392511981)
            ·
              refine ⟨11553211472175876147191993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30808563925802336392511981 11553211472175876147191993)
              ·
                refine ⟨8664908604131907110393995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11553211472175876147191993 8664908604131907110393995)
                ·
                  refine ⟨12997362906197860665590993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8664908604131907110393995 12997362906197860665590993)
                  ·
                    refine ⟨9748022179648395499193245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12997362906197860665590993 9748022179648395499193245)
                    ·
                      refine ⟨3655508317368148312197467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9748022179648395499193245 3655508317368148312197467)
                      ·
                        rfl

theorem cell23_7119077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_7119077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119077 prefixEnd_7119077 := by exact prefixLift 7119077
  have htrace : WordTrace (prefixWord ++ tailWord_7119077) baseStart_7119077 baseEnd_7119077 := by
    simpa [prefixWord, tailWord_7119077, baseEnd_7119077] using wordTrace_append hprefix tailTrace_7119077
  have hstable : (prefixWord ++ tailWord_7119077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119077).length < 2 ^ (prefixWord ++ tailWord_7119077).sum := by decide
  have hdescent : baseEnd_7119077 < baseStart_7119077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119090 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_7119090 : Nat := 118140960795 + 7119090 * 2 ^ 59
def prefixEnd_7119090 : Nat := 4983230072969 + 3 ^ 40 * 7119090 * 2
def baseEnd_7119090 : Nat := 3655514992616656761334907

theorem tailTrace_7119090 : CollatzResearch.WordTrace tailWord_7119090 prefixEnd_7119090 3655514992616656761334907 := by
  unfold tailWord_7119090
  simp only [CollatzResearch.WordTrace]
  refine ⟨64913635944690062154710681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173103029185840165745895149 64913635944690062154710681)
  ·
    refine ⟨48685226958517546616033011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64913635944690062154710681 48685226958517546616033011)
    ·
      refine ⟨73027840437776319924049517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48685226958517546616033011 73027840437776319924049517)
      ·
        refine ⟨27385440164166119971518569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73027840437776319924049517 27385440164166119971518569)
        ·
          refine ⟨20539080123124589978638927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27385440164166119971518569 20539080123124589978638927)
          ·
            refine ⟨30808620184686884967958391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20539080123124589978638927 30808620184686884967958391)
            ·
              refine ⟨46212930277030327451937587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30808620184686884967958391 46212930277030327451937587)
              ·
                refine ⟨69319395415545491177906381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46212930277030327451937587 69319395415545491177906381)
                ·
                  refine ⟨25994773280829559191714893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69319395415545491177906381 25994773280829559191714893)
                  ·
                    refine ⟨9748039980311084696893085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25994773280829559191714893 9748039980311084696893085)
                    ·
                      refine ⟨3655514992616656761334907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9748039980311084696893085 3655514992616656761334907)
                      ·
                        rfl

theorem cell23_7119090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_7119090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119090 prefixEnd_7119090 := by exact prefixLift 7119090
  have htrace : WordTrace (prefixWord ++ tailWord_7119090) baseStart_7119090 baseEnd_7119090 := by
    simpa [prefixWord, tailWord_7119090, baseEnd_7119090] using wordTrace_append hprefix tailTrace_7119090
  have hstable : (prefixWord ++ tailWord_7119090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119090).length < 2 ^ (prefixWord ++ tailWord_7119090).sum := by decide
  have hdescent : baseEnd_7119090 < baseStart_7119090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119107 : List Nat := [1, 1, 1, 3, 2, 3, 4, 2, 2, 1, 3]
def baseStart_7119107 : Nat := 118140960795 + 7119107 * 2 ^ 59
def prefixEnd_7119107 : Nat := 4983230072969 + 3 ^ 40 * 7119107 * 2
def baseEnd_7119107 : Nat := 3655523721787783194822329

theorem tailTrace_7119107 : CollatzResearch.WordTrace tailWord_7119107 prefixEnd_7119107 3655523721787783194822329 := by
  unfold tailWord_7119107
  simp only [CollatzResearch.WordTrace]
  refine ⟨259655163819698660522211575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173103442546465773681474383 259655163819698660522211575)
  ·
    refine ⟨389482745729547990783317363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259655163819698660522211575 389482745729547990783317363)
    ·
      refine ⟨584224118594321986174976045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389482745729547990783317363 584224118594321986174976045)
      ·
        refine ⟨219084044472870744815616017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 584224118594321986174976045 219084044472870744815616017)
        ·
          refine ⟨164313033354653058611712013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219084044472870744815616017 164313033354653058611712013)
          ·
            refine ⟨61617387507994896979392005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164313033354653058611712013 61617387507994896979392005)
            ·
              refine ⟨11553260157749043183636001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61617387507994896979392005 11553260157749043183636001)
              ·
                refine ⟨8664945118311782387727001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11553260157749043183636001 8664945118311782387727001)
                ·
                  refine ⟨6498708838733836790795251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8664945118311782387727001 6498708838733836790795251)
                  ·
                    refine ⟨9748063258100755186192877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6498708838733836790795251 9748063258100755186192877)
                    ·
                      refine ⟨3655523721787783194822329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9748063258100755186192877 3655523721787783194822329)
                      ·
                        rfl

theorem cell23_7119107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_7119107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119107 prefixEnd_7119107 := by exact prefixLift 7119107
  have htrace : WordTrace (prefixWord ++ tailWord_7119107) baseStart_7119107 baseEnd_7119107 := by
    simpa [prefixWord, tailWord_7119107, baseEnd_7119107] using wordTrace_append hprefix tailTrace_7119107
  have hstable : (prefixWord ++ tailWord_7119107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119107).length < 2 ^ (prefixWord ++ tailWord_7119107).sum := by decide
  have hdescent : baseEnd_7119107 < baseStart_7119107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119113 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 2, 3, 4]
def baseStart_7119113 : Nat := 118140960795 + 7119113 * 2 ^ 59
def prefixEnd_7119113 : Nat := 4983230072969 + 3 ^ 40 * 7119113 * 2
def baseEnd_7119113 : Nat := 3655526802671710171347301

theorem tailTrace_7119113 : CollatzResearch.WordTrace tailWord_7119113 prefixEnd_7119113 3655526802671710171347301 := by
  unfold tailWord_7119113
  simp only [CollatzResearch.WordTrace]
  refine ⟨259655382657676923546929993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173103588438451282364619995 259655382657676923546929993)
  ·
    refine ⟨194741536993257692660197495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259655382657676923546929993 194741536993257692660197495)
    ·
      refine ⟨292112305489886538990296243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194741536993257692660197495 292112305489886538990296243)
      ·
        refine ⟨438168458234829808485444365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292112305489886538990296243 438168458234829808485444365)
        ·
          refine ⟨164313171838061178182041637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438168458234829808485444365 164313171838061178182041637)
          ·
            refine ⟨30808719719636470909132807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164313171838061178182041637 30808719719636470909132807)
            ·
              refine ⟨46213079579454706363699211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30808719719636470909132807 46213079579454706363699211)
              ·
                refine ⟨69319619369182059545548817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46213079579454706363699211 69319619369182059545548817)
                ·
                  refine ⟨51989714526886544659161613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69319619369182059545548817 51989714526886544659161613)
                  ·
                    refine ⟨19496142947582454247185605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51989714526886544659161613 19496142947582454247185605)
                    ·
                      refine ⟨3655526802671710171347301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19496142947582454247185605 3655526802671710171347301)
                      ·
                        rfl

theorem cell23_7119113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 3, 4].length) (baseStart_7119113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119113 prefixEnd_7119113 := by exact prefixLift 7119113
  have htrace : WordTrace (prefixWord ++ tailWord_7119113) baseStart_7119113 baseEnd_7119113 := by
    simpa [prefixWord, tailWord_7119113, baseEnd_7119113] using wordTrace_append hprefix tailTrace_7119113
  have hstable : (prefixWord ++ tailWord_7119113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119113).length < 2 ^ (prefixWord ++ tailWord_7119113).sum := by decide
  have hdescent : baseEnd_7119113 < baseStart_7119113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119163 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 3]
def baseStart_7119163 : Nat := 118140960795 + 7119163 * 2 ^ 59
def prefixEnd_7119163 : Nat := 4983230072969 + 3 ^ 40 * 7119163 * 2
def baseEnd_7119163 : Nat := 3655552476704434975722071

theorem tailTrace_7119163 : CollatzResearch.WordTrace tailWord_7119163 prefixEnd_7119163 3655552476704434975722071 := by
  unfold tailWord_7119163
  simp only [CollatzResearch.WordTrace]
  refine ⟨259657206307495782086250143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173104804204997188057500095 259657206307495782086250143)
  ·
    refine ⟨389485809461243673129375215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259657206307495782086250143 389485809461243673129375215)
    ·
      refine ⟨584228714191865509694062823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389485809461243673129375215 584228714191865509694062823)
      ·
        refine ⟨876343071287798264541094235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584228714191865509694062823 876343071287798264541094235)
        ·
          refine ⟨1314514606931697396811641353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876343071287798264541094235 1314514606931697396811641353)
          ·
            refine ⟨985885955198773047608731015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314514606931697396811641353 985885955198773047608731015)
            ·
              refine ⟨1478828932798159571413096523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985885955198773047608731015 1478828932798159571413096523)
              ·
                refine ⟨2218243399197239357119644785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478828932798159571413096523 2218243399197239357119644785)
                ·
                  refine ⟨1663682549397929517839733589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2218243399197239357119644785 1663682549397929517839733589)
                  ·
                    refine ⟨9748139937878493268592189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1663682549397929517839733589 9748139937878493268592189)
                    ·
                      refine ⟨3655552476704434975722071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9748139937878493268592189 3655552476704434975722071)
                      ·
                        rfl

theorem cell23_7119163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 3].length) (baseStart_7119163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119163 prefixEnd_7119163 := by exact prefixLift 7119163
  have htrace : WordTrace (prefixWord ++ tailWord_7119163) baseStart_7119163 baseEnd_7119163 := by
    simpa [prefixWord, tailWord_7119163, baseEnd_7119163] using wordTrace_append hprefix tailTrace_7119163
  have hstable : (prefixWord ++ tailWord_7119163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119163).length < 2 ^ (prefixWord ++ tailWord_7119163).sum := by decide
  have hdescent : baseEnd_7119163 < baseStart_7119163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119180 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 2, 3, 3]
def baseStart_7119180 : Nat := 118140960795 + 7119180 * 2 ^ 59
def prefixEnd_7119180 : Nat := 4983230072969 + 3 ^ 40 * 7119180 * 2
def baseEnd_7119180 : Nat := 3655561205875561409209493

theorem tailTrace_7119180 : CollatzResearch.WordTrace tailWord_7119180 prefixEnd_7119180 3655561205875561409209493 := by
  unfold tailWord_7119180
  simp only [CollatzResearch.WordTrace]
  refine ⟨129828913174217096994809497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173105217565622795993079329 129828913174217096994809497)
  ·
    refine ⟨97371684880662822746107123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129828913174217096994809497 97371684880662822746107123)
    ·
      refine ⟨146057527320994234119160685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97371684880662822746107123 146057527320994234119160685)
      ·
        refine ⟨54771572745372837794685257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146057527320994234119160685 54771572745372837794685257)
        ·
          refine ⟨41078679559029628346013943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54771572745372837794685257 41078679559029628346013943)
          ·
            refine ⟨61618019338544442519020915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41078679559029628346013943 61618019338544442519020915)
            ·
              refine ⟨92427029007816663778531373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61618019338544442519020915 92427029007816663778531373)
              ·
                refine ⟨34660135877931248916949265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92427029007816663778531373 34660135877931248916949265)
                ·
                  refine ⟨25995101908448436687711949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34660135877931248916949265 25995101908448436687711949)
                  ·
                    refine ⟨9748163215668163757891981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25995101908448436687711949 9748163215668163757891981)
                    ·
                      refine ⟨3655561205875561409209493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9748163215668163757891981 3655561205875561409209493)
                      ·
                        rfl

theorem cell23_7119180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_7119180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119180 prefixEnd_7119180 := by exact prefixLift 7119180
  have htrace : WordTrace (prefixWord ++ tailWord_7119180) baseStart_7119180 baseEnd_7119180 := by
    simpa [prefixWord, tailWord_7119180, baseEnd_7119180] using wordTrace_append hprefix tailTrace_7119180
  have hstable : (prefixWord ++ tailWord_7119180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119180).length < 2 ^ (prefixWord ++ tailWord_7119180).sum := by decide
  have hdescent : baseEnd_7119180 < baseStart_7119180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119183 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 6, 5]
def baseStart_7119183 : Nat := 118140960795 + 7119183 * 2 ^ 59
def prefixEnd_7119183 : Nat := 4983230072969 + 3 ^ 40 * 7119183 * 2
def baseEnd_7119183 : Nat := 1218520915439174965823993

theorem tailTrace_7119183 : CollatzResearch.WordTrace tailWord_7119183 prefixEnd_7119183 1218520915439174965823993 := by
  unfold tailWord_7119183
  simp only [CollatzResearch.WordTrace]
  refine ⟨259657935767423325501978203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173105290511615550334652135 259657935767423325501978203)
  ·
    refine ⟨389486903651134988252967305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259657935767423325501978203 389486903651134988252967305)
    ·
      refine ⟨292115177738351241189725479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389486903651134988252967305 292115177738351241189725479)
      ·
        refine ⟨438172766607526861784588219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292115177738351241189725479 438172766607526861784588219)
        ·
          refine ⟨657259149911290292676882329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438172766607526861784588219 657259149911290292676882329)
          ·
            refine ⟨492944362433467719507661747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657259149911290292676882329 492944362433467719507661747)
            ·
              refine ⟨739416543650201579261492621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492944362433467719507661747 739416543650201579261492621)
              ·
                refine ⟨277281203868825592223059733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 739416543650201579261492621 277281203868825592223059733)
                ·
                  refine ⟨12997556431351199635455925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 277281203868825592223059733 12997556431351199635455925)
                  ·
                    refine ⟨1218520915439174965823993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12997556431351199635455925 1218520915439174965823993)
                    ·
                      rfl

theorem cell23_7119183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 5].length) (baseStart_7119183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119183 prefixEnd_7119183 := by exact prefixLift 7119183
  have htrace : WordTrace (prefixWord ++ tailWord_7119183) baseStart_7119183 baseEnd_7119183 := by
    simpa [prefixWord, tailWord_7119183, baseEnd_7119183] using wordTrace_append hprefix tailTrace_7119183
  have hstable : (prefixWord ++ tailWord_7119183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119183).length < 2 ^ (prefixWord ++ tailWord_7119183).sum := by decide
  have hdescent : baseEnd_7119183 < baseStart_7119183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119193 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 3, 2, 5]
def baseStart_7119193 : Nat := 118140960795 + 7119193 * 2 ^ 59
def prefixEnd_7119193 : Nat := 4983230072969 + 3 ^ 40 * 7119193 * 2
def baseEnd_7119193 : Nat := 3655567881124069858346933

theorem tailTrace_7119193 : CollatzResearch.WordTrace tailWord_7119193 prefixEnd_7119193 3655567881124069858346933 := by
  unfold tailWord_7119193
  simp only [CollatzResearch.WordTrace]
  refine ⟨259658300497387097209842233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173105533664924731473228155 259658300497387097209842233)
  ·
    refine ⟨194743725373040322907381675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259658300497387097209842233 194743725373040322907381675)
    ·
      refine ⟨292115588059560484361072513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194743725373040322907381675 292115588059560484361072513)
      ·
        refine ⟨219086691044670363270804385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292115588059560484361072513 219086691044670363270804385)
        ·
          refine ⟨164315018283502772453103289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219086691044670363270804385 164315018283502772453103289)
          ·
            refine ⟨123236263712627079339827467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164315018283502772453103289 123236263712627079339827467)
            ·
              refine ⟨184854395568940619009741201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123236263712627079339827467 184854395568940619009741201)
              ·
                refine ⟨138640796676705464257305901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184854395568940619009741201 138640796676705464257305901)
                ·
                  refine ⟨51990298753764549096489713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138640796676705464257305901 51990298753764549096489713)
                  ·
                    refine ⟨38992724065323411822367285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51990298753764549096489713 38992724065323411822367285)
                    ·
                      refine ⟨3655567881124069858346933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38992724065323411822367285 3655567881124069858346933)
                      ·
                        rfl

theorem cell23_7119193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_7119193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119193 prefixEnd_7119193 := by exact prefixLift 7119193
  have htrace : WordTrace (prefixWord ++ tailWord_7119193) baseStart_7119193 baseEnd_7119193 := by
    simpa [prefixWord, tailWord_7119193, baseEnd_7119193] using wordTrace_append hprefix tailTrace_7119193
  have hstable : (prefixWord ++ tailWord_7119193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119193).length < 2 ^ (prefixWord ++ tailWord_7119193).sum := by decide
  have hdescent : baseEnd_7119193 < baseStart_7119193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119223 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_7119223 : Nat := 118140960795 + 7119223 * 2 ^ 59
def prefixEnd_7119223 : Nat := 4983230072969 + 3 ^ 40 * 7119223 * 2
def baseEnd_7119223 : Nat := 3655583285543704740971795

theorem tailTrace_7119223 : CollatzResearch.WordTrace tailWord_7119223 prefixEnd_7119223 3655583285543704740971795 := by
  unfold tailWord_7119223
  simp only [CollatzResearch.WordTrace]
  refine ⟨259659394687278412333434323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173106263124852274888956215 259659394687278412333434323)
  ·
    refine ⟨389489092030917618500151485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259659394687278412333434323 389489092030917618500151485)
    ·
      refine ⟨146058409511594106937556807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389489092030917618500151485 146058409511594106937556807)
      ·
        refine ⟨219087614267391160406335211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146058409511594106937556807 219087614267391160406335211)
        ·
          refine ⟨328631421401086740609502817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219087614267391160406335211 328631421401086740609502817)
          ·
            refine ⟨246473566050815055457127113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328631421401086740609502817 246473566050815055457127113)
            ·
              refine ⟨184855174538111291592845335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246473566050815055457127113 184855174538111291592845335)
              ·
                refine ⟨277282761807166937389268003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184855174538111291592845335 277282761807166937389268003)
                ·
                  refine ⟨415924142710750406083902005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277282761807166937389268003 415924142710750406083902005)
                  ·
                    refine ⟨38992888379132850570365813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 415924142710750406083902005 38992888379132850570365813)
                    ·
                      refine ⟨3655583285543704740971795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38992888379132850570365813 3655583285543704740971795)
                      ·
                        rfl

theorem cell23_7119223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_7119223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119223 prefixEnd_7119223 := by exact prefixLift 7119223
  have htrace : WordTrace (prefixWord ++ tailWord_7119223) baseStart_7119223 baseEnd_7119223 := by
    simpa [prefixWord, tailWord_7119223, baseEnd_7119223] using wordTrace_append hprefix tailTrace_7119223
  have hstable : (prefixWord ++ tailWord_7119223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119223).length < 2 ^ (prefixWord ++ tailWord_7119223).sum := by decide
  have hdescent : baseEnd_7119223 < baseStart_7119223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119257 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 2, 2, 3]
def baseStart_7119257 : Nat := 118140960795 + 7119257 * 2 ^ 59
def prefixEnd_7119257 : Nat := 4983230072969 + 3 ^ 40 * 7119257 * 2
def baseEnd_7119257 : Nat := 3655600743885957607946639

theorem tailTrace_7119257 : CollatzResearch.WordTrace tailWord_7119257 prefixEnd_7119257 3655600743885957607946639 := by
  unfold tailWord_7119257
  simp only [CollatzResearch.WordTrace]
  refine ⟨259660634769155236140172025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173107089846103490760114683 259660634769155236140172025)
  ·
    refine ⟨194745476076866427105129019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259660634769155236140172025 194745476076866427105129019)
    ·
      refine ⟨292118214115299640657693529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194745476076866427105129019 292118214115299640657693529)
      ·
        refine ⟨219088660586474730493270147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292118214115299640657693529 219088660586474730493270147)
        ·
          refine ⟨328632990879712095739905221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219088660586474730493270147 328632990879712095739905221)
          ·
            refine ⟨61618685789946017951232229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 328632990879712095739905221 61618685789946017951232229)
            ·
              refine ⟨11553503585614878365856043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61618685789946017951232229 11553503585614878365856043)
              ·
                refine ⟨17330255378422317548784065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11553503585614878365856043 17330255378422317548784065)
                ·
                  refine ⟨12997691533816738161588049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17330255378422317548784065 12997691533816738161588049)
                  ·
                    refine ⟨9748268650362553621191037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12997691533816738161588049 9748268650362553621191037)
                    ·
                      refine ⟨3655600743885957607946639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9748268650362553621191037 3655600743885957607946639)
                      ·
                        rfl

theorem cell23_7119257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_7119257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119257 prefixEnd_7119257 := by exact prefixLift 7119257
  have htrace : WordTrace (prefixWord ++ tailWord_7119257) baseStart_7119257 baseEnd_7119257 := by
    simpa [prefixWord, tailWord_7119257, baseEnd_7119257] using wordTrace_append hprefix tailTrace_7119257
  have hstable : (prefixWord ++ tailWord_7119257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119257).length < 2 ^ (prefixWord ++ tailWord_7119257).sum := by decide
  have hdescent : baseEnd_7119257 < baseStart_7119257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119281 : List Nat := [1, 2, 2, 4, 1, 2, 4, 2, 1, 4]
def baseStart_7119281 : Nat := 118140960795 + 7119281 * 2 ^ 59
def prefixEnd_7119281 : Nat := 4983230072969 + 3 ^ 40 * 7119281 * 2
def baseEnd_7119281 : Nat := 1218537689140555171348843

theorem tailTrace_7119281 : CollatzResearch.WordTrace tailWord_7119281 prefixEnd_7119281 1218537689140555171348843 := by
  unfold tailWord_7119281
  simp only [CollatzResearch.WordTrace]
  refine ⟨259661510121068288239045697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173107673414045525492697131 259661510121068288239045697)
  ·
    refine ⟨194746132590801216179284273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259661510121068288239045697 194746132590801216179284273)
    ·
      refine ⟨146059599443100912134463205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194746132590801216179284273 146059599443100912134463205)
      ·
        refine ⟨27386174895581421025211851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146059599443100912134463205 27386174895581421025211851)
        ·
          refine ⟨41079262343372131537817777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27386174895581421025211851 41079262343372131537817777)
          ·
            refine ⟨30809446757529098653363333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41079262343372131537817777 30809446757529098653363333)
            ·
              refine ⟨5776771267036705997505625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30809446757529098653363333 5776771267036705997505625)
              ·
                refine ⟨4332578450277529498129219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5776771267036705997505625 4332578450277529498129219)
                ·
                  refine ⟨6498867675416294247193829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4332578450277529498129219 6498867675416294247193829)
                  ·
                    refine ⟨1218537689140555171348843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6498867675416294247193829 1218537689140555171348843)
                    ·
                      rfl

theorem cell23_7119281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_7119281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119281 prefixEnd_7119281 := by exact prefixLift 7119281
  have htrace : WordTrace (prefixWord ++ tailWord_7119281) baseStart_7119281 baseEnd_7119281 := by
    simpa [prefixWord, tailWord_7119281, baseEnd_7119281] using wordTrace_append hprefix tailTrace_7119281
  have hstable : (prefixWord ++ tailWord_7119281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119281).length < 2 ^ (prefixWord ++ tailWord_7119281).sum := by decide
  have hdescent : baseEnd_7119281 < baseStart_7119281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119304 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 3, 1, 3]
def baseStart_7119304 : Nat := 118140960795 + 7119304 * 2 ^ 59
def prefixEnd_7119304 : Nat := 4983230072969 + 3 ^ 40 * 7119304 * 2
def baseEnd_7119304 : Nat := 3655624877476718924058923

theorem tailTrace_7119304 : CollatzResearch.WordTrace tailWord_7119304 prefixEnd_7119304 3655624877476718924058923 := by
  unfold tailWord_7119304
  simp only [CollatzResearch.WordTrace]
  refine ⟨129831174499992481583566483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173108232666656642111421977 129831174499992481583566483)
  ·
    refine ⟨194746761749988722375349725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129831174499992481583566483 194746761749988722375349725)
    ·
      refine ⟨73030035656245770890756147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194746761749988722375349725 73030035656245770890756147)
      ·
        refine ⟨109545053484368656336134221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73030035656245770890756147 109545053484368656336134221)
        ·
          refine ⟨41079395056638246126050333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109545053484368656336134221 41079395056638246126050333)
          ·
            refine ⟨15404773146239342297268875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41079395056638246126050333 15404773146239342297268875)
            ·
              refine ⟨23107159719359013445903313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15404773146239342297268875 23107159719359013445903313)
              ·
                refine ⟨17330369789519260084427485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23107159719359013445903313 17330369789519260084427485)
                ·
                  refine ⟨6498888671069722531660307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17330369789519260084427485 6498888671069722531660307)
                  ·
                    refine ⟨9748333006604583797490461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6498888671069722531660307 9748333006604583797490461)
                    ·
                      refine ⟨3655624877476718924058923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9748333006604583797490461 3655624877476718924058923)
                      ·
                        rfl

theorem cell23_7119304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_7119304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119304 prefixEnd_7119304 := by exact prefixLift 7119304
  have htrace : WordTrace (prefixWord ++ tailWord_7119304) baseStart_7119304 baseEnd_7119304 := by
    simpa [prefixWord, tailWord_7119304, baseEnd_7119304] using wordTrace_append hprefix tailTrace_7119304
  have hstable : (prefixWord ++ tailWord_7119304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119304).length < 2 ^ (prefixWord ++ tailWord_7119304).sum := by decide
  have hdescent : baseEnd_7119304 < baseStart_7119304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119321 : List Nat := [1, 2, 1, 2, 4, 1, 4, 3, 1, 1, 3]
def baseStart_7119321 : Nat := 118140960795 + 7119321 * 2 ^ 59
def prefixEnd_7119321 : Nat := 4983230072969 + 3 ^ 40 * 7119321 * 2
def baseEnd_7119321 : Nat := 3655633606647845357546345

theorem tailTrace_7119321 : CollatzResearch.WordTrace tailWord_7119321 prefixEnd_7119321 3655633606647845357546345 := by
  unfold tailWord_7119321
  simp only [CollatzResearch.WordTrace]
  refine ⟨259662969040923375070501817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173108646027282250047001211 259662969040923375070501817)
  ·
    refine ⟨194747226780692531302876363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259662969040923375070501817 194747226780692531302876363)
    ·
      refine ⟨292120840171038796954314545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194747226780692531302876363 292120840171038796954314545)
      ·
        refine ⟨219090630128279097715735909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292120840171038796954314545 219090630128279097715735909)
        ·
          refine ⟨41079493149052330821700483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219090630128279097715735909 41079493149052330821700483)
          ·
            refine ⟨61619239723578496232550725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41079493149052330821700483 61619239723578496232550725)
            ·
              refine ⟨11553607448170968043603261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61619239723578496232550725 11553607448170968043603261)
              ·
                refine ⟨4332602793064113016351223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11553607448170968043603261 4332602793064113016351223)
                ·
                  refine ⟨6498904189596169524526835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4332602793064113016351223 6498904189596169524526835)
                  ·
                    refine ⟨9748356284394254286790253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6498904189596169524526835 9748356284394254286790253)
                    ·
                      refine ⟨3655633606647845357546345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9748356284394254286790253 3655633606647845357546345)
                      ·
                        rfl

theorem cell23_7119321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 1, 1, 3].length) (baseStart_7119321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119321 prefixEnd_7119321 := by exact prefixLift 7119321
  have htrace : WordTrace (prefixWord ++ tailWord_7119321) baseStart_7119321 baseEnd_7119321 := by
    simpa [prefixWord, tailWord_7119321, baseEnd_7119321] using wordTrace_append hprefix tailTrace_7119321
  have hstable : (prefixWord ++ tailWord_7119321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119321).length < 2 ^ (prefixWord ++ tailWord_7119321).sum := by decide
  have hdescent : baseEnd_7119321 < baseStart_7119321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119337 : List Nat := [1, 2, 1, 1, 1, 2, 1, 8, 2, 4]
def baseStart_7119337 : Nat := 118140960795 + 7119337 * 2 ^ 59
def prefixEnd_7119337 : Nat := 4983230072969 + 3 ^ 40 * 7119337 * 2
def baseEnd_7119337 : Nat := 1218547274112772431648757

theorem tailTrace_7119337 : CollatzResearch.WordTrace tailWord_7119337 prefixEnd_7119337 1218547274112772431648757 := by
  unfold tailWord_7119337
  simp only [CollatzResearch.WordTrace]
  refine ⟨259663552608865409803084265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173109035072576939868722843 259663552608865409803084265)
  ·
    refine ⟨194747664456649057352313199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259663552608865409803084265 194747664456649057352313199)
    ·
      refine ⟨292121496684973586028469799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194747664456649057352313199 292121496684973586028469799)
      ·
        refine ⟨438182245027460379042704699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292121496684973586028469799 438182245027460379042704699)
        ·
          refine ⟨657273367541190568564057049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438182245027460379042704699 657273367541190568564057049)
          ·
            refine ⟨492955025655892926423042787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657273367541190568564057049 492955025655892926423042787)
            ·
              refine ⟨739432538483839389634564181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492955025655892926423042787 739432538483839389634564181)
              ·
                refine ⟨8665225060357492847280049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 739432538483839389634564181 8665225060357492847280049)
                ·
                  refine ⟨6498918795268119635460037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8665225060357492847280049 6498918795268119635460037)
                  ·
                    refine ⟨1218547274112772431648757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6498918795268119635460037 1218547274112772431648757)
                    ·
                      rfl

theorem cell23_7119337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 4].length) (baseStart_7119337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119337 prefixEnd_7119337 := by exact prefixLift 7119337
  have htrace : WordTrace (prefixWord ++ tailWord_7119337) baseStart_7119337 baseEnd_7119337 := by
    simpa [prefixWord, tailWord_7119337, baseEnd_7119337] using wordTrace_append hprefix tailTrace_7119337
  have hstable : (prefixWord ++ tailWord_7119337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119337).length < 2 ^ (prefixWord ++ tailWord_7119337).sum := by decide
  have hdescent : baseEnd_7119337 < baseStart_7119337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119340 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_7119340 : Nat := 118140960795 + 7119340 * 2 ^ 59
def prefixEnd_7119340 : Nat := 4983230072969 + 3 ^ 40 * 7119340 * 2
def baseEnd_7119340 : Nat := 3655643362780280783208757

theorem tailTrace_7119340 : CollatzResearch.WordTrace tailWord_7119340 prefixEnd_7119340 3655643362780280783208757 := by
  unfold tailWord_7119340
  simp only [CollatzResearch.WordTrace]
  refine ⟨129831831013927270657721737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173109108018569694210295649 129831831013927270657721737)
  ·
    refine ⟨97373873260445452993291303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129831831013927270657721737 97373873260445452993291303)
    ·
      refine ⟨146060809890668179489936955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97373873260445452993291303 146060809890668179489936955)
      ·
        refine ⟨219091214836002269234905433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146060809890668179489936955 219091214836002269234905433)
        ·
          refine ⟨164318411127001701926179075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219091214836002269234905433 164318411127001701926179075)
          ·
            refine ⟨246477616690502552889268613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164318411127001701926179075 246477616690502552889268613)
            ·
              refine ⟨46214553129469228666737865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246477616690502552889268613 46214553129469228666737865)
              ·
                refine ⟨34660914847101921500053399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46214553129469228666737865 34660914847101921500053399)
                ·
                  refine ⟨51991372270652882250080099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34660914847101921500053399 51991372270652882250080099)
                  ·
                    refine ⟨77987058405979323375120149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51991372270652882250080099 77987058405979323375120149)
                    ·
                      refine ⟨3655643362780280783208757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77987058405979323375120149 3655643362780280783208757)
                      ·
                        rfl

theorem cell23_7119340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_7119340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119340 prefixEnd_7119340 := by exact prefixLift 7119340
  have htrace : WordTrace (prefixWord ++ tailWord_7119340) baseStart_7119340 baseEnd_7119340 := by
    simpa [prefixWord, tailWord_7119340, baseEnd_7119340] using wordTrace_append hprefix tailTrace_7119340
  have hstable : (prefixWord ++ tailWord_7119340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119340).length < 2 ^ (prefixWord ++ tailWord_7119340).sum := by decide
  have hdescent : baseEnd_7119340 < baseStart_7119340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119361 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_7119361 : Nat := 118140960795 + 7119361 * 2 ^ 59
def prefixEnd_7119361 : Nat := 4983230072969 + 3 ^ 40 * 7119361 * 2
def baseEnd_7119361 : Nat := 3655654145874025201046161

theorem tailTrace_7119361 : CollatzResearch.WordTrace tailWord_7119361 prefixEnd_7119361 3655654145874025201046161 := by
  unfold tailWord_7119361
  simp only [CollatzResearch.WordTrace]
  refine ⟨259664427960778461901957937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173109618640518974601305291 259664427960778461901957937)
  ·
    refine ⟨194748320970583846426468453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259664427960778461901957937 194748320970583846426468453)
    ·
      refine ⟨36515310181984471204962835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194748320970583846426468453 36515310181984471204962835)
      ·
        refine ⟨54772965272976706807444253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36515310181984471204962835 54772965272976706807444253)
        ·
          refine ⟨20539861977366265052791595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54772965272976706807444253 20539861977366265052791595)
          ·
            refine ⟨30809792966049397579187393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20539861977366265052791595 30809792966049397579187393)
            ·
              refine ⟨23107344724537048184390545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30809792966049397579187393 23107344724537048184390545)
              ·
                refine ⟨17330508543402786138292909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23107344724537048184390545 17330508543402786138292909)
                ·
                  refine ⟨6498940703776044801859841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17330508543402786138292909 6498940703776044801859841)
                  ·
                    refine ⟨4874205527832033601394881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6498940703776044801859841 4874205527832033601394881)
                    ·
                      refine ⟨3655654145874025201046161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4874205527832033601394881 3655654145874025201046161)
                      ·
                        rfl

theorem cell23_7119361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_7119361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119361 prefixEnd_7119361 := by exact prefixLift 7119361
  have htrace : WordTrace (prefixWord ++ tailWord_7119361) baseStart_7119361 baseEnd_7119361 := by
    simpa [prefixWord, tailWord_7119361, baseEnd_7119361] using wordTrace_append hprefix tailTrace_7119361
  have hstable : (prefixWord ++ tailWord_7119361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119361).length < 2 ^ (prefixWord ++ tailWord_7119361).sum := by decide
  have hdescent : baseEnd_7119361 < baseStart_7119361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119367 : List Nat := [1, 1, 4, 3, 3, 1, 1, 9]
def baseStart_7119367 : Nat := 118140960795 + 7119367 * 2 ^ 59
def prefixEnd_7119367 : Nat := 4983230072969 + 3 ^ 40 * 7119367 * 2
def baseEnd_7119367 : Nat := 135394712102146376947079

theorem tailTrace_7119367 : CollatzResearch.WordTrace tailWord_7119367 prefixEnd_7119367 135394712102146376947079 := by
  unfold tailWord_7119367
  simp only [CollatzResearch.WordTrace]
  refine ⟨259664646798756724926676355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173109764532504483284450903 259664646798756724926676355)
  ·
    refine ⟨389496970198135087390014533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259664646798756724926676355 389496970198135087390014533)
    ·
      refine ⟨73030681912150328885627725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389496970198135087390014533 73030681912150328885627725)
      ·
        refine ⟨27386505717056373332110397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73030681912150328885627725 27386505717056373332110397)
        ·
          refine ⟨10269939643896139999541399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27386505717056373332110397 10269939643896139999541399)
          ·
            refine ⟨15404909465844209999312099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10269939643896139999541399 15404909465844209999312099)
            ·
              refine ⟨23107364198766314998968149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15404909465844209999312099 23107364198766314998968149)
              ·
                refine ⟨135394712102146376947079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23107364198766314998968149 135394712102146376947079)
                ·
                  rfl

theorem cell23_7119367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 9].length) (baseStart_7119367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119367 prefixEnd_7119367 := by exact prefixLift 7119367
  have htrace : WordTrace (prefixWord ++ tailWord_7119367) baseStart_7119367 baseEnd_7119367 := by
    simpa [prefixWord, tailWord_7119367, baseEnd_7119367] using wordTrace_append hprefix tailTrace_7119367
  have hstable : (prefixWord ++ tailWord_7119367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119367).length < 2 ^ (prefixWord ++ tailWord_7119367).sum := by decide
  have hdescent : baseEnd_7119367 < baseStart_7119367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119395 : List Nat := [1, 1, 1, 4, 4, 2, 3, 2, 1, 2, 2]
def baseStart_7119395 : Nat := 118140960795 + 7119395 * 2 ^ 59
def prefixEnd_7119395 : Nat := 4983230072969 + 3 ^ 40 * 7119395 * 2
def baseEnd_7119395 : Nat := 3655671604216278068021005

theorem tailTrace_7119395 : CollatzResearch.WordTrace tailWord_7119395 prefixEnd_7119395 3655671604216278068021005 := by
  unfold tailWord_7119395
  simp only [CollatzResearch.WordTrace]
  refine ⟨259665668042655285708695639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173110445361770190472463759 259665668042655285708695639)
  ·
    refine ⟨389498502063982928563043459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259665668042655285708695639 389498502063982928563043459)
    ·
      refine ⟨584247753095974392844565189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389498502063982928563043459 584247753095974392844565189)
      ·
        refine ⟨109546453705495198658355973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 584247753095974392844565189 109546453705495198658355973)
        ·
          refine ⟨20539960069780349748441745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109546453705495198658355973 20539960069780349748441745)
          ·
            refine ⟨15404970052335262311331309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20539960069780349748441745 15404970052335262311331309)
            ·
              refine ⟨5776863769625723366749241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15404970052335262311331309 5776863769625723366749241)
              ·
                refine ⟨4332647827219292525061931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5776863769625723366749241 4332647827219292525061931)
                ·
                  refine ⟨6498971740828938787592897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4332647827219292525061931 6498971740828938787592897)
                  ·
                    refine ⟨4874228805621704090694673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6498971740828938787592897 4874228805621704090694673)
                    ·
                      refine ⟨3655671604216278068021005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4874228805621704090694673 3655671604216278068021005)
                      ·
                        rfl

theorem cell23_7119395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_7119395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119395 prefixEnd_7119395 := by exact prefixLift 7119395
  have htrace : WordTrace (prefixWord ++ tailWord_7119395) baseStart_7119395 baseEnd_7119395 := by
    simpa [prefixWord, tailWord_7119395, baseEnd_7119395] using wordTrace_append hprefix tailTrace_7119395
  have hstable : (prefixWord ++ tailWord_7119395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119395).length < 2 ^ (prefixWord ++ tailWord_7119395).sum := by decide
  have hdescent : baseEnd_7119395 < baseStart_7119395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119405 : List Nat := [1, 5, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_7119405 : Nat := 118140960795 + 7119405 * 2 ^ 59
def prefixEnd_7119405 : Nat := 4983230072969 + 3 ^ 40 * 7119405 * 2
def baseEnd_7119405 : Nat := 1218558913007607676298653

theorem tailTrace_7119405 : CollatzResearch.WordTrace tailWord_7119405 prefixEnd_7119405 1218558913007607676298653 := by
  unfold tailWord_7119405
  simp only [CollatzResearch.WordTrace]
  refine ⟨259666032772619057416559669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173110688515079371611039779 259666032772619057416559669)
  ·
    refine ⟨24343690572433036632802469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259666032772619057416559669 24343690572433036632802469)
    ·
      refine ⟨4564441982331194368650463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24343690572433036632802469 4564441982331194368650463)
      ·
        refine ⟨6846662973496791552975695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4564441982331194368650463 6846662973496791552975695)
        ·
          refine ⟨10269994460245187329463543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6846662973496791552975695 10269994460245187329463543)
          ·
            refine ⟨15404991690367780994195315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10269994460245187329463543 15404991690367780994195315)
            ·
              refine ⟨23107487535551671491292973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15404991690367780994195315 23107487535551671491292973)
              ·
                refine ⟨8665307825831876809234865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23107487535551671491292973 8665307825831876809234865)
                ·
                  refine ⟨6498980869373907606926149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8665307825831876809234865 6498980869373907606926149)
                  ·
                    refine ⟨1218558913007607676298653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6498980869373907606926149 1218558913007607676298653)
                    ·
                      rfl

theorem cell23_7119405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_7119405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119405 prefixEnd_7119405 := by exact prefixLift 7119405
  have htrace : WordTrace (prefixWord ++ tailWord_7119405) baseStart_7119405 baseEnd_7119405 := by
    simpa [prefixWord, tailWord_7119405, baseEnd_7119405] using wordTrace_append hprefix tailTrace_7119405
  have hstable : (prefixWord ++ tailWord_7119405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119405).length < 2 ^ (prefixWord ++ tailWord_7119405).sum := by decide
  have hdescent : baseEnd_7119405 < baseStart_7119405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119421 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 3, 3, 2]
def baseStart_7119421 : Nat := 118140960795 + 7119421 * 2 ^ 59
def prefixEnd_7119421 : Nat := 4983230072969 + 3 ^ 40 * 7119421 * 2
def baseEnd_7119421 : Nat := 3655684954713294966295885

theorem tailTrace_7119421 : CollatzResearch.WordTrace tailWord_7119421 prefixEnd_7119421 3655684954713294966295885 := by
  unfold tailWord_7119421
  simp only [CollatzResearch.WordTrace]
  refine ⟨259666616340561092149142117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173111077560374061432761411 259666616340561092149142117)
  ·
    refine ⟨48687490563855204777964147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259666616340561092149142117 48687490563855204777964147)
    ·
      refine ⟨73031235845782807166946221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48687490563855204777964147 73031235845782807166946221)
      ·
        refine ⟨27386713442168552687604833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73031235845782807166946221 27386713442168552687604833)
        ·
          refine ⟨20540035081626414515703625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27386713442168552687604833 20540035081626414515703625)
          ·
            refine ⟨15405026311219810886777719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20540035081626414515703625 15405026311219810886777719)
            ·
              refine ⟨23107539466829716330166579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15405026311219810886777719 23107539466829716330166579)
              ·
                refine ⟨34661309200244574495249869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23107539466829716330166579 34661309200244574495249869)
                ·
                  refine ⟨12997990950091715435718701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34661309200244574495249869 12997990950091715435718701)
                  ·
                    refine ⟨4874246606284393288394513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12997990950091715435718701 4874246606284393288394513)
                    ·
                      refine ⟨3655684954713294966295885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4874246606284393288394513 3655684954713294966295885)
                      ·
                        rfl

theorem cell23_7119421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_7119421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119421 prefixEnd_7119421 := by exact prefixLift 7119421
  have htrace : WordTrace (prefixWord ++ tailWord_7119421) baseStart_7119421 baseEnd_7119421 := by
    simpa [prefixWord, tailWord_7119421, baseEnd_7119421] using wordTrace_append hprefix tailTrace_7119421
  have hstable : (prefixWord ++ tailWord_7119421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119421).length < 2 ^ (prefixWord ++ tailWord_7119421).sum := by decide
  have hdescent : baseEnd_7119421 < baseStart_7119421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119434 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 3, 4, 2]
def baseStart_7119434 : Nat := 118140960795 + 7119434 * 2 ^ 59
def prefixEnd_7119434 : Nat := 4983230072969 + 3 ^ 40 * 7119434 * 2
def baseEnd_7119434 : Nat := 3655691629961803415433325

theorem tailTrace_7119434 : CollatzResearch.WordTrace tailWord_7119434 prefixEnd_7119434 3655691629961803415433325 := by
  unfold tailWord_7119434
  simp only [CollatzResearch.WordTrace]
  refine ⟨64916772622378498842341339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173111393659675996912910237 64916772622378498842341339)
  ·
    refine ⟨97375158933567748263512009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64916772622378498842341339 97375158933567748263512009)
    ·
      refine ⟨73031369200175811197634007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97375158933567748263512009 73031369200175811197634007)
      ·
        refine ⟨109547053800263716796451011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73031369200175811197634007 109547053800263716796451011)
        ·
          refine ⟨164320580700395575194676517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109547053800263716796451011 164320580700395575194676517)
          ·
            refine ⟨30810108881324170349001847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164320580700395575194676517 30810108881324170349001847)
            ·
              refine ⟨46215163321986255523502771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30810108881324170349001847 46215163321986255523502771)
              ·
                refine ⟨69322744982979383285254157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46215163321986255523502771 69322744982979383285254157)
                ·
                  refine ⟨25996029368617268731970309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69322744982979383285254157 25996029368617268731970309)
                  ·
                    refine ⟨4874255506615737887244433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25996029368617268731970309 4874255506615737887244433)
                    ·
                      refine ⟨3655691629961803415433325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4874255506615737887244433 3655691629961803415433325)
                      ·
                        rfl

theorem cell23_7119434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_7119434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119434 prefixEnd_7119434 := by exact prefixLift 7119434
  have htrace : WordTrace (prefixWord ++ tailWord_7119434) baseStart_7119434 baseEnd_7119434 := by
    simpa [prefixWord, tailWord_7119434, baseEnd_7119434] using wordTrace_append hprefix tailTrace_7119434
  have hstable : (prefixWord ++ tailWord_7119434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119434).length < 2 ^ (prefixWord ++ tailWord_7119434).sum := by decide
  have hdescent : baseEnd_7119434 < baseStart_7119434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119440 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 11]
def baseStart_7119440 : Nat := 118140960795 + 7119440 * 2 ^ 59
def prefixEnd_7119440 : Nat := 4983230072969 + 3 ^ 40 * 7119440 * 2
def baseEnd_7119440 : Nat := 406188301205081154662033

theorem tailTrace_7119440 : CollatzResearch.WordTrace tailWord_7119440 prefixEnd_7119440 406188301205081154662033 := by
  unfold tailWord_7119440
  simp only [CollatzResearch.WordTrace]
  refine ⟨129833654663746129197041887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173111539551661505596055849 129833654663746129197041887)
  ·
    refine ⟨194750481995619193795562831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129833654663746129197041887 194750481995619193795562831)
    ·
      refine ⟨292125722993428790693344247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194750481995619193795562831 292125722993428790693344247)
      ·
        refine ⟨438188584490143186040016371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292125722993428790693344247 438188584490143186040016371)
        ·
          refine ⟨657282876735214779060024557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438188584490143186040016371 657282876735214779060024557)
          ·
            refine ⟨246481078775705542147509209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 657282876735214779060024557 246481078775705542147509209)
            ·
              refine ⟨184860809081779156610631907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246481078775705542147509209 184860809081779156610631907)
              ·
                refine ⟨277291213622668734915947861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184860809081779156610631907 277291213622668734915947861)
                ·
                  refine ⟨406188301205081154662033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 277291213622668734915947861 406188301205081154662033)
                  ·
                    rfl

theorem cell23_7119440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 11].length) (baseStart_7119440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119440 prefixEnd_7119440 := by exact prefixLift 7119440
  have htrace : WordTrace (prefixWord ++ tailWord_7119440) baseStart_7119440 baseEnd_7119440 := by
    simpa [prefixWord, tailWord_7119440, baseEnd_7119440] using wordTrace_append hprefix tailTrace_7119440
  have hstable : (prefixWord ++ tailWord_7119440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119440).length < 2 ^ (prefixWord ++ tailWord_7119440).sum := by decide
  have hdescent : baseEnd_7119440 < baseStart_7119440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119447 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_7119447 : Nat := 118140960795 + 7119447 * 2 ^ 59
def prefixEnd_7119447 : Nat := 4983230072969 + 3 ^ 40 * 7119447 * 2
def baseEnd_7119447 : Nat := 3655698305210311864570765

theorem tailTrace_7119447 : CollatzResearch.WordTrace tailWord_7119447 prefixEnd_7119447 3655698305210311864570765 := by
  unfold tailWord_7119447
  simp only [CollatzResearch.WordTrace]
  refine ⟨259667564638466898589588595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173111709758977932393059063 259667564638466898589588595)
  ·
    refine ⟨389501346957700347884382893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259667564638466898589588595 389501346957700347884382893)
    ·
      refine ⟨146063005109137630456643585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389501346957700347884382893 146063005109137630456643585)
      ·
        refine ⟨109547253831853222842482689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146063005109137630456643585 109547253831853222842482689)
        ·
          refine ⟨82160440373889917131862017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109547253831853222842482689 82160440373889917131862017)
          ·
            refine ⟨61620330280417437848896513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82160440373889917131862017 61620330280417437848896513)
            ·
              refine ⟨46215247710313078386672385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61620330280417437848896513 46215247710313078386672385)
              ·
                refine ⟨34661435782734808790004289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46215247710313078386672385 34661435782734808790004289)
                ·
                  refine ⟨25996076837051106592503217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34661435782734808790004289 25996076837051106592503217)
                  ·
                    refine ⟨19497057627788329944377413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25996076837051106592503217 19497057627788329944377413)
                    ·
                      refine ⟨3655698305210311864570765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19497057627788329944377413 3655698305210311864570765)
                      ·
                        rfl

theorem cell23_7119447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_7119447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119447 prefixEnd_7119447 := by exact prefixLift 7119447
  have htrace : WordTrace (prefixWord ++ tailWord_7119447) baseStart_7119447 baseEnd_7119447 := by
    simpa [prefixWord, tailWord_7119447, baseEnd_7119447] using wordTrace_append hprefix tailTrace_7119447
  have hstable : (prefixWord ++ tailWord_7119447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119447).length < 2 ^ (prefixWord ++ tailWord_7119447).sum := by decide
  have hdescent : baseEnd_7119447 < baseStart_7119447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119474 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 7]
def baseStart_7119474 : Nat := 118140960795 + 7119474 * 2 ^ 59
def prefixEnd_7119474 : Nat := 4983230072969 + 3 ^ 40 * 7119474 * 2
def baseEnd_7119474 : Nat := 406190241020887028770349

theorem tailTrace_7119474 : CollatzResearch.WordTrace tailWord_7119474 prefixEnd_7119474 406190241020887028770349 := by
  unfold tailWord_7119474
  simp only [CollatzResearch.WordTrace]
  refine ⟨64917137352342270550205369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173112366272912721467214317 64917137352342270550205369)
  ·
    refine ⟨48687853014256702912654027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64917137352342270550205369 48687853014256702912654027)
    ·
      refine ⟨73031779521385054368981041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48687853014256702912654027 73031779521385054368981041)
      ·
        refine ⟨54773834641038790776735781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73031779521385054368981041 54773834641038790776735781)
        ·
          refine ⟨10270093995194773270637959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54773834641038790776735781 10270093995194773270637959)
          ·
            refine ⟨15405140992792159905956939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10270093995194773270637959 15405140992792159905956939)
            ·
              refine ⟨23107711489188239858935409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15405140992792159905956939 23107711489188239858935409)
              ·
                refine ⟨17330783616891179894201557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23107711489188239858935409 17330783616891179894201557)
                ·
                  refine ⟨406190241020887028770349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17330783616891179894201557 406190241020887028770349)
                  ·
                    rfl

theorem cell23_7119474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_7119474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119474 prefixEnd_7119474 := by exact prefixLift 7119474
  have htrace : WordTrace (prefixWord ++ tailWord_7119474) baseStart_7119474 baseEnd_7119474 := by
    simpa [prefixWord, tailWord_7119474, baseEnd_7119474] using wordTrace_append hprefix tailTrace_7119474
  have hstable : (prefixWord ++ tailWord_7119474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119474).length < 2 ^ (prefixWord ++ tailWord_7119474).sum := by decide
  have hdescent : baseEnd_7119474 < baseStart_7119474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119487 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 2, 5]
def baseStart_7119487 : Nat := 118140960795 + 7119487 * 2 ^ 59
def prefixEnd_7119487 : Nat := 4983230072969 + 3 ^ 40 * 7119487 * 2
def baseEnd_7119487 : Nat := 1218572948145497236023527

theorem tailTrace_7119487 : CollatzResearch.WordTrace tailWord_7119487 prefixEnd_7119487 1218572948145497236023527 := by
  unfold tailWord_7119487
  simp only [CollatzResearch.WordTrace]
  refine ⟨259669023558321985421044715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173112682372214656947363143 259669023558321985421044715)
  ·
    refine ⟨389503535337482978131567073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259669023558321985421044715 389503535337482978131567073)
    ·
      refine ⟨292127651503112233598675305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389503535337482978131567073 292127651503112233598675305)
      ·
        refine ⟨219095738627334175199006479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292127651503112233598675305 219095738627334175199006479)
        ·
          refine ⟨328643607941001262798509719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219095738627334175199006479 328643607941001262798509719)
          ·
            refine ⟨492965411911501894197764579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328643607941001262798509719 492965411911501894197764579)
            ·
              refine ⟨739448117867252841296646869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492965411911501894197764579 739448117867252841296646869)
              ·
                refine ⟨17330815262513738467890161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 739448117867252841296646869 17330815262513738467890161)
                ·
                  refine ⟨12998111446885303850917621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17330815262513738467890161 12998111446885303850917621)
                  ·
                    refine ⟨1218572948145497236023527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12998111446885303850917621 1218572948145497236023527)
                    ·
                      rfl

theorem cell23_7119487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 5].length) (baseStart_7119487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119487 prefixEnd_7119487 := by exact prefixLift 7119487
  have htrace : WordTrace (prefixWord ++ tailWord_7119487) baseStart_7119487 baseEnd_7119487 := by
    simpa [prefixWord, tailWord_7119487, baseEnd_7119487] using wordTrace_append hprefix tailTrace_7119487
  have hstable : (prefixWord ++ tailWord_7119487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119487).length < 2 ^ (prefixWord ++ tailWord_7119487).sum := by decide
  have hdescent : baseEnd_7119487 < baseStart_7119487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119542 : List Nat := [5, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_7119542 : Nat := 118140960795 + 7119542 * 2 ^ 59
def prefixEnd_7119542 : Nat := 4983230072969 + 3 ^ 40 * 7119542 * 2
def baseEnd_7119542 : Nat := 406194120652498776986981

theorem tailTrace_7119542 : CollatzResearch.WordTrace tailWord_7119542 prefixEnd_7119542 406194120652498776986981 := by
  unfold tailWord_7119542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16229439348320170613393555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 173114019715415153209531253 16229439348320170613393555)
  ·
    refine ⟨24344159022480255920090333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16229439348320170613393555 24344159022480255920090333)
    ·
      refine ⟨9129059633430095970033875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24344159022480255920090333 9129059633430095970033875)
      ·
        refine ⟨13693589450145143955050813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9129059633430095970033875 13693589450145143955050813)
        ·
          refine ⟨5135096043804428983144055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13693589450145143955050813 5135096043804428983144055)
          ·
            refine ⟨7702644065706643474716083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5135096043804428983144055 7702644065706643474716083)
            ·
              refine ⟨11553966098559965212074125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7702644065706643474716083 11553966098559965212074125)
              ·
                refine ⟨4332737286959986954527797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11553966098559965212074125 4332737286959986954527797)
                ·
                  refine ⟨406194120652498776986981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4332737286959986954527797 406194120652498776986981)
                  ·
                    rfl

theorem cell23_7119542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_7119542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119542 prefixEnd_7119542 := by exact prefixLift 7119542
  have htrace : WordTrace (prefixWord ++ tailWord_7119542) baseStart_7119542 baseEnd_7119542 := by
    simpa [prefixWord, tailWord_7119542, baseEnd_7119542] using wordTrace_append hprefix tailTrace_7119542
  have hstable : (prefixWord ++ tailWord_7119542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119542).length < 2 ^ (prefixWord ++ tailWord_7119542).sum := by decide
  have hdescent : baseEnd_7119542 < baseStart_7119542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119564 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 8]
def baseStart_7119564 : Nat := 118140960795 + 7119564 * 2 ^ 59
def prefixEnd_7119564 : Nat := 4983230072969 + 3 ^ 40 * 7119564 * 2
def baseEnd_7119564 : Nat := 406195375827431989645303

theorem tailTrace_7119564 : CollatzResearch.WordTrace tailWord_7119564 prefixEnd_7119564 406195375827431989645303 := by
  unfold tailWord_7119564
  simp only [CollatzResearch.WordTrace]
  refine ⟨129835915989521513785798873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173114554652695351714398497 129835915989521513785798873)
  ·
    refine ⟨97376936992141135339349155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129835915989521513785798873 97376936992141135339349155)
    ·
      refine ⟨146065405488211703009023733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97376936992141135339349155 146065405488211703009023733)
      ·
        refine ⟨13693631764519847157095975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146065405488211703009023733 13693631764519847157095975)
        ·
          refine ⟨20540447646779770735643963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13693631764519847157095975 20540447646779770735643963)
          ·
            refine ⟨30810671470169656103465945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20540447646779770735643963 30810671470169656103465945)
            ·
              refine ⟨23108003602627242077599459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30810671470169656103465945 23108003602627242077599459)
              ·
                refine ⟨34662005403940863116399189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23108003602627242077599459 34662005403940863116399189)
                ·
                  refine ⟨406195375827431989645303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34662005403940863116399189 406195375827431989645303)
                  ·
                    rfl

theorem cell23_7119564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_7119564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119564 prefixEnd_7119564 := by exact prefixLift 7119564
  have htrace : WordTrace (prefixWord ++ tailWord_7119564) baseStart_7119564 baseEnd_7119564 := by
    simpa [prefixWord, tailWord_7119564, baseEnd_7119564] using wordTrace_append hprefix tailTrace_7119564
  have hstable : (prefixWord ++ tailWord_7119564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119564).length < 2 ^ (prefixWord ++ tailWord_7119564).sum := by decide
  have hdescent : baseEnd_7119564 < baseStart_7119564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119608 : List Nat := [2, 1, 2, 1, 1, 2, 4, 5, 1, 1, 3]
def baseStart_7119608 : Nat := 118140960795 + 7119608 * 2 ^ 59
def prefixEnd_7119608 : Nat := 4983230072969 + 3 ^ 40 * 7119608 * 2
def baseEnd_7119608 : Nat := 3655780975595685734657525

theorem tailTrace_7119608 : CollatzResearch.WordTrace tailWord_7119608 prefixEnd_7119608 3655780975595685734657525 := by
  unfold tailWord_7119608
  simp only [CollatzResearch.WordTrace]
  refine ⟨129836718395441811543099739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173115624527255748724132985 129836718395441811543099739)
  ·
    refine ⟨194755077593162717314649609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129836718395441811543099739 194755077593162717314649609)
    ·
      refine ⟨146066308194872037985987207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194755077593162717314649609 146066308194872037985987207)
      ·
        refine ⟨219099462292308056978980811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146066308194872037985987207 219099462292308056978980811)
        ·
          refine ⟨328649193438462085468471217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219099462292308056978980811 328649193438462085468471217)
          ·
            refine ⟨246486895078846564101353413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328649193438462085468471217 246486895078846564101353413)
            ·
              refine ⟨46216292827283730769003765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246486895078846564101353413 46216292827283730769003765)
              ·
                refine ⟨4332777452557849759594103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46216292827283730769003765 4332777452557849759594103)
                ·
                  refine ⟨6499166178836774639391155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4332777452557849759594103 6499166178836774639391155)
                  ·
                    refine ⟨9748749268255161959086733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6499166178836774639391155 9748749268255161959086733)
                    ·
                      refine ⟨3655780975595685734657525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9748749268255161959086733 3655780975595685734657525)
                      ·
                        rfl

theorem cell23_7119608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 5, 1, 1, 3].length) (baseStart_7119608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119608 prefixEnd_7119608 := by exact prefixLift 7119608
  have htrace : WordTrace (prefixWord ++ tailWord_7119608) baseStart_7119608 baseEnd_7119608 := by
    simpa [prefixWord, tailWord_7119608, baseEnd_7119608] using wordTrace_append hprefix tailTrace_7119608
  have hstable : (prefixWord ++ tailWord_7119608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119608).length < 2 ^ (prefixWord ++ tailWord_7119608).sum := by decide
  have hdescent : baseEnd_7119608 < baseStart_7119608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119625 : List Nat := [1, 2, 1, 1, 3, 2, 6, 2, 1, 1, 3]
def baseStart_7119625 : Nat := 118140960795 + 7119625 * 2 ^ 59
def prefixEnd_7119625 : Nat := 4983230072969 + 3 ^ 40 * 7119625 * 2
def baseEnd_7119625 : Nat := 3655789704766812168144947

theorem tailTrace_7119625 : CollatzResearch.WordTrace tailWord_7119625 prefixEnd_7119625 3655789704766812168144947 := by
  unfold tailWord_7119625
  simp only [CollatzResearch.WordTrace]
  refine ⟨259674056831822034989568329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173116037887881356659712219 259674056831822034989568329)
  ·
    refine ⟨194755542623866526242176247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259674056831822034989568329 194755542623866526242176247)
    ·
      refine ⟨292133313935799789363264371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194755542623866526242176247 292133313935799789363264371)
      ·
        refine ⟨438199970903699684044896557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292133313935799789363264371 438199970903699684044896557)
        ·
          refine ⟨164324989088887381516836209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438199970903699684044896557 164324989088887381516836209)
          ·
            refine ⟨123243741816665536137627157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164324989088887381516836209 123243741816665536137627157)
            ·
              refine ⟨5777050397656197006451273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123243741816665536137627157 5777050397656197006451273)
              ·
                refine ⟨4332787798242147754838455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5777050397656197006451273 4332787798242147754838455)
                ·
                  refine ⟨6499181697363221632257683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4332787798242147754838455 6499181697363221632257683)
                  ·
                    refine ⟨9748772546044832448386525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6499181697363221632257683 9748772546044832448386525)
                    ·
                      refine ⟨3655789704766812168144947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9748772546044832448386525 3655789704766812168144947)
                      ·
                        rfl

theorem cell23_7119625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 1, 1, 3].length) (baseStart_7119625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119625 prefixEnd_7119625 := by exact prefixLift 7119625
  have htrace : WordTrace (prefixWord ++ tailWord_7119625) baseStart_7119625 baseEnd_7119625 := by
    simpa [prefixWord, tailWord_7119625, baseEnd_7119625] using wordTrace_append hprefix tailTrace_7119625
  have hstable : (prefixWord ++ tailWord_7119625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119625).length < 2 ^ (prefixWord ++ tailWord_7119625).sum := by decide
  have hdescent : baseEnd_7119625 < baseStart_7119625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119648 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 5, 2, 2]
def baseStart_7119648 : Nat := 118140960795 + 7119648 * 2 ^ 59
def prefixEnd_7119648 : Nat := 4983230072969 + 3 ^ 40 * 7119648 * 2
def baseEnd_7119648 : Nat := 3655801514821865578157341

theorem tailTrace_7119648 : CollatzResearch.WordTrace tailWord_7119648 prefixEnd_7119648 3655801514821865578157341 := by
  unfold tailWord_7119648
  simp only [CollatzResearch.WordTrace]
  refine ⟨129837447855369354958827799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173116597140492473278437065 129837447855369354958827799)
  ·
    refine ⟨194756171783054032438241699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129837447855369354958827799 194756171783054032438241699)
    ·
      refine ⟨292134257674581048657362549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194756171783054032438241699 292134257674581048657362549)
      ·
        refine ⟨27387586656991973311627739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 292134257674581048657362549 27387586656991973311627739)
        ·
          refine ⟨41081379985487959967441609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27387586656991973311627739 41081379985487959967441609)
          ·
            refine ⟨30811034989115969975581207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41081379985487959967441609 30811034989115969975581207)
            ·
              refine ⟨46216552483673954963371811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30811034989115969975581207 46216552483673954963371811)
              ·
                refine ⟨69324828725510932445057717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46216552483673954963371811 69324828725510932445057717)
                ·
                  refine ⟨6499202693016649916724161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69324828725510932445057717 6499202693016649916724161)
                  ·
                    refine ⟨4874402019762487437543121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6499202693016649916724161 4874402019762487437543121)
                    ·
                      refine ⟨3655801514821865578157341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4874402019762487437543121 3655801514821865578157341)
                      ·
                        rfl

theorem cell23_7119648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_7119648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119648 prefixEnd_7119648 := by exact prefixLift 7119648
  have htrace : WordTrace (prefixWord ++ tailWord_7119648) baseStart_7119648 baseEnd_7119648 := by
    simpa [prefixWord, tailWord_7119648, baseEnd_7119648] using wordTrace_append hprefix tailTrace_7119648
  have hstable : (prefixWord ++ tailWord_7119648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119648).length < 2 ^ (prefixWord ++ tailWord_7119648).sum := by decide
  have hdescent : baseEnd_7119648 < baseStart_7119648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119651 : List Nat := [1, 1, 1, 4, 2, 1, 1, 6, 1, 2, 3]
def baseStart_7119651 : Nat := 118140960795 + 7119651 * 2 ^ 59
def prefixEnd_7119651 : Nat := 4983230072969 + 3 ^ 40 * 7119651 * 2
def baseEnd_7119651 : Nat := 3655803055263829066419827

theorem tailTrace_7119651 : CollatzResearch.WordTrace tailWord_7119651 prefixEnd_7119651 3655803055263829066419827 := by
  unfold tailWord_7119651
  simp only [CollatzResearch.WordTrace]
  refine ⟨259675005129727841430014807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173116670086485227620009871 259675005129727841430014807)
  ·
    refine ⟨389512507694591762145022211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259675005129727841430014807 389512507694591762145022211)
    ·
      refine ⟨584268761541887643217533317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389512507694591762145022211 584268761541887643217533317)
      ·
        refine ⟨109550392789103933103287497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 584268761541887643217533317 109550392789103933103287497)
        ·
          refine ⟨82162794591827949827465623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109550392789103933103287497 82162794591827949827465623)
          ·
            refine ⟨123244191887741924741198435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82162794591827949827465623 123244191887741924741198435)
            ·
              refine ⟨184866287831612887111797653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123244191887741924741198435 184866287831612887111797653)
              ·
                refine ⟨8665607242106854083365515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184866287831612887111797653 8665607242106854083365515)
                ·
                  refine ⟨12998410863160281125048273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8665607242106854083365515 12998410863160281125048273)
                  ·
                    refine ⟨9748808147370210843786205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12998410863160281125048273 9748808147370210843786205)
                    ·
                      refine ⟨3655803055263829066419827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9748808147370210843786205 3655803055263829066419827)
                      ·
                        rfl

theorem cell23_7119651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_7119651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119651 prefixEnd_7119651 := by exact prefixLift 7119651
  have htrace : WordTrace (prefixWord ++ tailWord_7119651) baseStart_7119651 baseEnd_7119651 := by
    simpa [prefixWord, tailWord_7119651, baseEnd_7119651] using wordTrace_append hprefix tailTrace_7119651
  have hstable : (prefixWord ++ tailWord_7119651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119651).length < 2 ^ (prefixWord ++ tailWord_7119651).sum := by decide
  have hdescent : baseEnd_7119651 < baseStart_7119651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119652 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 2, 3, 2]
def baseStart_7119652 : Nat := 118140960795 + 7119652 * 2 ^ 59
def prefixEnd_7119652 : Nat := 4983230072969 + 3 ^ 40 * 7119652 * 2
def baseEnd_7119652 : Nat := 3655803568744483562507323

theorem tailTrace_7119652 : CollatzResearch.WordTrace tailWord_7119652 prefixEnd_7119652 3655803568744483562507323 := by
  unfold tailWord_7119652
  simp only [CollatzResearch.WordTrace]
  refine ⟨129837520801362109300400605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173116694401816145733867473 129837520801362109300400605)
  ·
    refine ⟨48689070300510790987650227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129837520801362109300400605 48689070300510790987650227)
    ·
      refine ⟨73033605450766186481475341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48689070300510790987650227 73033605450766186481475341)
      ·
        refine ⟨27387602044037319930553253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73033605450766186481475341 27387602044037319930553253)
        ·
          refine ⟨5135175383256997486978735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27387602044037319930553253 5135175383256997486978735)
          ·
            refine ⟨7702763074885496230468103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5135175383256997486978735 7702763074885496230468103)
            ·
              refine ⟨11554144612328244345702155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7702763074885496230468103 11554144612328244345702155)
              ·
                refine ⟨17331216918492366518553233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11554144612328244345702155 17331216918492366518553233)
                ·
                  refine ⟨12998412688869274888914925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17331216918492366518553233 12998412688869274888914925)
                  ·
                    refine ⟨4874404758325978083343097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12998412688869274888914925 4874404758325978083343097)
                    ·
                      refine ⟨3655803568744483562507323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4874404758325978083343097 3655803568744483562507323)
                      ·
                        rfl

theorem cell23_7119652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_7119652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119652 prefixEnd_7119652 := by exact prefixLift 7119652
  have htrace : WordTrace (prefixWord ++ tailWord_7119652) baseStart_7119652 baseEnd_7119652 := by
    simpa [prefixWord, tailWord_7119652, baseEnd_7119652] using wordTrace_append hprefix tailTrace_7119652
  have hstable : (prefixWord ++ tailWord_7119652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119652).length < 2 ^ (prefixWord ++ tailWord_7119652).sum := by decide
  have hdescent : baseEnd_7119652 < baseStart_7119652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119694 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_7119694 : Nat := 118140960795 + 7119694 * 2 ^ 59
def prefixEnd_7119694 : Nat := 4983230072969 + 3 ^ 40 * 7119694 * 2
def baseEnd_7119694 : Nat := 3655825134931972398182129

theorem tailTrace_7119694 : CollatzResearch.WordTrace tailWord_7119694 prefixEnd_7119694 3655825134931972398182129 := by
  unfold tailWord_7119694
  simp only [CollatzResearch.WordTrace]
  refine ⟨32459571683571507471728767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173117715645714706515886757 32459571683571507471728767)
  ·
    refine ⟨48689357525357261207593151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32459571683571507471728767 48689357525357261207593151)
    ·
      refine ⟨73034036288035891811389727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48689357525357261207593151 73034036288035891811389727)
      ·
        refine ⟨109551054432053837717084591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73034036288035891811389727 109551054432053837717084591)
        ·
          refine ⟨164326581648080756575626887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109551054432053837717084591 164326581648080756575626887)
          ·
            refine ⟨246489872472121134863440331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164326581648080756575626887 246489872472121134863440331)
            ·
              refine ⟨369734808708181702295160497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246489872472121134863440331 369734808708181702295160497)
              ·
                refine ⟨277301106531136276721370373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369734808708181702295160497 277301106531136276721370373)
                ·
                  refine ⟨51993957474588051885256945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 277301106531136276721370373 51993957474588051885256945)
                  ·
                    refine ⟨38995468105941038913942709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51993957474588051885256945 38995468105941038913942709)
                    ·
                      refine ⟨3655825134931972398182129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38995468105941038913942709 3655825134931972398182129)
                      ·
                        rfl

theorem cell23_7119694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_7119694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119694 prefixEnd_7119694 := by exact prefixLift 7119694
  have htrace : WordTrace (prefixWord ++ tailWord_7119694) baseStart_7119694 baseEnd_7119694 := by
    simpa [prefixWord, tailWord_7119694, baseEnd_7119694] using wordTrace_append hprefix tailTrace_7119694
  have hstable : (prefixWord ++ tailWord_7119694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119694).length < 2 ^ (prefixWord ++ tailWord_7119694).sum := by decide
  have hdescent : baseEnd_7119694 < baseStart_7119694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119704 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_7119704 : Nat := 118140960795 + 7119704 * 2 ^ 59
def prefixEnd_7119704 : Nat := 4983230072969 + 3 ^ 40 * 7119704 * 2
def baseEnd_7119704 : Nat := 3655830269738517359057083

theorem tailTrace_7119704 : CollatzResearch.WordTrace tailWord_7119704 prefixEnd_7119704 3655830269738517359057083 := by
  unfold tailWord_7119704
  simp only [CollatzResearch.WordTrace]
  refine ⟨129838469099267915740847083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173117958799023887654462777 129838469099267915740847083)
  ·
    refine ⟨194757703648901873611270625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129838469099267915740847083 194757703648901873611270625)
    ·
      refine ⟨146068277736676405208452969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194757703648901873611270625 146068277736676405208452969)
      ·
        refine ⟨109551208302507303906339727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146068277736676405208452969 109551208302507303906339727)
        ·
          refine ⟨164326812453760955859509591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109551208302507303906339727 164326812453760955859509591)
          ·
            refine ⟨246490218680641433789264387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164326812453760955859509591 246490218680641433789264387)
            ·
              refine ⟨369735328020962150683896581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246490218680641433789264387 369735328020962150683896581)
              ·
                refine ⟨69325374003930403253230609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 369735328020962150683896581 69325374003930403253230609)
                ·
                  refine ⟨51994030502947802439922957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69325374003930403253230609 51994030502947802439922957)
                  ·
                    refine ⟨19497761438605425914971109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51994030502947802439922957 19497761438605425914971109)
                    ·
                      refine ⟨3655830269738517359057083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19497761438605425914971109 3655830269738517359057083)
                      ·
                        rfl

theorem cell23_7119704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_7119704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119704 prefixEnd_7119704 := by exact prefixLift 7119704
  have htrace : WordTrace (prefixWord ++ tailWord_7119704) baseStart_7119704 baseEnd_7119704 := by
    simpa [prefixWord, tailWord_7119704, baseEnd_7119704] using wordTrace_append hprefix tailTrace_7119704
  have hstable : (prefixWord ++ tailWord_7119704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119704).length < 2 ^ (prefixWord ++ tailWord_7119704).sum := by decide
  have hdescent : baseEnd_7119704 < baseStart_7119704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119744 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 7]
def baseStart_7119744 : Nat := 118140960795 + 7119744 * 2 ^ 59
def prefixEnd_7119744 : Nat := 4983230072969 + 3 ^ 40 * 7119744 * 2
def baseEnd_7119744 : Nat := 406205645440521911395211

theorem tailTrace_7119744 : CollatzResearch.WordTrace tailWord_7119744 prefixEnd_7119744 406205645440521911395211 := by
  unfold tailWord_7119744
  simp only [CollatzResearch.WordTrace]
  refine ⟨129839198559195459156575143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173118931412260612208766857 129839198559195459156575143)
  ·
    refine ⟨194758797838793188734862715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129839198559195459156575143 194758797838793188734862715)
    ·
      refine ⟨292138196758189783102294073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194758797838793188734862715 292138196758189783102294073)
      ·
        refine ⟨219103647568642337326720555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292138196758189783102294073 219103647568642337326720555)
        ·
          refine ⟨328655471352963505990080833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219103647568642337326720555 328655471352963505990080833)
          ·
            refine ⟨246491603514722629492560625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328655471352963505990080833 246491603514722629492560625)
            ·
              refine ⟨184868702636041972119420469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246491603514722629492560625 184868702636041972119420469)
              ·
                refine ⟨17331440872128934886195669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184868702636041972119420469 17331440872128934886195669)
                ·
                  refine ⟨406205645440521911395211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17331440872128934886195669 406205645440521911395211)
                  ·
                    rfl

theorem cell23_7119744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 7].length) (baseStart_7119744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119744 prefixEnd_7119744 := by exact prefixLift 7119744
  have htrace : WordTrace (prefixWord ++ tailWord_7119744) baseStart_7119744 baseEnd_7119744 := by
    simpa [prefixWord, tailWord_7119744, baseEnd_7119744] using wordTrace_append hprefix tailTrace_7119744
  have hstable : (prefixWord ++ tailWord_7119744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119744).length < 2 ^ (prefixWord ++ tailWord_7119744).sum := by decide
  have hdescent : baseEnd_7119744 < baseStart_7119744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119801 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 1, 2, 5]
def baseStart_7119801 : Nat := 118140960795 + 7119801 * 2 ^ 59
def prefixEnd_7119801 : Nat := 4983230072969 + 3 ^ 40 * 7119801 * 2
def baseEnd_7119801 : Nat := 3655880077362003479544137

theorem tailTrace_7119801 : CollatzResearch.WordTrace tailWord_7119801 prefixEnd_7119801 3655880077362003479544137 := by
  unfold tailWord_7119801
  simp only [CollatzResearch.WordTrace]
  refine ⟨259680476079184417047975257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173120317386122944698650171 259680476079184417047975257)
  ·
    refine ⟨194760357059388312785981443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259680476079184417047975257 194760357059388312785981443)
    ·
      refine ⟨292140535589082469178972165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194760357059388312785981443 292140535589082469178972165)
      ·
        refine ⟨54776350422952962971057281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292140535589082469178972165 54776350422952962971057281)
        ·
          refine ⟨41082262817214722228292961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54776350422952962971057281 41082262817214722228292961)
          ·
            refine ⟨30811697112911041671219721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41082262817214722228292961 30811697112911041671219721)
            ·
              refine ⟨23108772834683281253414791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30811697112911041671219721 23108772834683281253414791)
              ·
                refine ⟨34663159252024921880122187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23108772834683281253414791 34663159252024921880122187)
                ·
                  refine ⟨51994738878037382820183281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34663159252024921880122187 51994738878037382820183281)
                  ·
                    refine ⟨38996054158528037115137461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51994738878037382820183281 38996054158528037115137461)
                    ·
                      refine ⟨3655880077362003479544137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38996054158528037115137461 3655880077362003479544137)
                      ·
                        rfl

theorem cell23_7119801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_7119801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119801 prefixEnd_7119801 := by exact prefixLift 7119801
  have htrace : WordTrace (prefixWord ++ tailWord_7119801) baseStart_7119801 baseEnd_7119801 := by
    simpa [prefixWord, tailWord_7119801, baseEnd_7119801] using wordTrace_append hprefix tailTrace_7119801
  have hstable : (prefixWord ++ tailWord_7119801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119801).length < 2 ^ (prefixWord ++ tailWord_7119801).sum := by decide
  have hdescent : baseEnd_7119801 < baseStart_7119801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119828 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_7119828 : Nat := 118140960795 + 7119828 * 2 ^ 59
def prefixEnd_7119828 : Nat := 4983230072969 + 3 ^ 40 * 7119828 * 2
def baseEnd_7119828 : Nat := 3655893941339674873906513

theorem tailTrace_7119828 : CollatzResearch.WordTrace tailWord_7119828 prefixEnd_7119828 3655893941339674873906513 := by
  unfold tailWord_7119828
  simp only [CollatzResearch.WordTrace]
  refine ⟨129840730425043300329604069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173120973900057733772805425 129840730425043300329604069)
  ·
    refine ⟨24345136954695618811800763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129840730425043300329604069 24345136954695618811800763)
    ·
      refine ⟨36517705432043428217701145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24345136954695618811800763 36517705432043428217701145)
      ·
        refine ⟨27388279074032571163275859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36517705432043428217701145 27388279074032571163275859)
        ·
          refine ⟨41082418611048856744913789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27388279074032571163275859 41082418611048856744913789)
          ·
            refine ⟨15405906979143321279342671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41082418611048856744913789 15405906979143321279342671)
            ·
              refine ⟨23108860468714981919014007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15405906979143321279342671 23108860468714981919014007)
              ·
                refine ⟨34663290703072472878521011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23108860468714981919014007 34663290703072472878521011)
                ·
                  refine ⟨51994936054608709317781517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34663290703072472878521011 51994936054608709317781517)
                  ·
                    refine ⟨19498101020478265994168069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51994936054608709317781517 19498101020478265994168069)
                    ·
                      refine ⟨3655893941339674873906513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19498101020478265994168069 3655893941339674873906513)
                      ·
                        rfl

theorem cell23_7119828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_7119828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119828 prefixEnd_7119828 := by exact prefixLift 7119828
  have htrace : WordTrace (prefixWord ++ tailWord_7119828) baseStart_7119828 baseEnd_7119828 := by
    simpa [prefixWord, tailWord_7119828, baseEnd_7119828] using wordTrace_append hprefix tailTrace_7119828
  have hstable : (prefixWord ++ tailWord_7119828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119828).length < 2 ^ (prefixWord ++ tailWord_7119828).sum := by decide
  have hdescent : baseEnd_7119828 < baseStart_7119828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119848 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_7119848 : Nat := 118140960795 + 7119848 * 2 ^ 59
def prefixEnd_7119848 : Nat := 4983230072969 + 3 ^ 40 * 7119848 * 2
def baseEnd_7119848 : Nat := 3655904210952764795656421

theorem tailTrace_7119848 : CollatzResearch.WordTrace tailWord_7119848 prefixEnd_7119848 3655904210952764795656421 := by
  unfold tailWord_7119848
  simp only [CollatzResearch.WordTrace]
  refine ⟨129841095155007072037468099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173121460206676096049957465 129841095155007072037468099)
  ·
    refine ⟨194761642732510608056202149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129841095155007072037468099 194761642732510608056202149)
    ·
      refine ⟨36517808012345739010537903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194761642732510608056202149 36517808012345739010537903)
      ·
        refine ⟨54776712018518608515806855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36517808012345739010537903 54776712018518608515806855)
        ·
          refine ⟨82165068027777912773710283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54776712018518608515806855 82165068027777912773710283)
          ·
            refine ⟨123247602041666869160565425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82165068027777912773710283 123247602041666869160565425)
            ·
              refine ⟨92435701531250151870424069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123247602041666869160565425 92435701531250151870424069)
              ·
                refine ⟨17331694037109403475704513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92435701531250151870424069 17331694037109403475704513)
                ·
                  refine ⟨12998770527832052606778385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17331694037109403475704513 12998770527832052606778385)
                  ·
                    refine ⟨9749077895874039455083789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12998770527832052606778385 9749077895874039455083789)
                    ·
                      refine ⟨3655904210952764795656421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9749077895874039455083789 3655904210952764795656421)
                      ·
                        rfl

theorem cell23_7119848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_7119848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119848 prefixEnd_7119848 := by exact prefixLift 7119848
  have htrace : WordTrace (prefixWord ++ tailWord_7119848) baseStart_7119848 baseEnd_7119848 := by
    simpa [prefixWord, tailWord_7119848, baseEnd_7119848] using wordTrace_append hprefix tailTrace_7119848
  have hstable : (prefixWord ++ tailWord_7119848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119848).length < 2 ^ (prefixWord ++ tailWord_7119848).sum := by decide
  have hdescent : baseEnd_7119848 < baseStart_7119848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119855 : List Nat := [1, 1, 2, 1, 4, 3, 2, 4, 1, 4]
def baseStart_7119855 : Nat := 118140960795 + 7119855 * 2 ^ 59
def prefixEnd_7119855 : Nat := 4983230072969 + 3 ^ 40 * 7119855 * 2
def baseEnd_7119855 : Nat := 1218635935105782089422963

theorem tailTrace_7119855 : CollatzResearch.WordTrace tailWord_7119855 prefixEnd_7119855 1218635935105782089422963 := by
  unfold tailWord_7119855
  simp only [CollatzResearch.WordTrace]
  refine ⟨259682445620988784270441019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173121630413992522846960679 259682445620988784270441019)
  ·
    refine ⟨389523668431483176405661529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259682445620988784270441019 389523668431483176405661529)
    ·
      refine ⟨292142751323612382304246147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389523668431483176405661529 292142751323612382304246147)
      ·
        refine ⟨438214126985418573456369221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292142751323612382304246147 438214126985418573456369221)
        ·
          refine ⟨82165148809765982523069229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 438214126985418573456369221 82165148809765982523069229)
          ·
            refine ⟨30811930803662243446150961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82165148809765982523069229 30811930803662243446150961)
            ·
              refine ⟨23108948102746682584613221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30811930803662243446150961 23108948102746682584613221)
              ·
                refine ⟨4332927769265002984614979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23108948102746682584613221 4332927769265002984614979)
                ·
                  refine ⟨6499391653897504476922469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4332927769265002984614979 6499391653897504476922469)
                  ·
                    refine ⟨1218635935105782089422963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6499391653897504476922469 1218635935105782089422963)
                    ·
                      rfl

theorem cell23_7119855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 1, 4].length) (baseStart_7119855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119855 prefixEnd_7119855 := by exact prefixLift 7119855
  have htrace : WordTrace (prefixWord ++ tailWord_7119855) baseStart_7119855 baseEnd_7119855 := by
    simpa [prefixWord, tailWord_7119855, baseEnd_7119855] using wordTrace_append hprefix tailTrace_7119855
  have hstable : (prefixWord ++ tailWord_7119855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119855).length < 2 ^ (prefixWord ++ tailWord_7119855).sum := by decide
  have hdescent : baseEnd_7119855 < baseStart_7119855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119881 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 3, 5]
def baseStart_7119881 : Nat := 118140960795 + 7119881 * 2 ^ 59
def prefixEnd_7119881 : Nat := 4983230072969 + 3 ^ 40 * 7119881 * 2
def baseEnd_7119881 : Nat := 1218640385271454388847923

theorem tailTrace_7119881 : CollatzResearch.WordTrace tailWord_7119881 prefixEnd_7119881 1218640385271454388847923 := by
  unfold tailWord_7119881
  simp only [CollatzResearch.WordTrace]
  refine ⟨259683393918894590710887497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173122262612596393807258331 259683393918894590710887497)
  ·
    refine ⟨194762545439170943033165623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259683393918894590710887497 194762545439170943033165623)
    ·
      refine ⟨292143818158756414549748435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194762545439170943033165623 292143818158756414549748435)
      ·
        refine ⟨438215727238134621824622653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292143818158756414549748435 438215727238134621824622653)
        ·
          refine ⟨164330897714300483184233495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438215727238134621824622653 164330897714300483184233495)
          ·
            refine ⟨246496346571450724776350243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164330897714300483184233495 246496346571450724776350243)
            ·
              refine ⟨369744519857176087164525365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246496346571450724776350243 369744519857176087164525365)
              ·
                refine ⟨34663548736610258171674253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 369744519857176087164525365 34663548736610258171674253)
                ·
                  refine ⟨12998830776228846814377845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34663548736610258171674253 12998830776228846814377845)
                  ·
                    refine ⟨1218640385271454388847923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12998830776228846814377845 1218640385271454388847923)
                    ·
                      rfl

theorem cell23_7119881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 5].length) (baseStart_7119881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119881 prefixEnd_7119881 := by exact prefixLift 7119881
  have htrace : WordTrace (prefixWord ++ tailWord_7119881) baseStart_7119881 baseEnd_7119881 := by
    simpa [prefixWord, tailWord_7119881, baseEnd_7119881] using wordTrace_append hprefix tailTrace_7119881
  have hstable : (prefixWord ++ tailWord_7119881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119881).length < 2 ^ (prefixWord ++ tailWord_7119881).sum := by decide
  have hdescent : baseEnd_7119881 < baseStart_7119881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119898 : List Nat := [3, 1, 1, 3, 1, 2, 1, 5, 1, 5]
def baseStart_7119898 : Nat := 118140960795 + 7119898 * 2 ^ 59
def prefixEnd_7119898 : Nat := 4983230072969 + 3 ^ 40 * 7119898 * 2
def baseEnd_7119898 : Nat := 1218643294995163200010397

theorem tailTrace_7119898 : CollatzResearch.WordTrace tailWord_7119898 prefixEnd_7119898 1218643294995163200010397 := by
  unfold tailWord_7119898
  simp only [CollatzResearch.WordTrace]
  refine ⟨64921003489958250653564087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173122675973222001742837565 64921003489958250653564087)
  ·
    refine ⟨97381505234937375980346131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64921003489958250653564087 97381505234937375980346131)
    ·
      refine ⟨146072257852406063970519197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97381505234937375980346131 146072257852406063970519197)
      ·
        refine ⟨54777096694652273988944699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146072257852406063970519197 54777096694652273988944699)
        ·
          refine ⟨82165645041978410983417049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54777096694652273988944699 82165645041978410983417049)
          ·
            refine ⟨61624233781483808237562787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82165645041978410983417049 61624233781483808237562787)
            ·
              refine ⟨92436350672225712356344181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61624233781483808237562787 92436350672225712356344181)
              ·
                refine ⟨8665907875521160533407267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92436350672225712356344181 8665907875521160533407267)
                ·
                  refine ⟨12998861813281740800110901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8665907875521160533407267 12998861813281740800110901)
                  ·
                    refine ⟨1218643294995163200010397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12998861813281740800110901 1218643294995163200010397)
                    ·
                      rfl

theorem cell23_7119898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_7119898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119898 prefixEnd_7119898 := by exact prefixLift 7119898
  have htrace : WordTrace (prefixWord ++ tailWord_7119898) baseStart_7119898 baseEnd_7119898 := by
    simpa [prefixWord, tailWord_7119898, baseEnd_7119898] using wordTrace_append hprefix tailTrace_7119898
  have hstable : (prefixWord ++ tailWord_7119898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119898).length < 2 ^ (prefixWord ++ tailWord_7119898).sum := by decide
  have hdescent : baseEnd_7119898 < baseStart_7119898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119905 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 4, 3, 2]
def baseStart_7119905 : Nat := 118140960795 + 7119905 * 2 ^ 59
def prefixEnd_7119905 : Nat := 4983230072969 + 3 ^ 40 * 7119905 * 2
def baseEnd_7119905 : Nat := 3655933479350071072643659

theorem tailTrace_7119905 : CollatzResearch.WordTrace tailWord_7119905 prefixEnd_7119905 3655933479350071072643659 := by
  unfold tailWord_7119905
  simp only [CollatzResearch.WordTrace]
  refine ⟨259684269270807642809761169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173122846180538428539840779 259684269270807642809761169)
  ·
    refine ⟨194763201953105732107320877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259684269270807642809761169 194763201953105732107320877)
    ·
      refine ⟨73036200732414649540245329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194763201953105732107320877 73036200732414649540245329)
      ·
        refine ⟨54777150549310987155183997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73036200732414649540245329 54777150549310987155183997)
        ·
          refine ⟨20541431455991620183193999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54777150549310987155183997 20541431455991620183193999)
          ·
            refine ⟨30812147183987430274790999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20541431455991620183193999 30812147183987430274790999)
            ·
              refine ⟨46218220775981145412186499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30812147183987430274790999 46218220775981145412186499)
              ·
                refine ⟨69327331163971718118279749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46218220775981145412186499 69327331163971718118279749)
                ·
                  refine ⟨12998874593244697147177453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69327331163971718118279749 12998874593244697147177453)
                  ·
                    refine ⟨4874577972466761430191545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12998874593244697147177453 4874577972466761430191545)
                    ·
                      refine ⟨3655933479350071072643659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4874577972466761430191545 3655933479350071072643659)
                      ·
                        rfl

theorem cell23_7119905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_7119905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119905 prefixEnd_7119905 := by exact prefixLift 7119905
  have htrace : WordTrace (prefixWord ++ tailWord_7119905) baseStart_7119905 baseEnd_7119905 := by
    simpa [prefixWord, tailWord_7119905, baseEnd_7119905] using wordTrace_append hprefix tailTrace_7119905
  have hstable : (prefixWord ++ tailWord_7119905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119905).length < 2 ^ (prefixWord ++ tailWord_7119905).sum := by decide
  have hdescent : baseEnd_7119905 < baseStart_7119905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119935 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 5, 2, 2]
def baseStart_7119935 : Nat := 118140960795 + 7119935 * 2 ^ 59
def prefixEnd_7119935 : Nat := 4983230072969 + 3 ^ 40 * 7119935 * 2
def baseEnd_7119935 : Nat := 3655948883769705955268521

theorem tailTrace_7119935 : CollatzResearch.WordTrace tailWord_7119935 prefixEnd_7119935 3655948883769705955268521 := by
  unfold tailWord_7119935
  simp only [CollatzResearch.WordTrace]
  refine ⟨259685363460698957933353259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173123575640465971955568839 259685363460698957933353259)
  ·
    refine ⟨389528045191048436900029889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259685363460698957933353259 389528045191048436900029889)
    ·
      refine ⟨292146033893286327675022417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389528045191048436900029889 292146033893286327675022417)
      ·
        refine ⟨219109525419964745756266813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292146033893286327675022417 219109525419964745756266813)
        ·
          refine ⟨82166072032486779658600055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219109525419964745756266813 82166072032486779658600055)
          ·
            refine ⟨123249108048730169487900083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82166072032486779658600055 123249108048730169487900083)
            ·
              refine ⟨184873662073095254231850125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123249108048730169487900083 184873662073095254231850125)
              ·
                refine ⟨69327623277410720336943797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184873662073095254231850125 69327623277410720336943797)
                ·
                  refine ⟨6499464682257255031588481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69327623277410720336943797 6499464682257255031588481)
                  ·
                    refine ⟨4874598511692941273691361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6499464682257255031588481 4874598511692941273691361)
                    ·
                      refine ⟨3655948883769705955268521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4874598511692941273691361 3655948883769705955268521)
                      ·
                        rfl

theorem cell23_7119935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 2, 2].length) (baseStart_7119935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119935 prefixEnd_7119935 := by exact prefixLift 7119935
  have htrace : WordTrace (prefixWord ++ tailWord_7119935) baseStart_7119935 baseEnd_7119935 := by
    simpa [prefixWord, tailWord_7119935, baseEnd_7119935] using wordTrace_append hprefix tailTrace_7119935
  have hstable : (prefixWord ++ tailWord_7119935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119935).length < 2 ^ (prefixWord ++ tailWord_7119935).sum := by decide
  have hdescent : baseEnd_7119935 < baseStart_7119935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119941 : List Nat := [1, 3, 1, 1, 1, 3, 4, 9]
def baseStart_7119941 : Nat := 118140960795 + 7119941 * 2 ^ 59
def prefixEnd_7119941 : Nat := 4983230072969 + 3 ^ 40 * 7119941 * 2
def baseEnd_7119941 : Nat := 135405628320504923399759

theorem tailTrace_7119941 : CollatzResearch.WordTrace tailWord_7119941 prefixEnd_7119941 135405628320504923399759 := by
  unfold tailWord_7119941
  simp only [CollatzResearch.WordTrace]
  refine ⟨259685582298677220958071677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173123721532451480638714451 259685582298677220958071677)
  ·
    refine ⟨97382093362003957859276879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259685582298677220958071677 97382093362003957859276879)
    ·
      refine ⟨146073140043005936788915319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97382093362003957859276879 146073140043005936788915319)
      ·
        refine ⟨219109710064508905183372979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146073140043005936788915319 219109710064508905183372979)
        ·
          refine ⟨328664565096763357775059469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219109710064508905183372979 328664565096763357775059469)
          ·
            refine ⟨123249211911286259165647301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328664565096763357775059469 123249211911286259165647301)
            ·
              refine ⟨23109227233366173593558869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123249211911286259165647301 23109227233366173593558869)
              ·
                refine ⟨135405628320504923399759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23109227233366173593558869 135405628320504923399759)
                ·
                  rfl

theorem cell23_7119941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 9].length) (baseStart_7119941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119941 prefixEnd_7119941 := by exact prefixLift 7119941
  have htrace : WordTrace (prefixWord ++ tailWord_7119941) baseStart_7119941 baseEnd_7119941 := by
    simpa [prefixWord, tailWord_7119941, baseEnd_7119941] using wordTrace_append hprefix tailTrace_7119941
  have hstable : (prefixWord ++ tailWord_7119941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119941).length < 2 ^ (prefixWord ++ tailWord_7119941).sum := by decide
  have hdescent : baseEnd_7119941 < baseStart_7119941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119961 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 6]
def baseStart_7119961 : Nat := 118140960795 + 7119961 * 2 ^ 59
def prefixEnd_7119961 : Nat := 4983230072969 + 3 ^ 40 * 7119961 * 2
def baseEnd_7119961 : Nat := 3655962234266722853543401

theorem tailTrace_7119961 : CollatzResearch.WordTrace tailWord_7119961 prefixEnd_7119961 3655962234266722853543401 := by
  unfold tailWord_7119961
  simp only [CollatzResearch.WordTrace]
  refine ⟨259686311758604764373799737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173124207839069842915866491 259686311758604764373799737)
  ·
    refine ⟨194764733818953573280349803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259686311758604764373799737 194764733818953573280349803)
    ·
      refine ⟨292147100728430359920524705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194764733818953573280349803 292147100728430359920524705)
      ·
        refine ⟨219110325546322769940393529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292147100728430359920524705 219110325546322769940393529)
        ·
          refine ⟨164332744159742077455295147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219110325546322769940393529 164332744159742077455295147)
          ·
            refine ⟨246499116239613116182942721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164332744159742077455295147 246499116239613116182942721)
            ·
              refine ⟨184874337179709837137207041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246499116239613116182942721 184874337179709837137207041)
              ·
                refine ⟨138655752884782377852905281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184874337179709837137207041 138655752884782377852905281)
                ·
                  refine ⟨103991814663586783389678961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138655752884782377852905281 103991814663586783389678961)
                  ·
                    refine ⟨77993860997690087542259221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103991814663586783389678961 77993860997690087542259221)
                    ·
                      refine ⟨3655962234266722853543401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77993860997690087542259221 3655962234266722853543401)
                      ·
                        rfl

theorem cell23_7119961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_7119961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119961 prefixEnd_7119961 := by exact prefixLift 7119961
  have htrace : WordTrace (prefixWord ++ tailWord_7119961) baseStart_7119961 baseEnd_7119961 := by
    simpa [prefixWord, tailWord_7119961, baseEnd_7119961] using wordTrace_append hprefix tailTrace_7119961
  have hstable : (prefixWord ++ tailWord_7119961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119961).length < 2 ^ (prefixWord ++ tailWord_7119961).sum := by decide
  have hdescent : baseEnd_7119961 < baseStart_7119961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7119968 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 3]
def baseStart_7119968 : Nat := 118140960795 + 7119968 * 2 ^ 59
def prefixEnd_7119968 : Nat := 4983230072969 + 3 ^ 40 * 7119968 * 2
def baseEnd_7119968 : Nat := 3655965828631304326155869

theorem tailTrace_7119968 : CollatzResearch.WordTrace tailWord_7119968 prefixEnd_7119968 3655965828631304326155869 := by
  unfold tailWord_7119968
  simp only [CollatzResearch.WordTrace]
  refine ⟨129843283534789702284652279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173124378046386269712869705 129843283534789702284652279)
  ·
    refine ⟨194764925302184553426978419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129843283534789702284652279 194764925302184553426978419)
    ·
      refine ⟨292147387953276830140467629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194764925302184553426978419 292147387953276830140467629)
      ·
        refine ⟨109555270482478811302675361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292147387953276830140467629 109555270482478811302675361)
        ·
          refine ⟨82166452861859108477006521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109555270482478811302675361 82166452861859108477006521)
          ·
            refine ⟨61624839646394331357754891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82166452861859108477006521 61624839646394331357754891)
            ·
              refine ⟨92437259469591497036632337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61624839646394331357754891 92437259469591497036632337)
              ·
                refine ⟨69327944602193622777474253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92437259469591497036632337 69327944602193622777474253)
                ·
                  refine ⟨25997979225822608541552845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69327944602193622777474253 25997979225822608541552845)
                  ·
                    refine ⟨9749242209683478203082317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25997979225822608541552845 9749242209683478203082317)
                    ·
                      refine ⟨3655965828631304326155869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9749242209683478203082317 3655965828631304326155869)
                      ·
                        rfl

theorem cell23_7119968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_7119968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7119968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7119968 prefixEnd_7119968 := by exact prefixLift 7119968
  have htrace : WordTrace (prefixWord ++ tailWord_7119968) baseStart_7119968 baseEnd_7119968 := by
    simpa [prefixWord, tailWord_7119968, baseEnd_7119968] using wordTrace_append hprefix tailTrace_7119968
  have hstable : (prefixWord ++ tailWord_7119968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7119968).length < 2 ^ (prefixWord ++ tailWord_7119968).sum := by decide
  have hdescent : baseEnd_7119968 < baseStart_7119968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7119968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120115 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 4]
def baseStart_7120115 : Nat := 118140960795 + 7120115 * 2 ^ 59
def prefixEnd_7120115 : Nat := 4983230072969 + 3 ^ 40 * 7120115 * 2
def baseEnd_7120115 : Nat := 3656041310287515251017693

theorem tailTrace_7120115 : CollatzResearch.WordTrace tailWord_7120115 prefixEnd_7120115 3656041310287515251017693 := by
  unfold tailWord_7120115
  simp only [CollatzResearch.WordTrace]
  refine ⟨259691928600046848674905799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173127952400031232449937199 259691928600046848674905799)
  ·
    refine ⟨389537892900070273012358699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259691928600046848674905799 389537892900070273012358699)
    ·
      refine ⟨584306839350105409518538049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389537892900070273012358699 584306839350105409518538049)
      ·
        refine ⟨438230129512579057138903537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 584306839350105409518538049 438230129512579057138903537)
        ·
          refine ⟨328672597134434292854177653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438230129512579057138903537 328672597134434292854177653)
          ·
            refine ⟨30813055981353214955079155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 328672597134434292854177653 30813055981353214955079155)
            ·
              refine ⟨46219583972029822432618733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30813055981353214955079155 46219583972029822432618733)
              ·
                refine ⟨17332343989511183412232025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46219583972029822432618733 17332343989511183412232025)
                ·
                  refine ⟨12999257992133387559174019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17332343989511183412232025 12999257992133387559174019)
                  ·
                    refine ⟨19498886988200081338761029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12999257992133387559174019 19498886988200081338761029)
                    ·
                      refine ⟨3656041310287515251017693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19498886988200081338761029 3656041310287515251017693)
                      ·
                        rfl

theorem cell23_7120115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_7120115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120115 prefixEnd_7120115 := by exact prefixLift 7120115
  have htrace : WordTrace (prefixWord ++ tailWord_7120115) baseStart_7120115 baseEnd_7120115 := by
    simpa [prefixWord, tailWord_7120115, baseEnd_7120115] using wordTrace_append hprefix tailTrace_7120115
  have hstable : (prefixWord ++ tailWord_7120115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120115).length < 2 ^ (prefixWord ++ tailWord_7120115).sum := by decide
  have hdescent : baseEnd_7120115 < baseStart_7120115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120128 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 6]
def baseStart_7120128 : Nat := 118140960795 + 7120128 * 2 ^ 59
def prefixEnd_7120128 : Nat := 4983230072969 + 3 ^ 40 * 7120128 * 2
def baseEnd_7120128 : Nat := 3656047985536023700155133

theorem tailTrace_7120128 : CollatzResearch.WordTrace tailWord_7120128 prefixEnd_7120128 3656047985536023700155133 := by
  unfold tailWord_7120128
  simp only [CollatzResearch.WordTrace]
  refine ⟨129846201374499875947564519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173128268499333167930086025 129846201374499875947564519)
  ·
    refine ⟨194769302061749813921346779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129846201374499875947564519 194769302061749813921346779)
    ·
      refine ⟨292153953092624720882020169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194769302061749813921346779 292153953092624720882020169)
      ·
        refine ⟨219115464819468540661515127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292153953092624720882020169 219115464819468540661515127)
        ·
          refine ⟨328673197229202810992272691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219115464819468540661515127 328673197229202810992272691)
          ·
            refine ⟨493009795843804216488409037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328673197229202810992272691 493009795843804216488409037)
            ·
              refine ⟨184878673441426581183153389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493009795843804216488409037 184878673441426581183153389)
              ·
                refine ⟨69329502540534967943682521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184878673441426581183153389 69329502540534967943682521)
                ·
                  refine ⟨51997126905401225957761891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69329502540534967943682521 51997126905401225957761891)
                  ·
                    refine ⟨77995690358101838936642837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51997126905401225957761891 77995690358101838936642837)
                    ·
                      refine ⟨3656047985536023700155133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77995690358101838936642837 3656047985536023700155133)
                      ·
                        rfl

theorem cell23_7120128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_7120128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120128 prefixEnd_7120128 := by exact prefixLift 7120128
  have htrace : WordTrace (prefixWord ++ tailWord_7120128) baseStart_7120128 baseEnd_7120128 := by
    simpa [prefixWord, tailWord_7120128, baseEnd_7120128] using wordTrace_append hprefix tailTrace_7120128
  have hstable : (prefixWord ++ tailWord_7120128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120128).length < 2 ^ (prefixWord ++ tailWord_7120128).sum := by decide
  have hdescent : baseEnd_7120128 < baseStart_7120128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120132 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_7120132 : Nat := 118140960795 + 7120132 * 2 ^ 59
def prefixEnd_7120132 : Nat := 4983230072969 + 3 ^ 40 * 7120132 * 2
def baseEnd_7120132 : Nat := 3656050039458641684505115

theorem tailTrace_7120132 : CollatzResearch.WordTrace tailWord_7120132 prefixEnd_7120132 3656050039458641684505115 := by
  unfold tailWord_7120132
  simp only [CollatzResearch.WordTrace]
  refine ⟨129846274320492630289137325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173128365760656840385516433 129846274320492630289137325)
  ·
    refine ⟨48692352870184736358426497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129846274320492630289137325 48692352870184736358426497)
    ·
      refine ⟨36519264652638552268819873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48692352870184736358426497 36519264652638552268819873)
      ·
        refine ⟨27389448489478914201614905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36519264652638552268819873 27389448489478914201614905)
        ·
          refine ⟨20542086367109185651211179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27389448489478914201614905 20542086367109185651211179)
          ·
            refine ⟨30813129550663778476816769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20542086367109185651211179 30813129550663778476816769)
            ·
              refine ⟨23109847162997833857612577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30813129550663778476816769 23109847162997833857612577)
              ·
                refine ⟨17332385372248375393209433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23109847162997833857612577 17332385372248375393209433)
                ·
                  refine ⟨12999289029186281544907075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17332385372248375393209433 12999289029186281544907075)
                  ·
                    refine ⟨19498933543779422317360613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12999289029186281544907075 19498933543779422317360613)
                    ·
                      refine ⟨3656050039458641684505115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19498933543779422317360613 3656050039458641684505115)
                      ·
                        rfl

theorem cell23_7120132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_7120132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120132 prefixEnd_7120132 := by exact prefixLift 7120132
  have htrace : WordTrace (prefixWord ++ tailWord_7120132) baseStart_7120132 baseEnd_7120132 := by
    simpa [prefixWord, tailWord_7120132, baseEnd_7120132] using wordTrace_append hprefix tailTrace_7120132
  have hstable : (prefixWord ++ tailWord_7120132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120132).length < 2 ^ (prefixWord ++ tailWord_7120132).sum := by decide
  have hdescent : baseEnd_7120132 < baseStart_7120132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120192 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 4, 3, 2]
def baseStart_7120192 : Nat := 118140960795 + 7120192 * 2 ^ 59
def prefixEnd_7120192 : Nat := 4983230072969 + 3 ^ 40 * 7120192 * 2
def baseEnd_7120192 : Nat := 3656080848297911449754839

theorem tailTrace_7120192 : CollatzResearch.WordTrace tailWord_7120192 prefixEnd_7120192 3656080848297911449754839 := by
  unfold tailWord_7120192
  simp only [CollatzResearch.WordTrace]
  refine ⟨129847368510383945412729415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173129824680511927216972553 129847368510383945412729415)
  ·
    refine ⟨194771052765575918119094123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129847368510383945412729415 194771052765575918119094123)
    ·
      refine ⟨292156579148363877178641185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194771052765575918119094123 292156579148363877178641185)
      ·
        refine ⟨219117434361272907883980889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292156579148363877178641185 219117434361272907883980889)
        ·
          refine ⟨164338075770954680912985667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219117434361272907883980889 164338075770954680912985667)
          ·
            refine ⟨246507113656432021369478501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164338075770954680912985667 246507113656432021369478501)
            ·
              refine ⟨46220083810581004006777219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246507113656432021369478501 46220083810581004006777219)
              ·
                refine ⟨69330125715871506010165829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46220083810581004006777219 69330125715871506010165829)
                ·
                  refine ⟨12999398571725907376906093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69330125715871506010165829 12999398571725907376906093)
                  ·
                    refine ⟨4874774464397215266339785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12999398571725907376906093 4874774464397215266339785)
                    ·
                      refine ⟨3656080848297911449754839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4874774464397215266339785 3656080848297911449754839)
                      ·
                        rfl

theorem cell23_7120192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 4, 3, 2].length) (baseStart_7120192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120192 prefixEnd_7120192 := by exact prefixLift 7120192
  have htrace : WordTrace (prefixWord ++ tailWord_7120192) baseStart_7120192 baseEnd_7120192 := by
    simpa [prefixWord, tailWord_7120192, baseEnd_7120192] using wordTrace_append hprefix tailTrace_7120192
  have hstable : (prefixWord ++ tailWord_7120192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120192).length < 2 ^ (prefixWord ++ tailWord_7120192).sum := by decide
  have hdescent : baseEnd_7120192 < baseStart_7120192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120199 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 3, 1, 3]
def baseStart_7120199 : Nat := 118140960795 + 7120199 * 2 ^ 59
def prefixEnd_7120199 : Nat := 4983230072969 + 3 ^ 40 * 7120199 * 2
def baseEnd_7120199 : Nat := 3656084442662492922367307

theorem tailTrace_7120199 : CollatzResearch.WordTrace tailWord_7120199 prefixEnd_7120199 3656084442662492922367307 := by
  unfold tailWord_7120199
  simp only [CollatzResearch.WordTrace]
  refine ⟨259694992331742531020963651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173129994887828354013975767 259694992331742531020963651)
  ·
    refine ⟨389542488497613796531445477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259694992331742531020963651 389542488497613796531445477)
    ·
      refine ⟨73039216593302586849646027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389542488497613796531445477 73039216593302586849646027)
      ·
        refine ⟨109558824889953880274469041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73039216593302586849646027 109558824889953880274469041)
        ·
          refine ⟨82169118667465410205851781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109558824889953880274469041 82169118667465410205851781)
          ·
            refine ⟨15406709750149764413597209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82169118667465410205851781 15406709750149764413597209)
            ·
              refine ⟨11555032312612323310197907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15406709750149764413597209 11555032312612323310197907)
              ·
                refine ⟨17332548468918484965296861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11555032312612323310197907 17332548468918484965296861)
                ·
                  refine ⟨6499705675844431861986323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17332548468918484965296861 6499705675844431861986323)
                  ·
                    refine ⟨9749558513766647792979485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6499705675844431861986323 9749558513766647792979485)
                    ·
                      refine ⟨3656084442662492922367307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9749558513766647792979485 3656084442662492922367307)
                      ·
                        rfl

theorem cell23_7120199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_7120199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120199 prefixEnd_7120199 := by exact prefixLift 7120199
  have htrace : WordTrace (prefixWord ++ tailWord_7120199) baseStart_7120199 baseEnd_7120199 := by
    simpa [prefixWord, tailWord_7120199, baseEnd_7120199] using wordTrace_append hprefix tailTrace_7120199
  have hstable : (prefixWord ++ tailWord_7120199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120199).length < 2 ^ (prefixWord ++ tailWord_7120199).sum := by decide
  have hdescent : baseEnd_7120199 < baseStart_7120199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120225 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_7120225 : Nat := 118140960795 + 7120225 * 2 ^ 59
def prefixEnd_7120225 : Nat := 4983230072969 + 3 ^ 40 * 7120225 * 2
def baseEnd_7120225 : Nat := 3656097793159509820642187

theorem tailTrace_7120225 : CollatzResearch.WordTrace tailWord_7120225 prefixEnd_7120225 3656097793159509820642187 := by
  unfold tailWord_7120225
  simp only [CollatzResearch.WordTrace]
  refine ⟨259695940629648337461410129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173130627086432224974273419 259695940629648337461410129)
  ·
    refine ⟨194771955472236253096057597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259695940629648337461410129 194771955472236253096057597)
    ·
      refine ⟨73039483302088594911021599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194771955472236253096057597 73039483302088594911021599)
      ·
        refine ⟨109559224953132892366532399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73039483302088594911021599 109559224953132892366532399)
        ·
          refine ⟨164338837429699338549798599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109559224953132892366532399 164338837429699338549798599)
          ·
            refine ⟨246508256144549007824697899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164338837429699338549798599 246508256144549007824697899)
            ·
              refine ⟨369762384216823511737046849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246508256144549007824697899 369762384216823511737046849)
              ·
                refine ⟨277321788162617633802785137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369762384216823511737046849 277321788162617633802785137)
                ·
                  refine ⟨207991341121963225352088853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277321788162617633802785137 207991341121963225352088853)
                  ·
                    refine ⟨9749594115092026188379165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 207991341121963225352088853 9749594115092026188379165)
                    ·
                      refine ⟨3656097793159509820642187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9749594115092026188379165 3656097793159509820642187)
                      ·
                        rfl

theorem cell23_7120225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_7120225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120225 prefixEnd_7120225 := by exact prefixLift 7120225
  have htrace : WordTrace (prefixWord ++ tailWord_7120225) baseStart_7120225 baseEnd_7120225 := by
    simpa [prefixWord, tailWord_7120225, baseEnd_7120225] using wordTrace_append hprefix tailTrace_7120225
  have hstable : (prefixWord ++ tailWord_7120225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120225).length < 2 ^ (prefixWord ++ tailWord_7120225).sum := by decide
  have hdescent : baseEnd_7120225 < baseStart_7120225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120242 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_7120242 : Nat := 118140960795 + 7120242 * 2 ^ 59
def prefixEnd_7120242 : Nat := 4983230072969 + 3 ^ 40 * 7120242 * 2
def baseEnd_7120242 : Nat := 3656106522330636254129609

theorem tailTrace_7120242 : CollatzResearch.WordTrace tailWord_7120242 prefixEnd_7120242 3656106522330636254129609 := by
  unfold tailWord_7120242
  simp only [CollatzResearch.WordTrace]
  refine ⟨64924140167646687341194745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173131040447057832909852653 64924140167646687341194745)
  ·
    refine ⟨48693105125735015505896059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64924140167646687341194745 48693105125735015505896059)
    ·
      refine ⟨73039657688602523258844089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48693105125735015505896059 73039657688602523258844089)
      ·
        refine ⟨54779743266451892444133067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73039657688602523258844089 54779743266451892444133067)
        ·
          refine ⟨82169614899677838666199601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54779743266451892444133067 82169614899677838666199601)
          ·
            refine ⟨61627211174758378999649701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82169614899677838666199601 61627211174758378999649701)
            ·
              refine ⟨11555102095267196062434319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61627211174758378999649701 11555102095267196062434319)
              ·
                refine ⟨17332653142900794093651479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11555102095267196062434319 17332653142900794093651479)
                ·
                  refine ⟨25998979714351191140477219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17332653142900794093651479 25998979714351191140477219)
                  ·
                    refine ⟨38998469571526786710715829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25998979714351191140477219 38998469571526786710715829)
                    ·
                      refine ⟨3656106522330636254129609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38998469571526786710715829 3656106522330636254129609)
                      ·
                        rfl

theorem cell23_7120242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_7120242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120242 prefixEnd_7120242 := by exact prefixLift 7120242
  have htrace : WordTrace (prefixWord ++ tailWord_7120242) baseStart_7120242 baseEnd_7120242 := by
    simpa [prefixWord, tailWord_7120242, baseEnd_7120242] using wordTrace_append hprefix tailTrace_7120242
  have hstable : (prefixWord ++ tailWord_7120242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120242).length < 2 ^ (prefixWord ++ tailWord_7120242).sum := by decide
  have hdescent : baseEnd_7120242 < baseStart_7120242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120255 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 3]
def baseStart_7120255 : Nat := 118140960795 + 7120255 * 2 ^ 59
def prefixEnd_7120255 : Nat := 4983230072969 + 3 ^ 40 * 7120255 * 2
def baseEnd_7120255 : Nat := 3656113197579144703267049

theorem tailTrace_7120255 : CollatzResearch.WordTrace tailWord_7120255 prefixEnd_7120255 3656113197579144703267049 := by
  unfold tailWord_7120255
  simp only [CollatzResearch.WordTrace]
  refine ⟨259697034819539652585002219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173131356546359768390001479 259697034819539652585002219)
  ·
    refine ⟨389545552229309478877503329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259697034819539652585002219 389545552229309478877503329)
    ·
      refine ⟨292159164171982109158127497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389545552229309478877503329 292159164171982109158127497)
      ·
        refine ⟨219119373128986581868595623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292159164171982109158127497 219119373128986581868595623)
        ·
          refine ⟨328679059693479872802893435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219119373128986581868595623 328679059693479872802893435)
          ·
            refine ⟨493018589540219809204340153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328679059693479872802893435 493018589540219809204340153)
            ·
              refine ⟨369763942155164856903255115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493018589540219809204340153 369763942155164856903255115)
              ·
                refine ⟨554645913232747285354882673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369763942155164856903255115 554645913232747285354882673)
                ·
                  refine ⟨415984434924560464016162005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554645913232747285354882673 415984434924560464016162005)
                  ·
                    refine ⟨9749635193544385875378797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 415984434924560464016162005 9749635193544385875378797)
                    ·
                      refine ⟨3656113197579144703267049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9749635193544385875378797 3656113197579144703267049)
                      ·
                        rfl

theorem cell23_7120255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_7120255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120255 prefixEnd_7120255 := by exact prefixLift 7120255
  have htrace : WordTrace (prefixWord ++ tailWord_7120255) baseStart_7120255 baseEnd_7120255 := by
    simpa [prefixWord, tailWord_7120255, baseEnd_7120255] using wordTrace_append hprefix tailTrace_7120255
  have hstable : (prefixWord ++ tailWord_7120255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120255).length < 2 ^ (prefixWord ++ tailWord_7120255).sum := by decide
  have hdescent : baseEnd_7120255 < baseStart_7120255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120256 : List Nat := [2, 1, 1, 2, 1, 2, 1, 8, 1, 2, 2]
def baseStart_7120256 : Nat := 118140960795 + 7120256 * 2 ^ 59
def prefixEnd_7120256 : Nat := 4983230072969 + 3 ^ 40 * 7120256 * 2
def baseEnd_7120256 : Nat := 3656113711059799199354545

theorem tailTrace_7120256 : CollatzResearch.WordTrace tailWord_7120256 prefixEnd_7120256 3656113711059799199354545 := by
  unfold tailWord_7120256
  simp only [CollatzResearch.WordTrace]
  refine ⟨129848535646268014877894311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173131380861690686503859081 129848535646268014877894311)
  ·
    refine ⟨194772803469402022316841467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129848535646268014877894311 194772803469402022316841467)
    ·
      refine ⟨292159205204103033475262201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194772803469402022316841467 292159205204103033475262201)
      ·
        refine ⟨219119403903077275106446651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292159205204103033475262201 219119403903077275106446651)
        ·
          refine ⟨328679105854615912659669977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219119403903077275106446651 328679105854615912659669977)
          ·
            refine ⟨246509329390961934494752483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328679105854615912659669977 246509329390961934494752483)
            ·
              refine ⟨369763994086442901742128725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246509329390961934494752483 369763994086442901742128725)
              ·
                refine ⟨4333171805700502754790571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 369763994086442901742128725 4333171805700502754790571)
                ·
                  refine ⟨6499757708550754132185857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4333171805700502754790571 6499757708550754132185857)
                  ·
                    refine ⟨4874818281413065599139393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6499757708550754132185857 4874818281413065599139393)
                    ·
                      refine ⟨3656113711059799199354545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4874818281413065599139393 3656113711059799199354545)
                      ·
                        rfl

theorem cell23_7120256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 1, 2, 2].length) (baseStart_7120256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120256 prefixEnd_7120256 := by exact prefixLift 7120256
  have htrace : WordTrace (prefixWord ++ tailWord_7120256) baseStart_7120256 baseEnd_7120256 := by
    simpa [prefixWord, tailWord_7120256, baseEnd_7120256] using wordTrace_append hprefix tailTrace_7120256
  have hstable : (prefixWord ++ tailWord_7120256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120256).length < 2 ^ (prefixWord ++ tailWord_7120256).sum := by decide
  have hdescent : baseEnd_7120256 < baseStart_7120256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120276 : List Nat := [2, 4, 2, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_7120276 : Nat := 118140960795 + 7120276 * 2 ^ 59
def prefixEnd_7120276 : Nat := 4983230072969 + 3 ^ 40 * 7120276 * 2
def baseEnd_7120276 : Nat := 3656123980672889121104453

theorem tailTrace_7120276 : CollatzResearch.WordTrace tailWord_7120276 prefixEnd_7120276 3656123980672889121104453 := by
  unfold tailWord_7120276
  simp only [CollatzResearch.WordTrace]
  refine ⟨129848900376231786585758341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173131867168309048781011121 129848900376231786585758341)
  ·
    refine ⟨24346668820543459984829689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129848900376231786585758341 24346668820543459984829689)
    ·
      refine ⟨18260001615407594988622267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24346668820543459984829689 18260001615407594988622267)
      ·
        refine ⟨27390002423111392482933401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18260001615407594988622267 27390002423111392482933401)
        ·
          refine ⟨20542501817333544362200051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27390002423111392482933401 20542501817333544362200051)
          ·
            refine ⟨30813752726000316543300077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20542501817333544362200051 30813752726000316543300077)
            ·
              refine ⟨11555157272250118703737529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30813752726000316543300077 11555157272250118703737529)
              ·
                refine ⟨8666367954187589027803147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11555157272250118703737529 8666367954187589027803147)
                ·
                  refine ⟨12999551931281383541704721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8666367954187589027803147 12999551931281383541704721)
                  ·
                    refine ⟨9749663948461037656278541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12999551931281383541704721 9749663948461037656278541)
                    ·
                      refine ⟨3656123980672889121104453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9749663948461037656278541 3656123980672889121104453)
                      ·
                        rfl

theorem cell23_7120276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_7120276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120276 prefixEnd_7120276 := by exact prefixLift 7120276
  have htrace : WordTrace (prefixWord ++ tailWord_7120276) baseStart_7120276 baseEnd_7120276 := by
    simpa [prefixWord, tailWord_7120276, baseEnd_7120276] using wordTrace_append hprefix tailTrace_7120276
  have hstable : (prefixWord ++ tailWord_7120276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120276).length < 2 ^ (prefixWord ++ tailWord_7120276).sum := by decide
  have hdescent : baseEnd_7120276 < baseStart_7120276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120286 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_7120286 : Nat := 118140960795 + 7120286 * 2 ^ 59
def prefixEnd_7120286 : Nat := 4983230072969 + 3 ^ 40 * 7120286 * 2
def baseEnd_7120286 : Nat := 3656129115479434081979407

theorem tailTrace_7120286 : CollatzResearch.WordTrace tailWord_7120286 prefixEnd_7120286 3656129115479434081979407 := by
  unfold tailWord_7120286
  simp only [CollatzResearch.WordTrace]
  refine ⟨32462270685303418109922589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173132110321618229919587141 32462270685303418109922589)
  ·
    refine ⟨12173351506988781791220971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32462270685303418109922589 12173351506988781791220971)
    ·
      refine ⟨18260027260483172686831457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12173351506988781791220971 18260027260483172686831457)
      ·
        refine ⟨13695020445362379515123593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18260027260483172686831457 13695020445362379515123593)
        ·
          refine ⟨10271265334021784636342695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13695020445362379515123593 10271265334021784636342695)
          ·
            refine ⟨15406898001032676954514043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10271265334021784636342695 15406898001032676954514043)
            ·
              refine ⟨23110347001549015431771065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15406898001032676954514043 23110347001549015431771065)
              ·
                refine ⟨17332760251161761573828299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23110347001549015431771065 17332760251161761573828299)
                ·
                  refine ⟨25999140376742642360742449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17332760251161761573828299 25999140376742642360742449)
                  ·
                    refine ⟨19499355282556981770556837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25999140376742642360742449 19499355282556981770556837)
                    ·
                      refine ⟨3656129115479434081979407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19499355282556981770556837 3656129115479434081979407)
                      ·
                        rfl

theorem cell23_7120286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_7120286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120286 prefixEnd_7120286 := by exact prefixLift 7120286
  have htrace : WordTrace (prefixWord ++ tailWord_7120286) baseStart_7120286 baseEnd_7120286 := by
    simpa [prefixWord, tailWord_7120286, baseEnd_7120286] using wordTrace_append hprefix tailTrace_7120286
  have hstable : (prefixWord ++ tailWord_7120286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120286).length < 2 ^ (prefixWord ++ tailWord_7120286).sum := by decide
  have hdescent : baseEnd_7120286 < baseStart_7120286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120329 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 6, 2, 2]
def baseStart_7120329 : Nat := 118140960795 + 7120329 * 2 ^ 59
def prefixEnd_7120329 : Nat := 4983230072969 + 3 ^ 40 * 7120329 * 2
def baseEnd_7120329 : Nat := 3656151195147577413741709

theorem tailTrace_7120329 : CollatzResearch.WordTrace tailWord_7120329 prefixEnd_7120329 3656151195147577413741709 := by
  unfold tailWord_7120329
  simp only [CollatzResearch.WordTrace]
  refine ⟨259699733821271563223196041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173133155880847708815464027 259699733821271563223196041)
  ·
    refine ⟨194774800365953672417397031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259699733821271563223196041 194774800365953672417397031)
    ·
      refine ⟨292162200548930508626095547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194774800365953672417397031 292162200548930508626095547)
      ·
        refine ⟨438243300823395762939143321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292162200548930508626095547 438243300823395762939143321)
        ·
          refine ⟨328682475617546822204357491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438243300823395762939143321 328682475617546822204357491)
          ·
            refine ⟨493023713426320233306536237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328682475617546822204357491 493023713426320233306536237)
            ·
              refine ⟨184883892534870087489951089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 493023713426320233306536237 184883892534870087489951089)
              ·
                refine ⟨138662919401152565617463317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184883892534870087489951089 138662919401152565617463317)
                ·
                  refine ⟨6499824346929026513318593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138662919401152565617463317 6499824346929026513318593)
                  ·
                    refine ⟨4874868260196769884988945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6499824346929026513318593 4874868260196769884988945)
                    ·
                      refine ⟨3656151195147577413741709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4874868260196769884988945 3656151195147577413741709)
                      ·
                        rfl

theorem cell23_7120329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 2, 2].length) (baseStart_7120329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120329 prefixEnd_7120329 := by exact prefixLift 7120329
  have htrace : WordTrace (prefixWord ++ tailWord_7120329) baseStart_7120329 baseEnd_7120329 := by
    simpa [prefixWord, tailWord_7120329, baseEnd_7120329] using wordTrace_append hprefix tailTrace_7120329
  have hstable : (prefixWord ++ tailWord_7120329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120329).length < 2 ^ (prefixWord ++ tailWord_7120329).sum := by decide
  have hdescent : baseEnd_7120329 < baseStart_7120329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120335 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 9]
def baseStart_7120335 : Nat := 118140960795 + 7120335 * 2 ^ 59
def prefixEnd_7120335 : Nat := 4983230072969 + 3 ^ 40 * 7120335 * 2
def baseEnd_7120335 : Nat := 406239364003500487807409

theorem tailTrace_7120335 : CollatzResearch.WordTrace tailWord_7120335 prefixEnd_7120335 406239364003500487807409 := by
  unfold tailWord_7120335
  simp only [CollatzResearch.WordTrace]
  refine ⟨259699952659249826247914459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173133301772833217498609639 259699952659249826247914459)
  ·
    refine ⟨389549928988874739371871689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259699952659249826247914459 389549928988874739371871689)
    ·
      refine ⟨292162446741656054528903767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389549928988874739371871689 292162446741656054528903767)
      ·
        refine ⟨438243670112484081793355651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292162446741656054528903767 438243670112484081793355651)
        ·
          refine ⟨657365505168726122690033477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438243670112484081793355651 657365505168726122690033477)
          ·
            refine ⟨123256032219136148004381277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 657365505168726122690033477 123256032219136148004381277)
            ·
              refine ⟨46221012082176055501642979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123256032219136148004381277 46221012082176055501642979)
              ·
                refine ⟨69331518123264083252464469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46221012082176055501642979 69331518123264083252464469)
                ·
                  refine ⟨406239364003500487807409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69331518123264083252464469 406239364003500487807409)
                  ·
                    rfl

theorem cell23_7120335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 9].length) (baseStart_7120335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120335 prefixEnd_7120335 := by exact prefixLift 7120335
  have htrace : WordTrace (prefixWord ++ tailWord_7120335) baseStart_7120335 baseEnd_7120335 := by
    simpa [prefixWord, tailWord_7120335, baseEnd_7120335] using wordTrace_append hprefix tailTrace_7120335
  have hstable : (prefixWord ++ tailWord_7120335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120335).length < 2 ^ (prefixWord ++ tailWord_7120335).sum := by decide
  have hdescent : baseEnd_7120335 < baseStart_7120335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120369 : List Nat := [1, 2, 2, 2, 3, 2, 2, 4, 5]
def baseStart_7120369 : Nat := 118140960795 + 7120369 * 2 ^ 59
def prefixEnd_7120369 : Nat := 4983230072969 + 3 ^ 40 * 7120369 * 2
def baseEnd_7120369 : Nat := 406241303819306361915725

theorem tailTrace_7120369 : CollatzResearch.WordTrace tailWord_7120369 prefixEnd_7120369 406241303819306361915725 := by
  unfold tailWord_7120369
  simp only [CollatzResearch.WordTrace]
  refine ⟨259701192741126650054652161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173134128494084433369768107 259701192741126650054652161)
  ·
    refine ⟨194775894555844987540989121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259701192741126650054652161 194775894555844987540989121)
    ·
      refine ⟨146081920916883740655741841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194775894555844987540989121 146081920916883740655741841)
      ·
        refine ⟨109561440687662805491806381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146081920916883740655741841 109561440687662805491806381)
        ·
          refine ⟨41085540257873552059427393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109561440687662805491806381 41085540257873552059427393)
          ·
            refine ⟨30814155193405164044570545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41085540257873552059427393 30814155193405164044570545)
            ·
              refine ⟨23110616395053873033427909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30814155193405164044570545 23110616395053873033427909)
              ·
                refine ⟨4333240574072601193767733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23110616395053873033427909 4333240574072601193767733)
                ·
                  refine ⟨406241303819306361915725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4333240574072601193767733 406241303819306361915725)
                  ·
                    rfl

theorem cell23_7120369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 5].length) (baseStart_7120369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120369 prefixEnd_7120369 := by exact prefixLift 7120369
  have htrace : WordTrace (prefixWord ++ tailWord_7120369) baseStart_7120369 baseEnd_7120369 := by
    simpa [prefixWord, tailWord_7120369, baseEnd_7120369] using wordTrace_append hprefix tailTrace_7120369
  have hstable : (prefixWord ++ tailWord_7120369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120369).length < 2 ^ (prefixWord ++ tailWord_7120369).sum := by decide
  have hdescent : baseEnd_7120369 < baseStart_7120369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120462 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_7120462 : Nat := 118140960795 + 7120462 * 2 ^ 59
def prefixEnd_7120462 : Nat := 4983230072969 + 3 ^ 40 * 7120462 * 2
def baseEnd_7120462 : Nat := 3656219488074625393378597

theorem tailTrace_7120462 : CollatzResearch.WordTrace tailWord_7120462 prefixEnd_7120462 3656219488074625393378597 := by
  unfold tailWord_7120462
  simp only [CollatzResearch.WordTrace]
  refine ⟨32463073091223715867223455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 173136389819859817958525093 32463073091223715867223455)
  ·
    refine ⟨48694609636835573800835183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32463073091223715867223455 48694609636835573800835183)
    ·
      refine ⟨73041914455253360701252775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48694609636835573800835183 73041914455253360701252775)
      ·
        refine ⟨109562871682880041051879163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73041914455253360701252775 109562871682880041051879163)
        ·
          refine ⟨164344307524320061577818745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109562871682880041051879163 164344307524320061577818745)
          ·
            refine ⟨123258230643240046183364059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164344307524320061577818745 123258230643240046183364059)
            ·
              refine ⟨184887345964860069275046089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123258230643240046183364059 184887345964860069275046089)
              ·
                refine ⟨138665509473645051956284567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184887345964860069275046089 138665509473645051956284567)
                ·
                  refine ⟨207998264210467577934426851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138665509473645051956284567 207998264210467577934426851)
                  ·
                    refine ⟨311997396315701366901640277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 207998264210467577934426851 311997396315701366901640277)
                    ·
                      refine ⟨3656219488074625393378597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 311997396315701366901640277 3656219488074625393378597)
                      ·
                        rfl

theorem cell23_7120462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_7120462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120462 prefixEnd_7120462 := by exact prefixLift 7120462
  have htrace : WordTrace (prefixWord ++ tailWord_7120462) baseStart_7120462 baseEnd_7120462 := by
    simpa [prefixWord, tailWord_7120462, baseEnd_7120462] using wordTrace_append hprefix tailTrace_7120462
  have hstable : (prefixWord ++ tailWord_7120462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120462).length < 2 ^ (prefixWord ++ tailWord_7120462).sum := by decide
  have hdescent : baseEnd_7120462 < baseStart_7120462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120476 : List Nat := [2, 2, 4, 1, 2, 2, 2, 2, 6]
def baseStart_7120476 : Nat := 118140960795 + 7120476 * 2 ^ 59
def prefixEnd_7120476 : Nat := 4983230072969 + 3 ^ 40 * 7120476 * 2
def baseEnd_7120476 : Nat := 406247408533754259844837

theorem tailTrace_7120476 : CollatzResearch.WordTrace tailWord_7120476 prefixEnd_7120476 406247408533754259844837 := by
  unfold tailWord_7120476
  simp only [CollatzResearch.WordTrace]
  refine ⟨129852547675869503664398641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173136730234492671552531521 129852547675869503664398641)
  ·
    refine ⟨97389410756902127748298981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129852547675869503664398641 97389410756902127748298981)
    ·
      refine ⟨18260514516919148952806059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97389410756902127748298981 18260514516919148952806059)
      ·
        refine ⟨27390771775378723429209089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18260514516919148952806059 27390771775378723429209089)
        ·
          refine ⟨20543078831534042571906817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27390771775378723429209089 20543078831534042571906817)
          ·
            refine ⟨15407309123650531928930113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20543078831534042571906817 15407309123650531928930113)
            ·
              refine ⟨11555481842737898946697585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15407309123650531928930113 11555481842737898946697585)
              ·
                refine ⟨8666611382053424210023189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11555481842737898946697585 8666611382053424210023189)
                ·
                  refine ⟨406247408533754259844837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8666611382053424210023189 406247408533754259844837)
                  ·
                    rfl

theorem cell23_7120476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 6].length) (baseStart_7120476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120476 prefixEnd_7120476 := by exact prefixLift 7120476
  have htrace : WordTrace (prefixWord ++ tailWord_7120476) baseStart_7120476 baseEnd_7120476 := by
    simpa [prefixWord, tailWord_7120476, baseEnd_7120476] using wordTrace_append hprefix tailTrace_7120476
  have hstable : (prefixWord ++ tailWord_7120476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120476).length < 2 ^ (prefixWord ++ tailWord_7120476).sum := by decide
  have hdescent : baseEnd_7120476 < baseStart_7120476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120479 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 5, 5, 2]
def baseStart_7120479 : Nat := 118140960795 + 7120479 * 2 ^ 59
def prefixEnd_7120479 : Nat := 4983230072969 + 3 ^ 40 * 7120479 * 2
def baseEnd_7120479 : Nat := 3656228217245751826866019

theorem tailTrace_7120479 : CollatzResearch.WordTrace tailWord_7120479 prefixEnd_7120479 3656228217245751826866019 := by
  unfold tailWord_7120479
  simp only [CollatzResearch.WordTrace]
  refine ⟨259705204770728138841156491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173136803180485425894104327 259705204770728138841156491)
  ·
    refine ⟨389557807156092208261734737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259705204770728138841156491 389557807156092208261734737)
    ·
      refine ⟨292168355367069156196301053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 389557807156092208261734737 292168355367069156196301053)
      ·
        refine ⟨109563133262650933573612895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 292168355367069156196301053 109563133262650933573612895)
        ·
          refine ⟨164344699893976400360419343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109563133262650933573612895 164344699893976400360419343)
          ·
            refine ⟨246517049840964600540629015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164344699893976400360419343 246517049840964600540629015)
            ·
              refine ⟨369775574761446900810943523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246517049840964600540629015 369775574761446900810943523)
              ·
                refine ⟨554663362142170351216415285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369775574761446900810943523 554663362142170351216415285)
                ·
                  refine ⟨51999690200828470426538933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 554663362142170351216415285 51999690200828470426538933)
                  ·
                    refine ⟨4874970956327669102488025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51999690200828470426538933 4874970956327669102488025)
                    ·
                      refine ⟨3656228217245751826866019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4874970956327669102488025 3656228217245751826866019)
                      ·
                        rfl

theorem cell23_7120479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_7120479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120479 prefixEnd_7120479 := by exact prefixLift 7120479
  have htrace : WordTrace (prefixWord ++ tailWord_7120479) baseStart_7120479 baseEnd_7120479 := by
    simpa [prefixWord, tailWord_7120479, baseEnd_7120479] using wordTrace_append hprefix tailTrace_7120479
  have hstable : (prefixWord ++ tailWord_7120479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120479).length < 2 ^ (prefixWord ++ tailWord_7120479).sum := by decide
  have hdescent : baseEnd_7120479 < baseStart_7120479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120513 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_7120513 : Nat := 118140960795 + 7120513 * 2 ^ 59
def prefixEnd_7120513 : Nat := 4983230072969 + 3 ^ 40 * 7120513 * 2
def baseEnd_7120513 : Nat := 3656245675588004693840863

theorem tailTrace_7120513 : CollatzResearch.WordTrace tailWord_7120513 prefixEnd_7120513 3656245675588004693840863 := by
  unfold tailWord_7120513
  simp only [CollatzResearch.WordTrace]
  refine ⟨259706444852604962647894193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173137629901736641765262795 259706444852604962647894193)
  ·
    refine ⟨194779833639453721985920645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259706444852604962647894193 194779833639453721985920645)
    ·
      refine ⟨36521218807397572872360121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194779833639453721985920645 36521218807397572872360121)
      ·
        refine ⟨27390914105548179654270091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36521218807397572872360121 27390914105548179654270091)
        ·
          refine ⟨41086371158322269481405137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27390914105548179654270091 41086371158322269481405137)
          ·
            refine ⟨30814778368741702111053853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41086371158322269481405137 30814778368741702111053853)
            ·
              refine ⟨11555541888278138291645195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30814778368741702111053853 11555541888278138291645195)
              ·
                refine ⟨17333312832417207437467793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11555541888278138291645195 17333312832417207437467793)
                ·
                  refine ⟨12999984624312905578100845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17333312832417207437467793 12999984624312905578100845)
                  ·
                    refine ⟨4874994234117339591787817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12999984624312905578100845 4874994234117339591787817)
                    ·
                      refine ⟨3656245675588004693840863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4874994234117339591787817 3656245675588004693840863)
                      ·
                        rfl

theorem cell23_7120513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_7120513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120513 prefixEnd_7120513 := by exact prefixLift 7120513
  have htrace : WordTrace (prefixWord ++ tailWord_7120513) baseStart_7120513 baseEnd_7120513 := by
    simpa [prefixWord, tailWord_7120513, baseEnd_7120513] using wordTrace_append hprefix tailTrace_7120513
  have hstable : (prefixWord ++ tailWord_7120513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120513).length < 2 ^ (prefixWord ++ tailWord_7120513).sum := by decide
  have hdescent : baseEnd_7120513 < baseStart_7120513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120519 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 1, 6]
def baseStart_7120519 : Nat := 118140960795 + 7120519 * 2 ^ 59
def prefixEnd_7120519 : Nat := 4983230072969 + 3 ^ 40 * 7120519 * 2
def baseEnd_7120519 : Nat := 1218749585490643890121945

theorem tailTrace_7120519 : CollatzResearch.WordTrace tailWord_7120519 prefixEnd_7120519 1218749585490643890121945 := by
  unfold tailWord_7120519
  simp only [CollatzResearch.WordTrace]
  refine ⟨259706663690583225672612611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173137775793722150448408407 259706663690583225672612611)
  ·
    refine ⟨389559995535874838508918917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259706663690583225672612611 389559995535874838508918917)
    ·
      refine ⟨73042499162976532220422297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389559995535874838508918917 73042499162976532220422297)
      ·
        refine ⟨54781874372232399165316723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73042499162976532220422297 54781874372232399165316723)
        ·
          refine ⟨82172811558348598747975085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54781874372232399165316723 82172811558348598747975085)
          ·
            refine ⟨30814804334380724530490657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82172811558348598747975085 30814804334380724530490657)
            ·
              refine ⟨23111103250785543397867993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30814804334380724530490657 23111103250785543397867993)
              ·
                refine ⟨17333327438089157548400995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23111103250785543397867993 17333327438089157548400995)
                ·
                  refine ⟨25999991157133736322601493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17333327438089157548400995 25999991157133736322601493)
                  ·
                    refine ⟨1218749585490643890121945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25999991157133736322601493 1218749585490643890121945)
                    ·
                      rfl

theorem cell23_7120519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_7120519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120519 prefixEnd_7120519 := by exact prefixLift 7120519
  have htrace : WordTrace (prefixWord ++ tailWord_7120519) baseStart_7120519 baseEnd_7120519 := by
    simpa [prefixWord, tailWord_7120519, baseEnd_7120519] using wordTrace_append hprefix tailTrace_7120519
  have hstable : (prefixWord ++ tailWord_7120519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120519).length < 2 ^ (prefixWord ++ tailWord_7120519).sum := by decide
  have hdescent : baseEnd_7120519 < baseStart_7120519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120529 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 3]
def baseStart_7120529 : Nat := 118140960795 + 7120529 * 2 ^ 59
def prefixEnd_7120529 : Nat := 4983230072969 + 3 ^ 40 * 7120529 * 2
def baseEnd_7120529 : Nat := 3656253891278476631240789

theorem tailTrace_7120529 : CollatzResearch.WordTrace tailWord_7120529 prefixEnd_7120529 3656253891278476631240789 := by
  unfold tailWord_7120529
  simp only [CollatzResearch.WordTrace]
  refine ⟨259707028420546997380476641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173138018947031331586984427 259707028420546997380476641)
  ·
    refine ⟨194780271315410248035357481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259707028420546997380476641 194780271315410248035357481)
    ·
      refine ⟨146085203486557686026518111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194780271315410248035357481 146085203486557686026518111)
      ·
        refine ⟨219127805229836529039777167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146085203486557686026518111 219127805229836529039777167)
        ·
          refine ⟨328691707844754793559665751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219127805229836529039777167 328691707844754793559665751)
          ·
            refine ⟨493037561767132190339498627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328691707844754793559665751 493037561767132190339498627)
            ·
              refine ⟨739556342650698285509247941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 493037561767132190339498627 739556342650698285509247941)
              ·
                refine ⟨138666814247005928532983989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 739556342650698285509247941 138666814247005928532983989)
                ·
                  refine ⟨13000013835656805799967249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138666814247005928532983989 13000013835656805799967249)
                  ·
                    refine ⟨9750010376742604349975437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13000013835656805799967249 9750010376742604349975437)
                    ·
                      refine ⟨3656253891278476631240789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9750010376742604349975437 3656253891278476631240789)
                      ·
                        rfl

theorem cell23_7120529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_7120529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120529 prefixEnd_7120529 := by exact prefixLift 7120529
  have htrace : WordTrace (prefixWord ++ tailWord_7120529) baseStart_7120529 baseEnd_7120529 := by
    simpa [prefixWord, tailWord_7120529, baseEnd_7120529] using wordTrace_append hprefix tailTrace_7120529
  have hstable : (prefixWord ++ tailWord_7120529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120529).length < 2 ^ (prefixWord ++ tailWord_7120529).sum := by decide
  have hdescent : baseEnd_7120529 < baseStart_7120529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120536 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 4, 4]
def baseStart_7120536 : Nat := 118140960795 + 7120536 * 2 ^ 59
def prefixEnd_7120536 : Nat := 4983230072969 + 3 ^ 40 * 7120536 * 2
def baseEnd_7120536 : Nat := 1218752495214352701284419

theorem tailTrace_7120536 : CollatzResearch.WordTrace tailWord_7120536 prefixEnd_7120536 1218752495214352701284419 := by
  unfold tailWord_7120536
  simp only [CollatzResearch.WordTrace]
  refine ⟨129853641865760818787990731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173138189154347758383987641 129853641865760818787990731)
  ·
    refine ⟨194780462798641228181986097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129853641865760818787990731 194780462798641228181986097)
    ·
      refine ⟨146085347098980921136489573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194780462798641228181986097 146085347098980921136489573)
      ·
        refine ⟨27391002581058922713091795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146085347098980921136489573 27391002581058922713091795)
        ·
          refine ⟨41086503871588384069637693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27391002581058922713091795 41086503871588384069637693)
          ·
            refine ⟨15407438951845644026114135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41086503871588384069637693 15407438951845644026114135)
            ·
              refine ⟨23111158427768466039171203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15407438951845644026114135 23111158427768466039171203)
              ·
                refine ⟨34666737641652699058756805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23111158427768466039171203 34666737641652699058756805)
                ·
                  refine ⟨6500013307809881073516901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34666737641652699058756805 6500013307809881073516901)
                  ·
                    refine ⟨1218752495214352701284419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6500013307809881073516901 1218752495214352701284419)
                    ·
                      rfl

theorem cell23_7120536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_7120536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120536 prefixEnd_7120536 := by exact prefixLift 7120536
  have htrace : WordTrace (prefixWord ++ tailWord_7120536) baseStart_7120536 baseEnd_7120536 := by
    simpa [prefixWord, tailWord_7120536, baseEnd_7120536] using wordTrace_append hprefix tailTrace_7120536
  have hstable : (prefixWord ++ tailWord_7120536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120536).length < 2 ^ (prefixWord ++ tailWord_7120536).sum := by decide
  have hdescent : baseEnd_7120536 < baseStart_7120536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120576 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 6, 1, 3]
def baseStart_7120576 : Nat := 118140960795 + 7120576 * 2 ^ 59
def prefixEnd_7120576 : Nat := 4983230072969 + 3 ^ 40 * 7120576 * 2
def baseEnd_7120576 : Nat := 3656278024869237947353073

theorem tailTrace_7120576 : CollatzResearch.WordTrace tailWord_7120576 prefixEnd_7120576 3656278024869237947353073 := by
  unfold tailWord_7120576
  simp only [CollatzResearch.WordTrace]
  refine ⟨129854371325688362203718791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173139161767584482938291721 129854371325688362203718791)
  ·
    refine ⟨194781556988532543305578187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129854371325688362203718791 194781556988532543305578187)
    ·
      refine ⟨292172335482798814958367281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194781556988532543305578187 292172335482798814958367281)
      ·
        refine ⟨219129251612099111218775461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292172335482798814958367281 219129251612099111218775461)
        ·
          refine ⟨41086734677268583353520399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219129251612099111218775461 41086734677268583353520399)
          ·
            refine ⟨61630102015902875030280599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41086734677268583353520399 61630102015902875030280599)
            ·
              refine ⟨92445153023854312545420899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61630102015902875030280599 92445153023854312545420899)
              ·
                refine ⟨138667729535781468818131349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92445153023854312545420899 138667729535781468818131349)
                ·
                  refine ⟨6500049821989756350849907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138667729535781468818131349 6500049821989756350849907)
                  ·
                    refine ⟨9750074732984634526274861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6500049821989756350849907 9750074732984634526274861)
                    ·
                      refine ⟨3656278024869237947353073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9750074732984634526274861 3656278024869237947353073)
                      ·
                        rfl

theorem cell23_7120576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_7120576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120576 prefixEnd_7120576 := by exact prefixLift 7120576
  have htrace : WordTrace (prefixWord ++ tailWord_7120576) baseStart_7120576 baseEnd_7120576 := by
    simpa [prefixWord, tailWord_7120576, baseEnd_7120576] using wordTrace_append hprefix tailTrace_7120576
  have hstable : (prefixWord ++ tailWord_7120576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120576).length < 2 ^ (prefixWord ++ tailWord_7120576).sum := by decide
  have hdescent : baseEnd_7120576 < baseStart_7120576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120594 : List Nat := [3, 2, 2, 2, 2, 2, 3, 2, 1, 2, 2]
def baseStart_7120594 : Nat := 118140960795 + 7120594 * 2 ^ 59
def prefixEnd_7120594 : Nat := 4983230072969 + 3 ^ 40 * 7120594 * 2
def baseEnd_7120594 : Nat := 3656287267521018876927991

theorem tailTrace_7120594 : CollatzResearch.WordTrace tailWord_7120594 prefixEnd_7120594 3656287267521018876927991 := by
  unfold tailWord_7120594
  simp only [CollatzResearch.WordTrace]
  refine ⟨64927349791327878370398209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173139599443541008987728557 64927349791327878370398209)
  ·
    refine ⟨48695512343495908777798657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64927349791327878370398209 48695512343495908777798657)
    ·
      refine ⟨36521634257621931583348993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48695512343495908777798657 36521634257621931583348993)
      ·
        refine ⟨27391225693216448687511745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36521634257621931583348993 27391225693216448687511745)
        ·
          refine ⟨20543419269912336515633809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27391225693216448687511745 20543419269912336515633809)
          ·
            refine ⟨15407564452434252386725357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20543419269912336515633809 15407564452434252386725357)
            ·
              refine ⟨5777836669662844645022009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15407564452434252386725357 5777836669662844645022009)
              ·
                refine ⟨4333377502247133483766507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5777836669662844645022009 4333377502247133483766507)
                ·
                  refine ⟨6500066253370700225649761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4333377502247133483766507 6500066253370700225649761)
                  ·
                    refine ⟨4875049690028025169237321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6500066253370700225649761 4875049690028025169237321)
                    ·
                      refine ⟨3656287267521018876927991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875049690028025169237321 3656287267521018876927991)
                      ·
                        rfl

theorem cell23_7120594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_7120594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120594 prefixEnd_7120594 := by exact prefixLift 7120594
  have htrace : WordTrace (prefixWord ++ tailWord_7120594) baseStart_7120594 baseEnd_7120594 := by
    simpa [prefixWord, tailWord_7120594, baseEnd_7120594] using wordTrace_append hprefix tailTrace_7120594
  have hstable : (prefixWord ++ tailWord_7120594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120594).length < 2 ^ (prefixWord ++ tailWord_7120594).sum := by decide
  have hdescent : baseEnd_7120594 < baseStart_7120594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120599 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_7120599 : Nat := 118140960795 + 7120599 * 2 ^ 59
def prefixEnd_7120599 : Nat := 4983230072969 + 3 ^ 40 * 7120599 * 2
def baseEnd_7120599 : Nat := 3656289834924291357365467

theorem tailTrace_7120599 : CollatzResearch.WordTrace tailWord_7120599 prefixEnd_7120599 3656289834924291357365467 := by
  unfold tailWord_7120599
  simp only [CollatzResearch.WordTrace]
  refine ⟨259709581530293399335524851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173139721020195599557016567 259709581530293399335524851)
  ·
    refine ⟨389564372295440099003287277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259709581530293399335524851 389564372295440099003287277)
    ·
      refine ⟨146086639610790037126232729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 389564372295440099003287277 146086639610790037126232729)
      ·
        refine ⟨109564979708092527844674547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146086639610790037126232729 109564979708092527844674547)
        ·
          refine ⟨164347469562138791767011821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109564979708092527844674547 164347469562138791767011821)
          ·
            refine ⟨61630301085802046912629433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164347469562138791767011821 61630301085802046912629433)
            ·
              refine ⟨46222725814351535184472075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61630301085802046912629433 46222725814351535184472075)
              ·
                refine ⟨69334088721527302776708113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46222725814351535184472075 69334088721527302776708113)
                ·
                  refine ⟨52000566541145477082531085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69334088721527302776708113 52000566541145477082531085)
                  ·
                    refine ⟨19500212452929553905949157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52000566541145477082531085 19500212452929553905949157)
                    ·
                      refine ⟨3656289834924291357365467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19500212452929553905949157 3656289834924291357365467)
                      ·
                        rfl

theorem cell23_7120599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_7120599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120599 prefixEnd_7120599 := by exact prefixLift 7120599
  have htrace : WordTrace (prefixWord ++ tailWord_7120599) baseStart_7120599 baseEnd_7120599 := by
    simpa [prefixWord, tailWord_7120599, baseEnd_7120599] using wordTrace_append hprefix tailTrace_7120599
  have hstable : (prefixWord ++ tailWord_7120599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120599).length < 2 ^ (prefixWord ++ tailWord_7120599).sum := by decide
  have hdescent : baseEnd_7120599 < baseStart_7120599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120604 : List Nat := [2, 2, 5, 1, 3, 1, 2, 1, 2, 4]
def baseStart_7120604 : Nat := 118140960795 + 7120604 * 2 ^ 59
def prefixEnd_7120604 : Nat := 4983230072969 + 3 ^ 40 * 7120604 * 2
def baseEnd_7120604 : Nat := 1218764134109187945934315

theorem tailTrace_7120604 : CollatzResearch.WordTrace tailWord_7120604 prefixEnd_7120604 1218764134109187945934315 := by
  unfold tailWord_7120604
  simp only [CollatzResearch.WordTrace]
  refine ⟨129854881947637642594728433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173139842596850190126304577 129854881947637642594728433)
  ·
    refine ⟨97391161460728231946046325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129854881947637642594728433 97391161460728231946046325)
    ·
      refine ⟨9130421386943271744941843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97391161460728231946046325 9130421386943271744941843)
      ·
        refine ⟨13695632080414907617412765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9130421386943271744941843 13695632080414907617412765)
        ·
          refine ⟨5135862030155590356529787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13695632080414907617412765 5135862030155590356529787)
          ·
            refine ⟨7703793045233385534794681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5135862030155590356529787 7703793045233385534794681)
            ·
              refine ⟨5777844783925039151096011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7703793045233385534794681 5777844783925039151096011)
              ·
                refine ⟨8666767175887558726644017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5777844783925039151096011 8666767175887558726644017)
                ·
                  refine ⟨6500075381915669044983013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8666767175887558726644017 6500075381915669044983013)
                  ·
                    refine ⟨1218764134109187945934315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6500075381915669044983013 1218764134109187945934315)
                    ·
                      rfl

theorem cell23_7120604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_7120604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120604 prefixEnd_7120604 := by exact prefixLift 7120604
  have htrace : WordTrace (prefixWord ++ tailWord_7120604) baseStart_7120604 baseEnd_7120604 := by
    simpa [prefixWord, tailWord_7120604, baseEnd_7120604] using wordTrace_append hprefix tailTrace_7120604
  have hstable : (prefixWord ++ tailWord_7120604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120604).length < 2 ^ (prefixWord ++ tailWord_7120604).sum := by decide
  have hdescent : baseEnd_7120604 < baseStart_7120604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120619 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 5]
def baseStart_7120619 : Nat := 118140960795 + 7120619 * 2 ^ 59
def prefixEnd_7120619 : Nat := 4983230072969 + 3 ^ 40 * 7120619 * 2
def baseEnd_7120619 : Nat := 3656300104537381279115375

theorem tailTrace_7120619 : CollatzResearch.WordTrace tailWord_7120619 prefixEnd_7120619 3656300104537381279115375 := by
  unfold tailWord_7120619
  simp only [CollatzResearch.WordTrace]
  refine ⟨259710310990220942751252911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173140207326813961834168607 259710310990220942751252911)
  ·
    refine ⟨389565466485331414126879367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259710310990220942751252911 389565466485331414126879367)
    ·
      refine ⟨584348199727997121190319051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 389565466485331414126879367 584348199727997121190319051)
      ·
        refine ⟨876522299591995681785478577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584348199727997121190319051 876522299591995681785478577)
        ·
          refine ⟨657391724693996761339108933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 876522299591995681785478577 657391724693996761339108933)
          ·
            refine ⟨123260948380124392751082925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 657391724693996761339108933 123260948380124392751082925)
            ·
              refine ⟨46222855642546647281656097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123260948380124392751082925 46222855642546647281656097)
              ·
                refine ⟨34667141731909985461242073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46222855642546647281656097 34667141731909985461242073)
                ·
                  refine ⟨26000356298932489095931555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34667141731909985461242073 26000356298932489095931555)
                  ·
                    refine ⟨39000534448398733643897333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26000356298932489095931555 39000534448398733643897333)
                    ·
                      refine ⟨3656300104537381279115375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39000534448398733643897333 3656300104537381279115375)
                      ·
                        rfl

theorem cell23_7120619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 5].length) (baseStart_7120619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120619 prefixEnd_7120619 := by exact prefixLift 7120619
  have htrace : WordTrace (prefixWord ++ tailWord_7120619) baseStart_7120619 baseEnd_7120619 := by
    simpa [prefixWord, tailWord_7120619, baseEnd_7120619] using wordTrace_append hprefix tailTrace_7120619
  have hstable : (prefixWord ++ tailWord_7120619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120619).length < 2 ^ (prefixWord ++ tailWord_7120619).sum := by decide
  have hdescent : baseEnd_7120619 < baseStart_7120619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120650 : List Nat := [3, 1, 2, 2, 1, 3, 1, 4, 2, 2, 2]
def baseStart_7120650 : Nat := 118140960795 + 7120650 * 2 ^ 59
def prefixEnd_7120650 : Nat := 4983230072969 + 3 ^ 40 * 7120650 * 2
def baseEnd_7120650 : Nat := 3656316022437670657827733

theorem tailTrace_7120650 : CollatzResearch.WordTrace tailWord_7120650 prefixEnd_7120650 3656316022437670657827733 := by
  unfold tailWord_7120650
  simp only [CollatzResearch.WordTrace]
  refine ⟨64927860413277158761407851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173140961102072423363754269 64927860413277158761407851)
  ·
    refine ⟨97391790619915738142111777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64927860413277158761407851 97391790619915738142111777)
    ·
      refine ⟨73043842964936803606583833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97391790619915738142111777 73043842964936803606583833)
      ·
        refine ⟨54782882223702602704937875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73043842964936803606583833 54782882223702602704937875)
        ·
          refine ⟨82174323335553904057406813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54782882223702602704937875 82174323335553904057406813)
          ·
            refine ⟨30815371250832714021527555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82174323335553904057406813 30815371250832714021527555)
            ·
              refine ⟨46223056876249071032291333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30815371250832714021527555 46223056876249071032291333)
              ·
                refine ⟨8666823164296700818554625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46223056876249071032291333 8666823164296700818554625)
                ·
                  refine ⟨6500117373222525613915969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8666823164296700818554625 6500117373222525613915969)
                  ·
                    refine ⟨4875088029916894210436977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6500117373222525613915969 4875088029916894210436977)
                    ·
                      refine ⟨3656316022437670657827733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4875088029916894210436977 3656316022437670657827733)
                      ·
                        rfl

theorem cell23_7120650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_7120650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120650 prefixEnd_7120650 := by exact prefixLift 7120650
  have htrace : WordTrace (prefixWord ++ tailWord_7120650) baseStart_7120650 baseEnd_7120650 := by
    simpa [prefixWord, tailWord_7120650, baseEnd_7120650] using wordTrace_append hprefix tailTrace_7120650
  have hstable : (prefixWord ++ tailWord_7120650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120650).length < 2 ^ (prefixWord ++ tailWord_7120650).sum := by decide
  have hdescent : baseEnd_7120650 < baseStart_7120650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120666 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3]
def baseStart_7120666 : Nat := 118140960795 + 7120666 * 2 ^ 59
def prefixEnd_7120666 : Nat := 4983230072969 + 3 ^ 40 * 7120666 * 2
def baseEnd_7120666 : Nat := 3656324238128142595227659

theorem tailTrace_7120666 : CollatzResearch.WordTrace tailWord_7120666 prefixEnd_7120666 3656324238128142595227659 := by
  unfold tailWord_7120666
  simp only [CollatzResearch.WordTrace]
  refine ⟨64928006305262667444553463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 173141350147367113185475901 64928006305262667444553463)
  ·
    refine ⟨97392009457894001166830195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64928006305262667444553463 97392009457894001166830195)
    ·
      refine ⟨146088014186841001750245293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97392009457894001166830195 146088014186841001750245293)
      ·
        refine ⟨54783005320065375656341985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146088014186841001750245293 54783005320065375656341985)
        ·
          refine ⟨41087253990049031742256489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54783005320065375656341985 41087253990049031742256489)
          ·
            refine ⟨30815440492536773806692367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41087253990049031742256489 30815440492536773806692367)
            ·
              refine ⟨46223160738805160710038551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30815440492536773806692367 46223160738805160710038551)
              ·
                refine ⟨69334741108207741065057827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46223160738805160710038551 69334741108207741065057827)
                ·
                  refine ⟨104002111662311611597586741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69334741108207741065057827 104002111662311611597586741)
                  ·
                    refine ⟨9750197968341713587273757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104002111662311611597586741 9750197968341713587273757)
                    ·
                      refine ⟨3656324238128142595227659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9750197968341713587273757 3656324238128142595227659)
                      ·
                        rfl

theorem cell23_7120666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_7120666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120666 prefixEnd_7120666 := by exact prefixLift 7120666
  have htrace : WordTrace (prefixWord ++ tailWord_7120666) baseStart_7120666 baseEnd_7120666 := by
    simpa [prefixWord, tailWord_7120666, baseEnd_7120666] using wordTrace_append hprefix tailTrace_7120666
  have hstable : (prefixWord ++ tailWord_7120666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120666).length < 2 ^ (prefixWord ++ tailWord_7120666).sum := by decide
  have hdescent : baseEnd_7120666 < baseStart_7120666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120743 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_7120743 : Nat := 118140960795 + 7120743 * 2 ^ 59
def prefixEnd_7120743 : Nat := 4983230072969 + 3 ^ 40 * 7120743 * 2
def baseEnd_7120743 : Nat := 3656363776138538793964805

theorem tailTrace_7120743 : CollatzResearch.WordTrace tailWord_7120743 prefixEnd_7120743 3656363776138538793964805 := by
  unfold tailWord_7120743
  simp only [CollatzResearch.WordTrace]
  refine ⟨259714833641771711928766883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173143222427847807952511255 259714833641771711928766883)
  ·
    refine ⟨389572250462657567893150325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259714833641771711928766883 389572250462657567893150325)
    ·
      refine ⟨36522398480874146989982843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 389572250462657567893150325 36522398480874146989982843)
      ·
        refine ⟨54783597721311220484974265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36522398480874146989982843 54783597721311220484974265)
        ·
          refine ⟨41087698290983415363730699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54783597721311220484974265 41087698290983415363730699)
          ·
            refine ⟨61631547436475123045596049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41087698290983415363730699 61631547436475123045596049)
            ·
              refine ⟨46223660577356342284197037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61631547436475123045596049 46223660577356342284197037)
              ·
                refine ⟨17333872716508628356573889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46223660577356342284197037 17333872716508628356573889)
                ·
                  refine ⟨13000404537381471267430417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17333872716508628356573889 13000404537381471267430417)
                  ·
                    refine ⟨9750303403036103450572813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13000404537381471267430417 9750303403036103450572813)
                    ·
                      refine ⟨3656363776138538793964805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9750303403036103450572813 3656363776138538793964805)
                      ·
                        rfl

theorem cell23_7120743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_7120743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120743 prefixEnd_7120743 := by exact prefixLift 7120743
  have htrace : WordTrace (prefixWord ++ tailWord_7120743) baseStart_7120743 baseEnd_7120743 := by
    simpa [prefixWord, tailWord_7120743, baseEnd_7120743] using wordTrace_append hprefix tailTrace_7120743
  have hstable : (prefixWord ++ tailWord_7120743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120743).length < 2 ^ (prefixWord ++ tailWord_7120743).sum := by decide
  have hdescent : baseEnd_7120743 < baseStart_7120743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7120793 : List Nat := [1, 2, 1, 2, 1, 3, 5, 2, 1, 5]
def baseStart_7120793 : Nat := 118140960795 + 7120793 * 2 ^ 59
def prefixEnd_7120793 : Nat := 4983230072969 + 3 ^ 40 * 7120793 * 2
def baseEnd_7120793 : Nat := 1218796483390421199446525

theorem tailTrace_7120793 : CollatzResearch.WordTrace tailWord_7120793 prefixEnd_7120793 1218796483390421199446525 := by
  unfold tailWord_7120793
  simp only [CollatzResearch.WordTrace]
  refine ⟨259716657291590570468087033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173144438194393713645391355 259716657291590570468087033)
  ·
    refine ⟨194787492968692927851065275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259716657291590570468087033 194787492968692927851065275)
    ·
      refine ⟨292181239453039391776597913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194787492968692927851065275 292181239453039391776597913)
      ·
        refine ⟨219135929589779543832448435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292181239453039391776597913 219135929589779543832448435)
        ·
          refine ⟨328703894384669315748672653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219135929589779543832448435 328703894384669315748672653)
          ·
            refine ⟨123263960394250993405752245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328703894384669315748672653 123263960394250993405752245)
            ·
              refine ⟨11555996286961030631789273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123263960394250993405752245 11555996286961030631789273)
              ·
                refine ⟨8666997215220772973841955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11555996286961030631789273 8666997215220772973841955)
                ·
                  refine ⟨13000495822831159460762933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8666997215220772973841955 13000495822831159460762933)
                  ·
                    refine ⟨1218796483390421199446525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13000495822831159460762933 1218796483390421199446525)
                    ·
                      rfl

theorem cell23_7120793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 5].length) (baseStart_7120793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7120793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7120793 prefixEnd_7120793 := by exact prefixLift 7120793
  have htrace : WordTrace (prefixWord ++ tailWord_7120793) baseStart_7120793 baseEnd_7120793 := by
    simpa [prefixWord, tailWord_7120793, baseEnd_7120793] using wordTrace_append hprefix tailTrace_7120793
  have hstable : (prefixWord ++ tailWord_7120793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7120793).length < 2 ^ (prefixWord ++ tailWord_7120793).sum := by decide
  have hdescent : baseEnd_7120793 < baseStart_7120793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7120793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
