import V185TrunkScan22Chunk135

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1216558 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_1216558 : Nat := 118140960795 + 1216558 * 2 ^ 59
def prefixEnd_1216558 : Nat := 4983230072969 + 3 ^ 40 * 1216558 * 2
def baseEnd_1216558 : Nat := 138817555127234765540035

theorem tailTrace_1216558 : CollatzResearch.WordTrace tailWord_1216558 prefixEnd_1216558 138817555127234765540035 := by
  unfold tailWord_1216558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5546439440828201551246291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29581010351083741606646885 5546439440828201551246291)
  ·
    refine ⟨8319659161242302326869437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5546439440828201551246291 8319659161242302326869437)
    ·
      refine ⟨3119872185465863372576039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8319659161242302326869437 3119872185465863372576039)
      ·
        refine ⟨4679808278198795058864059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3119872185465863372576039 4679808278198795058864059)
        ·
          refine ⟨7019712417298192588296089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4679808278198795058864059 7019712417298192588296089)
          ·
            refine ⟨5264784312973644441222067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7019712417298192588296089 5264784312973644441222067)
            ·
              refine ⟨7897176469460466661833101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5264784312973644441222067 7897176469460466661833101)
              ·
                refine ⟨2961441176047674998187413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7897176469460466661833101 2961441176047674998187413)
                ·
                  refine ⟨138817555127234765540035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2961441176047674998187413 138817555127234765540035)
                  ·
                    rfl

theorem cell22_1216558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_1216558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216558 prefixEnd_1216558 := by exact prefixLift 1216558
  have htrace : WordTrace (prefixWord ++ tailWord_1216558) baseStart_1216558 baseEnd_1216558 := by
    simpa [prefixWord, tailWord_1216558, baseEnd_1216558] using wordTrace_append hprefix tailTrace_1216558
  have hstable : (prefixWord ++ tailWord_1216558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216558).length < 2 ^ (prefixWord ++ tailWord_1216558).sum := by decide
  have hdescent : baseEnd_1216558 < baseStart_1216558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216571 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 4, 4]
def baseStart_1216571 : Nat := 118140960795 + 1216571 * 2 ^ 59
def prefixEnd_1216571 : Nat := 4983230072969 + 3 ^ 40 * 1216571 * 2
def baseEnd_1216571 : Nat := 416457115547376596045065

theorem tailTrace_1216571 : CollatzResearch.WordTrace tailWord_1216571 prefixEnd_1216571 416457115547376596045065 := by
  unfold tailWord_1216571
  simp only [CollatzResearch.WordTrace]
  refine ⟨44371989675578515630193567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29581326450385677086795711 44371989675578515630193567)
  ·
    refine ⟨66557984513367773445290351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44371989675578515630193567 66557984513367773445290351)
    ·
      refine ⟨99836976770051660167935527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66557984513367773445290351 99836976770051660167935527)
      ·
        refine ⟨149755465155077490251903291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99836976770051660167935527 149755465155077490251903291)
        ·
          refine ⟨224633197732616235377854937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149755465155077490251903291 224633197732616235377854937)
          ·
            refine ⟨168474898299462176533391203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224633197732616235377854937 168474898299462176533391203)
            ·
              refine ⟨252712347449193264800086805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168474898299462176533391203 252712347449193264800086805)
              ·
                refine ⟨11845891286680934287504069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 252712347449193264800086805 11845891286680934287504069)
                ·
                  refine ⟨2221104616252675178907013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11845891286680934287504069 2221104616252675178907013)
                  ·
                    refine ⟨416457115547376596045065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2221104616252675178907013 416457115547376596045065)
                    ·
                      rfl

theorem cell22_1216571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 4].length) (baseStart_1216571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216571 prefixEnd_1216571 := by exact prefixLift 1216571
  have htrace : WordTrace (prefixWord ++ tailWord_1216571) baseStart_1216571 baseEnd_1216571 := by
    simpa [prefixWord, tailWord_1216571, baseEnd_1216571] using wordTrace_append hprefix tailTrace_1216571
  have hstable : (prefixWord ++ tailWord_1216571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216571).length < 2 ^ (prefixWord ++ tailWord_1216571).sum := by decide
  have hdescent : baseEnd_1216571 < baseStart_1216571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216605 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1216605 : Nat := 118140960795 + 1216605 * 2 ^ 59
def prefixEnd_1216605 : Nat := 4983230072969 + 3 ^ 40 * 1216605 * 2
def baseEnd_1216605 : Nat := 416468754442211840694961

theorem tailTrace_1216605 : CollatzResearch.WordTrace tailWord_1216605 prefixEnd_1216605 416468754442211840694961 := by
  unfold tailWord_1216605
  simp only [CollatzResearch.WordTrace]
  refine ⟨44373229757455339436931269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29582153171636892957954179 44373229757455339436931269)
  ·
    refine ⟨8319980579522876144424613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44373229757455339436931269 8319980579522876144424613)
    ·
      refine ⟨1559996358660539277079615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8319980579522876144424613 1559996358660539277079615)
      ·
        refine ⟨2339994537990808915619423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559996358660539277079615 2339994537990808915619423)
        ·
          refine ⟨3509991806986213373429135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2339994537990808915619423 3509991806986213373429135)
          ·
            refine ⟨5264987710479320060143703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3509991806986213373429135 5264987710479320060143703)
            ·
              refine ⟨7897481565718980090215555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5264987710479320060143703 7897481565718980090215555)
              ·
                refine ⟨11846222348578470135323333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7897481565718980090215555 11846222348578470135323333)
                ·
                  refine ⟨2221166690358463150373125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11846222348578470135323333 2221166690358463150373125)
                  ·
                    refine ⟨416468754442211840694961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2221166690358463150373125 416468754442211840694961)
                    ·
                      rfl

theorem cell22_1216605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1216605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216605 prefixEnd_1216605 := by exact prefixLift 1216605
  have htrace : WordTrace (prefixWord ++ tailWord_1216605) baseStart_1216605 baseEnd_1216605 := by
    simpa [prefixWord, tailWord_1216605, baseEnd_1216605] using wordTrace_append hprefix tailTrace_1216605
  have hstable : (prefixWord ++ tailWord_1216605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216605).length < 2 ^ (prefixWord ++ tailWord_1216605).sum := by decide
  have hdescent : baseEnd_1216605 < baseStart_1216605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216669 : List Nat := [1, 4, 2, 1, 1, 3, 4, 2, 1, 3]
def baseStart_1216669 : Nat := 118140960795 + 1216669 * 2 ^ 59
def prefixEnd_1216669 : Nat := 4983230072969 + 3 ^ 40 * 1216669 * 2
def baseEnd_1216669 : Nat := 416490662950137007094765

theorem tailTrace_1216669 : CollatzResearch.WordTrace tailWord_1216669 prefixEnd_1216669 416490662950137007094765 := by
  unfold tailWord_1216669
  simp only [CollatzResearch.WordTrace]
  refine ⟨44375564029223478367261061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29583709352815652244840707 44375564029223478367261061)
  ·
    refine ⟨8320418255479402193861449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44375564029223478367261061 8320418255479402193861449)
    ·
      refine ⟨6240313691609551645396087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8320418255479402193861449 6240313691609551645396087)
      ·
        refine ⟨9360470537414327468094131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6240313691609551645396087 9360470537414327468094131)
        ·
          refine ⟨14040705806121491202141197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9360470537414327468094131 14040705806121491202141197)
          ·
            refine ⟨5265264677295559200802949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14040705806121491202141197 5265264677295559200802949)
            ·
              refine ⟨987237126992917350150553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5265264677295559200802949 987237126992917350150553)
              ·
                refine ⟨740427845244688012612915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 987237126992917350150553 740427845244688012612915)
                ·
                  refine ⟨1110641767867032018919373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740427845244688012612915 1110641767867032018919373)
                  ·
                    refine ⟨416490662950137007094765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1110641767867032018919373 416490662950137007094765)
                    ·
                      rfl

theorem cell22_1216669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_1216669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216669 prefixEnd_1216669 := by exact prefixLift 1216669
  have htrace : WordTrace (prefixWord ++ tailWord_1216669) baseStart_1216669 baseEnd_1216669 := by
    simpa [prefixWord, tailWord_1216669, baseEnd_1216669] using wordTrace_append hprefix tailTrace_1216669
  have hstable : (prefixWord ++ tailWord_1216669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216669).length < 2 ^ (prefixWord ++ tailWord_1216669).sum := by decide
  have hdescent : baseEnd_1216669 < baseStart_1216669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216772 : List Nat := [2, 3, 2, 2, 4, 1, 8]
def baseStart_1216772 : Nat := 118140960795 + 1216772 * 2 ^ 59
def prefixEnd_1216772 : Nat := 4983230072969 + 3 ^ 40 * 1216772 * 2
def baseEnd_1216772 : Nat := 15426885998336261917387

theorem tailTrace_1216772 : CollatzResearch.WordTrace tailWord_1216772 prefixEnd_1216772 15426885998336261917387 := by
  unfold tailWord_1216772
  simp only [CollatzResearch.WordTrace]
  refine ⟨22189660373925163479130285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29586213831900217972173713 22189660373925163479130285)
  ·
    refine ⟨8321122640221936304673857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22189660373925163479130285 8321122640221936304673857)
    ·
      refine ⟨6240841980166452228505393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8321122640221936304673857 6240841980166452228505393)
      ·
        refine ⟨4680631485124839171379045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6240841980166452228505393 4680631485124839171379045)
        ·
          refine ⟨877618403460907344633571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4680631485124839171379045 877618403460907344633571)
          ·
            refine ⟨1316427605191361016950357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877618403460907344633571 1316427605191361016950357)
            ·
              refine ⟨15426885998336261917387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1316427605191361016950357 15426885998336261917387)
              ·
                rfl

theorem cell22_1216772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 8].length) (baseStart_1216772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216772 prefixEnd_1216772 := by exact prefixLift 1216772
  have htrace : WordTrace (prefixWord ++ tailWord_1216772) baseStart_1216772 baseEnd_1216772 := by
    simpa [prefixWord, tailWord_1216772, baseEnd_1216772] using wordTrace_append hprefix tailTrace_1216772
  have hstable : (prefixWord ++ tailWord_1216772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216772).length < 2 ^ (prefixWord ++ tailWord_1216772).sum := by decide
  have hdescent : baseEnd_1216772 < baseStart_1216772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216787 : List Nat := [1, 1, 1, 2, 1, 3, 1, 8, 1, 3]
def baseStart_1216787 : Nat := 118140960795 + 1216787 * 2 ^ 59
def prefixEnd_1216787 : Nat := 4983230072969 + 3 ^ 40 * 1216787 * 2
def baseEnd_1216787 : Nat := 416531056761624032644403

theorem tailTrace_1216787 : CollatzResearch.WordTrace tailWord_1216787 prefixEnd_1216787 416531056761624032644403 := by
  unfold tailWord_1216787
  simp only [CollatzResearch.WordTrace]
  refine ⟨44379867842795984520056615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29586578561863989680037743 44379867842795984520056615)
  ·
    refine ⟨66569801764193976780084923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44379867842795984520056615 66569801764193976780084923)
    ·
      refine ⟨99854702646290965170127385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66569801764193976780084923 99854702646290965170127385)
      ·
        refine ⟨74891026984718223877595539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99854702646290965170127385 74891026984718223877595539)
        ·
          refine ⟨112336540477077335816393309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74891026984718223877595539 112336540477077335816393309)
          ·
            refine ⟨42126202678904000931147491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112336540477077335816393309 42126202678904000931147491)
            ·
              refine ⟨63189304018356001396721237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42126202678904000931147491 63189304018356001396721237)
              ·
                refine ⟨740499656465109391367827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 63189304018356001396721237 740499656465109391367827)
                ·
                  refine ⟨1110749484697664087051741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740499656465109391367827 1110749484697664087051741)
                  ·
                    refine ⟨416531056761624032644403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1110749484697664087051741 416531056761624032644403)
                    ·
                      rfl

theorem cell22_1216787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 8, 1, 3].length) (baseStart_1216787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216787 prefixEnd_1216787 := by exact prefixLift 1216787
  have htrace : WordTrace (prefixWord ++ tailWord_1216787) baseStart_1216787 baseEnd_1216787 := by
    simpa [prefixWord, tailWord_1216787, baseEnd_1216787] using wordTrace_append hprefix tailTrace_1216787
  have hstable : (prefixWord ++ tailWord_1216787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216787).length < 2 ^ (prefixWord ++ tailWord_1216787).sum := by decide
  have hdescent : baseEnd_1216787 < baseStart_1216787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216877 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_1216877 : Nat := 118140960795 + 1216877 * 2 ^ 59
def prefixEnd_1216877 : Nat := 4983230072969 + 3 ^ 40 * 1216877 * 2
def baseEnd_1216877 : Nat := 416561865600893797894127

theorem tailTrace_1216877 : CollatzResearch.WordTrace tailWord_1216877 prefixEnd_1216877 416561865600893797894127 := by
  unfold tailWord_1216877
  simp only [CollatzResearch.WordTrace]
  refine ⟨44383150412469929890832885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29588766941646619927221923 44383150412469929890832885)
  ·
    refine ⟨4160920351169055927265583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44383150412469929890832885 4160920351169055927265583)
    ·
      refine ⟨6241380526753583890898375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4160920351169055927265583 6241380526753583890898375)
      ·
        refine ⟨9362070790130375836347563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6241380526753583890898375 9362070790130375836347563)
        ·
          refine ⟨14043106185195563754521345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9362070790130375836347563 14043106185195563754521345)
          ·
            refine ⟨10532329638896672815891009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14043106185195563754521345 10532329638896672815891009)
            ·
              refine ⟨7899247229172504611918257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10532329638896672815891009 7899247229172504611918257)
              ·
                refine ⟨5924435421879378458938693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7899247229172504611918257 5924435421879378458938693)
                ·
                  refine ⟨1110831641602383461051005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5924435421879378458938693 1110831641602383461051005)
                  ·
                    refine ⟨416561865600893797894127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1110831641602383461051005 416561865600893797894127)
                    ·
                      rfl

theorem cell22_1216877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_1216877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216877 prefixEnd_1216877 := by exact prefixLift 1216877
  have htrace : WordTrace (prefixWord ++ tailWord_1216877) baseStart_1216877 baseEnd_1216877 := by
    simpa [prefixWord, tailWord_1216877, baseEnd_1216877] using wordTrace_append hprefix tailTrace_1216877
  have hstable : (prefixWord ++ tailWord_1216877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216877).length < 2 ^ (prefixWord ++ tailWord_1216877).sum := by decide
  have hdescent : baseEnd_1216877 < baseStart_1216877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216956 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 3, 3]
def baseStart_1216956 : Nat := 118140960795 + 1216956 * 2 ^ 59
def prefixEnd_1216956 : Nat := 4983230072969 + 3 ^ 40 * 1216956 * 2
def baseEnd_1216956 : Nat := 416588908915363925168885

theorem tailTrace_1216956 : CollatzResearch.WordTrace tailWord_1216956 prefixEnd_1216956 416588908915363925168885 := by
  unfold tailWord_1216956
  simp only [CollatzResearch.WordTrace]
  refine ⟨22193015889591863191479361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29590687852789150921972481 22193015889591863191479361)
  ·
    refine ⟨16644761917193897393609521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22193015889591863191479361 16644761917193897393609521)
    ·
      refine ⟨12483571437895423045207141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16644761917193897393609521 12483571437895423045207141)
      ·
        refine ⟨2340669644605391820976339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12483571437895423045207141 2340669644605391820976339)
        ·
          refine ⟨3511004466908087731464509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2340669644605391820976339 3511004466908087731464509)
          ·
            refine ⟨1316626675090532899299191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3511004466908087731464509 1316626675090532899299191)
            ·
              refine ⟨1974940012635799348948787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1316626675090532899299191 1974940012635799348948787)
              ·
                refine ⟨2962410018953699023423181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1974940012635799348948787 2962410018953699023423181)
                ·
                  refine ⟨1110903757107637133783693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2962410018953699023423181 1110903757107637133783693)
                  ·
                    refine ⟨416588908915363925168885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1110903757107637133783693 416588908915363925168885)
                    ·
                      rfl

theorem cell22_1216956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_1216956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1216956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1216956 prefixEnd_1216956 := by exact prefixLift 1216956
  have htrace : WordTrace (prefixWord ++ tailWord_1216956) baseStart_1216956 baseEnd_1216956 := by
    simpa [prefixWord, tailWord_1216956, baseEnd_1216956] using wordTrace_append hprefix tailTrace_1216956
  have hstable : (prefixWord ++ tailWord_1216956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216956).length < 2 ^ (prefixWord ++ tailWord_1216956).sum := by decide
  have hdescent : baseEnd_1216956 < baseStart_1216956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217029 : List Nat := [1, 3, 1, 1, 2, 2, 4, 3, 2, 3]
def baseStart_1217029 : Nat := 118140960795 + 1217029 * 2 ^ 59
def prefixEnd_1217029 : Nat := 4983230072969 + 3 ^ 40 * 1217029 * 2
def baseEnd_1217029 : Nat := 416613898307216068093661

theorem tailTrace_1217029 : CollatzResearch.WordTrace tailWord_1217029 prefixEnd_1217029 416613898307216068093661 := by
  unfold tailWord_1217029
  simp only [CollatzResearch.WordTrace]
  refine ⟨44388694307919259850366141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29592462871946173233577427 44388694307919259850366141)
  ·
    refine ⟨16645760365469722443887303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44388694307919259850366141 16645760365469722443887303)
    ·
      refine ⟨24968640548204583665830955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16645760365469722443887303 24968640548204583665830955)
      ·
        refine ⟨37452960822306875498746433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24968640548204583665830955 37452960822306875498746433)
        ·
          refine ⟨28089720616730156624059825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37452960822306875498746433 28089720616730156624059825)
          ·
            refine ⟨21067290462547617468044869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28089720616730156624059825 21067290462547617468044869)
            ·
              refine ⟨3950116961727678275258413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21067290462547617468044869 3950116961727678275258413)
              ·
                refine ⟨1481293860647879353221905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3950116961727678275258413 1481293860647879353221905)
                ·
                  refine ⟨1110970395485909514916429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1481293860647879353221905 1110970395485909514916429)
                  ·
                    refine ⟨416613898307216068093661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1110970395485909514916429 416613898307216068093661)
                    ·
                      rfl

theorem cell22_1217029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_1217029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217029 prefixEnd_1217029 := by exact prefixLift 1217029
  have htrace : WordTrace (prefixWord ++ tailWord_1217029) baseStart_1217029 baseEnd_1217029 := by
    simpa [prefixWord, tailWord_1217029, baseEnd_1217029] using wordTrace_append hprefix tailTrace_1217029
  have hstable : (prefixWord ++ tailWord_1217029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217029).length < 2 ^ (prefixWord ++ tailWord_1217029).sum := by decide
  have hdescent : baseEnd_1217029 < baseStart_1217029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217063 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1217063 : Nat := 118140960795 + 1217063 * 2 ^ 59
def prefixEnd_1217063 : Nat := 4983230072969 + 3 ^ 40 * 1217063 * 2
def baseEnd_1217063 : Nat := 416625537202051312743557

theorem tailTrace_1217063 : CollatzResearch.WordTrace tailWord_1217063 prefixEnd_1217063 416625537202051312743557 := by
  unfold tailWord_1217063
  simp only [CollatzResearch.WordTrace]
  refine ⟨44389934389796083657103843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29593289593197389104735895 44389934389796083657103843)
  ·
    refine ⟨66584901584694125485655765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44389934389796083657103843 66584901584694125485655765)
    ·
      refine ⟨1560583630891268566070057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 66584901584694125485655765 1560583630891268566070057)
      ·
        refine ⟨1170437723168451424552543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1560583630891268566070057 1170437723168451424552543)
        ·
          refine ⟨1755656584752677136828815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170437723168451424552543 1755656584752677136828815)
          ·
            refine ⟨2633484877129015705243223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755656584752677136828815 2633484877129015705243223)
            ·
              refine ⟨3950227315693523557864835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633484877129015705243223 3950227315693523557864835)
              ·
                refine ⟨5925340973540285336797253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3950227315693523557864835 5925340973540285336797253)
                ·
                  refine ⟨1111001432538803500649485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5925340973540285336797253 1111001432538803500649485)
                  ·
                    refine ⟨416625537202051312743557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1111001432538803500649485 416625537202051312743557)
                    ·
                      rfl

theorem cell22_1217063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1217063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217063 prefixEnd_1217063 := by exact prefixLift 1217063
  have htrace : WordTrace (prefixWord ++ tailWord_1217063) baseStart_1217063 baseEnd_1217063 := by
    simpa [prefixWord, tailWord_1217063, baseEnd_1217063] using wordTrace_append hprefix tailTrace_1217063
  have hstable : (prefixWord ++ tailWord_1217063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217063).length < 2 ^ (prefixWord ++ tailWord_1217063).sum := by decide
  have hdescent : baseEnd_1217063 < baseStart_1217063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217074 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_1217074 : Nat := 118140960795 + 1217074 * 2 ^ 59
def prefixEnd_1217074 : Nat := 4983230072969 + 3 ^ 40 * 1217074 * 2
def baseEnd_1217074 : Nat := 416629302726850950718523

theorem tailTrace_1217074 : CollatzResearch.WordTrace tailWord_1217074 prefixEnd_1217074 416629302726850950718523 := by
  unfold tailWord_1217074
  simp only [CollatzResearch.WordTrace]
  refine ⟨11097583898189058133938569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29593557061837488357169517 11097583898189058133938569)
  ·
    refine ⟨8323187923641793600453927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11097583898189058133938569 8323187923641793600453927)
    ·
      refine ⟨12484781885462690400680891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8323187923641793600453927 12484781885462690400680891)
      ·
        refine ⟨18727172828194035601021337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12484781885462690400680891 18727172828194035601021337)
        ·
          refine ⟨14045379621145526700766003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18727172828194035601021337 14045379621145526700766003)
          ·
            refine ⟨21068069431718290051149005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14045379621145526700766003 21068069431718290051149005)
            ·
              refine ⟨7900526036894358769180877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21068069431718290051149005 7900526036894358769180877)
              ·
                refine ⟨2962697263835384538442829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7900526036894358769180877 2962697263835384538442829)
                ·
                  refine ⟨1111011473938269201916061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2962697263835384538442829 1111011473938269201916061)
                  ·
                    refine ⟨416629302726850950718523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1111011473938269201916061 416629302726850950718523)
                    ·
                      rfl

theorem cell22_1217074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_1217074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217074 prefixEnd_1217074 := by exact prefixLift 1217074
  have htrace : WordTrace (prefixWord ++ tailWord_1217074) baseStart_1217074 baseEnd_1217074 := by
    simpa [prefixWord, tailWord_1217074, baseEnd_1217074] using wordTrace_append hprefix tailTrace_1217074
  have hstable : (prefixWord ++ tailWord_1217074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217074).length < 2 ^ (prefixWord ++ tailWord_1217074).sum := by decide
  have hdescent : baseEnd_1217074 < baseStart_1217074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217102 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_1217102 : Nat := 118140960795 + 1217102 * 2 ^ 59
def prefixEnd_1217102 : Nat := 4983230072969 + 3 ^ 40 * 1217102 * 2
def baseEnd_1217102 : Nat := 416638887699068211018437

theorem tailTrace_1217102 : CollatzResearch.WordTrace tailWord_1217102 prefixEnd_1217102 416638887699068211018437 := by
  unfold tailWord_1217102
  simp only [CollatzResearch.WordTrace]
  refine ⟨5548919604581849164721695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29594237891103195545182373 5548919604581849164721695)
  ·
    refine ⟨8323379406872773747082543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5548919604581849164721695 8323379406872773747082543)
    ·
      refine ⟨12485069110309160620623815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8323379406872773747082543 12485069110309160620623815)
      ·
        refine ⟨18727603665463740930935723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12485069110309160620623815 18727603665463740930935723)
        ·
          refine ⟨28091405498195611396403585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18727603665463740930935723 28091405498195611396403585)
          ·
            refine ⟨21068554123646708547302689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28091405498195611396403585 21068554123646708547302689)
            ·
              refine ⟨15801415592735031410477017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21068554123646708547302689 15801415592735031410477017)
              ·
                refine ⟨11851061694551273557857763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15801415592735031410477017 11851061694551273557857763)
                ·
                  refine ⟨17776592541826910336786645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11851061694551273557857763 17776592541826910336786645)
                  ·
                    refine ⟨416638887699068211018437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17776592541826910336786645 416638887699068211018437)
                    ·
                      rfl

theorem cell22_1217102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_1217102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217102 prefixEnd_1217102 := by exact prefixLift 1217102
  have htrace : WordTrace (prefixWord ++ tailWord_1217102) baseStart_1217102 baseEnd_1217102 := by
    simpa [prefixWord, tailWord_1217102, baseEnd_1217102] using wordTrace_append hprefix tailTrace_1217102
  have hstable : (prefixWord ++ tailWord_1217102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217102).length < 2 ^ (prefixWord ++ tailWord_1217102).sum := by decide
  have hdescent : baseEnd_1217102 < baseStart_1217102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217108 : List Nat := [2, 4, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_1217108 : Nat := 118140960795 + 1217108 * 2 ^ 59
def prefixEnd_1217108 : Nat := 4983230072969 + 3 ^ 40 * 1217108 * 2
def baseEnd_1217108 : Nat := 416640941621686195368419

theorem tailTrace_1217108 : CollatzResearch.WordTrace tailWord_1217108 prefixEnd_1217108 416640941621686195368419 := by
  unfold tailWord_1217108
  simp only [CollatzResearch.WordTrace]
  refine ⟨22195787837316528171245989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29594383783088704228327985 22195787837316528171245989)
  ·
    refine ⟨4161710219496849032108623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22195787837316528171245989 4161710219496849032108623)
    ·
      refine ⟨6242565329245273548162935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4161710219496849032108623 6242565329245273548162935)
      ·
        refine ⟨9363847993867910322244403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6242565329245273548162935 9363847993867910322244403)
        ·
          refine ⟨14045771990801865483366605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9363847993867910322244403 14045771990801865483366605)
          ·
            refine ⟨5267164496550699556262477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14045771990801865483366605 5267164496550699556262477)
            ·
              refine ⟨1975186686206512333598429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5267164496550699556262477 1975186686206512333598429)
              ·
                refine ⟨740695007327442125099411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1975186686206512333598429 740695007327442125099411)
                ·
                  refine ⟨1111042510991163187649117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740695007327442125099411 1111042510991163187649117)
                  ·
                    refine ⟨416640941621686195368419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1111042510991163187649117 416640941621686195368419)
                    ·
                      rfl

theorem cell22_1217108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_1217108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217108 prefixEnd_1217108 := by exact prefixLift 1217108
  have htrace : WordTrace (prefixWord ++ tailWord_1217108) baseStart_1217108 baseEnd_1217108 := by
    simpa [prefixWord, tailWord_1217108, baseEnd_1217108] using wordTrace_append hprefix tailTrace_1217108
  have hstable : (prefixWord ++ tailWord_1217108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217108).length < 2 ^ (prefixWord ++ tailWord_1217108).sum := by decide
  have hdescent : baseEnd_1217108 < baseStart_1217108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217125 : List Nat := [1, 3, 1, 3, 4, 1, 3, 2, 1, 3]
def baseStart_1217125 : Nat := 118140960795 + 1217125 * 2 ^ 59
def prefixEnd_1217125 : Nat := 4983230072969 + 3 ^ 40 * 1217125 * 2
def baseEnd_1217125 : Nat := 416646761069103817693367

theorem tailTrace_1217125 : CollatzResearch.WordTrace tailWord_1217125 prefixEnd_1217125 416646761069103817693367 := by
  unfold tailWord_1217125
  simp only [CollatzResearch.WordTrace]
  refine ⟨44392195715571468245860829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29594797143714312163907219 44392195715571468245860829)
  ·
    refine ⟨16647073393339300592197811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44392195715571468245860829 16647073393339300592197811)
    ·
      refine ⟨24970610090008950888296717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16647073393339300592197811 24970610090008950888296717)
      ·
        refine ⟨9363978783753356583111269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24970610090008950888296717 9363978783753356583111269)
        ·
          refine ⟨1755746021953754359333363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9363978783753356583111269 1755746021953754359333363)
          ·
            refine ⟨2633619032930631539000045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755746021953754359333363 2633619032930631539000045)
            ·
              refine ⟨987607137348986827125017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2633619032930631539000045 987607137348986827125017)
              ·
                refine ⟨740705353011740120343763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 987607137348986827125017 740705353011740120343763)
                ·
                  refine ⟨1111058029517610180515645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740705353011740120343763 1111058029517610180515645)
                  ·
                    refine ⟨416646761069103817693367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1111058029517610180515645 416646761069103817693367)
                    ·
                      rfl

theorem cell22_1217125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_1217125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217125 prefixEnd_1217125 := by exact prefixLift 1217125
  have htrace : WordTrace (prefixWord ++ tailWord_1217125) baseStart_1217125 baseEnd_1217125 := by
    simpa [prefixWord, tailWord_1217125, baseEnd_1217125] using wordTrace_append hprefix tailTrace_1217125
  have hstable : (prefixWord ++ tailWord_1217125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217125).length < 2 ^ (prefixWord ++ tailWord_1217125).sum := by decide
  have hdescent : baseEnd_1217125 < baseStart_1217125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217138 : List Nat := [3, 2, 1, 2, 4, 2, 2, 1, 5]
def baseStart_1217138 : Nat := 118140960795 + 1217138 * 2 ^ 59
def prefixEnd_1217138 : Nat := 4983230072969 + 3 ^ 40 * 1217138 * 2
def baseEnd_1217138 : Nat := 138883737078258705706109

theorem tailTrace_1217138 : CollatzResearch.WordTrace tailWord_1217138 prefixEnd_1217138 138883737078258705706109 := by
  unfold tailWord_1217138
  simp only [CollatzResearch.WordTrace]
  refine ⟨11098167466131092866521017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29595113243016247644056045 11098167466131092866521017)
  ·
    refine ⟨8323625599598319649890763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11098167466131092866521017 8323625599598319649890763)
    ·
      refine ⟨12485438399397479474836145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8323625599598319649890763 12485438399397479474836145)
      ·
        refine ⟨9364078799548109606127109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12485438399397479474836145 9364078799548109606127109)
        ·
          refine ⟨1755764774915270551148833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9364078799548109606127109 1755764774915270551148833)
          ·
            refine ⟨1316823581186452913361625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1755764774915270551148833 1316823581186452913361625)
            ·
              refine ⟨987617685889839685021219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1316823581186452913361625 987617685889839685021219)
              ·
                refine ⟨1481426528834759527531829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987617685889839685021219 1481426528834759527531829)
                ·
                  refine ⟨138883737078258705706109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1481426528834759527531829 138883737078258705706109)
                  ·
                    rfl

theorem cell22_1217138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_1217138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217138 prefixEnd_1217138 := by exact prefixLift 1217138
  have htrace : WordTrace (prefixWord ++ tailWord_1217138) baseStart_1217138 baseEnd_1217138 := by
    simpa [prefixWord, tailWord_1217138, baseEnd_1217138] using wordTrace_append hprefix tailTrace_1217138
  have hstable : (prefixWord ++ tailWord_1217138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217138).length < 2 ^ (prefixWord ++ tailWord_1217138).sum := by decide
  have hdescent : baseEnd_1217138 < baseStart_1217138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217164 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 4, 3]
def baseStart_1217164 : Nat := 118140960795 + 1217164 * 2 ^ 59
def prefixEnd_1217164 : Nat := 4983230072969 + 3 ^ 40 * 1217164 * 2
def baseEnd_1217164 : Nat := 416660111566120715968247

theorem tailTrace_1217164 : CollatzResearch.WordTrace tailWord_1217164 prefixEnd_1217164 416660111566120715968247 := by
  unfold tailWord_1217164
  simp only [CollatzResearch.WordTrace]
  refine ⟨22196809081215088953265273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29595745441620118604353697 22196809081215088953265273)
  ·
    refine ⟨16647606810911316714948955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22196809081215088953265273 16647606810911316714948955)
    ·
      refine ⟨24971410216366975072423433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16647606810911316714948955 24971410216366975072423433)
      ·
        refine ⟨18728557662275231304317575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24971410216366975072423433 18728557662275231304317575)
        ·
          refine ⟨28092836493412846956476363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18728557662275231304317575 28092836493412846956476363)
          ·
            refine ⟨42139254740119270434714545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28092836493412846956476363 42139254740119270434714545)
            ·
              refine ⟨31604441055089452826035909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42139254740119270434714545 31604441055089452826035909)
              ·
                refine ⟨5925832697829272404881733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31604441055089452826035909 5925832697829272404881733)
                ·
                  refine ⟨1111093630842988575915325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5925832697829272404881733 1111093630842988575915325)
                  ·
                    refine ⟨416660111566120715968247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1111093630842988575915325 416660111566120715968247)
                    ·
                      rfl

theorem cell22_1217164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_1217164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217164 prefixEnd_1217164 := by exact prefixLift 1217164
  have htrace : WordTrace (prefixWord ++ tailWord_1217164) baseStart_1217164 baseEnd_1217164 := by
    simpa [prefixWord, tailWord_1217164, baseEnd_1217164] using wordTrace_append hprefix tailTrace_1217164
  have hstable : (prefixWord ++ tailWord_1217164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217164).length < 2 ^ (prefixWord ++ tailWord_1217164).sum := by decide
  have hdescent : baseEnd_1217164 < baseStart_1217164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217166 : List Nat := [4, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_1217166 : Nat := 118140960795 + 1217166 * 2 ^ 59
def prefixEnd_1217166 : Nat := 4983230072969 + 3 ^ 40 * 1217166 * 2
def baseEnd_1217166 : Nat := 138886932068997792472747

theorem tailTrace_1217166 : CollatzResearch.WordTrace tailWord_1217166 prefixEnd_1217166 138886932068997792472747 := by
  unfold tailWord_1217166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5549211388552866531012919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29595794072281954832068901 5549211388552866531012919)
  ·
    refine ⟨8323817082829299796519379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5549211388552866531012919 8323817082829299796519379)
    ·
      refine ⟨12485725624243949694779069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8323817082829299796519379 12485725624243949694779069)
      ·
        refine ⟨4682147109091481135542151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12485725624243949694779069 4682147109091481135542151)
        ·
          refine ⟨7023220663637221703313227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4682147109091481135542151 7023220663637221703313227)
          ·
            refine ⟨10534830995455832554969841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7023220663637221703313227 10534830995455832554969841)
            ·
              refine ⟨7901123246591874416227381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10534830995455832554969841 7901123246591874416227381)
              ·
                refine ⟨740730304367988226521317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7901123246591874416227381 740730304367988226521317)
                ·
                  refine ⟨138886932068997792472747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 740730304367988226521317 138886932068997792472747)
                  ·
                    rfl

theorem cell22_1217166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_1217166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217166 prefixEnd_1217166 := by exact prefixLift 1217166
  have htrace : WordTrace (prefixWord ++ tailWord_1217166) baseStart_1217166 baseEnd_1217166 := by
    simpa [prefixWord, tailWord_1217166, baseEnd_1217166] using wordTrace_append hprefix tailTrace_1217166
  have hstable : (prefixWord ++ tailWord_1217166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217166).length < 2 ^ (prefixWord ++ tailWord_1217166).sum := by decide
  have hdescent : baseEnd_1217166 < baseStart_1217166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217181 : List Nat := [1, 4, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_1217181 : Nat := 118140960795 + 1217181 * 2 ^ 59
def prefixEnd_1217181 : Nat := 4983230072969 + 3 ^ 40 * 1217181 * 2
def baseEnd_1217181 : Nat := 416665931013538338293195

theorem tailTrace_1217181 : CollatzResearch.WordTrace tailWord_1217181 prefixEnd_1217181 416665931013538338293195 := by
  unfold tailWord_1217181
  simp only [CollatzResearch.WordTrace]
  refine ⟨44394238203368589809899397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29596158802245726539932931 44394238203368589809899397)
  ·
    refine ⟨8323919663131610589356137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44394238203368589809899397 8323919663131610589356137)
    ·
      refine ⟨6242939747348707942017103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8323919663131610589356137 6242939747348707942017103)
      ·
        refine ⟨9364409621023061913025655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6242939747348707942017103 9364409621023061913025655)
        ·
          refine ⟨14046614431534592869538483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9364409621023061913025655 14046614431534592869538483)
          ·
            refine ⟨21069921647301889304307725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14046614431534592869538483 21069921647301889304307725)
            ·
              refine ⟨7901220617738208489115397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21069921647301889304307725 7901220617738208489115397)
              ·
                refine ⟨1481478865825914091709137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7901220617738208489115397 1481478865825914091709137)
                ·
                  refine ⟨1111109149369435568781853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1481478865825914091709137 1111109149369435568781853)
                  ·
                    refine ⟨416665931013538338293195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1111109149369435568781853 416665931013538338293195)
                    ·
                      rfl

theorem cell22_1217181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_1217181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217181 prefixEnd_1217181 := by exact prefixLift 1217181
  have htrace : WordTrace (prefixWord ++ tailWord_1217181) baseStart_1217181 baseEnd_1217181 := by
    simpa [prefixWord, tailWord_1217181, baseEnd_1217181] using wordTrace_append hprefix tailTrace_1217181
  have hstable : (prefixWord ++ tailWord_1217181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217181).length < 2 ^ (prefixWord ++ tailWord_1217181).sum := by decide
  have hdescent : baseEnd_1217181 < baseStart_1217181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217198 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1217198 : Nat := 118140960795 + 1217198 * 2 ^ 59
def prefixEnd_1217198 : Nat := 4983230072969 + 3 ^ 40 * 1217198 * 2
def baseEnd_1217198 : Nat := 416671750460955960618143

theorem tailTrace_1217198 : CollatzResearch.WordTrace tailWord_1217198 prefixEnd_1217198 416671750460955960618143 := by
  unfold tailWord_1217198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5549357280538375214158531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29596572162871334475512165 5549357280538375214158531)
  ·
    refine ⟨8324035920807562821237797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5549357280538375214158531 8324035920807562821237797)
    ·
      refine ⟨1560756735151418028982087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8324035920807562821237797 1560756735151418028982087)
      ·
        refine ⟨2341135102727127043473131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1560756735151418028982087 2341135102727127043473131)
        ·
          refine ⟨3511702654090690565209697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2341135102727127043473131 3511702654090690565209697)
          ·
            refine ⟨2633776990568017923907273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3511702654090690565209697 2633776990568017923907273)
            ·
              refine ⟨1975332742926013442930455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2633776990568017923907273 1975332742926013442930455)
              ·
                refine ⟨2962999114389020164395683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975332742926013442930455 2962999114389020164395683)
                ·
                  refine ⟨4444498671583530246593525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2962999114389020164395683 4444498671583530246593525)
                  ·
                    refine ⟨416671750460955960618143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4444498671583530246593525 416671750460955960618143)
                    ·
                      rfl

theorem cell22_1217198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1217198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217198 prefixEnd_1217198 := by exact prefixLift 1217198
  have htrace : WordTrace (prefixWord ++ tailWord_1217198) baseStart_1217198 baseEnd_1217198 := by
    simpa [prefixWord, tailWord_1217198, baseEnd_1217198] using wordTrace_append hprefix tailTrace_1217198
  have hstable : (prefixWord ++ tailWord_1217198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217198).length < 2 ^ (prefixWord ++ tailWord_1217198).sum := by decide
  have hdescent : baseEnd_1217198 < baseStart_1217198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217239 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 7]
def baseStart_1217239 : Nat := 118140960795 + 1217239 * 2 ^ 59
def prefixEnd_1217239 : Nat := 4983230072969 + 3 ^ 40 * 1217239 * 2
def baseEnd_1217239 : Nat := 138895261866281840114339

theorem tailTrace_1217239 : CollatzResearch.WordTrace tailWord_1217239 prefixEnd_1217239 138895261866281840114339 := by
  unfold tailWord_1217239
  simp only [CollatzResearch.WordTrace]
  refine ⟨44396353637158465715510771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29597569091438977143673847 44396353637158465715510771)
  ·
    refine ⟨66594530455737698573266157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44396353637158465715510771 66594530455737698573266157)
    ·
      refine ⟨24972948920901636964974809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66594530455737698573266157 24972948920901636964974809)
      ·
        refine ⟨18729711690676227723731107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24972948920901636964974809 18729711690676227723731107)
        ·
          refine ⟨28094567536014341585596661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18729711690676227723731107 28094567536014341585596661)
          ·
            refine ⟨2633865706501344523649687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28094567536014341585596661 2633865706501344523649687)
            ·
              refine ⟨3950798559752016785474531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633865706501344523649687 3950798559752016785474531)
              ·
                refine ⟨5926197839628025178211797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3950798559752016785474531 5926197839628025178211797)
                ·
                  refine ⟨138895261866281840114339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5926197839628025178211797 138895261866281840114339)
                  ·
                    rfl

theorem cell22_1217239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 7].length) (baseStart_1217239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217239 prefixEnd_1217239 := by exact prefixLift 1217239
  have htrace : WordTrace (prefixWord ++ tailWord_1217239) baseStart_1217239 baseEnd_1217239 := by
    simpa [prefixWord, tailWord_1217239, baseEnd_1217239] using wordTrace_append hprefix tailTrace_1217239
  have hstable : (prefixWord ++ tailWord_1217239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217239).length < 2 ^ (prefixWord ++ tailWord_1217239).sum := by decide
  have hdescent : baseEnd_1217239 < baseStart_1217239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217329 : List Nat := [1, 2, 2, 3, 2, 1, 1, 10]
def baseStart_1217329 : Nat := 118140960795 + 1217329 * 2 ^ 59
def prefixEnd_1217329 : Nat := 4983230072969 + 3 ^ 40 * 1217329 * 2
def baseEnd_1217329 : Nat := 46301843826457253954749

theorem tailTrace_1217329 : CollatzResearch.WordTrace tailWord_1217329 prefixEnd_1217329 46301843826457253954749 := by
  unfold tailWord_1217329
  simp only [CollatzResearch.WordTrace]
  refine ⟨44399636206832411086287041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29599757471221607390858027 44399636206832411086287041)
  ·
    refine ⟨33299727155124308314715281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44399636206832411086287041 33299727155124308314715281)
    ·
      refine ⟨24974795366343231236036461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33299727155124308314715281 24974795366343231236036461)
      ·
        refine ⟨9365548262378711713513673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24974795366343231236036461 9365548262378711713513673)
        ·
          refine ⟨7024161196784033785135255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9365548262378711713513673 7024161196784033785135255)
          ·
            refine ⟨10536241795176050677702883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7024161196784033785135255 10536241795176050677702883)
            ·
              refine ⟨15804362692764076016554325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10536241795176050677702883 15804362692764076016554325)
              ·
                refine ⟨46301843826457253954749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15804362692764076016554325 46301843826457253954749)
                ·
                  rfl

theorem cell22_1217329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 10].length) (baseStart_1217329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217329 prefixEnd_1217329 := by exact prefixLift 1217329
  have htrace : WordTrace (prefixWord ++ tailWord_1217329) baseStart_1217329 baseEnd_1217329 := by
    simpa [prefixWord, tailWord_1217329, baseEnd_1217329] using wordTrace_append hprefix tailTrace_1217329
  have hstable : (prefixWord ++ tailWord_1217329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217329).length < 2 ^ (prefixWord ++ tailWord_1217329).sum := by decide
  have hdescent : baseEnd_1217329 < baseStart_1217329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217331 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 2, 4]
def baseStart_1217331 : Nat := 118140960795 + 1217331 * 2 ^ 59
def prefixEnd_1217331 : Nat := 4983230072969 + 3 ^ 40 * 1217331 * 2
def baseEnd_1217331 : Nat := 416717279078987947042735

theorem tailTrace_1217331 : CollatzResearch.WordTrace tailWord_1217331 prefixEnd_1217331 416717279078987947042735 := by
  unfold tailWord_1217331
  simp only [CollatzResearch.WordTrace]
  refine ⟨44399709152825165427859847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29599806101883443618573231 44399709152825165427859847)
  ·
    refine ⟨66599563729237748141789771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44399709152825165427859847 66599563729237748141789771)
    ·
      refine ⟨99899345593856622212684657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66599563729237748141789771 99899345593856622212684657)
      ·
        refine ⟨74924509195392466659513493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99899345593856622212684657 74924509195392466659513493)
        ·
          refine ⟨3512086368534021874664695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74924509195392466659513493 3512086368534021874664695)
          ·
            refine ⟨5268129552801032811997043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3512086368534021874664695 5268129552801032811997043)
            ·
              refine ⟨7902194329201549217995565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5268129552801032811997043 7902194329201549217995565)
              ·
                refine ⟨2963322873450580956748337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7902194329201549217995565 2963322873450580956748337)
                ·
                  refine ⟨2222492155087935717561253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2963322873450580956748337 2222492155087935717561253)
                  ·
                    refine ⟨416717279078987947042735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2222492155087935717561253 416717279078987947042735)
                    ·
                      rfl

theorem cell22_1217331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 4].length) (baseStart_1217331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217331 prefixEnd_1217331 := by exact prefixLift 1217331
  have htrace : WordTrace (prefixWord ++ tailWord_1217331) baseStart_1217331 baseEnd_1217331 := by
    simpa [prefixWord, tailWord_1217331, baseEnd_1217331] using wordTrace_append hprefix tailTrace_1217331
  have hstable : (prefixWord ++ tailWord_1217331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217331).length < 2 ^ (prefixWord ++ tailWord_1217331).sum := by decide
  have hdescent : baseEnd_1217331 < baseStart_1217331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217543 : List Nat := [1, 1, 4, 3, 1, 1, 1, 5, 5]
def baseStart_1217543 : Nat := 118140960795 + 1217543 * 2 ^ 59
def prefixEnd_1217543 : Nat := 4983230072969 + 3 ^ 40 * 1217543 * 2
def baseEnd_1217543 : Nat := 138929950337163353580695

theorem tailTrace_1217543 : CollatzResearch.WordTrace tailWord_1217543 prefixEnd_1217543 138929950337163353580695 := by
  unfold tailWord_1217543
  simp only [CollatzResearch.WordTrace]
  refine ⟨44407441428057125634577283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29604960952038083756384855 44407441428057125634577283)
  ·
    refine ⟨66611162142085688451865925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44407441428057125634577283 66611162142085688451865925)
    ·
      refine ⟨12489592901641066584724861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66611162142085688451865925 12489592901641066584724861)
      ·
        refine ⟨4683597338115399969271823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12489592901641066584724861 4683597338115399969271823)
        ·
          refine ⟨7025396007173099953907735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4683597338115399969271823 7025396007173099953907735)
          ·
            refine ⟨10538094010759649930861603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7025396007173099953907735 10538094010759649930861603)
            ·
              refine ⟨15807141016139474896292405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10538094010759649930861603 15807141016139474896292405)
              ·
                refine ⟨1481919470263075771527413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15807141016139474896292405 1481919470263075771527413)
                ·
                  refine ⟨138929950337163353580695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1481919470263075771527413 138929950337163353580695)
                  ·
                    rfl

theorem cell22_1217543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 5].length) (baseStart_1217543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217543 prefixEnd_1217543 := by exact prefixLift 1217543
  have htrace : WordTrace (prefixWord ++ tailWord_1217543) baseStart_1217543 baseEnd_1217543 := by
    simpa [prefixWord, tailWord_1217543, baseEnd_1217543] using wordTrace_append hprefix tailTrace_1217543
  have hstable : (prefixWord ++ tailWord_1217543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217543).length < 2 ^ (prefixWord ++ tailWord_1217543).sum := by decide
  have hdescent : baseEnd_1217543 < baseStart_1217543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217564 : List Nat := [2, 2, 3, 1, 4, 1, 2, 3, 1, 3]
def baseStart_1217564 : Nat := 118140960795 + 1217564 * 2 ^ 59
def prefixEnd_1217564 : Nat := 4983230072969 + 3 ^ 40 * 1217564 * 2
def baseEnd_1217564 : Nat := 416797039740653005967021

theorem tailTrace_1217564 : CollatzResearch.WordTrace tailWord_1217564 prefixEnd_1217564 416797039740653005967021 := by
  unfold tailWord_1217564
  simp only [CollatzResearch.WordTrace]
  refine ⟨22204103680490523110545873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29605471573987364147394497 22204103680490523110545873)
  ·
    refine ⟨16653077760367892332909405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22204103680490523110545873 16653077760367892332909405)
    ·
      refine ⟨6244904160137959624841027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16653077760367892332909405 6244904160137959624841027)
      ·
        refine ⟨9367356240206939437261541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6244904160137959624841027 9367356240206939437261541)
        ·
          refine ⟨1756379295038801144486539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9367356240206939437261541 1756379295038801144486539)
          ·
            refine ⟨2634568942558201716729809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756379295038801144486539 2634568942558201716729809)
            ·
              refine ⟨1975926706918651287547357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2634568942558201716729809 1975926706918651287547357)
              ·
                refine ⟨740972515094494232830259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1975926706918651287547357 740972515094494232830259)
                ·
                  refine ⟨1111458772641741349245389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740972515094494232830259 1111458772641741349245389)
                  ·
                    refine ⟨416797039740653005967021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1111458772641741349245389 416797039740653005967021)
                    ·
                      rfl

theorem cell22_1217564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_1217564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217564 prefixEnd_1217564 := by exact prefixLift 1217564
  have htrace : WordTrace (prefixWord ++ tailWord_1217564) baseStart_1217564 baseEnd_1217564 := by
    simpa [prefixWord, tailWord_1217564, baseEnd_1217564] using wordTrace_append hprefix tailTrace_1217564
  have hstable : (prefixWord ++ tailWord_1217564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217564).length < 2 ^ (prefixWord ++ tailWord_1217564).sum := by decide
  have hdescent : baseEnd_1217564 < baseStart_1217564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217575 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1217575 : Nat := 118140960795 + 1217575 * 2 ^ 59
def prefixEnd_1217575 : Nat := 4983230072969 + 3 ^ 40 * 1217575 * 2
def baseEnd_1217575 : Nat := 416800805265452643941987

theorem tailTrace_1217575 : CollatzResearch.WordTrace tailWord_1217575 prefixEnd_1217575 416800805265452643941987 := by
  unfold tailWord_1217575
  simp only [CollatzResearch.WordTrace]
  refine ⟨44408608563941195099742179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29605739042627463399828119 44408608563941195099742179)
  ·
    refine ⟨66612912845911792649613269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44408608563941195099742179 66612912845911792649613269)
    ·
      refine ⟨1561240144826057640225311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 66612912845911792649613269 1561240144826057640225311)
      ·
        refine ⟨2341860217239086460337967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1561240144826057640225311 2341860217239086460337967)
        ·
          refine ⟨3512790325858629690506951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2341860217239086460337967 3512790325858629690506951)
          ·
            refine ⟨5269185488787944535760427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3512790325858629690506951 5269185488787944535760427)
            ·
              refine ⟨7903778233181916803640641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5269185488787944535760427 7903778233181916803640641)
              ·
                refine ⟨5927833674886437602730481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7903778233181916803640641 5927833674886437602730481)
                ·
                  refine ⟨4445875256164828202047861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5927833674886437602730481 4445875256164828202047861)
                  ·
                    refine ⟨416800805265452643941987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4445875256164828202047861 416800805265452643941987)
                    ·
                      rfl

theorem cell22_1217575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1217575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217575 prefixEnd_1217575 := by exact prefixLift 1217575
  have htrace : WordTrace (prefixWord ++ tailWord_1217575) baseStart_1217575 baseEnd_1217575 := by
    simpa [prefixWord, tailWord_1217575, baseEnd_1217575] using wordTrace_append hprefix tailTrace_1217575
  have hstable : (prefixWord ++ tailWord_1217575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217575).length < 2 ^ (prefixWord ++ tailWord_1217575).sum := by decide
  have hdescent : baseEnd_1217575 < baseStart_1217575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217620 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_1217620 : Nat := 118140960795 + 1217620 * 2 ^ 59
def prefixEnd_1217620 : Nat := 4983230072969 + 3 ^ 40 * 1217620 * 2
def baseEnd_1217620 : Nat := 416816209685087526566849

theorem tailTrace_1217620 : CollatzResearch.WordTrace tailWord_1217620 prefixEnd_1217620 416816209685087526566849 := by
  unfold tailWord_1217620
  simp only [CollatzResearch.WordTrace]
  refine ⟨22205124924389083892565157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29606833232518778523420209 22205124924389083892565157)
  ·
    refine ⟨4163460923322953229855967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22205124924389083892565157 4163460923322953229855967)
    ·
      refine ⟨6245191384984429844783951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4163460923322953229855967 6245191384984429844783951)
      ·
        refine ⟨9367787077476644767175927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6245191384984429844783951 9367787077476644767175927)
        ·
          refine ⟨14051680616214967150763891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9367787077476644767175927 14051680616214967150763891)
          ·
            refine ⟨21077520924322450726145837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14051680616214967150763891 21077520924322450726145837)
            ·
              refine ⟨7904070346620919022304689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21077520924322450726145837 7904070346620919022304689)
              ·
                refine ⟨5928052759965689266728517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7904070346620919022304689 5928052759965689266728517)
                ·
                  refine ⟨1111509892493566737511597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5928052759965689266728517 1111509892493566737511597)
                  ·
                    refine ⟨416816209685087526566849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1111509892493566737511597 416816209685087526566849)
                    ·
                      rfl

theorem cell22_1217620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_1217620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217620 prefixEnd_1217620 := by exact prefixLift 1217620
  have htrace : WordTrace (prefixWord ++ tailWord_1217620) baseStart_1217620 baseEnd_1217620 := by
    simpa [prefixWord, tailWord_1217620, baseEnd_1217620] using wordTrace_append hprefix tailTrace_1217620
  have hstable : (prefixWord ++ tailWord_1217620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217620).length < 2 ^ (prefixWord ++ tailWord_1217620).sum := by decide
  have hdescent : baseEnd_1217620 < baseStart_1217620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217725 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_1217725 : Nat := 118140960795 + 1217725 * 2 ^ 59
def prefixEnd_1217725 : Nat := 4983230072969 + 3 ^ 40 * 1217725 * 2
def baseEnd_1217725 : Nat := 416852153330902252691527

theorem tailTrace_1217725 : CollatzResearch.WordTrace tailWord_1217725 prefixEnd_1217725 416852153330902252691527 := by
  unfold tailWord_1217725
  simp only [CollatzResearch.WordTrace]
  refine ⟨44414079513397770717702629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29609386342265180478468419 44414079513397770717702629)
  ·
    refine ⟨8327639908762082009569243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44414079513397770717702629 8327639908762082009569243)
    ·
      refine ⟨12491459863143123014353865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8327639908762082009569243 12491459863143123014353865)
      ·
        refine ⟨9368594897357342260765399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12491459863143123014353865 9368594897357342260765399)
        ·
          refine ⟨14052892346036013391148099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9368594897357342260765399 14052892346036013391148099)
          ·
            refine ⟨21079338519054020086722149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14052892346036013391148099 21079338519054020086722149)
            ·
              refine ⟨3952375972322628766260403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21079338519054020086722149 3952375972322628766260403)
              ·
                refine ⟨5928563958483943149390605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3952375972322628766260403 5928563958483943149390605)
                ·
                  refine ⟨2223211484431478681021477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5928563958483943149390605 2223211484431478681021477)
                  ·
                    refine ⟨416852153330902252691527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2223211484431478681021477 416852153330902252691527)
                    ·
                      rfl

theorem cell22_1217725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_1217725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217725 prefixEnd_1217725 := by exact prefixLift 1217725
  have htrace : WordTrace (prefixWord ++ tailWord_1217725) baseStart_1217725 baseEnd_1217725 := by
    simpa [prefixWord, tailWord_1217725, baseEnd_1217725] using wordTrace_append hprefix tailTrace_1217725
  have hstable : (prefixWord ++ tailWord_1217725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217725).length < 2 ^ (prefixWord ++ tailWord_1217725).sum := by decide
  have hdescent : baseEnd_1217725 < baseStart_1217725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217770 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_1217770 : Nat := 118140960795 + 1217770 * 2 ^ 59
def prefixEnd_1217770 : Nat := 4983230072969 + 3 ^ 40 * 1217770 * 2
def baseEnd_1217770 : Nat := 416867557750537135316389

theorem tailTrace_1217770 : CollatzResearch.WordTrace tailWord_1217770 prefixEnd_1217770 416867557750537135316389 := by
  unfold tailWord_1217770
  simp only [CollatzResearch.WordTrace]
  refine ⟨11103930199558685850772691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29610480532156495602060509 11103930199558685850772691)
  ·
    refine ⟨16655895299338028776159037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11103930199558685850772691 16655895299338028776159037)
    ·
      refine ⟨6245960737251760791059639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16655895299338028776159037 6245960737251760791059639)
      ·
        refine ⟨9368941105877641186589459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6245960737251760791059639 9368941105877641186589459)
        ·
          refine ⟨14053411658816461779884189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9368941105877641186589459 14053411658816461779884189)
          ·
            refine ⟨5270029372056173167456571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14053411658816461779884189 5270029372056173167456571)
            ·
              refine ⟨7905044058084259751184857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5270029372056173167456571 7905044058084259751184857)
              ·
                refine ⟨5928783043563194813388643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7905044058084259751184857 5928783043563194813388643)
                ·
                  refine ⟨8893174565344792220082965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5928783043563194813388643 8893174565344792220082965)
                  ·
                    refine ⟨416867557750537135316389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8893174565344792220082965 416867557750537135316389)
                    ·
                      rfl

theorem cell22_1217770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_1217770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217770 prefixEnd_1217770 := by exact prefixLift 1217770
  have htrace : WordTrace (prefixWord ++ tailWord_1217770) baseStart_1217770 baseEnd_1217770 := by
    simpa [prefixWord, tailWord_1217770, baseEnd_1217770] using wordTrace_append hprefix tailTrace_1217770
  have hstable : (prefixWord ++ tailWord_1217770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217770).length < 2 ^ (prefixWord ++ tailWord_1217770).sum := by decide
  have hdescent : baseEnd_1217770 < baseStart_1217770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217772 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 1, 5]
def baseStart_1217772 : Nat := 118140960795 + 1217772 * 2 ^ 59
def prefixEnd_1217772 : Nat := 4983230072969 + 3 ^ 40 * 1217772 * 2
def baseEnd_1217772 : Nat := 416868242391409796766383

theorem tailTrace_1217772 : CollatzResearch.WordTrace tailWord_1217772 prefixEnd_1217772 416868242391409796766383 := by
  unfold tailWord_1217772
  simp only [CollatzResearch.WordTrace]
  refine ⟨22207896872113748872331785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29610529162818331829775713 22207896872113748872331785)
  ·
    refine ⟨16655922654085311654248839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22207896872113748872331785 16655922654085311654248839)
    ·
      refine ⟨24983883981127967481373259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16655922654085311654248839 24983883981127967481373259)
      ·
        refine ⟨37475825971691951222059889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24983883981127967481373259 37475825971691951222059889)
        ·
          refine ⟨28106869478768963416544917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37475825971691951222059889 28106869478768963416544917)
          ·
            refine ⟨1317509506817295160150543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28106869478768963416544917 1317509506817295160150543)
            ·
              refine ⟨1976264260225942740225815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1317509506817295160150543 1976264260225942740225815)
              ·
                refine ⟨2964396390338914110338723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1976264260225942740225815 2964396390338914110338723)
                ·
                  refine ⟨4446594585508371165508085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964396390338914110338723 4446594585508371165508085)
                  ·
                    refine ⟨416868242391409796766383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4446594585508371165508085 416868242391409796766383)
                    ·
                      rfl

theorem cell22_1217772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_1217772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217772 prefixEnd_1217772 := by exact prefixLift 1217772
  have htrace : WordTrace (prefixWord ++ tailWord_1217772) baseStart_1217772 baseEnd_1217772 := by
    simpa [prefixWord, tailWord_1217772, baseEnd_1217772] using wordTrace_append hprefix tailTrace_1217772
  have hstable : (prefixWord ++ tailWord_1217772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217772).length < 2 ^ (prefixWord ++ tailWord_1217772).sum := by decide
  have hdescent : baseEnd_1217772 < baseStart_1217772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217815 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 2, 6]
def baseStart_1217815 : Nat := 118140960795 + 1217815 * 2 ^ 59
def prefixEnd_1217815 : Nat := 4983230072969 + 3 ^ 40 * 1217815 * 2
def baseEnd_1217815 : Nat := 416882962170172017941251

theorem tailTrace_1217815 : CollatzResearch.WordTrace tailWord_1217815 prefixEnd_1217815 416882962170172017941251 := by
  unfold tailWord_1217815
  simp only [CollatzResearch.WordTrace]
  refine ⟨44417362083071716088478899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29611574722047810725652599 44417362083071716088478899)
  ·
    refine ⟨66626043124607574132718349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44417362083071716088478899 66626043124607574132718349)
    ·
      refine ⟨24984766171727840299769381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66626043124607574132718349 24984766171727840299769381)
      ·
        refine ⟨4684643657198970056206759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24984766171727840299769381 4684643657198970056206759)
        ·
          refine ⟨7026965485798455084310139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4684643657198970056206759 7026965485798455084310139)
          ·
            refine ⟨10540448228697682626465209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7026965485798455084310139 10540448228697682626465209)
            ·
              refine ⟨7905336171523261969848907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10540448228697682626465209 7905336171523261969848907)
              ·
                refine ⟨11858004257284892954773361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7905336171523261969848907 11858004257284892954773361)
                ·
                  refine ⟨8893503192963669716080021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11858004257284892954773361 8893503192963669716080021)
                  ·
                    refine ⟨416882962170172017941251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8893503192963669716080021 416882962170172017941251)
                    ·
                      rfl

theorem cell22_1217815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_1217815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217815 prefixEnd_1217815 := by exact prefixLift 1217815
  have htrace : WordTrace (prefixWord ++ tailWord_1217815) baseStart_1217815 baseEnd_1217815 := by
    simpa [prefixWord, tailWord_1217815, baseEnd_1217815] using wordTrace_append hprefix tailTrace_1217815
  have hstable : (prefixWord ++ tailWord_1217815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217815).length < 2 ^ (prefixWord ++ tailWord_1217815).sum := by decide
  have hdescent : baseEnd_1217815 < baseStart_1217815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217823 : List Nat := [1, 1, 2, 4, 5, 1, 2, 1, 2, 3]
def baseStart_1217823 : Nat := 118140960795 + 1217823 * 2 ^ 59
def prefixEnd_1217823 : Nat := 4983230072969 + 3 ^ 40 * 1217823 * 2
def baseEnd_1217823 : Nat := 416885700733662663741227

theorem tailTrace_1217823 : CollatzResearch.WordTrace tailWord_1217823 prefixEnd_1217823 416885700733662663741227 := by
  unfold tailWord_1217823
  simp only [CollatzResearch.WordTrace]
  refine ⟨44417653867042733454770123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29611769244695155636513415 44417653867042733454770123)
  ·
    refine ⟨66626480800564100182155185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44417653867042733454770123 66626480800564100182155185)
    ·
      refine ⟨49969860600423075136616389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66626480800564100182155185 49969860600423075136616389)
      ·
        refine ⟨9369348862579326588115573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49969860600423075136616389 9369348862579326588115573)
        ·
          refine ⟨878376455866811867635835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9369348862579326588115573 878376455866811867635835)
          ·
            refine ⟨1317564683800217801453753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878376455866811867635835 1317564683800217801453753)
            ·
              refine ⟨988173512850163351090315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317564683800217801453753 988173512850163351090315)
              ·
                refine ⟨1482260269275245026635473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988173512850163351090315 1482260269275245026635473)
                ·
                  refine ⟨1111695201956433769976605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1482260269275245026635473 1111695201956433769976605)
                  ·
                    refine ⟨416885700733662663741227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1111695201956433769976605 416885700733662663741227)
                    ·
                      rfl

theorem cell22_1217823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 2, 3].length) (baseStart_1217823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217823 prefixEnd_1217823 := by exact prefixLift 1217823
  have htrace : WordTrace (prefixWord ++ tailWord_1217823) baseStart_1217823 baseEnd_1217823 := by
    simpa [prefixWord, tailWord_1217823, baseEnd_1217823] using wordTrace_append hprefix tailTrace_1217823
  have hstable : (prefixWord ++ tailWord_1217823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217823).length < 2 ^ (prefixWord ++ tailWord_1217823).sum := by decide
  have hdescent : baseEnd_1217823 < baseStart_1217823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217868 : List Nat := [2, 2, 1, 3, 2, 4, 2, 2, 1, 3]
def baseStart_1217868 : Nat := 118140960795 + 1217868 * 2 ^ 59
def prefixEnd_1217868 : Nat := 4983230072969 + 3 ^ 40 * 1217868 * 2
def baseEnd_1217868 : Nat := 416901105153297546366089

theorem tailTrace_1217868 : CollatzResearch.WordTrace tailWord_1217868 prefixEnd_1217868 416901105153297546366089 := by
  unfold tailWord_1217868
  simp only [CollatzResearch.WordTrace]
  refine ⟨22209647575939853070079129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29612863434586470760105505 22209647575939853070079129)
  ·
    refine ⟨16657235681954889802559347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22209647575939853070079129 16657235681954889802559347)
    ·
      refine ⟨24985853522932334703839021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16657235681954889802559347 24985853522932334703839021)
      ·
        refine ⟨9369695071099625513939633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24985853522932334703839021 9369695071099625513939633)
        ·
          refine ⟨7027271303324719135454725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9369695071099625513939633 7027271303324719135454725)
          ·
            refine ⟨1317613369373384837897761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7027271303324719135454725 1317613369373384837897761)
            ·
              refine ⟨988210027030038628423321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317613369373384837897761 988210027030038628423321)
              ·
                refine ⟨741157520272528971317491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 988210027030038628423321 741157520272528971317491)
                ·
                  refine ⟨1111736280408793456976237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 741157520272528971317491 1111736280408793456976237)
                  ·
                    refine ⟨416901105153297546366089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1111736280408793456976237 416901105153297546366089)
                    ·
                      rfl

theorem cell22_1217868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_1217868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217868 prefixEnd_1217868 := by exact prefixLift 1217868
  have htrace : WordTrace (prefixWord ++ tailWord_1217868) baseStart_1217868 baseEnd_1217868 := by
    simpa [prefixWord, tailWord_1217868, baseEnd_1217868] using wordTrace_append hprefix tailTrace_1217868
  have hstable : (prefixWord ++ tailWord_1217868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217868).length < 2 ^ (prefixWord ++ tailWord_1217868).sum := by decide
  have hdescent : baseEnd_1217868 < baseStart_1217868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217875 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 6]
def baseStart_1217875 : Nat := 118140960795 + 1217875 * 2 ^ 59
def prefixEnd_1217875 : Nat := 4983230072969 + 3 ^ 40 * 1217875 * 2
def baseEnd_1217875 : Nat := 138967833798783953813689

theorem tailTrace_1217875 : CollatzResearch.WordTrace tailWord_1217875 prefixEnd_1217875 138967833798783953813689 := by
  unfold tailWord_1217875
  simp only [CollatzResearch.WordTrace]
  refine ⟨44419550462854346335663079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29613033641902897557108719 44419550462854346335663079)
  ·
    refine ⟨66629325694281519503494619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44419550462854346335663079 66629325694281519503494619)
    ·
      refine ⟨99943988541422279255241929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66629325694281519503494619 99943988541422279255241929)
      ·
        refine ⟨74957991406066709441431447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99943988541422279255241929 74957991406066709441431447)
        ·
          refine ⟨112436987109100064162147171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74957991406066709441431447 112436987109100064162147171)
          ·
            refine ⟨168655480663650096243220757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112436987109100064162147171 168655480663650096243220757)
            ·
              refine ⟨7905725656108598261400973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 168655480663650096243220757 7905725656108598261400973)
              ·
                refine ⟨2964647121040724348025365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7905725656108598261400973 2964647121040724348025365)
                ·
                  refine ⟨138967833798783953813689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2964647121040724348025365 138967833798783953813689)
                  ·
                    rfl

theorem cell22_1217875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 6].length) (baseStart_1217875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217875 prefixEnd_1217875 := by exact prefixLift 1217875
  have htrace : WordTrace (prefixWord ++ tailWord_1217875) baseStart_1217875 baseEnd_1217875 := by
    simpa [prefixWord, tailWord_1217875, baseEnd_1217875] using wordTrace_append hprefix tailTrace_1217875
  have hstable : (prefixWord ++ tailWord_1217875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217875).length < 2 ^ (prefixWord ++ tailWord_1217875).sum := by decide
  have hdescent : baseEnd_1217875 < baseStart_1217875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217877 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_1217877 : Nat := 118140960795 + 1217877 * 2 ^ 59
def prefixEnd_1217877 : Nat := 4983230072969 + 3 ^ 40 * 1217877 * 2
def baseEnd_1217877 : Nat := 416904186037224522891061

theorem tailTrace_1217877 : CollatzResearch.WordTrace tailWord_1217877 prefixEnd_1217877 416904186037224522891061 := by
  unfold tailWord_1217877
  simp only [CollatzResearch.WordTrace]
  refine ⟨44419623408847100677235885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29613082272564733784823923 44419623408847100677235885)
  ·
    refine ⟨16657358778317662753963457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44419623408847100677235885 16657358778317662753963457)
    ·
      refine ⟨12493019083738247065472593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16657358778317662753963457 12493019083738247065472593)
      ·
        refine ⟨9369764312803685299104445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12493019083738247065472593 9369764312803685299104445)
        ·
          refine ⟨3513661617301381987164167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9369764312803685299104445 3513661617301381987164167)
          ·
            refine ⟨5270492425952072980746251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3513661617301381987164167 5270492425952072980746251)
            ·
              refine ⟨7905738638928109471119377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5270492425952072980746251 7905738638928109471119377)
              ·
                refine ⟨5929303979196082103339533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7905738638928109471119377 5929303979196082103339533)
                ·
                  refine ⟨2223488992198530788752325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5929303979196082103339533 2223488992198530788752325)
                  ·
                    refine ⟨416904186037224522891061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2223488992198530788752325 416904186037224522891061)
                    ·
                      rfl

theorem cell22_1217877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_1217877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217877 prefixEnd_1217877 := by exact prefixLift 1217877
  have htrace : WordTrace (prefixWord ++ tailWord_1217877) baseStart_1217877 baseEnd_1217877 := by
    simpa [prefixWord, tailWord_1217877, baseEnd_1217877] using wordTrace_append hprefix tailTrace_1217877
  have hstable : (prefixWord ++ tailWord_1217877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217877).length < 2 ^ (prefixWord ++ tailWord_1217877).sum := by decide
  have hdescent : baseEnd_1217877 < baseStart_1217877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217892 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 6]
def baseStart_1217892 : Nat := 118140960795 + 1217892 * 2 ^ 59
def prefixEnd_1217892 : Nat := 4983230072969 + 3 ^ 40 * 1217892 * 2
def baseEnd_1217892 : Nat := 138969773614589827922005

theorem tailTrace_1217892 : CollatzResearch.WordTrace tailWord_1217892 prefixEnd_1217892 138969773614589827922005 := by
  unfold tailWord_1217892
  simp only [CollatzResearch.WordTrace]
  refine ⟨22210085251896379119515965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29613447002528505492687953 22210085251896379119515965)
  ·
    refine ⟨8328781969461142169818487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22210085251896379119515965 8328781969461142169818487)
    ·
      refine ⟨12493172954191713254727731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8328781969461142169818487 12493172954191713254727731)
      ·
        refine ⟨18739759431287569882091597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12493172954191713254727731 18739759431287569882091597)
        ·
          refine ⟨7027409786732838705784349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18739759431287569882091597 7027409786732838705784349)
          ·
            refine ⟨2635278670024814514669131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7027409786732838705784349 2635278670024814514669131)
            ·
              refine ⟨3952918005037221772003697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2635278670024814514669131 3952918005037221772003697)
              ·
                refine ⟨2964688503777916329002773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3952918005037221772003697 2964688503777916329002773)
                ·
                  refine ⟨138969773614589827922005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2964688503777916329002773 138969773614589827922005)
                  ·
                    rfl

theorem cell22_1217892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_1217892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217892 prefixEnd_1217892 := by exact prefixLift 1217892
  have htrace : WordTrace (prefixWord ++ tailWord_1217892) baseStart_1217892 baseEnd_1217892 := by
    simpa [prefixWord, tailWord_1217892, baseEnd_1217892] using wordTrace_append hprefix tailTrace_1217892
  have hstable : (prefixWord ++ tailWord_1217892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217892).length < 2 ^ (prefixWord ++ tailWord_1217892).sum := by decide
  have hdescent : baseEnd_1217892 < baseStart_1217892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217924 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_1217924 : Nat := 118140960795 + 1217924 * 2 ^ 59
def prefixEnd_1217924 : Nat := 4983230072969 + 3 ^ 40 * 1217924 * 2
def baseEnd_1217924 : Nat := 416920275097732066965917

theorem tailTrace_1217924 : CollatzResearch.WordTrace tailWord_1217924 prefixEnd_1217924 416920275097732066965917 := by
  unfold tailWord_1217924
  simp only [CollatzResearch.WordTrace]
  refine ⟨22210668819838413852098413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29614225093117885136131217 22210668819838413852098413)
  ·
    refine ⟨8329000807439405194536905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22210668819838413852098413 8329000807439405194536905)
    ·
      refine ⟨6246750605579553895902679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8329000807439405194536905 6246750605579553895902679)
      ·
        refine ⟨9370125908369330843854019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6246750605579553895902679 9370125908369330843854019)
        ·
          refine ⟨14055188862553996265781029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9370125908369330843854019 14055188862553996265781029)
          ·
            refine ⟨2635347911728874299833943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14055188862553996265781029 2635347911728874299833943)
            ·
              refine ⟨3953021867593311449750915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2635347911728874299833943 3953021867593311449750915)
              ·
                refine ⟨5929532801389967174626373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3953021867593311449750915 5929532801389967174626373)
                ·
                  refine ⟨1111787400260618845242445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5929532801389967174626373 1111787400260618845242445)
                  ·
                    refine ⟨416920275097732066965917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1111787400260618845242445 416920275097732066965917)
                    ·
                      rfl

theorem cell22_1217924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_1217924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217924 prefixEnd_1217924 := by exact prefixLift 1217924
  have htrace : WordTrace (prefixWord ++ tailWord_1217924) baseStart_1217924 baseEnd_1217924 := by
    simpa [prefixWord, tailWord_1217924, baseEnd_1217924] using wordTrace_append hprefix tailTrace_1217924
  have hstable : (prefixWord ++ tailWord_1217924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217924).length < 2 ^ (prefixWord ++ tailWord_1217924).sum := by decide
  have hdescent : baseEnd_1217924 < baseStart_1217924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217954 : List Nat := [3, 3, 1, 2, 1, 2, 4, 6]
def baseStart_1217954 : Nat := 118140960795 + 1217954 * 2 ^ 59
def prefixEnd_1217954 : Nat := 4983230072969 + 3 ^ 40 * 1217954 * 2
def baseEnd_1217954 : Nat := 46325616078980220968425

theorem tailTrace_1217954 : CollatzResearch.WordTrace tailWord_1217954 prefixEnd_1217954 46325616078980220968425 := by
  unfold tailWord_1217954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11105607957392035706947229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29614954553045428551859277 11105607957392035706947229)
  ·
    refine ⟨4164602984022013390105211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11105607957392035706947229 4164602984022013390105211)
    ·
      refine ⟨6246904476033020085157817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4164602984022013390105211 6246904476033020085157817)
      ·
        refine ⟨4685178357024765063868363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6246904476033020085157817 4685178357024765063868363)
        ·
          refine ⟨7027767535537147595802545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4685178357024765063868363 7027767535537147595802545)
          ·
            refine ⟨5270825651652860696851909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7027767535537147595802545 5270825651652860696851909)
            ·
              refine ⟨988279809684911380659733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5270825651652860696851909 988279809684911380659733)
              ·
                refine ⟨46325616078980220968425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 988279809684911380659733 46325616078980220968425)
                ·
                  rfl

theorem cell22_1217954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 6].length) (baseStart_1217954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217954 prefixEnd_1217954 := by exact prefixLift 1217954
  have htrace : WordTrace (prefixWord ++ tailWord_1217954) baseStart_1217954 baseEnd_1217954 := by
    simpa [prefixWord, tailWord_1217954, baseEnd_1217954] using wordTrace_append hprefix tailTrace_1217954
  have hstable : (prefixWord ++ tailWord_1217954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217954).length < 2 ^ (prefixWord ++ tailWord_1217954).sum := by decide
  have hdescent : baseEnd_1217954 < baseStart_1217954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217960 : List Nat := [2, 1, 6, 1, 3, 1, 1, 3, 4]
def baseStart_1217960 : Nat := 118140960795 + 1217960 * 2 ^ 59
def prefixEnd_1217960 : Nat := 4983230072969 + 3 ^ 40 * 1217960 * 2
def baseEnd_1217960 : Nat := 138977532877813324355269

theorem tailTrace_1217960 : CollatzResearch.WordTrace tailWord_1217960 prefixEnd_1217960 138977532877813324355269 := by
  unfold tailWord_1217960
  simp only [CollatzResearch.WordTrace]
  refine ⟨22211325333773202926253667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29615100445030937235004889 22211325333773202926253667)
  ·
    refine ⟨33316988000659804389380501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22211325333773202926253667 33316988000659804389380501)
    ·
      refine ⟨1561733812530928330752211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33316988000659804389380501 1561733812530928330752211)
      ·
        refine ⟨2342600718796392496128317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1561733812530928330752211 2342600718796392496128317)
        ·
          refine ⟨878475269548647186048119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2342600718796392496128317 878475269548647186048119)
          ·
            refine ⟨1317712904322970779072179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878475269548647186048119 1317712904322970779072179)
            ·
              refine ⟨1976569356484456168608269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1317712904322970779072179 1976569356484456168608269)
              ·
                refine ⟨741213508681671063228101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1976569356484456168608269 741213508681671063228101)
                ·
                  refine ⟨138977532877813324355269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 741213508681671063228101 138977532877813324355269)
                  ·
                    rfl

theorem cell22_1217960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 4].length) (baseStart_1217960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217960 prefixEnd_1217960 := by exact prefixLift 1217960
  have htrace : WordTrace (prefixWord ++ tailWord_1217960) baseStart_1217960 baseEnd_1217960 := by
    simpa [prefixWord, tailWord_1217960, baseEnd_1217960] using wordTrace_append hprefix tailTrace_1217960
  have hstable : (prefixWord ++ tailWord_1217960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217960).length < 2 ^ (prefixWord ++ tailWord_1217960).sum := by decide
  have hdescent : baseEnd_1217960 < baseStart_1217960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217999 : List Nat := [1, 1, 2, 1, 1, 4, 6, 1, 5]
def baseStart_1217999 : Nat := 118140960795 + 1217999 * 2 ^ 59
def prefixEnd_1217999 : Nat := 4983230072969 + 3 ^ 40 * 1217999 * 2
def baseEnd_1217999 : Nat := 138981983043485623780229

theorem tailTrace_1217999 : CollatzResearch.WordTrace tailWord_1217999 prefixEnd_1217999 138981983043485623780229 := by
  unfold tailWord_1217999
  simp only [CollatzResearch.WordTrace]
  refine ⟨44424073114405115513177051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29616048742936743675451367 44424073114405115513177051)
  ·
    refine ⟨66636109671607673269765577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44424073114405115513177051 66636109671607673269765577)
    ·
      refine ⟨49977082253705754952324183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66636109671607673269765577 49977082253705754952324183)
      ·
        refine ⟨74965623380558632428486275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49977082253705754952324183 74965623380558632428486275)
        ·
          refine ⟨112448435070837948642729413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74965623380558632428486275 112448435070837948642729413)
          ·
            refine ⟨21084081575782115370511765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112448435070837948642729413 21084081575782115370511765)
            ·
              refine ⟨988316323864786657992739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21084081575782115370511765 988316323864786657992739)
              ·
                refine ⟨1482474485797179986989109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988316323864786657992739 1482474485797179986989109)
                ·
                  refine ⟨138981983043485623780229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1482474485797179986989109 138981983043485623780229)
                  ·
                    rfl

theorem cell22_1217999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 5].length) (baseStart_1217999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1217999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1217999 prefixEnd_1217999 := by exact prefixLift 1217999
  have htrace : WordTrace (prefixWord ++ tailWord_1217999) baseStart_1217999 baseEnd_1217999 := by
    simpa [prefixWord, tailWord_1217999, baseEnd_1217999] using wordTrace_append hprefix tailTrace_1217999
  have hstable : (prefixWord ++ tailWord_1217999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217999).length < 2 ^ (prefixWord ++ tailWord_1217999).sum := by decide
  have hdescent : baseEnd_1217999 < baseStart_1217999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218037 : List Nat := [1, 3, 5, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1218037 : Nat := 118140960795 + 1218037 * 2 ^ 59
def prefixEnd_1218037 : Nat := 4983230072969 + 3 ^ 40 * 1218037 * 2
def baseEnd_1218037 : Nat := 416958957307037438890571

theorem tailTrace_1218037 : CollatzResearch.WordTrace tailWord_1218037 prefixEnd_1218037 416958957307037438890571 := by
  unfold tailWord_1218037
  simp only [CollatzResearch.WordTrace]
  refine ⟨44425459088267448003060365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29616972725511632002040243 44425459088267448003060365)
  ·
    refine ⟨16659547158100293001147637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44425459088267448003060365 16659547158100293001147637)
    ·
      refine ⟨1561832546071902468857591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16659547158100293001147637 1561832546071902468857591)
      ·
        refine ⟨2342748819107853703286387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1561832546071902468857591 2342748819107853703286387)
        ·
          refine ⟨3514123228661780554929581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2342748819107853703286387 3514123228661780554929581)
          ·
            refine ⟨1317796210748167708098593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3514123228661780554929581 1317796210748167708098593)
            ·
              refine ⟨988347158061125781073945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317796210748167708098593 988347158061125781073945)
              ·
                refine ⟨741260368545844335805459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 988347158061125781073945 741260368545844335805459)
                ·
                  refine ⟨1111890552818766503708189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 741260368545844335805459 1111890552818766503708189)
                  ·
                    refine ⟨416958957307037438890571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1111890552818766503708189 416958957307037438890571)
                    ·
                      rfl

theorem cell22_1218037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1218037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218037 prefixEnd_1218037 := by exact prefixLift 1218037
  have htrace : WordTrace (prefixWord ++ tailWord_1218037) baseStart_1218037 baseEnd_1218037 := by
    simpa [prefixWord, tailWord_1218037, baseEnd_1218037] using wordTrace_append hprefix tailTrace_1218037
  have hstable : (prefixWord ++ tailWord_1218037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218037).length < 2 ^ (prefixWord ++ tailWord_1218037).sum := by decide
  have hdescent : baseEnd_1218037 < baseStart_1218037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218042 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_1218042 : Nat := 118140960795 + 1218042 * 2 ^ 59
def prefixEnd_1218042 : Nat := 4983230072969 + 3 ^ 40 * 1218042 * 2
def baseEnd_1218042 : Nat := 416960668909219092515555

theorem tailTrace_1218042 : CollatzResearch.WordTrace tailWord_1218042 prefixEnd_1218042 416960668909219092515555 := by
  unfold tailWord_1218042
  simp only [CollatzResearch.WordTrace]
  refine ⟨11106410363312333464248095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29617094302166222571328253 11106410363312333464248095)
  ·
    refine ⟨16659615544968500196372143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11106410363312333464248095 16659615544968500196372143)
    ·
      refine ⟨24989423317452750294558215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16659615544968500196372143 24989423317452750294558215)
      ·
        refine ⟨37484134976179125441837323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24989423317452750294558215 37484134976179125441837323)
        ·
          refine ⟨56226202464268688162755985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37484134976179125441837323 56226202464268688162755985)
          ·
            refine ⟨42169651848201516122066989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56226202464268688162755985 42169651848201516122066989)
            ·
              refine ⟨15813619443075568545775121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42169651848201516122066989 15813619443075568545775121)
              ·
                refine ⟨11860214582306676409331341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15813619443075568545775121 11860214582306676409331341)
                ·
                  refine ⟨4447580468365003653499253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11860214582306676409331341 4447580468365003653499253)
                  ·
                    refine ⟨416960668909219092515555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4447580468365003653499253 416960668909219092515555)
                    ·
                      rfl

theorem cell22_1218042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_1218042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218042 prefixEnd_1218042 := by exact prefixLift 1218042
  have htrace : WordTrace (prefixWord ++ tailWord_1218042) baseStart_1218042 baseEnd_1218042 := by
    simpa [prefixWord, tailWord_1218042, baseEnd_1218042] using wordTrace_append hprefix tailTrace_1218042
  have hstable : (prefixWord ++ tailWord_1218042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218042).length < 2 ^ (prefixWord ++ tailWord_1218042).sum := by decide
  have hdescent : baseEnd_1218042 < baseStart_1218042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218057 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 1, 6]
def baseStart_1218057 : Nat := 118140960795 + 1218057 * 2 ^ 59
def prefixEnd_1218057 : Nat := 4983230072969 + 3 ^ 40 * 1218057 * 2
def baseEnd_1218057 : Nat := 416965803715764053390509

theorem tailTrace_1218057 : CollatzResearch.WordTrace tailWord_1218057 prefixEnd_1218057 416965803715764053390509 := by
  unfold tailWord_1218057
  simp only [CollatzResearch.WordTrace]
  refine ⟨44426188548194991418788425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29617459032129994279192283 44426188548194991418788425)
  ·
    refine ⟨33319641411146243564091319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44426188548194991418788425 33319641411146243564091319)
    ·
      refine ⟨49979462116719365346136979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33319641411146243564091319 49979462116719365346136979)
      ·
        refine ⟨74969193175079048019205469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49979462116719365346136979 74969193175079048019205469)
        ·
          refine ⟨28113447440654643007202051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74969193175079048019205469 28113447440654643007202051)
          ·
            refine ⟨42170171160981964510803077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28113447440654643007202051 42170171160981964510803077)
            ·
              refine ⟨7906907092684118345775577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42170171160981964510803077 7906907092684118345775577)
              ·
                refine ⟨5930180319513088759331683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7906907092684118345775577 5930180319513088759331683)
                ·
                  refine ⟨8895270479269633138997525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5930180319513088759331683 8895270479269633138997525)
                  ·
                    refine ⟨416965803715764053390509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8895270479269633138997525 416965803715764053390509)
                    ·
                      rfl

theorem cell22_1218057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_1218057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218057 prefixEnd_1218057 := by exact prefixLift 1218057
  have htrace : WordTrace (prefixWord ++ tailWord_1218057) baseStart_1218057 baseEnd_1218057 := by
    simpa [prefixWord, tailWord_1218057, baseEnd_1218057] using wordTrace_append hprefix tailTrace_1218057
  have hstable : (prefixWord ++ tailWord_1218057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218057).length < 2 ^ (prefixWord ++ tailWord_1218057).sum := by decide
  have hdescent : baseEnd_1218057 < baseStart_1218057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218213 : List Nat := [1, 3, 1, 2, 1, 2, 6, 2, 4]
def baseStart_1218213 : Nat := 118140960795 + 1218213 * 2 ^ 59
def prefixEnd_1218213 : Nat := 4983230072969 + 3 ^ 40 * 1218213 * 2
def baseEnd_1218213 : Nat := 139006401901277215496677

theorem tailTrace_1218213 : CollatzResearch.WordTrace tailWord_1218213 prefixEnd_1218213 139006401901277215496677 := by
  unfold tailWord_1218213
  simp only [CollatzResearch.WordTrace]
  refine ⟨44431878335629830061467293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29621252223753220040978195 44431878335629830061467293)
  ·
    refine ⟨16661954375861186273050235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44431878335629830061467293 16661954375861186273050235)
    ·
      refine ⟨24992931563791779409575353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16661954375861186273050235 24992931563791779409575353)
      ·
        refine ⟨18744698672843834557181515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24992931563791779409575353 18744698672843834557181515)
        ·
          refine ⟨28117048009265751835772273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18744698672843834557181515 28117048009265751835772273)
          ·
            refine ⟨21087786006949313876829205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28117048009265751835772273 21087786006949313876829205)
            ·
              refine ⟨988489969075749087976369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21087786006949313876829205 988489969075749087976369)
              ·
                refine ⟨741367476806811815982277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 988489969075749087976369 741367476806811815982277)
                ·
                  refine ⟨139006401901277215496677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 741367476806811815982277 139006401901277215496677)
                  ·
                    rfl

theorem cell22_1218213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_1218213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218213 prefixEnd_1218213 := by exact prefixLift 1218213
  have htrace : WordTrace (prefixWord ++ tailWord_1218213) baseStart_1218213 baseEnd_1218213 := by
    simpa [prefixWord, tailWord_1218213, baseEnd_1218213] using wordTrace_append hprefix tailTrace_1218213
  have hstable : (prefixWord ++ tailWord_1218213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218213).length < 2 ^ (prefixWord ++ tailWord_1218213).sum := by decide
  have hdescent : baseEnd_1218213 < baseStart_1218213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218224 : List Nat := [2, 1, 1, 1, 2, 1, 7, 7]
def baseStart_1218224 : Nat := 118140960795 + 1218224 * 2 ^ 59
def prefixEnd_1218224 : Nat := 4983230072969 + 3 ^ 40 * 1218224 * 2
def baseEnd_1218224 : Nat := 46335885692070142718333

theorem tailTrace_1218224 : CollatzResearch.WordTrace tailWord_1218224 prefixEnd_1218224 46335885692070142718333 := by
  unfold tailWord_1218224
  simp only [CollatzResearch.WordTrace]
  refine ⟨22216139769294989470058863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29621519692393319293411817 22216139769294989470058863)
  ·
    refine ⟨33324209653942484205088295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22216139769294989470058863 33324209653942484205088295)
    ·
      refine ⟨49986314480913726307632443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33324209653942484205088295 49986314480913726307632443)
      ·
        refine ⟨74979471721370589461448665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49986314480913726307632443 74979471721370589461448665)
        ·
          refine ⟨56234603791027942096086499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74979471721370589461448665 56234603791027942096086499)
          ·
            refine ⟨84351905686541913144129749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56234603791027942096086499 84351905686541913144129749)
            ·
              refine ⟨1976997789528326089315541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 84351905686541913144129749 1976997789528326089315541)
              ·
                refine ⟨46335885692070142718333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1976997789528326089315541 46335885692070142718333)
                ·
                  rfl

theorem cell22_1218224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 7].length) (baseStart_1218224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218224 prefixEnd_1218224 := by exact prefixLift 1218224
  have htrace : WordTrace (prefixWord ++ tailWord_1218224) baseStart_1218224 baseEnd_1218224 := by
    simpa [prefixWord, tailWord_1218224, baseEnd_1218224] using wordTrace_append hprefix tailTrace_1218224
  have hstable : (prefixWord ++ tailWord_1218224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218224).length < 2 ^ (prefixWord ++ tailWord_1218224).sum := by decide
  have hdescent : baseEnd_1218224 < baseStart_1218224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218262 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1218262 : Nat := 118140960795 + 1218262 * 2 ^ 59
def prefixEnd_1218262 : Nat := 4983230072969 + 3 ^ 40 * 1218262 * 2
def baseEnd_1218262 : Nat := 417035979405211852014881

theorem tailTrace_1218262 : CollatzResearch.WordTrace tailWord_1218262 prefixEnd_1218262 417035979405211852014881 := by
  unfold tailWord_1218262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2777104094528269464375065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29622443674968207620000693 2777104094528269464375065)
  ·
    refine ⟨2082828070896202098281299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2777104094528269464375065 2082828070896202098281299)
    ·
      refine ⟨3124242106344303147421949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2082828070896202098281299 3124242106344303147421949)
      ·
        refine ⟨1171590789879113680283231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3124242106344303147421949 1171590789879113680283231)
        ·
          refine ⟨1757386184818670520424847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171590789879113680283231 1757386184818670520424847)
          ·
            refine ⟨2636079277228005780637271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757386184818670520424847 2636079277228005780637271)
            ·
              refine ⟨3954118915842008670955907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2636079277228005780637271 3954118915842008670955907)
              ·
                refine ⟨5931178373763013006433861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3954118915842008670955907 5931178373763013006433861)
                ·
                  refine ⟨1112095945080564938706349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5931178373763013006433861 1112095945080564938706349)
                  ·
                    refine ⟨417035979405211852014881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1112095945080564938706349 417035979405211852014881)
                    ·
                      rfl

theorem cell22_1218262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1218262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218262 prefixEnd_1218262 := by exact prefixLift 1218262
  have htrace : WordTrace (prefixWord ++ tailWord_1218262) baseStart_1218262 baseEnd_1218262 := by
    simpa [prefixWord, tailWord_1218262, baseEnd_1218262] using wordTrace_append hprefix tailTrace_1218262
  have hstable : (prefixWord ++ tailWord_1218262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218262).length < 2 ^ (prefixWord ++ tailWord_1218262).sum := by decide
  have hdescent : baseEnd_1218262 < baseStart_1218262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218292 : List Nat := [2, 6, 1, 1, 1, 3, 2, 6]
def baseStart_1218292 : Nat := 118140960795 + 1218292 * 2 ^ 59
def prefixEnd_1218292 : Nat := 4983230072969 + 3 ^ 40 * 1218292 * 2
def baseEnd_1218292 : Nat := 46338472113144641529421

theorem tailTrace_1218292 : CollatzResearch.WordTrace tailWord_1218292 prefixEnd_1218292 46338472113144641529421 := by
  unfold tailWord_1218292
  simp only [CollatzResearch.WordTrace]
  refine ⟨22217379851171813276796565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29623173134895751035728753 22217379851171813276796565)
  ·
    refine ⟨1041439680523678747349839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22217379851171813276796565 1041439680523678747349839)
    ·
      refine ⟨1562159520785518121024759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1041439680523678747349839 1562159520785518121024759)
      ·
        refine ⟨2343239281178277181537139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1562159520785518121024759 2343239281178277181537139)
        ·
          refine ⟨3514858921767415772305709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2343239281178277181537139 3514858921767415772305709)
          ·
            refine ⟨1318072095662780914614641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3514858921767415772305709 1318072095662780914614641)
            ·
              refine ⟨988554071747085685960981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318072095662780914614641 988554071747085685960981)
              ·
                refine ⟨46338472113144641529421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 988554071747085685960981 46338472113144641529421)
                ·
                  rfl

theorem cell22_1218292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 6].length) (baseStart_1218292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218292 prefixEnd_1218292 := by exact prefixLift 1218292
  have htrace : WordTrace (prefixWord ++ tailWord_1218292) baseStart_1218292 baseEnd_1218292 := by
    simpa [prefixWord, tailWord_1218292, baseEnd_1218292] using wordTrace_append hprefix tailTrace_1218292
  have hstable : (prefixWord ++ tailWord_1218292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218292).length < 2 ^ (prefixWord ++ tailWord_1218292).sum := by decide
  have hdescent : baseEnd_1218292 < baseStart_1218292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218350 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1218350 : Nat := 118140960795 + 1218350 * 2 ^ 59
def prefixEnd_1218350 : Nat := 4983230072969 + 3 ^ 40 * 1218350 * 2
def baseEnd_1218350 : Nat := 417066103603608955814611

theorem tailTrace_1218350 : CollatzResearch.WordTrace tailWord_1218350 prefixEnd_1218350 417066103603608955814611 := by
  unfold tailWord_1218350
  simp only [CollatzResearch.WordTrace]
  refine ⟨5554609392016687807400563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29624583424089001639469669 5554609392016687807400563)
  ·
    refine ⟨8331914088025031711100845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5554609392016687807400563 8331914088025031711100845)
    ·
      refine ⟨3124467783009386891662817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8331914088025031711100845 3124467783009386891662817)
      ·
        refine ⟨2343350837257040168747113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3124467783009386891662817 2343350837257040168747113)
        ·
          refine ⟨1757513127942780126560335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2343350837257040168747113 1757513127942780126560335)
          ·
            refine ⟨2636269691914170189840503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757513127942780126560335 2636269691914170189840503)
            ·
              refine ⟨3954404537871255284760755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2636269691914170189840503 3954404537871255284760755)
              ·
                refine ⟨5931606806806882927141133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3954404537871255284760755 5931606806806882927141133)
                ·
                  refine ⟨2224352552552581097677925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5931606806806882927141133 2224352552552581097677925)
                  ·
                    refine ⟨417066103603608955814611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2224352552552581097677925 417066103603608955814611)
                    ·
                      rfl

theorem cell22_1218350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1218350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218350 prefixEnd_1218350 := by exact prefixLift 1218350
  have htrace : WordTrace (prefixWord ++ tailWord_1218350) baseStart_1218350 baseEnd_1218350 := by
    simpa [prefixWord, tailWord_1218350, baseEnd_1218350] using wordTrace_append hprefix tailTrace_1218350
  have hstable : (prefixWord ++ tailWord_1218350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218350).length < 2 ^ (prefixWord ++ tailWord_1218350).sum := by decide
  have hdescent : baseEnd_1218350 < baseStart_1218350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218442 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 3, 3]
def baseStart_1218442 : Nat := 118140960795 + 1218442 * 2 ^ 59
def prefixEnd_1218442 : Nat := 4983230072969 + 3 ^ 40 * 1218442 * 2
def baseEnd_1218442 : Nat := 417097597083751382514329

theorem tailTrace_1218442 : CollatzResearch.WordTrace tailWord_1218442 prefixEnd_1218442 417097597083751382514329 := by
  unfold tailWord_1218442
  simp only [CollatzResearch.WordTrace]
  refine ⟨11110057662950050542888395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29626820434533468114369053 11110057662950050542888395)
  ·
    refine ⟨16665086494425075814332593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11110057662950050542888395 16665086494425075814332593)
    ·
      refine ⟨12498814870818806860749445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16665086494425075814332593 12498814870818806860749445)
      ·
        refine ⟨2343527788278526286390521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12498814870818806860749445 2343527788278526286390521)
        ·
          refine ⟨1757645841208894714792891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2343527788278526286390521 1757645841208894714792891)
          ·
            refine ⟨2636468761813342072189337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757645841208894714792891 2636468761813342072189337)
            ·
              refine ⟨1977351571360006554142003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2636468761813342072189337 1977351571360006554142003)
              ·
                refine ⟨2966027357040009831213005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977351571360006554142003 2966027357040009831213005)
                ·
                  refine ⟨1112260258890003686704877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2966027357040009831213005 1112260258890003686704877)
                  ·
                    refine ⟨417097597083751382514329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1112260258890003686704877 417097597083751382514329)
                    ·
                      rfl

theorem cell22_1218442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_1218442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218442 prefixEnd_1218442 := by exact prefixLift 1218442
  have htrace : WordTrace (prefixWord ++ tailWord_1218442) baseStart_1218442 baseEnd_1218442 := by
    simpa [prefixWord, tailWord_1218442, baseEnd_1218442] using wordTrace_append hprefix tailTrace_1218442
  have hstable : (prefixWord ++ tailWord_1218442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218442).length < 2 ^ (prefixWord ++ tailWord_1218442).sum := by decide
  have hdescent : baseEnd_1218442 < baseStart_1218442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218455 : List Nat := [1, 1, 3, 3, 1, 4, 3, 1, 5]
def baseStart_1218455 : Nat := 118140960795 + 1218455 * 2 ^ 59
def prefixEnd_1218455 : Nat := 4983230072969 + 3 ^ 40 * 1218455 * 2
def baseEnd_1218455 : Nat := 139034015749807893979763

theorem tailTrace_1218455 : CollatzResearch.WordTrace tailWord_1218455 prefixEnd_1218455 139034015749807893979763 := by
  unfold tailWord_1218455
  simp only [CollatzResearch.WordTrace]
  refine ⟨44440704800753105391776819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29627136533835403594517879 44440704800753105391776819)
  ·
    refine ⟨66661057201129658087665229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44440704800753105391776819 66661057201129658087665229)
    ·
      refine ⟨24997896450423621782874461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66661057201129658087665229 24997896450423621782874461)
      ·
        refine ⟨9374211168908858168577923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24997896450423621782874461 9374211168908858168577923)
        ·
          refine ⟨14061316753363287252866885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9374211168908858168577923 14061316753363287252866885)
          ·
            refine ⟨2636496891255616359912541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14061316753363287252866885 2636496891255616359912541)
            ·
              refine ⟨988686334220856134967203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2636496891255616359912541 988686334220856134967203)
              ·
                refine ⟨1483029501331284202450805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988686334220856134967203 1483029501331284202450805)
                ·
                  refine ⟨139034015749807893979763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1483029501331284202450805 139034015749807893979763)
                  ·
                    rfl

theorem cell22_1218455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 5].length) (baseStart_1218455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218455 prefixEnd_1218455 := by exact prefixLift 1218455
  have htrace : WordTrace (prefixWord ++ tailWord_1218455) baseStart_1218455 baseEnd_1218455 := by
    simpa [prefixWord, tailWord_1218455, baseEnd_1218455] using wordTrace_append hprefix tailTrace_1218455
  have hstable : (prefixWord ++ tailWord_1218455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218455).length < 2 ^ (prefixWord ++ tailWord_1218455).sum := by decide
  have hdescent : baseEnd_1218455 < baseStart_1218455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218485 : List Nat := [1, 3, 3, 2, 1, 2, 2, 3, 1, 4]
def baseStart_1218485 : Nat := 118140960795 + 1218485 * 2 ^ 59
def prefixEnd_1218485 : Nat := 4983230072969 + 3 ^ 40 * 1218485 * 2
def baseEnd_1218485 : Nat := 417112316862513603689197

theorem tailTrace_1218485 : CollatzResearch.WordTrace tailWord_1218485 prefixEnd_1218485 417112316862513603689197 := by
  unfold tailWord_1218485
  simp only [CollatzResearch.WordTrace]
  refine ⟨44441798990644420515368909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29627865993762947010245939 44441798990644420515368909)
  ·
    refine ⟨16665674621491657693263341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44441798990644420515368909 16665674621491657693263341)
    ·
      refine ⟨6249627983059371634973753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16665674621491657693263341 6249627983059371634973753)
      ·
        refine ⟨4687220987294528726230315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6249627983059371634973753 4687220987294528726230315)
        ·
          refine ⟨7030831480941793089345473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4687220987294528726230315 7030831480941793089345473)
          ·
            refine ⟨5273123610706344817009105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7030831480941793089345473 5273123610706344817009105)
            ·
              refine ⟨3954842708029758612756829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5273123610706344817009105 3954842708029758612756829)
              ·
                refine ⟨1483066015511159479783811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3954842708029758612756829 1483066015511159479783811)
                ·
                  refine ⟨2224599023266739219675717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483066015511159479783811 2224599023266739219675717)
                  ·
                    refine ⟨417112316862513603689197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2224599023266739219675717 417112316862513603689197)
                    ·
                      rfl

theorem cell22_1218485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_1218485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218485 prefixEnd_1218485 := by exact prefixLift 1218485
  have htrace : WordTrace (prefixWord ++ tailWord_1218485) baseStart_1218485 baseEnd_1218485 := by
    simpa [prefixWord, tailWord_1218485, baseEnd_1218485] using wordTrace_append hprefix tailTrace_1218485
  have hstable : (prefixWord ++ tailWord_1218485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218485).length < 2 ^ (prefixWord ++ tailWord_1218485).sum := by decide
  have hdescent : baseEnd_1218485 < baseStart_1218485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218594 : List Nat := [3, 3, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_1218594 : Nat := 118140960795 + 1218594 * 2 ^ 59
def prefixEnd_1218594 : Nat := 4983230072969 + 3 ^ 40 * 1218594 * 2
def baseEnd_1218594 : Nat := 417149629790073652713863

theorem tailTrace_1218594 : CollatzResearch.WordTrace tailWord_1218594 prefixEnd_1218594 417149629790073652713863 := by
  unfold tailWord_1218594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11111443636812383032771709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29630516364833021420724557 11111443636812383032771709)
  ·
    refine ⟨4166791363804643637289391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11111443636812383032771709 4166791363804643637289391)
    ·
      refine ⟨6250187045706965455934087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4166791363804643637289391 6250187045706965455934087)
      ·
        refine ⟨9375280568560448183901131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6250187045706965455934087 9375280568560448183901131)
        ·
          refine ⟨14062920852840672275851697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9375280568560448183901131 14062920852840672275851697)
          ·
            refine ⟨10547190639630504206888773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14062920852840672275851697 10547190639630504206888773)
            ·
              refine ⟨1977598244930719538791645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10547190639630504206888773 1977598244930719538791645)
              ·
                refine ⟨741599341849019827046867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1977598244930719538791645 741599341849019827046867)
                ·
                  refine ⟨1112399012773529740570301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 741599341849019827046867 1112399012773529740570301)
                  ·
                    refine ⟨417149629790073652713863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1112399012773529740570301 417149629790073652713863)
                    ·
                      rfl

theorem cell22_1218594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_1218594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218594 prefixEnd_1218594 := by exact prefixLift 1218594
  have htrace : WordTrace (prefixWord ++ tailWord_1218594) baseStart_1218594 baseEnd_1218594 := by
    simpa [prefixWord, tailWord_1218594, baseEnd_1218594] using wordTrace_append hprefix tailTrace_1218594
  have hstable : (prefixWord ++ tailWord_1218594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218594).length < 2 ^ (prefixWord ++ tailWord_1218594).sum := by decide
  have hdescent : baseEnd_1218594 < baseStart_1218594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218603 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 5, 4]
def baseStart_1218603 : Nat := 118140960795 + 1218603 * 2 ^ 59
def prefixEnd_1218603 : Nat := 4983230072969 + 3 ^ 40 * 1218603 * 2
def baseEnd_1218603 : Nat := 417152710674000629238835

theorem tailTrace_1218603 : CollatzResearch.WordTrace tailWord_1218603 prefixEnd_1218603 417152710674000629238835 := by
  unfold tailWord_1218603
  simp only [CollatzResearch.WordTrace]
  refine ⟨44446102804216926668164463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29630735202811284445442975 44446102804216926668164463)
  ·
    refine ⟨66669154206325390002246695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44446102804216926668164463 66669154206325390002246695)
    ·
      refine ⟨100003731309488085003370043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66669154206325390002246695 100003731309488085003370043)
      ·
        refine ⟨150005596964232127505055065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100003731309488085003370043 150005596964232127505055065)
        ·
          refine ⟨112504197723174095628791299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150005596964232127505055065 112504197723174095628791299)
          ·
            refine ⟨168756296584761143443186949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112504197723174095628791299 168756296584761143443186949)
            ·
              refine ⟨31641805609642714395597553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168756296584761143443186949 31641805609642714395597553)
              ·
                refine ⟨23731354207232035796698165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31641805609642714395597553 23731354207232035796698165)
                ·
                  refine ⟨2224814456928003355940453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23731354207232035796698165 2224814456928003355940453)
                  ·
                    refine ⟨417152710674000629238835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2224814456928003355940453 417152710674000629238835)
                    ·
                      rfl

theorem cell22_1218603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 4].length) (baseStart_1218603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218603 prefixEnd_1218603 := by exact prefixLift 1218603
  have htrace : WordTrace (prefixWord ++ tailWord_1218603) baseStart_1218603 baseEnd_1218603 := by
    simpa [prefixWord, tailWord_1218603, baseEnd_1218603] using wordTrace_append hprefix tailTrace_1218603
  have hstable : (prefixWord ++ tailWord_1218603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218603).length < 2 ^ (prefixWord ++ tailWord_1218603).sum := by decide
  have hdescent : baseEnd_1218603 < baseStart_1218603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218650 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 6, 3]
def baseStart_1218650 : Nat := 118140960795 + 1218650 * 2 ^ 59
def prefixEnd_1218650 : Nat := 4983230072969 + 3 ^ 40 * 1218650 * 2
def baseEnd_1218650 : Nat := 417168799734508173313691

theorem tailTrace_1218650 : CollatzResearch.WordTrace tailWord_1218650 prefixEnd_1218650 417168799734508173313691 := by
  unfold tailWord_1218650
  simp only [CollatzResearch.WordTrace]
  refine ⟨11111954258761663423781351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29631878023364435796750269 11111954258761663423781351)
  ·
    refine ⟨16667931388142495135672027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11111954258761663423781351 16667931388142495135672027)
    ·
      refine ⟨25001897082213742703508041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16667931388142495135672027 25001897082213742703508041)
      ·
        refine ⟨18751422811660307027631031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25001897082213742703508041 18751422811660307027631031)
        ·
          refine ⟨28127134217490460541446547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18751422811660307027631031 28127134217490460541446547)
          ·
            refine ⟨42190701326235690812169821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28127134217490460541446547 42190701326235690812169821)
            ·
              refine ⟨15821512997338384054563683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42190701326235690812169821 15821512997338384054563683)
              ·
                refine ⟨23732269496007576081845525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15821512997338384054563683 23732269496007576081845525)
                ·
                  refine ⟨1112450132625355128836509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23732269496007576081845525 1112450132625355128836509)
                  ·
                    refine ⟨417168799734508173313691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1112450132625355128836509 417168799734508173313691)
                    ·
                      rfl

theorem cell22_1218650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_1218650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218650 prefixEnd_1218650 := by exact prefixLift 1218650
  have htrace : WordTrace (prefixWord ++ tailWord_1218650) baseStart_1218650 baseEnd_1218650 := by
    simpa [prefixWord, tailWord_1218650, baseEnd_1218650] using wordTrace_append hprefix tailTrace_1218650
  have hstable : (prefixWord ++ tailWord_1218650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218650).length < 2 ^ (prefixWord ++ tailWord_1218650).sum := by decide
  have hdescent : baseEnd_1218650 < baseStart_1218650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218665 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 2, 4]
def baseStart_1218665 : Nat := 118140960795 + 1218665 * 2 ^ 59
def prefixEnd_1218665 : Nat := 4983230072969 + 3 ^ 40 * 1218665 * 2
def baseEnd_1218665 : Nat := 417173934541053134188645

theorem tailTrace_1218665 : CollatzResearch.WordTrace tailWord_1218665 prefixEnd_1218665 417173934541053134188645 := by
  unfold tailWord_1218665
  simp only [CollatzResearch.WordTrace]
  refine ⟨44448364129992311256921449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29632242753328207504614299 44448364129992311256921449)
  ·
    refine ⟨33336273097494233442691087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44448364129992311256921449 33336273097494233442691087)
    ·
      refine ⟨50004409646241350164036631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33336273097494233442691087 50004409646241350164036631)
      ·
        refine ⟨75006614469362025246054947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50004409646241350164036631 75006614469362025246054947)
        ·
          refine ⟨112509921704043037869082421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75006614469362025246054947 112509921704043037869082421)
          ·
            refine ⟨10547805159754034800226477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112509921704043037869082421 10547805159754034800226477)
            ·
              refine ⟨3955426934907763050084929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10547805159754034800226477 3955426934907763050084929)
              ·
                refine ⟨2966570201180822287563697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3955426934907763050084929 2966570201180822287563697)
                ·
                  refine ⟨2224927650885616715672773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2966570201180822287563697 2224927650885616715672773)
                  ·
                    refine ⟨417173934541053134188645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2224927650885616715672773 417173934541053134188645)
                    ·
                      rfl

theorem cell22_1218665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_1218665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218665 prefixEnd_1218665 := by exact prefixLift 1218665
  have htrace : WordTrace (prefixWord ++ tailWord_1218665) baseStart_1218665 baseEnd_1218665 := by
    simpa [prefixWord, tailWord_1218665, baseEnd_1218665] using wordTrace_append hprefix tailTrace_1218665
  have hstable : (prefixWord ++ tailWord_1218665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218665).length < 2 ^ (prefixWord ++ tailWord_1218665).sum := by decide
  have hdescent : baseEnd_1218665 < baseStart_1218665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218669 : List Nat := [1, 5, 1, 1, 2, 1, 5, 2, 4]
def baseStart_1218669 : Nat := 118140960795 + 1218669 * 2 ^ 59
def prefixEnd_1218669 : Nat := 4983230072969 + 3 ^ 40 * 1218669 * 2
def baseEnd_1218669 : Nat := 139058434607599485696211

theorem tailTrace_1218669 : CollatzResearch.WordTrace tailWord_1218669 prefixEnd_1218669 139058434607599485696211 := by
  unfold tailWord_1218669
  simp only [CollatzResearch.WordTrace]
  refine ⟨44448510021977819940067061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29632340014651879960044707 44448510021977819940067061)
  ·
    refine ⟨4167047814560420619381287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44448510021977819940067061 4167047814560420619381287)
    ·
      refine ⟨6250571721840630929071931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4167047814560420619381287 6250571721840630929071931)
      ·
        refine ⟨9375857582760946393607897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6250571721840630929071931 9375857582760946393607897)
        ·
          refine ⟨7031893187070709795205923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9375857582760946393607897 7031893187070709795205923)
          ·
            refine ⟨10547839780606064692808885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7031893187070709795205923 10547839780606064692808885)
            ·
              refine ⟨988859979431818564950833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10547839780606064692808885 988859979431818564950833)
              ·
                refine ⟨741644984573863923713125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 988859979431818564950833 741644984573863923713125)
                ·
                  refine ⟨139058434607599485696211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 741644984573863923713125 139058434607599485696211)
                  ·
                    rfl

theorem cell22_1218669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_1218669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218669 prefixEnd_1218669 := by exact prefixLift 1218669
  have htrace : WordTrace (prefixWord ++ tailWord_1218669) baseStart_1218669 baseEnd_1218669 := by
    simpa [prefixWord, tailWord_1218669, baseEnd_1218669] using wordTrace_append hprefix tailTrace_1218669
  have hstable : (prefixWord ++ tailWord_1218669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218669).length < 2 ^ (prefixWord ++ tailWord_1218669).sum := by decide
  have hdescent : baseEnd_1218669 < baseStart_1218669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218684 : List Nat := [2, 2, 2, 1, 1, 4, 4, 1, 2, 3]
def baseStart_1218684 : Nat := 118140960795 + 1218684 * 2 ^ 59
def prefixEnd_1218684 : Nat := 4983230072969 + 3 ^ 40 * 1218684 * 2
def baseEnd_1218684 : Nat := 417180438629343417963587

theorem tailTrace_1218684 : CollatzResearch.WordTrace tailWord_1218684 prefixEnd_1218684 417180438629343417963587 := by
  unfold tailWord_1218684
  simp only [CollatzResearch.WordTrace]
  refine ⟨22224528558461738750931553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29632704744615651667908737 22224528558461738750931553)
  ·
    refine ⟨16668396418846304063198665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22224528558461738750931553 16668396418846304063198665)
    ·
      refine ⟨12501297314134728047398999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16668396418846304063198665 12501297314134728047398999)
      ·
        refine ⟨18751945971202092071098499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12501297314134728047398999 18751945971202092071098499)
        ·
          refine ⟨28127918956803138106647749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18751945971202092071098499 28127918956803138106647749)
          ·
            refine ⟨5273984804400588394996453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28127918956803138106647749 5273984804400588394996453)
            ·
              refine ⟨988872150825110324061835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5273984804400588394996453 988872150825110324061835)
              ·
                refine ⟨1483308226237665486092753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988872150825110324061835 1483308226237665486092753)
                ·
                  refine ⟨1112481169678249114569565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1483308226237665486092753 1112481169678249114569565)
                  ·
                    refine ⟨417180438629343417963587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1112481169678249114569565 417180438629343417963587)
                    ·
                      rfl

theorem cell22_1218684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_1218684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218684 prefixEnd_1218684 := by exact prefixLift 1218684
  have htrace : WordTrace (prefixWord ++ tailWord_1218684) baseStart_1218684 baseEnd_1218684 := by
    simpa [prefixWord, tailWord_1218684, baseEnd_1218684] using wordTrace_append hprefix tailTrace_1218684
  have hstable : (prefixWord ++ tailWord_1218684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218684).length < 2 ^ (prefixWord ++ tailWord_1218684).sum := by decide
  have hdescent : baseEnd_1218684 < baseStart_1218684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218774 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1218774 : Nat := 118140960795 + 1218774 * 2 ^ 59
def prefixEnd_1218774 : Nat := 4983230072969 + 3 ^ 40 * 1218774 * 2
def baseEnd_1218774 : Nat := 417211247468613183213311

theorem tailTrace_1218774 : CollatzResearch.WordTrace tailWord_1218774 prefixEnd_1218774 417211247468613183213311 := by
  unfold tailWord_1218774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2778271230412338929539961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29634893124398281915092917 2778271230412338929539961)
  ·
    refine ⟨2083703422809254197154971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2778271230412338929539961 2083703422809254197154971)
    ·
      refine ⟨3125555134213881295732457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2083703422809254197154971 3125555134213881295732457)
      ·
        refine ⟨2344166350660410971799343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3125555134213881295732457 2344166350660410971799343)
        ·
          refine ⟨3516249525990616457699015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2344166350660410971799343 3516249525990616457699015)
          ·
            refine ⟨5274374288985924686548523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3516249525990616457699015 5274374288985924686548523)
            ·
              refine ⟨7911561433478887029822785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5274374288985924686548523 7911561433478887029822785)
              ·
                refine ⟨5933671075109165272367089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7911561433478887029822785 5933671075109165272367089)
                ·
                  refine ⟨4450253306331873954275317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5933671075109165272367089 4450253306331873954275317)
                  ·
                    refine ⟨417211247468613183213311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4450253306331873954275317 417211247468613183213311)
                    ·
                      rfl

theorem cell22_1218774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1218774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218774 prefixEnd_1218774 := by exact prefixLift 1218774
  have htrace : WordTrace (prefixWord ++ tailWord_1218774) baseStart_1218774 baseEnd_1218774 := by
    simpa [prefixWord, tailWord_1218774, baseEnd_1218774] using wordTrace_append hprefix tailTrace_1218774
  have hstable : (prefixWord ++ tailWord_1218774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218774).length < 2 ^ (prefixWord ++ tailWord_1218774).sum := by decide
  have hdescent : baseEnd_1218774 < baseStart_1218774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218815 : List Nat := [1, 1, 2, 2, 1, 4, 3, 8]
def baseStart_1218815 : Nat := 118140960795 + 1218815 * 2 ^ 59
def prefixEnd_1218815 : Nat := 4983230072969 + 3 ^ 40 * 1218815 * 2
def baseEnd_1218815 : Nat := 46358364734055860326465

theorem tailTrace_1218815 : CollatzResearch.WordTrace tailWord_1218815 prefixEnd_1218815 46358364734055860326465 := by
  unfold tailWord_1218815
  simp only [CollatzResearch.WordTrace]
  refine ⟨44453835079448886874881899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29635890052965924583254599 44453835079448886874881899)
  ·
    refine ⟨66680752619173330312322849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44453835079448886874881899 66680752619173330312322849)
    ·
      refine ⟨50010564464379997734242137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66680752619173330312322849 50010564464379997734242137)
      ·
        refine ⟨37507923348284998300681603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50010564464379997734242137 37507923348284998300681603)
        ·
          refine ⟨56261885022427497451022405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37507923348284998300681603 56261885022427497451022405)
          ·
            refine ⟨10549103441705155772066701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56261885022427497451022405 10549103441705155772066701)
            ·
              refine ⟨3955913790639433414525013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10549103441705155772066701 3955913790639433414525013)
              ·
                refine ⟨46358364734055860326465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3955913790639433414525013 46358364734055860326465)
                ·
                  rfl

theorem cell22_1218815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 8].length) (baseStart_1218815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218815 prefixEnd_1218815 := by exact prefixLift 1218815
  have htrace : WordTrace (prefixWord ++ tailWord_1218815) baseStart_1218815 baseEnd_1218815 := by
    simpa [prefixWord, tailWord_1218815, baseEnd_1218815] using wordTrace_append hprefix tailTrace_1218815
  have hstable : (prefixWord ++ tailWord_1218815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218815).length < 2 ^ (prefixWord ++ tailWord_1218815).sum := by decide
  have hdescent : baseEnd_1218815 < baseStart_1218815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218817 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1218817 : Nat := 118140960795 + 1218817 * 2 ^ 59
def prefixEnd_1218817 : Nat := 4983230072969 + 3 ^ 40 * 1218817 * 2
def baseEnd_1218817 : Nat := 417225967247375404388179

theorem tailTrace_1218817 : CollatzResearch.WordTrace tailWord_1218817 prefixEnd_1218817 417225967247375404388179 := by
  unfold tailWord_1218817
  simp only [CollatzResearch.WordTrace]
  refine ⟨44453908025441641216454705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29635938683627760810969803 44453908025441641216454705)
  ·
    refine ⟨33340431019081230912341029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44453908025441641216454705 33340431019081230912341029)
    ·
      refine ⟨6251330816077730796063943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33340431019081230912341029 6251330816077730796063943)
      ·
        refine ⟨9376996224116596194095915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6251330816077730796063943 9376996224116596194095915)
        ·
          refine ⟨14065494336174894291143873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9376996224116596194095915 14065494336174894291143873)
          ·
            refine ⟨10549120752131170718357905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14065494336174894291143873 10549120752131170718357905)
            ·
              refine ⟨7911840564098378038768429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10549120752131170718357905 7911840564098378038768429)
              ·
                refine ⟨2966940211536891764538161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7911840564098378038768429 2966940211536891764538161)
                ·
                  refine ⟨2225205158652668823403621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2966940211536891764538161 2225205158652668823403621)
                  ·
                    refine ⟨417225967247375404388179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2225205158652668823403621 417225967247375404388179)
                    ·
                      rfl

theorem cell22_1218817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1218817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218817 prefixEnd_1218817 := by exact prefixLift 1218817
  have htrace : WordTrace (prefixWord ++ tailWord_1218817) baseStart_1218817 baseEnd_1218817 := by
    simpa [prefixWord, tailWord_1218817, baseEnd_1218817] using wordTrace_append hprefix tailTrace_1218817
  have hstable : (prefixWord ++ tailWord_1218817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218817).length < 2 ^ (prefixWord ++ tailWord_1218817).sum := by decide
  have hdescent : baseEnd_1218817 < baseStart_1218817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218853 : List Nat := [1, 3, 1, 2, 5, 2, 2, 1, 2, 3]
def baseStart_1218853 : Nat := 118140960795 + 1218853 * 2 ^ 59
def prefixEnd_1218853 : Nat := 4983230072969 + 3 ^ 40 * 1218853 * 2
def baseEnd_1218853 : Nat := 417238290783083310488069

theorem tailTrace_1218853 : CollatzResearch.WordTrace tailWord_1218853 prefixEnd_1218853 417238290783083310488069 := by
  unfold tailWord_1218853
  simp only [CollatzResearch.WordTrace]
  refine ⟨44455221053311219364765213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29636814035540812909843475 44455221053311219364765213)
  ·
    refine ⟨16670707894991707261786955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44455221053311219364765213 16670707894991707261786955)
    ·
      refine ⟨25006061842487560892680433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16670707894991707261786955 25006061842487560892680433)
      ·
        refine ⟨18754546381865670669510325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25006061842487560892680433 18754546381865670669510325)
        ·
          refine ⟨1758238723299906625266593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18754546381865670669510325 1758238723299906625266593)
          ·
            refine ⟨1318679042474929968949945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1758238723299906625266593 1318679042474929968949945)
            ·
              refine ⟨989009281856197476712459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318679042474929968949945 989009281856197476712459)
              ·
                refine ⟨1483513922784296215068689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989009281856197476712459 1483513922784296215068689)
                ·
                  refine ⟨1112635442088222161301517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1483513922784296215068689 1112635442088222161301517)
                  ·
                    refine ⟨417238290783083310488069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1112635442088222161301517 417238290783083310488069)
                    ·
                      rfl

theorem cell22_1218853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_1218853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218853 prefixEnd_1218853 := by exact prefixLift 1218853
  have htrace : WordTrace (prefixWord ++ tailWord_1218853) baseStart_1218853 baseEnd_1218853 := by
    simpa [prefixWord, tailWord_1218853, baseEnd_1218853] using wordTrace_append hprefix tailTrace_1218853
  have hstable : (prefixWord ++ tailWord_1218853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218853).length < 2 ^ (prefixWord ++ tailWord_1218853).sum := by decide
  have hdescent : baseEnd_1218853 < baseStart_1218853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218892 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_1218892 : Nat := 118140960795 + 1218892 * 2 ^ 59
def prefixEnd_1218892 : Nat := 4983230072969 + 3 ^ 40 * 1218892 * 2
def baseEnd_1218892 : Nat := 417251641280100208762949

theorem tailTrace_1218892 : CollatzResearch.WordTrace tailWord_1218892 prefixEnd_1218892 417251641280100208762949 := by
  unfold tailWord_1218892
  simp only [CollatzResearch.WordTrace]
  refine ⟨22228321750084964512717465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29637762333446619350289953 22228321750084964512717465)
  ·
    refine ⟨16671241312563723384538099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22228321750084964512717465 16671241312563723384538099)
    ·
      refine ⟨25006861968845585076807149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16671241312563723384538099 25006861968845585076807149)
      ·
        refine ⟨9377573238317094403802681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25006861968845585076807149 9377573238317094403802681)
        ·
          refine ⟨7033179928737820802852011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9377573238317094403802681 7033179928737820802852011)
          ·
            refine ⟨10549769893106731204278017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7033179928737820802852011 10549769893106731204278017)
            ·
              refine ⟨7912327419830048403208513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10549769893106731204278017 7912327419830048403208513)
              ·
                refine ⟨5934245564872536302406385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7912327419830048403208513 5934245564872536302406385)
                ·
                  refine ⟨4450684173654402226804789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5934245564872536302406385 4450684173654402226804789)
                  ·
                    refine ⟨417251641280100208762949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4450684173654402226804789 417251641280100208762949)
                    ·
                      rfl

theorem cell22_1218892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_1218892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218892 prefixEnd_1218892 := by exact prefixLift 1218892
  have htrace : WordTrace (prefixWord ++ tailWord_1218892) baseStart_1218892 baseEnd_1218892 := by
    simpa [prefixWord, tailWord_1218892, baseEnd_1218892] using wordTrace_append hprefix tailTrace_1218892
  have hstable : (prefixWord ++ tailWord_1218892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218892).length < 2 ^ (prefixWord ++ tailWord_1218892).sum := by decide
  have hdescent : baseEnd_1218892 < baseStart_1218892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218898 : List Nat := [3, 2, 2, 1, 1, 1, 6, 2, 1, 3]
def baseStart_1218898 : Nat := 118140960795 + 1218898 * 2 ^ 59
def prefixEnd_1218898 : Nat := 4983230072969 + 3 ^ 40 * 1218898 * 2
def baseEnd_1218898 : Nat := 417253695202718193112931

theorem tailTrace_1218898 : CollatzResearch.WordTrace tailWord_1218898 prefixEnd_1218898 417253695202718193112931 := by
  unfold tailWord_1218898
  simp only [CollatzResearch.WordTrace]
  refine ⟨11114215584537048012538337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29637908225432128033435565 11114215584537048012538337)
  ·
    refine ⟨8335661688402786009403753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11114215584537048012538337 8335661688402786009403753)
    ·
      refine ⟨6251746266302089507052815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8335661688402786009403753 6251746266302089507052815)
      ·
        refine ⟨9377619399453134260579223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6251746266302089507052815 9377619399453134260579223)
        ·
          refine ⟨14066429099179701390868835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9377619399453134260579223 14066429099179701390868835)
          ·
            refine ⟨21099643648769552086303253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14066429099179701390868835 21099643648769552086303253)
            ·
              refine ⟨989045796036072754045465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21099643648769552086303253 989045796036072754045465)
              ·
                refine ⟨741784347027054565534099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 989045796036072754045465 741784347027054565534099)
                ·
                  refine ⟨1112676520540581848301149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 741784347027054565534099 1112676520540581848301149)
                  ·
                    refine ⟨417253695202718193112931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1112676520540581848301149 417253695202718193112931)
                    ·
                      rfl

theorem cell22_1218898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_1218898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218898 prefixEnd_1218898 := by exact prefixLift 1218898
  have htrace : WordTrace (prefixWord ++ tailWord_1218898) baseStart_1218898 baseEnd_1218898 := by
    simpa [prefixWord, tailWord_1218898, baseEnd_1218898] using wordTrace_append hprefix tailTrace_1218898
  have hstable : (prefixWord ++ tailWord_1218898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218898).length < 2 ^ (prefixWord ++ tailWord_1218898).sum := by decide
  have hdescent : baseEnd_1218898 < baseStart_1218898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218939 : List Nat := [1, 1, 1, 1, 1, 7, 1, 5, 4]
def baseStart_1218939 : Nat := 118140960795 + 1218939 * 2 ^ 59
def prefixEnd_1218939 : Nat := 4983230072969 + 3 ^ 40 * 1218939 * 2
def baseEnd_1218939 : Nat := 139089243446869250945935

theorem tailTrace_1218939 : CollatzResearch.WordTrace tailWord_1218939 prefixEnd_1218939 139089243446869250945935 := by
  unfold tailWord_1218939
  simp only [CollatzResearch.WordTrace]
  refine ⟨44458357730999656052395871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29638905153999770701597247 44458357730999656052395871)
  ·
    refine ⟨66687536596499484078593807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44458357730999656052395871 66687536596499484078593807)
    ·
      refine ⟨100031304894749226117890711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66687536596499484078593807 100031304894749226117890711)
      ·
        refine ⟨150046957342123839176836067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100031304894749226117890711 150046957342123839176836067)
        ·
          refine ⟨225070436013185758765254101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150046957342123839176836067 225070436013185758765254101)
          ·
            refine ⟨5275088344059041221060643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 225070436013185758765254101 5275088344059041221060643)
            ·
              refine ⟨7912632516088561831590965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5275088344059041221060643 7912632516088561831590965)
              ·
                refine ⟨741809298383302671711653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7912632516088561831590965 741809298383302671711653)
                ·
                  refine ⟨139089243446869250945935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 741809298383302671711653 139089243446869250945935)
                  ·
                    rfl

theorem cell22_1218939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 4].length) (baseStart_1218939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218939 prefixEnd_1218939 := by exact prefixLift 1218939
  have htrace : WordTrace (prefixWord ++ tailWord_1218939) baseStart_1218939 baseEnd_1218939 := by
    simpa [prefixWord, tailWord_1218939, baseEnd_1218939] using wordTrace_append hprefix tailTrace_1218939
  have hstable : (prefixWord ++ tailWord_1218939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218939).length < 2 ^ (prefixWord ++ tailWord_1218939).sum := by decide
  have hdescent : baseEnd_1218939 < baseStart_1218939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218941 : List Nat := [1, 4, 1, 1, 2, 3, 4, 1, 1, 4]
def baseStart_1218941 : Nat := 118140960795 + 1218941 * 2 ^ 59
def prefixEnd_1218941 : Nat := 4983230072969 + 3 ^ 40 * 1218941 * 2
def baseEnd_1218941 : Nat := 417268414981480414287799

theorem tailTrace_1218941 : CollatzResearch.WordTrace tailWord_1218941 prefixEnd_1218941 417268414981480414287799 := by
  unfold tailWord_1218941
  simp only [CollatzResearch.WordTrace]
  refine ⟨44458430676992410393968677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29638953784661606929312451 44458430676992410393968677)
  ·
    refine ⟨8335955751936076948869127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44458430676992410393968677 8335955751936076948869127)
    ·
      refine ⟨12503933627904115423303691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8335955751936076948869127 12503933627904115423303691)
      ·
        refine ⟨18755900441856173134955537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12503933627904115423303691 18755900441856173134955537)
        ·
          refine ⟨14066925331392129851216653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18755900441856173134955537 14066925331392129851216653)
          ·
            refine ⟨5275096999272048694206245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14066925331392129851216653 5275096999272048694206245)
            ·
              refine ⟨989080687363509130163671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5275096999272048694206245 989080687363509130163671)
              ·
                refine ⟨1483621031045263695245507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989080687363509130163671 1483621031045263695245507)
                ·
                  refine ⟨2225431546567895542868261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483621031045263695245507 2225431546567895542868261)
                  ·
                    refine ⟨417268414981480414287799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2225431546567895542868261 417268414981480414287799)
                    ·
                      rfl

theorem cell22_1218941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_1218941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1218941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1218941 prefixEnd_1218941 := by exact prefixLift 1218941
  have htrace : WordTrace (prefixWord ++ tailWord_1218941) baseStart_1218941 baseEnd_1218941 := by
    simpa [prefixWord, tailWord_1218941, baseEnd_1218941] using wordTrace_append hprefix tailTrace_1218941
  have hstable : (prefixWord ++ tailWord_1218941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218941).length < 2 ^ (prefixWord ++ tailWord_1218941).sum := by decide
  have hdescent : baseEnd_1218941 < baseStart_1218941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219016 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 3, 3]
def baseStart_1219016 : Nat := 118140960795 + 1219016 * 2 ^ 59
def prefixEnd_1219016 : Nat := 4983230072969 + 3 ^ 40 * 1219016 * 2
def baseEnd_1219016 : Nat := 417294089014205218662569

theorem tailTrace_1219016 : CollatzResearch.WordTrace tailWord_1219016 prefixEnd_1219016 417294089014205218662569 := by
  unfold tailWord_1219016
  simp only [CollatzResearch.WordTrace]
  refine ⟨22230583075860349101474451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29640777434480465468632601 22230583075860349101474451)
  ·
    refine ⟨33345874613790523652211677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22230583075860349101474451 33345874613790523652211677)
    ·
      refine ⟨12504702980171446369579379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33345874613790523652211677 12504702980171446369579379)
      ·
        refine ⟨18757054470257169554369069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12504702980171446369579379 18757054470257169554369069)
        ·
          refine ⟨7033895426346438582888401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18757054470257169554369069 7033895426346438582888401)
          ·
            refine ⟨5275421569759828937166301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7033895426346438582888401 5275421569759828937166301)
            ·
              refine ⟨1978283088659935851437363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5275421569759828937166301 1978283088659935851437363)
              ·
                refine ⟨2967424632989903777156045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978283088659935851437363 2967424632989903777156045)
                ·
                  refine ⟨1112784237371213916433517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2967424632989903777156045 1112784237371213916433517)
                  ·
                    refine ⟨417294089014205218662569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1112784237371213916433517 417294089014205218662569)
                    ·
                      rfl

theorem cell22_1219016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_1219016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219016 prefixEnd_1219016 := by exact prefixLift 1219016
  have htrace : WordTrace (prefixWord ++ tailWord_1219016) baseStart_1219016 baseEnd_1219016 := by
    simpa [prefixWord, tailWord_1219016, baseEnd_1219016] using wordTrace_append hprefix tailTrace_1219016
  have hstable : (prefixWord ++ tailWord_1219016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219016).length < 2 ^ (prefixWord ++ tailWord_1219016).sum := by decide
  have hdescent : baseEnd_1219016 < baseStart_1219016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219027 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 8, 5]
def baseStart_1219027 : Nat := 118140960795 + 1219027 * 2 ^ 59
def prefixEnd_1219027 : Nat := 4983230072969 + 3 ^ 40 * 1219027 * 2
def baseEnd_1219027 : Nat := 417297854539004856637535

theorem tailTrace_1219027 : CollatzResearch.WordTrace tailWord_1219027 prefixEnd_1219027 417297854539004856637535 := by
  unfold tailWord_1219027
  simp only [CollatzResearch.WordTrace]
  refine ⟨44461567354680847081599335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29641044903120564721066223 44461567354680847081599335)
  ·
    refine ⟨66692351032021270622399003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44461567354680847081599335 66692351032021270622399003)
    ·
      refine ⟨100038526548031905933598505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66692351032021270622399003 100038526548031905933598505)
      ·
        refine ⟨75028894911023929450198879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100038526548031905933598505 75028894911023929450198879)
        ·
          refine ⟨112543342366535894175298319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75028894911023929450198879 112543342366535894175298319)
          ·
            refine ⟨168815013549803841262947479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112543342366535894175298319 168815013549803841262947479)
            ·
              refine ⟨253222520324705761894421219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168815013549803841262947479 253222520324705761894421219)
              ·
                refine ⟨379833780487058642841631829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253222520324705761894421219 379833780487058642841631829)
                ·
                  refine ⟨4451177115082718470800373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 379833780487058642841631829 4451177115082718470800373)
                  ·
                    refine ⟨417297854539004856637535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4451177115082718470800373 417297854539004856637535)
                    ·
                      rfl

theorem cell22_1219027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 5].length) (baseStart_1219027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219027 prefixEnd_1219027 := by exact prefixLift 1219027
  have htrace : WordTrace (prefixWord ++ tailWord_1219027) baseStart_1219027 baseEnd_1219027 := by
    simpa [prefixWord, tailWord_1219027, baseEnd_1219027] using wordTrace_append hprefix tailTrace_1219027
  have hstable : (prefixWord ++ tailWord_1219027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219027).length < 2 ^ (prefixWord ++ tailWord_1219027).sum := by decide
  have hdescent : baseEnd_1219027 < baseStart_1219027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219076 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_1219076 : Nat := 118140960795 + 1219076 * 2 ^ 59
def prefixEnd_1219076 : Nat := 4983230072969 + 3 ^ 40 * 1219076 * 2
def baseEnd_1219076 : Nat := 417314628240385062162385

theorem tailTrace_1219076 : CollatzResearch.WordTrace tailWord_1219076 prefixEnd_1219076 417314628240385062162385 := by
  unfold tailWord_1219076
  simp only [CollatzResearch.WordTrace]
  refine ⟨22231677265751664225066541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29642236354335552300088721 22231677265751664225066541)
  ·
    refine ⟨8336878974656874084399953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22231677265751664225066541 8336878974656874084399953)
    ·
      refine ⟨6252659230992655563299965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8336878974656874084399953 6252659230992655563299965)
      ·
        refine ⟨2344747211622245836237487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6252659230992655563299965 2344747211622245836237487)
        ·
          refine ⟨3517120817433368754356231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2344747211622245836237487 3517120817433368754356231)
          ·
            refine ⟨5275681226150053131534347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3517120817433368754356231 5275681226150053131534347)
            ·
              refine ⟨7913521839225079697301521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5275681226150053131534347 7913521839225079697301521)
              ·
                refine ⟨5935141379418809772976141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7913521839225079697301521 5935141379418809772976141)
                ·
                  refine ⟨2225678017282053664866053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5935141379418809772976141 2225678017282053664866053)
                  ·
                    refine ⟨417314628240385062162385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2225678017282053664866053 417314628240385062162385)
                    ·
                      rfl

theorem cell22_1219076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_1219076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219076 prefixEnd_1219076 := by exact prefixLift 1219076
  have htrace : WordTrace (prefixWord ++ tailWord_1219076) baseStart_1219076 baseEnd_1219076 := by
    simpa [prefixWord, tailWord_1219076, baseEnd_1219076] using wordTrace_append hprefix tailTrace_1219076
  have hstable : (prefixWord ++ tailWord_1219076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219076).length < 2 ^ (prefixWord ++ tailWord_1219076).sum := by decide
  have hdescent : baseEnd_1219076 < baseStart_1219076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219106 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_1219106 : Nat := 118140960795 + 1219106 * 2 ^ 59
def prefixEnd_1219106 : Nat := 4983230072969 + 3 ^ 40 * 1219106 * 2
def baseEnd_1219106 : Nat := 417324897853474983912293

theorem tailTrace_1219106 : CollatzResearch.WordTrace tailWord_1219106 prefixEnd_1219106 417324897853474983912293 := by
  unfold tailWord_1219106
  simp only [CollatzResearch.WordTrace]
  refine ⟨11116112180348660893431293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29642965814263095715816781 11116112180348660893431293)
  ·
    refine ⟨4168542067630747835036735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11116112180348660893431293 4168542067630747835036735)
    ·
      refine ⟨6252813101446121752555103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4168542067630747835036735 6252813101446121752555103)
      ·
        refine ⟨9379219652169182628832655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6252813101446121752555103 9379219652169182628832655)
        ·
          refine ⟨14068829478253773943248983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9379219652169182628832655 14068829478253773943248983)
          ·
            refine ⟨21103244217380660914873475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14068829478253773943248983 21103244217380660914873475)
            ·
              refine ⟨31654866326070991372310213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21103244217380660914873475 31654866326070991372310213)
              ·
                refine ⟨5935287436138310882308165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31654866326070991372310213 5935287436138310882308165)
                ·
                  refine ⟨1112866394275933290432781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5935287436138310882308165 1112866394275933290432781)
                  ·
                    refine ⟨417324897853474983912293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1112866394275933290432781 417324897853474983912293)
                    ·
                      rfl

theorem cell22_1219106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_1219106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219106 prefixEnd_1219106 := by exact prefixLift 1219106
  have htrace : WordTrace (prefixWord ++ tailWord_1219106) baseStart_1219106 baseEnd_1219106 := by
    simpa [prefixWord, tailWord_1219106, baseEnd_1219106] using wordTrace_append hprefix tailTrace_1219106
  have hstable : (prefixWord ++ tailWord_1219106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219106).length < 2 ^ (prefixWord ++ tailWord_1219106).sum := by decide
  have hdescent : baseEnd_1219106 < baseStart_1219106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219151 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 3, 3]
def baseStart_1219151 : Nat := 118140960795 + 1219151 * 2 ^ 59
def prefixEnd_1219151 : Nat := 4983230072969 + 3 ^ 40 * 1219151 * 2
def baseEnd_1219151 : Nat := 417340302273109866537155

theorem tailTrace_1219151 : CollatzResearch.WordTrace tailWord_1219151 prefixEnd_1219151 417340302273109866537155 := by
  unfold tailWord_1219151
  simp only [CollatzResearch.WordTrace]
  refine ⟨44466090006231616259113307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29644060004154410839408871 44466090006231616259113307)
  ·
    refine ⟨66699135009347424388669961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44466090006231616259113307 66699135009347424388669961)
    ·
      refine ⟨50024351257010568291502471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66699135009347424388669961 50024351257010568291502471)
      ·
        refine ⟨75036526885515852437253707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50024351257010568291502471 75036526885515852437253707)
        ·
          refine ⟨112554790328273778655880561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75036526885515852437253707 112554790328273778655880561)
          ·
            refine ⟨84416092746205333991910421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112554790328273778655880561 84416092746205333991910421)
            ·
              refine ⟨3957004347478375030870801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84416092746205333991910421 3957004347478375030870801)
              ·
                refine ⟨2967753260608781273153101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3957004347478375030870801 2967753260608781273153101)
                ·
                  refine ⟨1112907472728292977432413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2967753260608781273153101 1112907472728292977432413)
                  ·
                    refine ⟨417340302273109866537155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1112907472728292977432413 417340302273109866537155)
                    ·
                      rfl

theorem cell22_1219151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 3].length) (baseStart_1219151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219151 prefixEnd_1219151 := by exact prefixLift 1219151
  have htrace : WordTrace (prefixWord ++ tailWord_1219151) baseStart_1219151 baseEnd_1219151 := by
    simpa [prefixWord, tailWord_1219151, baseEnd_1219151] using wordTrace_append hprefix tailTrace_1219151
  have hstable : (prefixWord ++ tailWord_1219151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219151).length < 2 ^ (prefixWord ++ tailWord_1219151).sum := by decide
  have hdescent : baseEnd_1219151 < baseStart_1219151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219170 : List Nat := [3, 3, 2, 3, 2, 1, 8]
def baseStart_1219170 : Nat := 118140960795 + 1219170 * 2 ^ 59
def prefixEnd_1219170 : Nat := 4983230072969 + 3 ^ 40 * 1219170 * 2
def baseEnd_1219170 : Nat := 15457289124496301863411

theorem tailTrace_1219170 : CollatzResearch.WordTrace tailWord_1219170 prefixEnd_1219170 15457289124496301863411 := by
  unfold tailWord_1219170
  simp only [CollatzResearch.WordTrace]
  refine ⟨11116695748290695626013741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29644521995441855002703309 11116695748290695626013741)
  ·
    refine ⟨4168760905609010859755153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11116695748290695626013741 4168760905609010859755153)
    ·
      refine ⟨3126570679206758144816365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4168760905609010859755153 3126570679206758144816365)
      ·
        refine ⟨1172464004702534304306137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3126570679206758144816365 1172464004702534304306137)
        ·
          refine ⟨879348003526900728229603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1172464004702534304306137 879348003526900728229603)
          ·
            refine ⟨1319022005290351092344405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879348003526900728229603 1319022005290351092344405)
            ·
              refine ⟨15457289124496301863411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1319022005290351092344405 15457289124496301863411)
              ·
                rfl

theorem cell22_1219170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 8].length) (baseStart_1219170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219170 prefixEnd_1219170 := by exact prefixLift 1219170
  have htrace : WordTrace (prefixWord ++ tailWord_1219170) baseStart_1219170 baseEnd_1219170 := by
    simpa [prefixWord, tailWord_1219170, baseEnd_1219170] using wordTrace_append hprefix tailTrace_1219170
  have hstable : (prefixWord ++ tailWord_1219170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219170).length < 2 ^ (prefixWord ++ tailWord_1219170).sum := by decide
  have hdescent : baseEnd_1219170 < baseStart_1219170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219179 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 2, 5]
def baseStart_1219179 : Nat := 118140960795 + 1219179 * 2 ^ 59
def prefixEnd_1219179 : Nat := 4983230072969 + 3 ^ 40 * 1219179 * 2
def baseEnd_1219179 : Nat := 417349887245327126837069

theorem tailTrace_1219179 : CollatzResearch.WordTrace tailWord_1219179 prefixEnd_1219179 417349887245327126837069 := by
  unfold tailWord_1219179
  simp only [CollatzResearch.WordTrace]
  refine ⟨44467111250130177041132591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29644740833420118027421727 44467111250130177041132591)
  ·
    refine ⟨66700666875195265561698887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44467111250130177041132591 66700666875195265561698887)
    ·
      refine ⟨100051000312792898342548331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66700666875195265561698887 100051000312792898342548331)
      ·
        refine ⟨150076500469189347513822497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100051000312792898342548331 150076500469189347513822497)
        ·
          refine ⟨112557375351892010635366873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150076500469189347513822497 112557375351892010635366873)
          ·
            refine ⟨84418031513919007976525155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112557375351892010635366873 84418031513919007976525155)
            ·
              refine ⟨126627047270878511964787733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84418031513919007976525155 126627047270878511964787733)
              ·
                refine ⟨5935642840822430248349425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126627047270878511964787733 5935642840822430248349425)
                ·
                  refine ⟨4451732130616822686262069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5935642840822430248349425 4451732130616822686262069)
                  ·
                    refine ⟨417349887245327126837069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4451732130616822686262069 417349887245327126837069)
                    ·
                      rfl

theorem cell22_1219179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 5].length) (baseStart_1219179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219179 prefixEnd_1219179 := by exact prefixLift 1219179
  have htrace : WordTrace (prefixWord ++ tailWord_1219179) baseStart_1219179 baseEnd_1219179 := by
    simpa [prefixWord, tailWord_1219179, baseEnd_1219179] using wordTrace_append hprefix tailTrace_1219179
  have hstable : (prefixWord ++ tailWord_1219179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219179).length < 2 ^ (prefixWord ++ tailWord_1219179).sum := by decide
  have hdescent : baseEnd_1219179 < baseStart_1219179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219181 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 7]
def baseStart_1219181 : Nat := 118140960795 + 1219181 * 2 ^ 59
def prefixEnd_1219181 : Nat := 4983230072969 + 3 ^ 40 * 1219181 * 2
def baseEnd_1219181 : Nat := 139116857295399929429021

theorem tailTrace_1219181 : CollatzResearch.WordTrace tailWord_1219181 prefixEnd_1219181 139116857295399929429021 := by
  unfold tailWord_1219181
  simp only [CollatzResearch.WordTrace]
  refine ⟨44467184196122931382705397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29644789464081954255136931 44467184196122931382705397)
  ·
    refine ⟨4168798518386524817128631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44467184196122931382705397 4168798518386524817128631)
    ·
      refine ⟨6253197777579787225692947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4168798518386524817128631 6253197777579787225692947)
      ·
        refine ⟨9379796666369680838539421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6253197777579787225692947 9379796666369680838539421)
        ·
          refine ⟨3517423749888630314452283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9379796666369680838539421 3517423749888630314452283)
          ·
            refine ⟨5276135624832945471678425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3517423749888630314452283 5276135624832945471678425)
            ·
              refine ⟨3957101718624709103758819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5276135624832945471678425 3957101718624709103758819)
              ·
                refine ⟨5935652577937063655638229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3957101718624709103758819 5935652577937063655638229)
                ·
                  refine ⟨139116857295399929429021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5935652577937063655638229 139116857295399929429021)
                  ·
                    rfl

theorem cell22_1219181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_1219181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219181 prefixEnd_1219181 := by exact prefixLift 1219181
  have htrace : WordTrace (prefixWord ++ tailWord_1219181) baseStart_1219181 baseEnd_1219181 := by
    simpa [prefixWord, tailWord_1219181, baseEnd_1219181] using wordTrace_append hprefix tailTrace_1219181
  have hstable : (prefixWord ++ tailWord_1219181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219181).length < 2 ^ (prefixWord ++ tailWord_1219181).sum := by decide
  have hdescent : baseEnd_1219181 < baseStart_1219181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219209 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 8]
def baseStart_1219209 : Nat := 118140960795 + 1219209 * 2 ^ 59
def prefixEnd_1219209 : Nat := 4983230072969 + 3 ^ 40 * 1219209 * 2
def baseEnd_1219209 : Nat := 139120052286139016195659

theorem tailTrace_1219209 : CollatzResearch.WordTrace tailWord_1219209 prefixEnd_1219209 139120052286139016195659 := by
  unfold tailWord_1219209
  simp only [CollatzResearch.WordTrace]
  refine ⟨44468205440021492164724681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29645470293347661443149787 44468205440021492164724681)
  ·
    refine ⟨33351154080016119123543511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44468205440021492164724681 33351154080016119123543511)
    ·
      refine ⟨50026731120024178685315267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33351154080016119123543511 50026731120024178685315267)
      ·
        refine ⟨75040096680036268027972901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50026731120024178685315267 75040096680036268027972901)
        ·
          refine ⟨14070018127506800255244919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75040096680036268027972901 14070018127506800255244919)
          ·
            refine ⟨21105027191260200382867379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14070018127506800255244919 21105027191260200382867379)
            ·
              refine ⟨31657540786890300574301069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21105027191260200382867379 31657540786890300574301069)
              ·
                refine ⟨11871577795083862715362901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31657540786890300574301069 11871577795083862715362901)
                ·
                  refine ⟨139120052286139016195659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11871577795083862715362901 139120052286139016195659)
                  ·
                    rfl

theorem cell22_1219209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_1219209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219209 prefixEnd_1219209 := by exact prefixLift 1219209
  have htrace : WordTrace (prefixWord ++ tailWord_1219209) baseStart_1219209 baseEnd_1219209 := by
    simpa [prefixWord, tailWord_1219209, baseEnd_1219209] using wordTrace_append hprefix tailTrace_1219209
  have hstable : (prefixWord ++ tailWord_1219209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219209).length < 2 ^ (prefixWord ++ tailWord_1219209).sum := by decide
  have hdescent : baseEnd_1219209 < baseStart_1219209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219211 : List Nat := [1, 1, 1, 1, 4, 1, 2, 6, 1, 4]
def baseStart_1219211 : Nat := 118140960795 + 1219211 * 2 ^ 59
def prefixEnd_1219211 : Nat := 4983230072969 + 3 ^ 40 * 1219211 * 2
def baseEnd_1219211 : Nat := 417360841499289710036971

theorem tailTrace_1219211 : CollatzResearch.WordTrace tailWord_1219211 prefixEnd_1219211 417360841499289710036971 := by
  unfold tailWord_1219211
  simp only [CollatzResearch.WordTrace]
  refine ⟨44468278386014246506297487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29645518924009497670864991 44468278386014246506297487)
  ·
    refine ⟨66702417579021369759446231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44468278386014246506297487 66702417579021369759446231)
    ·
      refine ⟨100053626368532054639169347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66702417579021369759446231 100053626368532054639169347)
      ·
        refine ⟨150080439552798081958754021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100053626368532054639169347 150080439552798081958754021)
        ·
          refine ⟨28140082416149640367266379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150080439552798081958754021 28140082416149640367266379)
          ·
            refine ⟨42210123624224460550899569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28140082416149640367266379 42210123624224460550899569)
            ·
              refine ⟨31657592718168345413174677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42210123624224460550899569 31657592718168345413174677)
              ·
                refine ⟨1483949658664141191242563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31657592718168345413174677 1483949658664141191242563)
                ·
                  refine ⟨2225924487996211786863845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483949658664141191242563 2225924487996211786863845)
                  ·
                    refine ⟨417360841499289710036971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2225924487996211786863845 417360841499289710036971)
                    ·
                      rfl

theorem cell22_1219211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 4].length) (baseStart_1219211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219211 prefixEnd_1219211 := by exact prefixLift 1219211
  have htrace : WordTrace (prefixWord ++ tailWord_1219211) baseStart_1219211 baseEnd_1219211 := by
    simpa [prefixWord, tailWord_1219211, baseEnd_1219211] using wordTrace_append hprefix tailTrace_1219211
  have hstable : (prefixWord ++ tailWord_1219211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219211).length < 2 ^ (prefixWord ++ tailWord_1219211).sum := by decide
  have hdescent : baseEnd_1219211 < baseStart_1219211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219258 : List Nat := [3, 1, 1, 1, 2, 3, 1, 5, 2, 3]
def baseStart_1219258 : Nat := 118140960795 + 1219258 * 2 ^ 59
def prefixEnd_1219258 : Nat := 4983230072969 + 3 ^ 40 * 1219258 * 2
def baseEnd_1219258 : Nat := 417376930559797254111827

theorem tailTrace_1219258 : CollatzResearch.WordTrace tailWord_1219258 prefixEnd_1219258 417376930559797254111827 := by
  unfold tailWord_1219258
  simp only [CollatzResearch.WordTrace]
  refine ⟨11117498154210993383314607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29646661744562649022172285 11117498154210993383314607)
  ·
    refine ⟨16676247231316490074971911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11117498154210993383314607 16676247231316490074971911)
    ·
      refine ⟨25014370846974735112457867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16676247231316490074971911 25014370846974735112457867)
      ·
        refine ⟨37521556270462102668686801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25014370846974735112457867 37521556270462102668686801)
        ·
          refine ⟨28141167202846577001515101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37521556270462102668686801 28141167202846577001515101)
          ·
            refine ⟨10552937701067466375568163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28141167202846577001515101 10552937701067466375568163)
            ·
              refine ⟨15829406551601199563352245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10552937701067466375568163 15829406551601199563352245)
              ·
                refine ⟨1484006864212612459064273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15829406551601199563352245 1484006864212612459064273)
                ·
                  refine ⟨1113005148159459344298205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1484006864212612459064273 1113005148159459344298205)
                  ·
                    refine ⟨417376930559797254111827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1113005148159459344298205 417376930559797254111827)
                    ·
                      rfl

theorem cell22_1219258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_1219258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219258 prefixEnd_1219258 := by exact prefixLift 1219258
  have htrace : WordTrace (prefixWord ++ tailWord_1219258) baseStart_1219258 baseEnd_1219258 := by
    simpa [prefixWord, tailWord_1219258, baseEnd_1219258] using wordTrace_append hprefix tailTrace_1219258
  have hstable : (prefixWord ++ tailWord_1219258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219258).length < 2 ^ (prefixWord ++ tailWord_1219258).sum := by decide
  have hdescent : baseEnd_1219258 < baseStart_1219258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219292 : List Nat := [2, 2, 5, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1219292 : Nat := 118140960795 + 1219292 * 2 ^ 59
def prefixEnd_1219292 : Nat := 4983230072969 + 3 ^ 40 * 1219292 * 2
def baseEnd_1219292 : Nat := 417388569454632498761723

theorem tailTrace_1219292 : CollatzResearch.WordTrace tailWord_1219292 prefixEnd_1219292 417388569454632498761723 := by
  unfold tailWord_1219292
  simp only [CollatzResearch.WordTrace]
  refine ⟨22235616349360398669998065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29647488465813864893330753 22235616349360398669998065)
  ·
    refine ⟨16676712262020299002498549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22235616349360398669998065 16676712262020299002498549)
    ·
      refine ⟨1563441774564403031484239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16676712262020299002498549 1563441774564403031484239)
      ·
        refine ⟨2345162661846604547226359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1563441774564403031484239 2345162661846604547226359)
        ·
          refine ⟨3517743992769906820839539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2345162661846604547226359 3517743992769906820839539)
          ·
            refine ⟨5276615989154860231259309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3517743992769906820839539 5276615989154860231259309)
            ·
              refine ⟨1978730995933072586722241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5276615989154860231259309 1978730995933072586722241)
              ·
                refine ⟨1484048246949804440041681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1978730995933072586722241 1484048246949804440041681)
                ·
                  refine ⟨1113036185212353330031261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1484048246949804440041681 1113036185212353330031261)
                  ·
                    refine ⟨417388569454632498761723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1113036185212353330031261 417388569454632498761723)
                    ·
                      rfl

theorem cell22_1219292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1219292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219292 prefixEnd_1219292 := by exact prefixLift 1219292
  have htrace : WordTrace (prefixWord ++ tailWord_1219292) baseStart_1219292 baseEnd_1219292 := by
    simpa [prefixWord, tailWord_1219292, baseEnd_1219292] using wordTrace_append hprefix tailTrace_1219292
  have hstable : (prefixWord ++ tailWord_1219292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219292).length < 2 ^ (prefixWord ++ tailWord_1219292).sum := by decide
  have hdescent : baseEnd_1219292 < baseStart_1219292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219376 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 5, 5]
def baseStart_1219376 : Nat := 118140960795 + 1219376 * 2 ^ 59
def prefixEnd_1219376 : Nat := 4983230072969 + 3 ^ 40 * 1219376 * 2
def baseEnd_1219376 : Nat := 417417324371284279661465

theorem tailTrace_1219376 : CollatzResearch.WordTrace tailWord_1219376 prefixEnd_1219376 417417324371284279661465 := by
  unfold tailWord_1219376
  simp only [CollatzResearch.WordTrace]
  refine ⟨22237148215208239843026991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29649530953610986457369321 22237148215208239843026991)
  ·
    refine ⟨33355722322812359764540487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22237148215208239843026991 33355722322812359764540487)
    ·
      refine ⟨50033583484218539646810731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33355722322812359764540487 50033583484218539646810731)
      ·
        refine ⟨75050375226327809470216097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50033583484218539646810731 75050375226327809470216097)
        ·
          refine ⟨56287781419745857102662073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75050375226327809470216097 56287781419745857102662073)
          ·
            refine ⟨42215836064809392826996555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56287781419745857102662073 42215836064809392826996555)
            ·
              refine ⟨63323754097214089240494833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42215836064809392826996555 63323754097214089240494833)
              ·
                refine ⟨47492815572910566930371125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63323754097214089240494833 47492815572910566930371125)
                ·
                  refine ⟨4452451459960365649722293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47492815572910566930371125 4452451459960365649722293)
                  ·
                    refine ⟨417417324371284279661465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4452451459960365649722293 417417324371284279661465)
                    ·
                      rfl

theorem cell22_1219376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_1219376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219376 prefixEnd_1219376 := by exact prefixLift 1219376
  have htrace : WordTrace (prefixWord ++ tailWord_1219376) baseStart_1219376 baseEnd_1219376 := by
    simpa [prefixWord, tailWord_1219376, baseEnd_1219376] using wordTrace_append hprefix tailTrace_1219376
  have hstable : (prefixWord ++ tailWord_1219376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219376).length < 2 ^ (prefixWord ++ tailWord_1219376).sum := by decide
  have hdescent : baseEnd_1219376 < baseStart_1219376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219408 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 2, 4]
def baseStart_1219408 : Nat := 118140960795 + 1219408 * 2 ^ 59
def prefixEnd_1219408 : Nat := 4983230072969 + 3 ^ 40 * 1219408 * 2
def baseEnd_1219408 : Nat := 417428278625246862861367

theorem tailTrace_1219408 : CollatzResearch.WordTrace tailWord_1219408 prefixEnd_1219408 417428278625246862861367 := by
  unfold tailWord_1219408
  simp only [CollatzResearch.WordTrace]
  refine ⟨22237731783150274575609439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29650309044200366100812585 22237731783150274575609439)
  ·
    refine ⟨33356597674725411863414159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22237731783150274575609439 33356597674725411863414159)
    ·
      refine ⟨50034896512088117795121239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33356597674725411863414159 50034896512088117795121239)
      ·
        refine ⟨75052344768132176692681859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50034896512088117795121239 75052344768132176692681859)
        ·
          refine ⟨112578517152198265039022789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75052344768132176692681859 112578517152198265039022789)
          ·
            refine ⟨21108471966037174694816773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112578517152198265039022789 21108471966037174694816773)
            ·
              refine ⟨3957838493631970255278145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21108471966037174694816773 3957838493631970255278145)
              ·
                refine ⟨2968378870223977691458609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3957838493631970255278145 2968378870223977691458609)
                ·
                  refine ⟨2226284152667983268593957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2968378870223977691458609 2226284152667983268593957)
                  ·
                    refine ⟨417428278625246862861367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2226284152667983268593957 417428278625246862861367)
                    ·
                      rfl

theorem cell22_1219408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_1219408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219408 prefixEnd_1219408 := by exact prefixLift 1219408
  have htrace : WordTrace (prefixWord ++ tailWord_1219408) baseStart_1219408 baseEnd_1219408 := by
    simpa [prefixWord, tailWord_1219408, baseEnd_1219408] using wordTrace_append hprefix tailTrace_1219408
  have hstable : (prefixWord ++ tailWord_1219408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219408).length < 2 ^ (prefixWord ++ tailWord_1219408).sum := by decide
  have hdescent : baseEnd_1219408 < baseStart_1219408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219412 : List Nat := [2, 4, 1, 1, 4, 1, 1, 4, 4]
def baseStart_1219412 : Nat := 118140960795 + 1219412 * 2 ^ 59
def prefixEnd_1219412 : Nat := 4983230072969 + 3 ^ 40 * 1219412 * 2
def baseEnd_1219412 : Nat := 139143215968997395253785

theorem tailTrace_1219412 : CollatzResearch.WordTrace tailWord_1219412 prefixEnd_1219412 139143215968997395253785 := by
  unfold tailWord_1219412
  simp only [CollatzResearch.WordTrace]
  refine ⟨22237804729143028917182245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29650406305524038556242993 22237804729143028917182245)
  ·
    refine ⟨4169588386714317921971671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22237804729143028917182245 4169588386714317921971671)
    ·
      refine ⟨6254382580071476882957507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4169588386714317921971671 6254382580071476882957507)
      ·
        refine ⟨9381573870107215324436261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6254382580071476882957507 9381573870107215324436261)
        ·
          refine ⟨1759045100645102873331799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9381573870107215324436261 1759045100645102873331799)
          ·
            refine ⟨2638567650967654309997699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759045100645102873331799 2638567650967654309997699)
            ·
              refine ⟨3957851476451481464996549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638567650967654309997699 3957851476451481464996549)
              ·
                refine ⟨742097151834652774686853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3957851476451481464996549 742097151834652774686853)
                ·
                  refine ⟨139143215968997395253785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 742097151834652774686853 139143215968997395253785)
                  ·
                    rfl

theorem cell22_1219412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_1219412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219412 prefixEnd_1219412 := by exact prefixLift 1219412
  have htrace : WordTrace (prefixWord ++ tailWord_1219412) baseStart_1219412 baseEnd_1219412 := by
    simpa [prefixWord, tailWord_1219412, baseEnd_1219412] using wordTrace_append hprefix tailTrace_1219412
  have hstable : (prefixWord ++ tailWord_1219412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219412).length < 2 ^ (prefixWord ++ tailWord_1219412).sum := by decide
  have hdescent : baseEnd_1219412 < baseStart_1219412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219478 : List Nat := [5, 3, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1219478 : Nat := 118140960795 + 1219478 * 2 ^ 59
def prefixEnd_1219478 : Nat := 4983230072969 + 3 ^ 40 * 1219478 * 2
def baseEnd_1219478 : Nat := 417452241055790013611153

theorem tailTrace_1219478 : CollatzResearch.WordTrace tailWord_1219478 prefixEnd_1219478 417452241055790013611153 := by
  unfold tailWord_1219478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2779876042252934444141693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29652011117364634070844725 2779876042252934444141693)
  ·
    refine ⟨1042453515844850416553135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2779876042252934444141693 1042453515844850416553135)
    ·
      refine ⟨1563680273767275624829703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1042453515844850416553135 1563680273767275624829703)
      ·
        refine ⟨2345520410650913437244555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1563680273767275624829703 2345520410650913437244555)
        ·
          refine ⟨3518280615976370155866833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2345520410650913437244555 3518280615976370155866833)
          ·
            refine ⟨2638710461982277616900125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3518280615976370155866833 2638710461982277616900125)
            ·
              refine ⟨989516423243354106337547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2638710461982277616900125 989516423243354106337547)
              ·
                refine ⟨1484274634865031159506321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989516423243354106337547 1484274634865031159506321)
                ·
                  refine ⟨1113205976148773369629741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1484274634865031159506321 1113205976148773369629741)
                  ·
                    refine ⟨417452241055790013611153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1113205976148773369629741 417452241055790013611153)
                    ·
                      rfl

theorem cell22_1219478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1219478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219478 prefixEnd_1219478 := by exact prefixLift 1219478
  have htrace : WordTrace (prefixWord ++ tailWord_1219478) baseStart_1219478 baseEnd_1219478 := by
    simpa [prefixWord, tailWord_1219478, baseEnd_1219478] using wordTrace_append hprefix tailTrace_1219478
  have hstable : (prefixWord ++ tailWord_1219478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219478).length < 2 ^ (prefixWord ++ tailWord_1219478).sum := by decide
  have hdescent : baseEnd_1219478 < baseStart_1219478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219543 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 1, 6]
def baseStart_1219543 : Nat := 118140960795 + 1219543 * 2 ^ 59
def prefixEnd_1219543 : Nat := 4983230072969 + 3 ^ 40 * 1219543 * 2
def baseEnd_1219543 : Nat := 417474491884151510735953

theorem tailTrace_1219543 : CollatzResearch.WordTrace tailWord_1219543 prefixEnd_1219543 417474491884151510735953 := by
  unfold tailWord_1219543
  simp only [CollatzResearch.WordTrace]
  refine ⟨44480387420811467207383283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29653591613874311471588855 44480387420811467207383283)
  ·
    refine ⟨66720581131217200811074925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44480387420811467207383283 66720581131217200811074925)
    ·
      refine ⟨25020217924206450304153097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66720581131217200811074925 25020217924206450304153097)
      ·
        refine ⟨18765163443154837728114823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25020217924206450304153097 18765163443154837728114823)
        ·
          refine ⟨28147745164732256592172235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18765163443154837728114823 28147745164732256592172235)
          ·
            refine ⟨42221617747098384888258353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28147745164732256592172235 42221617747098384888258353)
            ·
              refine ⟨31666213310323788666193765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42221617747098384888258353 31666213310323788666193765)
              ·
                refine ⟨5937414995685710374911331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31666213310323788666193765 5937414995685710374911331)
                ·
                  refine ⟨8906122493528565562366997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5937414995685710374911331 8906122493528565562366997)
                  ·
                    refine ⟨417474491884151510735953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8906122493528565562366997 417474491884151510735953)
                    ·
                      rfl

theorem cell22_1219543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_1219543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219543 prefixEnd_1219543 := by exact prefixLift 1219543
  have htrace : WordTrace (prefixWord ++ tailWord_1219543) baseStart_1219543 baseEnd_1219543 := by
    simpa [prefixWord, tailWord_1219543, baseEnd_1219543] using wordTrace_append hprefix tailTrace_1219543
  have hstable : (prefixWord ++ tailWord_1219543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219543).length < 2 ^ (prefixWord ++ tailWord_1219543).sum := by decide
  have hdescent : baseEnd_1219543 < baseStart_1219543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219549 : List Nat := [1, 4, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_1219549 : Nat := 118140960795 + 1219549 * 2 ^ 59
def prefixEnd_1219549 : Nat := 4983230072969 + 3 ^ 40 * 1219549 * 2
def baseEnd_1219549 : Nat := 417476545806769495085935

theorem tailTrace_1219549 : CollatzResearch.WordTrace tailWord_1219549 prefixEnd_1219549 417476545806769495085935 := by
  unfold tailWord_1219549
  simp only [CollatzResearch.WordTrace]
  refine ⟨44480606258789730232101701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29653737505859820154734467 44480606258789730232101701)
  ·
    refine ⟨8340113673523074418519069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44480606258789730232101701 8340113673523074418519069)
    ·
      refine ⟨3127542627571152906944651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8340113673523074418519069 3127542627571152906944651)
      ·
        refine ⟨4691313941356729360416977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3127542627571152906944651 4691313941356729360416977)
        ·
          refine ⟨3518485456017547020312733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4691313941356729360416977 3518485456017547020312733)
          ·
            refine ⟨1319432046006580132617275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3518485456017547020312733 1319432046006580132617275)
            ·
              refine ⟨1979148069009870198925913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319432046006580132617275 1979148069009870198925913)
              ·
                refine ⟨1484361051757402649194435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1979148069009870198925913 1484361051757402649194435)
                ·
                  refine ⟨2226541577636103973791653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484361051757402649194435 2226541577636103973791653)
                  ·
                    refine ⟨417476545806769495085935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2226541577636103973791653 417476545806769495085935)
                    ·
                      rfl

theorem cell22_1219549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_1219549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219549 prefixEnd_1219549 := by exact prefixLift 1219549
  have htrace : WordTrace (prefixWord ++ tailWord_1219549) baseStart_1219549 baseEnd_1219549 := by
    simpa [prefixWord, tailWord_1219549, baseEnd_1219549] using wordTrace_append hprefix tailTrace_1219549
  have hstable : (prefixWord ++ tailWord_1219549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219549).length < 2 ^ (prefixWord ++ tailWord_1219549).sum := by decide
  have hdescent : baseEnd_1219549 < baseStart_1219549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219560 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 2, 4]
def baseStart_1219560 : Nat := 118140960795 + 1219560 * 2 ^ 59
def prefixEnd_1219560 : Nat := 4983230072969 + 3 ^ 40 * 1219560 * 2
def baseEnd_1219560 : Nat := 417480311331569133060901

theorem tailTrace_1219560 : CollatzResearch.WordTrace tailWord_1219560 prefixEnd_1219560 417480311331569133060901 := by
  unfold tailWord_1219560
  simp only [CollatzResearch.WordTrace]
  refine ⟨22240503730874939555376067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29654004974499919407168089 22240503730874939555376067)
  ·
    refine ⟨33360755596312409333064101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22240503730874939555376067 33360755596312409333064101)
    ·
      refine ⟨6255141674308576749949519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33360755596312409333064101 6255141674308576749949519)
      ·
        refine ⟨9382712511462865124924279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6255141674308576749949519 9382712511462865124924279)
        ·
          refine ⟨14074068767194297687386419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9382712511462865124924279 14074068767194297687386419)
          ·
            refine ⟨21111103150791446531079629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14074068767194297687386419 21111103150791446531079629)
            ·
              refine ⟨7916663681546792449154861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21111103150791446531079629 7916663681546792449154861)
              ·
                refine ⟨2968748880580047168433073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7916663681546792449154861 2968748880580047168433073)
                ·
                  refine ⟨2226561660435035376324805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2968748880580047168433073 2226561660435035376324805)
                  ·
                    refine ⟨417480311331569133060901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2226561660435035376324805 417480311331569133060901)
                    ·
                      rfl

theorem cell22_1219560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_1219560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219560 prefixEnd_1219560 := by exact prefixLift 1219560
  have htrace : WordTrace (prefixWord ++ tailWord_1219560) baseStart_1219560 baseEnd_1219560 := by
    simpa [prefixWord, tailWord_1219560, baseEnd_1219560] using wordTrace_append hprefix tailTrace_1219560
  have hstable : (prefixWord ++ tailWord_1219560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219560).length < 2 ^ (prefixWord ++ tailWord_1219560).sum := by decide
  have hdescent : baseEnd_1219560 < baseStart_1219560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219603 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 9]
def baseStart_1219603 : Nat := 118140960795 + 1219603 * 2 ^ 59
def prefixEnd_1219603 : Nat := 4983230072969 + 3 ^ 40 * 1219603 * 2
def baseEnd_1219603 : Nat := 139165010370110451411923

theorem tailTrace_1219603 : CollatzResearch.WordTrace tailWord_1219603 prefixEnd_1219603 139165010370110451411923 := by
  unfold tailWord_1219603
  simp only [CollatzResearch.WordTrace]
  refine ⟨44482575800594097454567463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29655050533729398303044975 44482575800594097454567463)
  ·
    refine ⟨66723863700891146181851195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44482575800594097454567463 66723863700891146181851195)
    ·
      refine ⟨100085795551336719272776793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66723863700891146181851195 100085795551336719272776793)
      ·
        refine ⟨75064346663502539454582595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100085795551336719272776793 75064346663502539454582595)
        ·
          refine ⟨112596519995253809181873893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75064346663502539454582595 112596519995253809181873893)
          ·
            refine ⟨21111847499110089221601355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112596519995253809181873893 21111847499110089221601355)
            ·
              refine ⟨31667771248665133832402033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21111847499110089221601355 31667771248665133832402033)
              ·
                refine ⟨23750828436498850374301525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31667771248665133832402033 23750828436498850374301525)
                ·
                  refine ⟨139165010370110451411923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23750828436498850374301525 139165010370110451411923)
                  ·
                    rfl

theorem cell22_1219603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 9].length) (baseStart_1219603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219603 prefixEnd_1219603 := by exact prefixLift 1219603
  have htrace : WordTrace (prefixWord ++ tailWord_1219603) baseStart_1219603 baseEnd_1219603 := by
    simpa [prefixWord, tailWord_1219603, baseEnd_1219603] using wordTrace_append hprefix tailTrace_1219603
  have hstable : (prefixWord ++ tailWord_1219603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219603).length < 2 ^ (prefixWord ++ tailWord_1219603).sum := by decide
  have hdescent : baseEnd_1219603 < baseStart_1219603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219607 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 5, 3]
def baseStart_1219607 : Nat := 118140960795 + 1219607 * 2 ^ 59
def prefixEnd_1219607 : Nat := 4983230072969 + 3 ^ 40 * 1219607 * 2
def baseEnd_1219607 : Nat := 417496400392076677135757

theorem tailTrace_1219607 : CollatzResearch.WordTrace tailWord_1219607 prefixEnd_1219607 417496400392076677135757 := by
  unfold tailWord_1219607
  simp only [CollatzResearch.WordTrace]
  refine ⟨44482721692579606137713075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29655147795053070758475383 44482721692579606137713075)
  ·
    refine ⟨66724082538869409206569613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44482721692579606137713075 66724082538869409206569613)
    ·
      refine ⟨25021530952076028452463605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66724082538869409206569613 25021530952076028452463605)
      ·
        refine ⟨2345768526757127667418463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25021530952076028452463605 2345768526757127667418463)
        ·
          refine ⟨3518652790135691501127695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2345768526757127667418463 3518652790135691501127695)
          ·
            refine ⟨5277979185203537251691543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3518652790135691501127695 5277979185203537251691543)
            ·
              refine ⟨7916968777805305877537315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5277979185203537251691543 7916968777805305877537315)
              ·
                refine ⟨11875453166707958816305973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7916968777805305877537315 11875453166707958816305973)
                ·
                  refine ⟨1113323734378871139028685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11875453166707958816305973 1113323734378871139028685)
                  ·
                    refine ⟨417496400392076677135757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1113323734378871139028685 417496400392076677135757)
                    ·
                      rfl

theorem cell22_1219607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_1219607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219607 prefixEnd_1219607 := by exact prefixLift 1219607
  have htrace : WordTrace (prefixWord ++ tailWord_1219607) baseStart_1219607 baseEnd_1219607 := by
    simpa [prefixWord, tailWord_1219607, baseEnd_1219607] using wordTrace_append hprefix tailTrace_1219607
  have hstable : (prefixWord ++ tailWord_1219607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219607).length < 2 ^ (prefixWord ++ tailWord_1219607).sum := by decide
  have hdescent : baseEnd_1219607 < baseStart_1219607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219665 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 6]
def baseStart_1219665 : Nat := 118140960795 + 1219665 * 2 ^ 59
def prefixEnd_1219665 : Nat := 4983230072969 + 3 ^ 40 * 1219665 * 2
def baseEnd_1219665 : Nat := 139172084992461286395193

theorem tailTrace_1219665 : CollatzResearch.WordTrace tailWord_1219665 prefixEnd_1219665 139172084992461286395193 := by
  unfold tailWord_1219665
  simp only [CollatzResearch.WordTrace]
  refine ⟨44484837126369482043324449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29656558084246321362216299 44484837126369482043324449)
  ·
    refine ⟨33363627844777111532493337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44484837126369482043324449 33363627844777111532493337)
    ·
      refine ⟨25022720883582833649370003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33363627844777111532493337 25022720883582833649370003)
      ·
        refine ⟨37534081325374250474055005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25022720883582833649370003 37534081325374250474055005)
        ·
          refine ⟨14075280497015343927770627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37534081325374250474055005 14075280497015343927770627)
          ·
            refine ⟨21112920745523015891655941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14075280497015343927770627 21112920745523015891655941)
            ·
              refine ⟨3958672639785565479685489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21112920745523015891655941 3958672639785565479685489)
              ·
                refine ⟨2969004479839174109764117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3958672639785565479685489 2969004479839174109764117)
                ·
                  refine ⟨139172084992461286395193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2969004479839174109764117 139172084992461286395193)
                  ·
                    rfl

theorem cell22_1219665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 6].length) (baseStart_1219665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219665 prefixEnd_1219665 := by exact prefixLift 1219665
  have htrace : WordTrace (prefixWord ++ tailWord_1219665) baseStart_1219665 baseEnd_1219665 := by
    simpa [prefixWord, tailWord_1219665, baseEnd_1219665] using wordTrace_append hprefix tailTrace_1219665
  have hstable : (prefixWord ++ tailWord_1219665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219665).length < 2 ^ (prefixWord ++ tailWord_1219665).sum := by decide
  have hdescent : baseEnd_1219665 < baseStart_1219665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219680 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 3, 5]
def baseStart_1219680 : Nat := 118140960795 + 1219680 * 2 ^ 59
def prefixEnd_1219680 : Nat := 4983230072969 + 3 ^ 40 * 1219680 * 2
def baseEnd_1219680 : Nat := 417521389783928820060533

theorem tailTrace_1219680 : CollatzResearch.WordTrace tailWord_1219680 prefixEnd_1219680 417521389783928820060533 := by
  unfold tailWord_1219680
  simp only [CollatzResearch.WordTrace]
  refine ⟨22242692110657569802560247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29656922814210093070080329 22242692110657569802560247)
  ·
    refine ⟨33364038165986354703840371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22242692110657569802560247 33364038165986354703840371)
    ·
      refine ⟨50046057248979532055760557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33364038165986354703840371 50046057248979532055760557)
      ·
        refine ⟨18767271468367324520910209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50046057248979532055760557 18767271468367324520910209)
        ·
          refine ⟨14075453601275493390682657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18767271468367324520910209 14075453601275493390682657)
          ·
            refine ⟨10556590200956620043011993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14075453601275493390682657 10556590200956620043011993)
            ·
              refine ⟨7917442650717465032258995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10556590200956620043011993 7917442650717465032258995)
              ·
                refine ⟨11876163976076197548388493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7917442650717465032258995 11876163976076197548388493)
                ·
                  refine ⟨4453561491028574080645685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11876163976076197548388493 4453561491028574080645685)
                  ·
                    refine ⟨417521389783928820060533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4453561491028574080645685 417521389783928820060533)
                    ·
                      rfl

theorem cell22_1219680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_1219680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219680 prefixEnd_1219680 := by exact prefixLift 1219680
  have htrace : WordTrace (prefixWord ++ tailWord_1219680) baseStart_1219680 baseEnd_1219680 := by
    simpa [prefixWord, tailWord_1219680, baseEnd_1219680] using wordTrace_append hprefix tailTrace_1219680
  have hstable : (prefixWord ++ tailWord_1219680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219680).length < 2 ^ (prefixWord ++ tailWord_1219680).sum := by decide
  have hdescent : baseEnd_1219680 < baseStart_1219680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219778 : List Nat := [3, 5, 1, 1, 2, 1, 3, 6]
def baseStart_1219778 : Nat := 118140960795 + 1219778 * 2 ^ 59
def prefixEnd_1219778 : Nat := 4983230072969 + 3 ^ 40 * 1219778 * 2
def baseEnd_1219778 : Nat := 46394993020743247901137

theorem tailTrace_1219778 : CollatzResearch.WordTrace tailWord_1219778 prefixEnd_1219778 46394993020743247901137 := by
  unfold tailWord_1219778
  simp only [CollatzResearch.WordTrace]
  refine ⟨11122239643740025585546997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29659305716640068228125325 11122239643740025585546997)
  ·
    refine ⟨1042709966600627398645031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11122239643740025585546997 1042709966600627398645031)
    ·
      refine ⟨1564064949900941097967547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1042709966600627398645031 1564064949900941097967547)
      ·
        refine ⟨2346097424851411646951321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1564064949900941097967547 2346097424851411646951321)
        ·
          refine ⟨1759573068638558735213491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2346097424851411646951321 1759573068638558735213491)
          ·
            refine ⟨2639359602957838102820237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759573068638558735213491 2639359602957838102820237)
            ·
              refine ⟨989759851109189288557589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2639359602957838102820237 989759851109189288557589)
              ·
                refine ⟨46394993020743247901137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 989759851109189288557589 46394993020743247901137)
                ·
                  rfl

theorem cell22_1219778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 6].length) (baseStart_1219778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219778 prefixEnd_1219778 := by exact prefixLift 1219778
  have htrace : WordTrace (prefixWord ++ tailWord_1219778) baseStart_1219778 baseEnd_1219778 := by
    simpa [prefixWord, tailWord_1219778, baseEnd_1219778] using wordTrace_append hprefix tailTrace_1219778
  have hstable : (prefixWord ++ tailWord_1219778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219778).length < 2 ^ (prefixWord ++ tailWord_1219778).sum := by decide
  have hdescent : baseEnd_1219778 < baseStart_1219778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219836 : List Nat := [2, 2, 2, 1, 5, 1, 2, 2, 1, 4]
def baseStart_1219836 : Nat := 118140960795 + 1219836 * 2 ^ 59
def prefixEnd_1219836 : Nat := 4983230072969 + 3 ^ 40 * 1219836 * 2
def baseEnd_1219836 : Nat := 417574791771996413160055

theorem tailTrace_1219836 : CollatzResearch.WordTrace tailWord_1219836 prefixEnd_1219836 417574791771996413160055 := by
  unfold tailWord_1219836
  simp only [CollatzResearch.WordTrace]
  refine ⟨22245537004374989123899681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29660716005833318831866241 22245537004374989123899681)
  ·
    refine ⟨16684152753281241842924761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22245537004374989123899681 16684152753281241842924761)
    ·
      refine ⟨12513114564960931382193571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16684152753281241842924761 12513114564960931382193571)
      ·
        refine ⟨18769671847441397073290357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12513114564960931382193571 18769671847441397073290357)
        ·
          refine ⟨1759656735697630975620971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18769671847441397073290357 1759656735697630975620971)
          ·
            refine ⟨2639485103546446463431457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759656735697630975620971 2639485103546446463431457)
            ·
              refine ⟨1979613827659834847573593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2639485103546446463431457 1979613827659834847573593)
              ·
                refine ⟨1484710370744876135680195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1979613827659834847573593 1484710370744876135680195)
                ·
                  refine ⟨2227065556117314203520293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484710370744876135680195 2227065556117314203520293)
                  ·
                    refine ⟨417574791771996413160055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2227065556117314203520293 417574791771996413160055)
                    ·
                      rfl

theorem cell22_1219836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_1219836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219836 prefixEnd_1219836 := by exact prefixLift 1219836
  have htrace : WordTrace (prefixWord ++ tailWord_1219836) baseStart_1219836 baseEnd_1219836 := by
    simpa [prefixWord, tailWord_1219836, baseEnd_1219836] using wordTrace_append hprefix tailTrace_1219836
  have hstable : (prefixWord ++ tailWord_1219836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219836).length < 2 ^ (prefixWord ++ tailWord_1219836).sum := by decide
  have hdescent : baseEnd_1219836 < baseStart_1219836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219851 : List Nat := [1, 1, 1, 1, 5, 5, 1, 3, 4]
def baseStart_1219851 : Nat := 118140960795 + 1219851 * 2 ^ 59
def prefixEnd_1219851 : Nat := 4983230072969 + 3 ^ 40 * 1219851 * 2
def baseEnd_1219851 : Nat := 139193308859513791345003

theorem tailTrace_1219851 : CollatzResearch.WordTrace tailWord_1219851 prefixEnd_1219851 139193308859513791345003 := by
  unfold tailWord_1219851
  simp only [CollatzResearch.WordTrace]
  refine ⟨44491621103695635809595407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29661080735797090539730271 44491621103695635809595407)
  ·
    refine ⟨66737431655543453714393111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44491621103695635809595407 66737431655543453714393111)
    ·
      refine ⟨100106147483315180571589667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66737431655543453714393111 100106147483315180571589667)
      ·
        refine ⟨150159221224972770857384501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100106147483315180571589667 150159221224972770857384501)
        ·
          refine ⟨14077426989841197267879797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150159221224972770857384501 14077426989841197267879797)
          ·
            refine ⟨1319758780297612243863731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14077426989841197267879797 1319758780297612243863731)
            ·
              refine ⟨1979638170446418365795597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319758780297612243863731 1979638170446418365795597)
              ·
                refine ⟨742364313917406887173349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1979638170446418365795597 742364313917406887173349)
                ·
                  refine ⟨139193308859513791345003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 742364313917406887173349 139193308859513791345003)
                  ·
                    rfl

theorem cell22_1219851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 4].length) (baseStart_1219851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219851 prefixEnd_1219851 := by exact prefixLift 1219851
  have htrace : WordTrace (prefixWord ++ tailWord_1219851) baseStart_1219851 baseEnd_1219851 := by
    simpa [prefixWord, tailWord_1219851, baseEnd_1219851] using wordTrace_append hprefix tailTrace_1219851
  have hstable : (prefixWord ++ tailWord_1219851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219851).length < 2 ^ (prefixWord ++ tailWord_1219851).sum := by decide
  have hdescent : baseEnd_1219851 < baseStart_1219851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219864 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 2, 4]
def baseStart_1219864 : Nat := 118140960795 + 1219864 * 2 ^ 59
def prefixEnd_1219864 : Nat := 4983230072969 + 3 ^ 40 * 1219864 * 2
def baseEnd_1219864 : Nat := 417584376744213673459969

theorem tailTrace_1219864 : CollatzResearch.WordTrace tailWord_1219864 prefixEnd_1219864 417584376744213673459969 := by
  unfold tailWord_1219864
  simp only [CollatzResearch.WordTrace]
  refine ⟨22246047626324269514909323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29661396835099026019879097 22246047626324269514909323)
  ·
    refine ⟨33369071439486404272363985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22246047626324269514909323 33369071439486404272363985)
    ·
      refine ⟨25026803579614803204272989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33369071439486404272363985 25026803579614803204272989)
      ·
        refine ⟨9385051342355551201602371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25026803579614803204272989 9385051342355551201602371)
        ·
          refine ⟨14077577013533326802403557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9385051342355551201602371 14077577013533326802403557)
          ·
            refine ⟨2639545690037498775450667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14077577013533326802403557 2639545690037498775450667)
            ·
              refine ⟨3959318535056248163176001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639545690037498775450667 3959318535056248163176001)
              ·
                refine ⟨2969488901292186122382001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3959318535056248163176001 2969488901292186122382001)
                ·
                  refine ⟨2227116675969139591786501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2969488901292186122382001 2227116675969139591786501)
                  ·
                    refine ⟨417584376744213673459969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2227116675969139591786501 417584376744213673459969)
                    ·
                      rfl

theorem cell22_1219864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_1219864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219864 prefixEnd_1219864 := by exact prefixLift 1219864
  have htrace : WordTrace (prefixWord ++ tailWord_1219864) baseStart_1219864 baseEnd_1219864 := by
    simpa [prefixWord, tailWord_1219864, baseEnd_1219864] using wordTrace_append hprefix tailTrace_1219864
  have hstable : (prefixWord ++ tailWord_1219864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219864).length < 2 ^ (prefixWord ++ tailWord_1219864).sum := by decide
  have hdescent : baseEnd_1219864 < baseStart_1219864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219939 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 2, 5]
def baseStart_1219939 : Nat := 118140960795 + 1219939 * 2 ^ 59
def prefixEnd_1219939 : Nat := 4983230072969 + 3 ^ 40 * 1219939 * 2
def baseEnd_1219939 : Nat := 417610050776938477834739

theorem tailTrace_1219939 : CollatzResearch.WordTrace tailWord_1219939 prefixEnd_1219939 417610050776938477834739 := by
  unfold tailWord_1219939
  simp only [CollatzResearch.WordTrace]
  refine ⟨44494830727376826838798871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29663220484917884559199247 44494830727376826838798871)
  ·
    refine ⟨66742246091065240258198307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44494830727376826838798871 66742246091065240258198307)
    ·
      refine ⟨100113369136597860387297461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66742246091065240258198307 100113369136597860387297461)
      ·
        refine ⟨9385628356556049411309137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100113369136597860387297461 9385628356556049411309137)
        ·
          refine ⟨7039221267417037058481853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9385628356556049411309137 7039221267417037058481853)
          ·
            refine ⟨2639707975281388896930695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7039221267417037058481853 2639707975281388896930695)
            ·
              refine ⟨3959561962922083345396043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639707975281388896930695 3959561962922083345396043)
              ·
                refine ⟨5939342944383125018094065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3959561962922083345396043 5939342944383125018094065)
                ·
                  refine ⟨4454507208287343763570549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5939342944383125018094065 4454507208287343763570549)
                  ·
                    refine ⟨417610050776938477834739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4454507208287343763570549 417610050776938477834739)
                    ·
                      rfl

theorem cell22_1219939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 5].length) (baseStart_1219939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219939 prefixEnd_1219939 := by exact prefixLift 1219939
  have htrace : WordTrace (prefixWord ++ tailWord_1219939) baseStart_1219939 baseEnd_1219939 := by
    simpa [prefixWord, tailWord_1219939, baseEnd_1219939] using wordTrace_append hprefix tailTrace_1219939
  have hstable : (prefixWord ++ tailWord_1219939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219939).length < 2 ^ (prefixWord ++ tailWord_1219939).sum := by decide
  have hdescent : baseEnd_1219939 < baseStart_1219939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219954 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_1219954 : Nat := 118140960795 + 1219954 * 2 ^ 59
def prefixEnd_1219954 : Nat := 4983230072969 + 3 ^ 40 * 1219954 * 2
def baseEnd_1219954 : Nat := 417615185583483438709693

theorem tailTrace_1219954 : CollatzResearch.WordTrace tailWord_1219954 prefixEnd_1219954 417615185583483438709693 := by
  unfold tailWord_1219954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11123844455580621100148729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29663585214881656267063277 11123844455580621100148729)
  ·
    refine ⟨8342883341685465825111547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11123844455580621100148729 8342883341685465825111547)
    ·
      refine ⟨12514325012528198737667321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8342883341685465825111547 12514325012528198737667321)
      ·
        refine ⟨9385743759396149053250491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12514325012528198737667321 9385743759396149053250491)
        ·
          refine ⟨14078615639094223579875737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9385743759396149053250491 14078615639094223579875737)
          ·
            refine ⟨10558961729320667684906803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14078615639094223579875737 10558961729320667684906803)
            ·
              refine ⟨15838442593981001527360205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10558961729320667684906803 15838442593981001527360205)
              ·
                refine ⟨5939415972742875572760077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15838442593981001527360205 5939415972742875572760077)
                ·
                  refine ⟨2227280989778578339785029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5939415972742875572760077 2227280989778578339785029)
                  ·
                    refine ⟨417615185583483438709693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2227280989778578339785029 417615185583483438709693)
                    ·
                      rfl

theorem cell22_1219954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_1219954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219954 prefixEnd_1219954 := by exact prefixLift 1219954
  have htrace : WordTrace (prefixWord ++ tailWord_1219954) baseStart_1219954 baseEnd_1219954 := by
    simpa [prefixWord, tailWord_1219954, baseEnd_1219954] using wordTrace_append hprefix tailTrace_1219954
  have hstable : (prefixWord ++ tailWord_1219954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219954).length < 2 ^ (prefixWord ++ tailWord_1219954).sum := by decide
  have hdescent : baseEnd_1219954 < baseStart_1219954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219971 : List Nat := [1, 1, 1, 3, 5, 2, 1, 3, 1, 4]
def baseStart_1219971 : Nat := 118140960795 + 1219971 * 2 ^ 59
def prefixEnd_1219971 : Nat := 4983230072969 + 3 ^ 40 * 1219971 * 2
def baseEnd_1219971 : Nat := 417621005030901061034641

theorem tailTrace_1219971 : CollatzResearch.WordTrace tailWord_1219971 prefixEnd_1219971 417621005030901061034641 := by
  unfold tailWord_1219971
  simp only [CollatzResearch.WordTrace]
  refine ⟨44495997863260896303963767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29663998575507264202642511 44495997863260896303963767)
  ·
    refine ⟨66743996794891344455945651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44495997863260896303963767 66743996794891344455945651)
    ·
      refine ⟨100115995192337016683918477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66743996794891344455945651 100115995192337016683918477)
      ·
        refine ⟨37543498197126381256469429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100115995192337016683918477 37543498197126381256469429)
        ·
          refine ⟨3519702955980598242794009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37543498197126381256469429 3519702955980598242794009)
          ·
            refine ⟨2639777216985448682095507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3519702955980598242794009 2639777216985448682095507)
            ·
              refine ⟨3959665825478173023143261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639777216985448682095507 3959665825478173023143261)
              ·
                refine ⟨1484874684554314883678723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3959665825478173023143261 1484874684554314883678723)
                ·
                  refine ⟨2227312026831472325518085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484874684554314883678723 2227312026831472325518085)
                  ·
                    refine ⟨417621005030901061034641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2227312026831472325518085 417621005030901061034641)
                    ·
                      rfl

theorem cell22_1219971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 4].length) (baseStart_1219971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219971 prefixEnd_1219971 := by exact prefixLift 1219971
  have htrace : WordTrace (prefixWord ++ tailWord_1219971) baseStart_1219971 baseEnd_1219971 := by
    simpa [prefixWord, tailWord_1219971, baseEnd_1219971] using wordTrace_append hprefix tailTrace_1219971
  have hstable : (prefixWord ++ tailWord_1219971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219971).length < 2 ^ (prefixWord ++ tailWord_1219971).sum := by decide
  have hdescent : baseEnd_1219971 < baseStart_1219971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219999 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 1, 6]
def baseStart_1219999 : Nat := 118140960795 + 1219999 * 2 ^ 59
def prefixEnd_1219999 : Nat := 4983230072969 + 3 ^ 40 * 1219999 * 2
def baseEnd_1219999 : Nat := 417630590003118321334555

theorem tailTrace_1219999 : CollatzResearch.WordTrace tailWord_1219999 prefixEnd_1219999 417630590003118321334555 := by
  unfold tailWord_1219999
  simp only [CollatzResearch.WordTrace]
  refine ⟨44497019107159457085983051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29664679404772971390655367 44497019107159457085983051)
  ·
    refine ⟨66745528660739185628974577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44497019107159457085983051 66745528660739185628974577)
    ·
      refine ⟨50059146495554389221730933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66745528660739185628974577 50059146495554389221730933)
      ·
        refine ⟨4693044983958223989537275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50059146495554389221730933 4693044983958223989537275)
        ·
          refine ⟨7039567475937335984305913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4693044983958223989537275 7039567475937335984305913)
          ·
            refine ⟨5279675606953001988229435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7039567475937335984305913 5279675606953001988229435)
            ·
              refine ⟨7919513410429502982344153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5279675606953001988229435 7919513410429502982344153)
              ·
                refine ⟨5939635057822127236758115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7919513410429502982344153 5939635057822127236758115)
                ·
                  refine ⟨8909452586733190855137173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5939635057822127236758115 8909452586733190855137173)
                  ·
                    refine ⟨417630590003118321334555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8909452586733190855137173 417630590003118321334555)
                    ·
                      rfl

theorem cell22_1219999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_1219999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1219999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1219999 prefixEnd_1219999 := by exact prefixLift 1219999
  have htrace : WordTrace (prefixWord ++ tailWord_1219999) baseStart_1219999 baseEnd_1219999 := by
    simpa [prefixWord, tailWord_1219999, baseEnd_1219999] using wordTrace_append hprefix tailTrace_1219999
  have hstable : (prefixWord ++ tailWord_1219999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219999).length < 2 ^ (prefixWord ++ tailWord_1219999).sum := by decide
  have hdescent : baseEnd_1219999 < baseStart_1219999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220052 : List Nat := [2, 4, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_1220052 : Nat := 118140960795 + 1220052 * 2 ^ 59
def prefixEnd_1220052 : Nat := 4983230072969 + 3 ^ 40 * 1220052 * 2
def baseEnd_1220052 : Nat := 417648732986243849759393

theorem tailTrace_1220052 : CollatzResearch.WordTrace tailWord_1220052 prefixEnd_1220052 417648732986243849759393 := by
  unfold tailWord_1220052
  simp only [CollatzResearch.WordTrace]
  refine ⟨22249476087983723568831205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29665968117311631425108273 22249476087983723568831205)
  ·
    refine ⟨4171776766496948169155851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22249476087983723568831205 4171776766496948169155851)
    ·
      refine ⟨6257665149745422253733777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4171776766496948169155851 6257665149745422253733777)
      ·
        refine ⟨4693248862309066690300333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6257665149745422253733777 4693248862309066690300333)
        ·
          refine ⟨1759968323365900008862625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4693248862309066690300333 1759968323365900008862625)
          ·
            refine ⟨1319976242524425006646969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1759968323365900008862625 1319976242524425006646969)
            ·
              refine ⟨989982181893318754985227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1319976242524425006646969 989982181893318754985227)
              ·
                refine ⟨1484973272839978132477841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989982181893318754985227 1484973272839978132477841)
                ·
                  refine ⟨1113729954629983599358381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1484973272839978132477841 1113729954629983599358381)
                  ·
                    refine ⟨417648732986243849759393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1113729954629983599358381 417648732986243849759393)
                    ·
                      rfl

theorem cell22_1220052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_1220052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220052 prefixEnd_1220052 := by exact prefixLift 1220052
  have htrace : WordTrace (prefixWord ++ tailWord_1220052) baseStart_1220052 baseEnd_1220052 := by
    simpa [prefixWord, tailWord_1220052, baseEnd_1220052] using wordTrace_append hprefix tailTrace_1220052
  have hstable : (prefixWord ++ tailWord_1220052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220052).length < 2 ^ (prefixWord ++ tailWord_1220052).sum := by decide
  have hdescent : baseEnd_1220052 < baseStart_1220052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220106 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_1220106 : Nat := 118140960795 + 1220106 * 2 ^ 59
def prefixEnd_1220106 : Nat := 4983230072969 + 3 ^ 40 * 1220106 * 2
def baseEnd_1220106 : Nat := 417667218289805708909227

theorem tailTrace_1220106 : CollatzResearch.WordTrace tailWord_1220106 prefixEnd_1220106 417667218289805708909227 := by
  unfold tailWord_1220106
  simp only [CollatzResearch.WordTrace]
  refine ⟨11125230429442953590032043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29667281145181209573418781 11125230429442953590032043)
  ·
    refine ⟨16687845644164430385048065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11125230429442953590032043 16687845644164430385048065)
    ·
      refine ⟨12515884233123322788786049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16687845644164430385048065 12515884233123322788786049)
      ·
        refine ⟨9386913174842492091589537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12515884233123322788786049 9386913174842492091589537)
        ·
          refine ⟨7040184881131869068692153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9386913174842492091589537 7040184881131869068692153)
          ·
            refine ⟨5280138660848901801519115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7040184881131869068692153 5280138660848901801519115)
            ·
              refine ⟨7920207991273352702278673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5280138660848901801519115 7920207991273352702278673)
              ·
                refine ⟨5940155993455014526709005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7920207991273352702278673 5940155993455014526709005)
                ·
                  refine ⟨2227558497545630447515877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5940155993455014526709005 2227558497545630447515877)
                  ·
                    refine ⟨417667218289805708909227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2227558497545630447515877 417667218289805708909227)
                    ·
                      rfl

theorem cell22_1220106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_1220106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220106 prefixEnd_1220106 := by exact prefixLift 1220106
  have htrace : WordTrace (prefixWord ++ tailWord_1220106) baseStart_1220106 baseEnd_1220106 := by
    simpa [prefixWord, tailWord_1220106, baseEnd_1220106] using wordTrace_append hprefix tailTrace_1220106
  have hstable : (prefixWord ++ tailWord_1220106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220106).length < 2 ^ (prefixWord ++ tailWord_1220106).sum := by decide
  have hdescent : baseEnd_1220106 < baseStart_1220106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220153 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 4, 3]
def baseStart_1220153 : Nat := 118140960795 + 1220153 * 2 ^ 59
def prefixEnd_1220153 : Nat := 4983230072969 + 3 ^ 40 * 1220153 * 2
def baseEnd_1220153 : Nat := 417683307350313252984083

theorem tailTrace_1220153 : CollatzResearch.WordTrace tailWord_1220153 prefixEnd_1220153 417683307350313252984083 := by
  unfold tailWord_1220153
  simp only [CollatzResearch.WordTrace]
  refine ⟨44502635948601541387089113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29668423965734360924726075 44502635948601541387089113)
  ·
    refine ⟨33376976961451156040316835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44502635948601541387089113 33376976961451156040316835)
    ·
      refine ⟨50065465442176734060475253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33376976961451156040316835 50065465442176734060475253)
      ·
        refine ⟨4693637385204068818169555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50065465442176734060475253 4693637385204068818169555)
        ·
          refine ⟨7040456077806103227254333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4693637385204068818169555 7040456077806103227254333)
          ·
            refine ⟨2640171029177288710220375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7040456077806103227254333 2640171029177288710220375)
            ·
              refine ⟨3960256543765933065330563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2640171029177288710220375 3960256543765933065330563)
              ·
                refine ⟨5940384815648899597995845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3960256543765933065330563 5940384815648899597995845)
                ·
                  refine ⟨1113822152934168674624221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5940384815648899597995845 1113822152934168674624221)
                  ·
                    refine ⟨417683307350313252984083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1113822152934168674624221 417683307350313252984083)
                    ·
                      rfl

theorem cell22_1220153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 3].length) (baseStart_1220153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220153 prefixEnd_1220153 := by exact prefixLift 1220153
  have htrace : WordTrace (prefixWord ++ tailWord_1220153) baseStart_1220153 baseEnd_1220153 := by
    simpa [prefixWord, tailWord_1220153, baseEnd_1220153] using wordTrace_append hprefix tailTrace_1220153
  have hstable : (prefixWord ++ tailWord_1220153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220153).length < 2 ^ (prefixWord ++ tailWord_1220153).sum := by decide
  have hdescent : baseEnd_1220153 < baseStart_1220153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220170 : List Nat := [3, 1, 2, 1, 1, 3, 5, 1, 2, 3]
def baseStart_1220170 : Nat := 118140960795 + 1220170 * 2 ^ 59
def prefixEnd_1220170 : Nat := 4983230072969 + 3 ^ 40 * 1220170 * 2
def baseEnd_1220170 : Nat := 417689126797730875309031

theorem tailTrace_1220170 : CollatzResearch.WordTrace tailWord_1220170 prefixEnd_1220170 417689126797730875309031 := by
  unfold tailWord_1220170
  simp only [CollatzResearch.WordTrace]
  refine ⟨11125813997384988322614491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29668837326359968860305309 11125813997384988322614491)
  ·
    refine ⟨16688720996077482483921737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11125813997384988322614491 16688720996077482483921737)
    ·
      refine ⟨12516540747058111862941303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16688720996077482483921737 12516540747058111862941303)
      ·
        refine ⟨18774811120587167794411955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12516540747058111862941303 18774811120587167794411955)
        ·
          refine ⟨28162216680880751691617933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18774811120587167794411955 28162216680880751691617933)
          ·
            refine ⟨10560831255330281884356725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28162216680880751691617933 10560831255330281884356725)
            ·
              refine ⟨990077930187213926658443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10560831255330281884356725 990077930187213926658443)
              ·
                refine ⟨1485116895280820889987665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990077930187213926658443 1485116895280820889987665)
                ·
                  refine ⟨1113837671460615667490749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1485116895280820889987665 1113837671460615667490749)
                  ·
                    refine ⟨417689126797730875309031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1113837671460615667490749 417689126797730875309031)
                    ·
                      rfl

theorem cell22_1220170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_1220170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220170 prefixEnd_1220170 := by exact prefixLift 1220170
  have htrace : WordTrace (prefixWord ++ tailWord_1220170) baseStart_1220170 baseEnd_1220170 := by
    simpa [prefixWord, tailWord_1220170, baseEnd_1220170] using wordTrace_append hprefix tailTrace_1220170
  have hstable : (prefixWord ++ tailWord_1220170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220170).length < 2 ^ (prefixWord ++ tailWord_1220170).sum := by decide
  have hdescent : baseEnd_1220170 < baseStart_1220170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220183 : List Nat := [1, 1, 3, 2, 2, 5, 2, 6]
def baseStart_1220183 : Nat := 118140960795 + 1220183 * 2 ^ 59
def prefixEnd_1220183 : Nat := 4983230072969 + 3 ^ 40 * 1220183 * 2
def baseEnd_1220183 : Nat := 46410397440378130525999

theorem tailTrace_1220183 : CollatzResearch.WordTrace tailWord_1220183 prefixEnd_1220183 46410397440378130525999 := by
  unfold tailWord_1220183
  simp only [CollatzResearch.WordTrace]
  refine ⟨44503730138492856510681203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29669153425661904340454135 44503730138492856510681203)
  ·
    refine ⟨66755595207739284766021805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44503730138492856510681203 66755595207739284766021805)
    ·
      refine ⟨25033348202902231787258177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66755595207739284766021805 25033348202902231787258177)
      ·
        refine ⟨18775011152176673840443633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25033348202902231787258177 18775011152176673840443633)
        ·
          refine ⟨14081258364132505380332725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18775011152176673840443633 14081258364132505380332725)
          ·
            refine ⟨1320117971637422379406193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14081258364132505380332725 1320117971637422379406193)
            ·
              refine ⟨990088478728066784554645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1320117971637422379406193 990088478728066784554645)
              ·
                refine ⟨46410397440378130525999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 990088478728066784554645 46410397440378130525999)
                ·
                  rfl

theorem cell22_1220183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 6].length) (baseStart_1220183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220183 prefixEnd_1220183 := by exact prefixLift 1220183
  have htrace : WordTrace (prefixWord ++ tailWord_1220183) baseStart_1220183 baseEnd_1220183 := by
    simpa [prefixWord, tailWord_1220183, baseEnd_1220183] using wordTrace_append hprefix tailTrace_1220183
  have hstable : (prefixWord ++ tailWord_1220183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220183).length < 2 ^ (prefixWord ++ tailWord_1220183).sum := by decide
  have hdescent : baseEnd_1220183 < baseStart_1220183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220189 : List Nat := [1, 4, 4, 2, 1, 2, 1, 3, 4]
def baseStart_1220189 : Nat := 118140960795 + 1220189 * 2 ^ 59
def prefixEnd_1220189 : Nat := 4983230072969 + 3 ^ 40 * 1220189 * 2
def baseEnd_1220189 : Nat := 139231876962007053027991

theorem tailTrace_1220189 : CollatzResearch.WordTrace tailWord_1220189 prefixEnd_1220189 139231876962007053027991 := by
  unfold tailWord_1220189
  simp only [CollatzResearch.WordTrace]
  refine ⟨44503948976471119535399621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29669299317647413023599747 44503948976471119535399621)
  ·
    refine ⟨8344490433088334912887429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44503948976471119535399621 8344490433088334912887429)
    ·
      refine ⟨1564591956204062796166393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8344490433088334912887429 1564591956204062796166393)
      ·
        refine ⟨1173443967153047097124795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1564591956204062796166393 1173443967153047097124795)
        ·
          refine ⟨1760165950729570645687193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1173443967153047097124795 1760165950729570645687193)
          ·
            refine ⟨1320124463047177984265395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1760165950729570645687193 1320124463047177984265395)
            ·
              refine ⟨1980186694570766976398093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320124463047177984265395 1980186694570766976398093)
              ·
                refine ⟨742570010464037616149285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1980186694570766976398093 742570010464037616149285)
                ·
                  refine ⟨139231876962007053027991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 742570010464037616149285 139231876962007053027991)
                  ·
                    rfl

theorem cell22_1220189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_1220189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220189 prefixEnd_1220189 := by exact prefixLift 1220189
  have htrace : WordTrace (prefixWord ++ tailWord_1220189) baseStart_1220189 baseEnd_1220189 := by
    simpa [prefixWord, tailWord_1220189, baseEnd_1220189] using wordTrace_append hprefix tailTrace_1220189
  have hstable : (prefixWord ++ tailWord_1220189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220189).length < 2 ^ (prefixWord ++ tailWord_1220189).sum := by decide
  have hdescent : baseEnd_1220189 < baseStart_1220189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220271 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 3, 5]
def baseStart_1220271 : Nat := 118140960795 + 1220271 * 2 ^ 59
def prefixEnd_1220271 : Nat := 4983230072969 + 3 ^ 40 * 1220271 * 2
def baseEnd_1220271 : Nat := 417723701161800278533721

theorem tailTrace_1220271 : CollatzResearch.WordTrace tailWord_1220271 prefixEnd_1220271 417723701161800278533721 := by
  unfold tailWord_1220271
  simp only [CollatzResearch.WordTrace]
  refine ⟨44506939762174047539884667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29671293174782698359923111 44506939762174047539884667)
  ·
    refine ⟨66760409643261071309827001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44506939762174047539884667 66760409643261071309827001)
    ·
      refine ⟨50070307232445803482370251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66760409643261071309827001 50070307232445803482370251)
      ·
        refine ⟨75105460848668705223555377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50070307232445803482370251 75105460848668705223555377)
        ·
          refine ⟨56329095636501528917666533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75105460848668705223555377 56329095636501528917666533)
          ·
            refine ⟨10561705431844036672062475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56329095636501528917666533 10561705431844036672062475)
            ·
              refine ⟨15842558147766055008093713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10561705431844036672062475 15842558147766055008093713)
              ·
                refine ⟨11881918610824541256070285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15842558147766055008093713 11881918610824541256070285)
                ·
                  refine ⟨4455719479059202971026357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11881918610824541256070285 4455719479059202971026357)
                  ·
                    refine ⟨417723701161800278533721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4455719479059202971026357 417723701161800278533721)
                    ·
                      rfl

theorem cell22_1220271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_1220271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220271 prefixEnd_1220271 := by exact prefixLift 1220271
  have htrace : WordTrace (prefixWord ++ tailWord_1220271) baseStart_1220271 baseEnd_1220271 := by
    simpa [prefixWord, tailWord_1220271, baseEnd_1220271] using wordTrace_append hprefix tailTrace_1220271
  have hstable : (prefixWord ++ tailWord_1220271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220271).length < 2 ^ (prefixWord ++ tailWord_1220271).sum := by decide
  have hdescent : baseEnd_1220271 < baseStart_1220271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220288 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 1, 5]
def baseStart_1220288 : Nat := 118140960795 + 1220288 * 2 ^ 59
def prefixEnd_1220288 : Nat := 4983230072969 + 3 ^ 40 * 1220288 * 2
def baseEnd_1220288 : Nat := 417729520609217900858669

theorem tailTrace_1220288 : CollatzResearch.WordTrace tailWord_1220288 prefixEnd_1220288 417729520609217900858669 := by
  unfold tailWord_1220288
  simp only [CollatzResearch.WordTrace]
  refine ⟨22253779901556229721626759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29671706535408306295502345 22253779901556229721626759)
  ·
    refine ⟨33380669852334344582440139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22253779901556229721626759 33380669852334344582440139)
    ·
      refine ⟨50071004778501516873660209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33380669852334344582440139 50071004778501516873660209)
      ·
        refine ⟨37553253583876137655245157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50071004778501516873660209 37553253583876137655245157)
        ·
          refine ⟨7041235046976775810358467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37553253583876137655245157 7041235046976775810358467)
          ·
            refine ⟨10561852570465163715537701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7041235046976775810358467 10561852570465163715537701)
            ·
              refine ⟨1980347356962218196663319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10561852570465163715537701 1980347356962218196663319)
              ·
                refine ⟨2970521035443327294994979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980347356962218196663319 2970521035443327294994979)
                ·
                  refine ⟨4455781553164990942492469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2970521035443327294994979 4455781553164990942492469)
                  ·
                    refine ⟨417729520609217900858669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4455781553164990942492469 417729520609217900858669)
                    ·
                      rfl

theorem cell22_1220288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_1220288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220288 prefixEnd_1220288 := by exact prefixLift 1220288
  have htrace : WordTrace (prefixWord ++ tailWord_1220288) baseStart_1220288 baseEnd_1220288 := by
    simpa [prefixWord, tailWord_1220288, baseEnd_1220288] using wordTrace_append hprefix tailTrace_1220288
  have hstable : (prefixWord ++ tailWord_1220288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220288).length < 2 ^ (prefixWord ++ tailWord_1220288).sum := by decide
  have hdescent : baseEnd_1220288 < baseStart_1220288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220331 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 1, 8]
def baseStart_1220331 : Nat := 118140960795 + 1220331 * 2 ^ 59
def prefixEnd_1220331 : Nat := 4983230072969 + 3 ^ 40 * 1220331 * 2
def baseEnd_1220331 : Nat := 417744240387980122033537

theorem tailTrace_1220331 : CollatzResearch.WordTrace tailWord_1220331 prefixEnd_1220331 417744240387980122033537 := by
  unfold tailWord_1220331
  simp only [CollatzResearch.WordTrace]
  refine ⟨44509128141956677787068847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29672752094637785191379231 44509128141956677787068847)
  ·
    refine ⟨66763692212935016680603271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44509128141956677787068847 66763692212935016680603271)
    ·
      refine ⟨100145538319402525020904907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66763692212935016680603271 100145538319402525020904907)
      ·
        refine ⟨150218307479103787531357361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100145538319402525020904907 150218307479103787531357361)
        ·
          refine ⟨112663730609327840648518021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150218307479103787531357361 112663730609327840648518021)
          ·
            refine ⟨21124449489248970121597129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112663730609327840648518021 21124449489248970121597129)
            ·
              refine ⟨15843337116936727591197847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21124449489248970121597129 15843337116936727591197847)
              ·
                refine ⟨23765005675405091386796771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15843337116936727591197847 23765005675405091386796771)
                ·
                  refine ⟨35647508513107637080195157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23765005675405091386796771 35647508513107637080195157)
                  ·
                    refine ⟨417744240387980122033537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35647508513107637080195157 417744240387980122033537)
                    ·
                      rfl

theorem cell22_1220331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_1220331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220331 prefixEnd_1220331 := by exact prefixLift 1220331
  have htrace : WordTrace (prefixWord ++ tailWord_1220331) baseStart_1220331 baseEnd_1220331 := by
    simpa [prefixWord, tailWord_1220331, baseEnd_1220331] using wordTrace_append hprefix tailTrace_1220331
  have hstable : (prefixWord ++ tailWord_1220331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220331).length < 2 ^ (prefixWord ++ tailWord_1220331).sum := by decide
  have hdescent : baseEnd_1220331 < baseStart_1220331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220384 : List Nat := [2, 1, 1, 5, 1, 1, 5, 2, 1, 3]
def baseStart_1220384 : Nat := 118140960795 + 1220384 * 2 ^ 59
def prefixEnd_1220384 : Nat := 4983230072969 + 3 ^ 40 * 1220384 * 2
def baseEnd_1220384 : Nat := 417762383371105650458375

theorem tailTrace_1220384 : CollatzResearch.WordTrace tailWord_1220384 prefixEnd_1220384 417762383371105650458375 := by
  unfold tailWord_1220384
  simp only [CollatzResearch.WordTrace]
  refine ⟨22255530605382333919374103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29674040807176445225832137 22255530605382333919374103)
  ·
    refine ⟨33383295908073500879061155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22255530605382333919374103 33383295908073500879061155)
    ·
      refine ⟨50074943862110251318591733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33383295908073500879061155 50074943862110251318591733)
      ·
        refine ⟨4694525987072836061117975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50074943862110251318591733 4694525987072836061117975)
        ·
          refine ⟨7041788980609254091676963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4694525987072836061117975 7041788980609254091676963)
          ·
            refine ⟨10562683470913881137515445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7041788980609254091676963 10562683470913881137515445)
            ·
              refine ⟨990251575398176356642073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10562683470913881137515445 990251575398176356642073)
              ·
                refine ⟨742688681548632267481555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 990251575398176356642073 742688681548632267481555)
                ·
                  refine ⟨1114033022322948401222333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742688681548632267481555 1114033022322948401222333)
                  ·
                    refine ⟨417762383371105650458375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1114033022322948401222333 417762383371105650458375)
                    ·
                      rfl

theorem cell22_1220384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 1, 3].length) (baseStart_1220384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220384 prefixEnd_1220384 := by exact prefixLift 1220384
  have htrace : WordTrace (prefixWord ++ tailWord_1220384) baseStart_1220384 baseEnd_1220384 := by
    simpa [prefixWord, tailWord_1220384, baseEnd_1220384] using wordTrace_append hprefix tailTrace_1220384
  have hstable : (prefixWord ++ tailWord_1220384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220384).length < 2 ^ (prefixWord ++ tailWord_1220384).sum := by decide
  have hdescent : baseEnd_1220384 < baseStart_1220384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220410 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_1220410 : Nat := 118140960795 + 1220410 * 2 ^ 59
def prefixEnd_1220410 : Nat := 4983230072969 + 3 ^ 40 * 1220410 * 2
def baseEnd_1220410 : Nat := 417771283702450249308295

theorem tailTrace_1220410 : CollatzResearch.WordTrace tailWord_1220410 prefixEnd_1220410 417771283702450249308295 := by
  unfold tailWord_1220410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11128002377167618569798671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29674673005780316186129789 11128002377167618569798671)
  ·
    refine ⟨16692003565751427854698007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11128002377167618569798671 16692003565751427854698007)
    ·
      refine ⟨25038005348627141782047011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16692003565751427854698007 25038005348627141782047011)
      ·
        refine ⟨37557008022940712673070517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25038005348627141782047011 37557008022940712673070517)
        ·
          refine ⟨3520969502150691813100361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37557008022940712673070517 3520969502150691813100361)
          ·
            refine ⟨2640727126613018859825271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3520969502150691813100361 2640727126613018859825271)
            ·
              refine ⟨3961090689919528289737907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2640727126613018859825271 3961090689919528289737907)
              ·
                refine ⟨5941636034879292434606861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3961090689919528289737907 5941636034879292434606861)
                ·
                  refine ⟨2228113513079734662977573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5941636034879292434606861 2228113513079734662977573)
                  ·
                    refine ⟨417771283702450249308295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2228113513079734662977573 417771283702450249308295)
                    ·
                      rfl

theorem cell22_1220410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_1220410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220410 prefixEnd_1220410 := by exact prefixLift 1220410
  have htrace : WordTrace (prefixWord ++ tailWord_1220410) baseStart_1220410 baseEnd_1220410 := by
    simpa [prefixWord, tailWord_1220410, baseEnd_1220410] using wordTrace_append hprefix tailTrace_1220410
  have hstable : (prefixWord ++ tailWord_1220410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220410).length < 2 ^ (prefixWord ++ tailWord_1220410).sum := by decide
  have hdescent : baseEnd_1220410 < baseStart_1220410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220423 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 3, 5]
def baseStart_1220423 : Nat := 118140960795 + 1220423 * 2 ^ 59
def prefixEnd_1220423 : Nat := 4983230072969 + 3 ^ 40 * 1220423 * 2
def baseEnd_1220423 : Nat := 417775733868122548733255

theorem tailTrace_1220423 : CollatzResearch.WordTrace tailWord_1220423 prefixEnd_1220423 417775733868122548733255 := by
  unfold tailWord_1220423
  simp only [CollatzResearch.WordTrace]
  refine ⟨44512483657623377499417923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29674989105082251666278615 44512483657623377499417923)
  ·
    refine ⟨66768725486435066249126885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44512483657623377499417923 66768725486435066249126885)
    ·
      refine ⟨12519136028706574921711291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66768725486435066249126885 12519136028706574921711291)
      ·
        refine ⟨18778704043059862382566937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12519136028706574921711291 18778704043059862382566937)
        ·
          refine ⟨14084028032294896786925203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18778704043059862382566937 14084028032294896786925203)
          ·
            refine ⟨21126042048442345180387805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14084028032294896786925203 21126042048442345180387805)
            ·
              refine ⟨7922265768165879442645427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21126042048442345180387805 7922265768165879442645427)
              ·
                refine ⟨11883398652248819163968141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7922265768165879442645427 11883398652248819163968141)
                ·
                  refine ⟨4456274494593307186488053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11883398652248819163968141 4456274494593307186488053)
                  ·
                    refine ⟨417775733868122548733255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4456274494593307186488053 417775733868122548733255)
                    ·
                      rfl

theorem cell22_1220423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_1220423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220423 prefixEnd_1220423 := by exact prefixLift 1220423
  have htrace : WordTrace (prefixWord ++ tailWord_1220423) baseStart_1220423 baseEnd_1220423 := by
    simpa [prefixWord, tailWord_1220423, baseEnd_1220423] using wordTrace_append hprefix tailTrace_1220423
  have hstable : (prefixWord ++ tailWord_1220423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220423).length < 2 ^ (prefixWord ++ tailWord_1220423).sum := by decide
  have hdescent : baseEnd_1220423 < baseStart_1220423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220425 : List Nat := [1, 2, 1, 1, 2, 4, 2, 5, 4]
def baseStart_1220425 : Nat := 118140960795 + 1220425 * 2 ^ 59
def prefixEnd_1220425 : Nat := 4983230072969 + 3 ^ 40 * 1220425 * 2
def baseEnd_1220425 : Nat := 139258806169665070061083

theorem tailTrace_1220425 : CollatzResearch.WordTrace tailWord_1220425 prefixEnd_1220425 139258806169665070061083 := by
  unfold tailWord_1220425
  simp only [CollatzResearch.WordTrace]
  refine ⟨44512556603616131840990729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29675037735744087893993819 44512556603616131840990729)
  ·
    refine ⟨33384417452712098880743047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44512556603616131840990729 33384417452712098880743047)
    ·
      refine ⟨50076626179068148321114571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33384417452712098880743047 50076626179068148321114571)
      ·
        refine ⟨75114939268602222481671857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50076626179068148321114571 75114939268602222481671857)
        ·
          refine ⟨56336204451451666861253893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75114939268602222481671857 56336204451451666861253893)
          ·
            refine ⟨10563038334647187536485105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56336204451451666861253893 10563038334647187536485105)
            ·
              refine ⟨7922278750985390652363829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10563038334647187536485105 7922278750985390652363829)
              ·
                refine ⟨742713632904880373659109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7922278750985390652363829 742713632904880373659109)
                ·
                  refine ⟨139258806169665070061083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 742713632904880373659109 139258806169665070061083)
                  ·
                    rfl

theorem cell22_1220425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 4].length) (baseStart_1220425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220425 prefixEnd_1220425 := by exact prefixLift 1220425
  have htrace : WordTrace (prefixWord ++ tailWord_1220425) baseStart_1220425 baseEnd_1220425 := by
    simpa [prefixWord, tailWord_1220425, baseEnd_1220425] using wordTrace_append hprefix tailTrace_1220425
  have hstable : (prefixWord ++ tailWord_1220425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220425).length < 2 ^ (prefixWord ++ tailWord_1220425).sum := by decide
  have hdescent : baseEnd_1220425 < baseStart_1220425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220485 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 5, 3]
def baseStart_1220485 : Nat := 118140960795 + 1220485 * 2 ^ 59
def prefixEnd_1220485 : Nat := 4983230072969 + 3 ^ 40 * 1220485 * 2
def baseEnd_1220485 : Nat := 417796957735175053683065

theorem tailTrace_1220485 : CollatzResearch.WordTrace tailWord_1220485 prefixEnd_1220485 417796957735175053683065 := by
  unfold tailWord_1220485
  simp only [CollatzResearch.WordTrace]
  refine ⟨44514744983398762088174909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29676496655599174725449939 44514744983398762088174909)
  ·
    refine ⟨16693029368774535783065591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44514744983398762088174909 16693029368774535783065591)
    ·
      refine ⟨25039544053161803674598387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16693029368774535783065591 25039544053161803674598387)
      ·
        refine ⟨37559316079742705511897581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25039544053161803674598387 37559316079742705511897581)
        ·
          refine ⟨14084743529903514566961593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37559316079742705511897581 14084743529903514566961593)
          ·
            refine ⟨10563557647427635925221195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14084743529903514566961593 10563557647427635925221195)
            ·
              refine ⟨15845336471141453887831793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10563557647427635925221195 15845336471141453887831793)
              ·
                refine ⟨11884002353356090415873845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15845336471141453887831793 11884002353356090415873845)
                ·
                  refine ⟨1114125220627133476488173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11884002353356090415873845 1114125220627133476488173)
                  ·
                    refine ⟨417796957735175053683065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1114125220627133476488173 417796957735175053683065)
                    ·
                      rfl

theorem cell22_1220485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_1220485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220485 prefixEnd_1220485 := by exact prefixLift 1220485
  have htrace : WordTrace (prefixWord ++ tailWord_1220485) baseStart_1220485 baseEnd_1220485 := by
    simpa [prefixWord, tailWord_1220485, baseEnd_1220485] using wordTrace_append hprefix tailTrace_1220485
  have hstable : (prefixWord ++ tailWord_1220485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220485).length < 2 ^ (prefixWord ++ tailWord_1220485).sum := by decide
  have hdescent : baseEnd_1220485 < baseStart_1220485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220528 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 4, 8]
def baseStart_1220528 : Nat := 118140960795 + 1220528 * 2 ^ 59
def prefixEnd_1220528 : Nat := 4983230072969 + 3 ^ 40 * 1220528 * 2
def baseEnd_1220528 : Nat := 417811677513937274857933

theorem tailTrace_1220528 : CollatzResearch.WordTrace tailWord_1220528 prefixEnd_1220528 417811677513937274857933 := by
  unfold tailWord_1220528
  simp only [CollatzResearch.WordTrace]
  refine ⟨22258156661121490215995119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29677542214828653621326825 22258156661121490215995119)
  ·
    refine ⟨33387234991682235323992679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22258156661121490215995119 33387234991682235323992679)
    ·
      refine ⟨50080852487523352985989019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33387234991682235323992679 50080852487523352985989019)
      ·
        refine ⟨75121278731285029478983529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50080852487523352985989019 75121278731285029478983529)
        ·
          refine ⟨56340959048463772109237647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75121278731285029478983529 56340959048463772109237647)
          ·
            refine ⟨84511438572695658163856471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56340959048463772109237647 84511438572695658163856471)
            ·
              refine ⟨126767157859043487245784707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84511438572695658163856471 126767157859043487245784707)
              ·
                refine ⟨190150736788565230868677061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126767157859043487245784707 190150736788565230868677061)
                ·
                  refine ⟨35653263147855980787876949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190150736788565230868677061 35653263147855980787876949)
                  ·
                    refine ⟨417811677513937274857933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35653263147855980787876949 417811677513937274857933)
                    ·
                      rfl

theorem cell22_1220528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_1220528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220528 prefixEnd_1220528 := by exact prefixLift 1220528
  have htrace : WordTrace (prefixWord ++ tailWord_1220528) baseStart_1220528 baseEnd_1220528 := by
    simpa [prefixWord, tailWord_1220528, baseEnd_1220528] using wordTrace_append hprefix tailTrace_1220528
  have hstable : (prefixWord ++ tailWord_1220528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220528).length < 2 ^ (prefixWord ++ tailWord_1220528).sum := by decide
  have hdescent : baseEnd_1220528 < baseStart_1220528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220560 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 6]
def baseStart_1220560 : Nat := 118140960795 + 1220560 * 2 ^ 59
def prefixEnd_1220560 : Nat := 4983230072969 + 3 ^ 40 * 1220560 * 2
def baseEnd_1220560 : Nat := 139274210589299952685945

theorem tailTrace_1220560 : CollatzResearch.WordTrace tailWord_1220560 prefixEnd_1220560 139274210589299952685945 := by
  unfold tailWord_1220560
  simp only [CollatzResearch.WordTrace]
  refine ⟨22258740229063524948577567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29678320305418033264770089 22258740229063524948577567)
  ·
    refine ⟨33388110343595287422866351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22258740229063524948577567 33388110343595287422866351)
    ·
      refine ⟨50082165515392931134299527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33388110343595287422866351 50082165515392931134299527)
      ·
        refine ⟨75123248273089396701449291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50082165515392931134299527 75123248273089396701449291)
        ·
          refine ⟨112684872409634095052173937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75123248273089396701449291 112684872409634095052173937)
          ·
            refine ⟨84513654307225571289130453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112684872409634095052173937 84513654307225571289130453)
            ·
              refine ⟨1980788772825599327088995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 84513654307225571289130453 1980788772825599327088995)
              ·
                refine ⟨2971183159238398990633493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980788772825599327088995 2971183159238398990633493)
                ·
                  refine ⟨139274210589299952685945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2971183159238398990633493 139274210589299952685945)
                  ·
                    rfl

theorem cell22_1220560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 6].length) (baseStart_1220560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220560 prefixEnd_1220560 := by exact prefixLift 1220560
  have htrace : WordTrace (prefixWord ++ tailWord_1220560) baseStart_1220560 baseEnd_1220560 := by
    simpa [prefixWord, tailWord_1220560, baseEnd_1220560] using wordTrace_append hprefix tailTrace_1220560
  have hstable : (prefixWord ++ tailWord_1220560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220560).length < 2 ^ (prefixWord ++ tailWord_1220560).sum := by decide
  have hdescent : baseEnd_1220560 < baseStart_1220560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220579 : List Nat := [1, 1, 1, 6, 1, 4, 1, 2, 1, 4]
def baseStart_1220579 : Nat := 118140960795 + 1220579 * 2 ^ 59
def prefixEnd_1220579 : Nat := 4983230072969 + 3 ^ 40 * 1220579 * 2
def baseEnd_1220579 : Nat := 417829135856190141832777

theorem tailTrace_1220579 : CollatzResearch.WordTrace tailWord_1220579 prefixEnd_1220579 417829135856190141832777 := by
  unfold tailWord_1220579
  simp only [CollatzResearch.WordTrace]
  refine ⟨44518173445058216142096791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29678782296705477428064527 44518173445058216142096791)
  ·
    refine ⟨66777260167587324213145187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44518173445058216142096791 66777260167587324213145187)
    ·
      refine ⟨100165890251380986319717781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66777260167587324213145187 100165890251380986319717781)
      ·
        refine ⟨4695276105533483733736771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100165890251380986319717781 4695276105533483733736771)
        ·
          refine ⟨7042914158300225600605157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4695276105533483733736771 7042914158300225600605157)
          ·
            refine ⟨1320546404681292300113467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7042914158300225600605157 1320546404681292300113467)
            ·
              refine ⟨1980819607021938450170201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320546404681292300113467 1980819607021938450170201)
              ·
                refine ⟨1485614705266453837627651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1980819607021938450170201 1485614705266453837627651)
                ·
                  refine ⟨2228422057899680756441477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485614705266453837627651 2228422057899680756441477)
                  ·
                    refine ⟨417829135856190141832777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2228422057899680756441477 417829135856190141832777)
                    ·
                      rfl

theorem cell22_1220579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 4].length) (baseStart_1220579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220579 prefixEnd_1220579 := by exact prefixLift 1220579
  have htrace : WordTrace (prefixWord ++ tailWord_1220579) baseStart_1220579 baseEnd_1220579 := by
    simpa [prefixWord, tailWord_1220579, baseEnd_1220579] using wordTrace_append hprefix tailTrace_1220579
  have hstable : (prefixWord ++ tailWord_1220579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220579).length < 2 ^ (prefixWord ++ tailWord_1220579).sum := by decide
  have hdescent : baseEnd_1220579 < baseStart_1220579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220609 : List Nat := [1, 2, 4, 1, 2, 1, 4, 2, 2, 3]
def baseStart_1220609 : Nat := 118140960795 + 1220609 * 2 ^ 59
def prefixEnd_1220609 : Nat := 4983230072969 + 3 ^ 40 * 1220609 * 2
def baseEnd_1220609 : Nat := 417839405469280063582685

theorem tailTrace_1220609 : CollatzResearch.WordTrace tailWord_1220609 prefixEnd_1220609 417839405469280063582685 := by
  unfold tailWord_1220609
  simp only [CollatzResearch.WordTrace]
  refine ⟨44519267634949531265688881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29679511756633020843792587 44519267634949531265688881)
  ·
    refine ⟨33389450726212148449266661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44519267634949531265688881 33389450726212148449266661)
    ·
      refine ⟨6260522011164777834237499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33389450726212148449266661 6260522011164777834237499)
      ·
        refine ⟨9390783016747166751356249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6260522011164777834237499 9390783016747166751356249)
        ·
          refine ⟨7043087262560375063517187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9390783016747166751356249 7043087262560375063517187)
          ·
            refine ⟨10564630893840562595275781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7043087262560375063517187 10564630893840562595275781)
            ·
              refine ⟨1980868292595105486614209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10564630893840562595275781 1980868292595105486614209)
              ·
                refine ⟨1485651219446329114960657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1980868292595105486614209 1485651219446329114960657)
                ·
                  refine ⟨1114238414584746836220493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1485651219446329114960657 1114238414584746836220493)
                  ·
                    refine ⟨417839405469280063582685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1114238414584746836220493 417839405469280063582685)
                    ·
                      rfl

theorem cell22_1220609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_1220609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220609 prefixEnd_1220609 := by exact prefixLift 1220609
  have htrace : WordTrace (prefixWord ++ tailWord_1220609) baseStart_1220609 baseEnd_1220609 := by
    simpa [prefixWord, tailWord_1220609, baseEnd_1220609] using wordTrace_append hprefix tailTrace_1220609
  have hstable : (prefixWord ++ tailWord_1220609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220609).length < 2 ^ (prefixWord ++ tailWord_1220609).sum := by decide
  have hdescent : baseEnd_1220609 < baseStart_1220609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220641 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 2, 4]
def baseStart_1220641 : Nat := 118140960795 + 1220641 * 2 ^ 59
def prefixEnd_1220641 : Nat := 4983230072969 + 3 ^ 40 * 1220641 * 2
def baseEnd_1220641 : Nat := 417850359723242646782587

theorem tailTrace_1220641 : CollatzResearch.WordTrace tailWord_1220641 prefixEnd_1220641 417850359723242646782587 := by
  unfold tailWord_1220641
  simp only [CollatzResearch.WordTrace]
  refine ⟨44520434770833600730853777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29680289847222400487235851 44520434770833600730853777)
  ·
    refine ⟨33390326078125200548140333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44520434770833600730853777 33390326078125200548140333)
    ·
      refine ⟨12521372279296950205552625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33390326078125200548140333 12521372279296950205552625)
      ·
        refine ⟨9391029209472712654164469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12521372279296950205552625 9391029209472712654164469)
        ·
          refine ⟨880408988388066811327919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9391029209472712654164469 880408988388066811327919)
          ·
            refine ⟨1320613482582100216991879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880408988388066811327919 1320613482582100216991879)
            ·
              refine ⟨1980920223873150325487819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320613482582100216991879 1980920223873150325487819)
              ·
                refine ⟨2971380335809725488231729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980920223873150325487819 2971380335809725488231729)
                ·
                  refine ⟨2228535251857294116173797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2971380335809725488231729 2228535251857294116173797)
                  ·
                    refine ⟨417850359723242646782587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2228535251857294116173797 417850359723242646782587)
                    ·
                      rfl

theorem cell22_1220641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_1220641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220641 prefixEnd_1220641 := by exact prefixLift 1220641
  have htrace : WordTrace (prefixWord ++ tailWord_1220641) baseStart_1220641 baseEnd_1220641 := by
    simpa [prefixWord, tailWord_1220641, baseEnd_1220641] using wordTrace_append hprefix tailTrace_1220641
  have hstable : (prefixWord ++ tailWord_1220641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220641).length < 2 ^ (prefixWord ++ tailWord_1220641).sum := by decide
  have hdescent : baseEnd_1220641 < baseStart_1220641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220660 : List Nat := [2, 5, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_1220660 : Nat := 118140960795 + 1220660 * 2 ^ 59
def prefixEnd_1220660 : Nat := 4983230072969 + 3 ^ 40 * 1220660 * 2
def baseEnd_1220660 : Nat := 417856863811532930557529

theorem tailTrace_1220660 : CollatzResearch.WordTrace tailWord_1220660 prefixEnd_1220660 417856863811532930557529 := by
  unfold tailWord_1220660
  simp only [CollatzResearch.WordTrace]
  refine ⟨22260563878882383487897717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29680751838509844650530289 22260563878882383487897717)
  ·
    refine ⟨2086927863645223451990411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22260563878882383487897717 2086927863645223451990411)
    ·
      refine ⟨3130391795467835177985617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2086927863645223451990411 3130391795467835177985617)
      ·
        refine ⟨2347793846600876383489213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3130391795467835177985617 2347793846600876383489213)
        ·
          refine ⟨880422692475328643808455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2347793846600876383489213 880422692475328643808455)
          ·
            refine ⟨1320634038712992965712683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880422692475328643808455 1320634038712992965712683)
            ·
              refine ⟨1980951058069489448569025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320634038712992965712683 1980951058069489448569025)
              ·
                refine ⟨1485713293552117086426769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1980951058069489448569025 1485713293552117086426769)
                ·
                  refine ⟨1114284970164087814820077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1485713293552117086426769 1114284970164087814820077)
                  ·
                    refine ⟨417856863811532930557529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1114284970164087814820077 417856863811532930557529)
                    ·
                      rfl

theorem cell22_1220660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_1220660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220660 prefixEnd_1220660 := by exact prefixLift 1220660
  have htrace : WordTrace (prefixWord ++ tailWord_1220660) baseStart_1220660 baseEnd_1220660 := by
    simpa [prefixWord, tailWord_1220660, baseEnd_1220660] using wordTrace_append hprefix tailTrace_1220660
  have hstable : (prefixWord ++ tailWord_1220660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220660).length < 2 ^ (prefixWord ++ tailWord_1220660).sum := by decide
  have hdescent : baseEnd_1220660 < baseStart_1220660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220680 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 2, 8]
def baseStart_1220680 : Nat := 118140960795 + 1220680 * 2 ^ 59
def prefixEnd_1220680 : Nat := 4983230072969 + 3 ^ 40 * 1220680 * 2
def baseEnd_1220680 : Nat := 417863710220259545057467

theorem tailTrace_1220680 : CollatzResearch.WordTrace tailWord_1220680 prefixEnd_1220680 417863710220259545057467 := by
  unfold tailWord_1220680
  simp only [CollatzResearch.WordTrace]
  refine ⟨22260928608846155195761747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29681238145128206927682329 22260928608846155195761747)
  ·
    refine ⟨33391392913269232793642621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22260928608846155195761747 33391392913269232793642621)
    ·
      refine ⟨12521772342475962297615983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33391392913269232793642621 12521772342475962297615983)
      ·
        refine ⟨18782658513713943446423975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12521772342475962297615983 18782658513713943446423975)
        ·
          refine ⟨28173987770570915169635963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18782658513713943446423975 28173987770570915169635963)
          ·
            refine ⟨42260981655856372754453945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28173987770570915169635963 42260981655856372754453945)
            ·
              refine ⟨31695736241892279565840459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42260981655856372754453945 31695736241892279565840459)
              ·
                refine ⟨47543604362838419348760689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31695736241892279565840459 47543604362838419348760689)
                ·
                  refine ⟨35657703272128814511570517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47543604362838419348760689 35657703272128814511570517)
                  ·
                    refine ⟨417863710220259545057467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35657703272128814511570517 417863710220259545057467)
                    ·
                      rfl

theorem cell22_1220680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_1220680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220680 prefixEnd_1220680 := by exact prefixLift 1220680
  have htrace : WordTrace (prefixWord ++ tailWord_1220680) baseStart_1220680 baseEnd_1220680 := by
    simpa [prefixWord, tailWord_1220680, baseEnd_1220680] using wordTrace_append hprefix tailTrace_1220680
  have hstable : (prefixWord ++ tailWord_1220680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220680).length < 2 ^ (prefixWord ++ tailWord_1220680).sum := by decide
  have hdescent : baseEnd_1220680 < baseStart_1220680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220729 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 6]
def baseStart_1220729 : Nat := 118140960795 + 1220729 * 2 ^ 59
def prefixEnd_1220729 : Nat := 4983230072969 + 3 ^ 40 * 1220729 * 2
def baseEnd_1220729 : Nat := 139293494640546583527439

theorem tailTrace_1220729 : CollatzResearch.WordTrace tailWord_1220729 prefixEnd_1220729 139293494640546583527439 := by
  unfold tailWord_1220729
  simp only [CollatzResearch.WordTrace]
  refine ⟨44523644394514791760057241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29682429596343194506704827 44523644394514791760057241)
  ·
    refine ⟨33392733295886093820042931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44523644394514791760057241 33392733295886093820042931)
    ·
      refine ⟨50089099943829140730064397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33392733295886093820042931 50089099943829140730064397)
      ·
        refine ⟨18783412478935927773774149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50089099943829140730064397 18783412478935927773774149)
        ·
          refine ⟨3521889839800486457582653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18783412478935927773774149 3521889839800486457582653)
          ·
            refine ⟨1320708689925182421593495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3521889839800486457582653 1320708689925182421593495)
            ·
              refine ⟨1981063034887773632390243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320708689925182421593495 1981063034887773632390243)
              ·
                refine ⟨2971594552331660448585365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981063034887773632390243 2971594552331660448585365)
                ·
                  refine ⟨139293494640546583527439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2971594552331660448585365 139293494640546583527439)
                  ·
                    rfl

theorem cell22_1220729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 6].length) (baseStart_1220729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220729 prefixEnd_1220729 := by exact prefixLift 1220729
  have htrace : WordTrace (prefixWord ++ tailWord_1220729) baseStart_1220729 baseEnd_1220729 := by
    simpa [prefixWord, tailWord_1220729, baseEnd_1220729] using wordTrace_append hprefix tailTrace_1220729
  have hstable : (prefixWord ++ tailWord_1220729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220729).length < 2 ^ (prefixWord ++ tailWord_1220729).sum := by decide
  have hdescent : baseEnd_1220729 < baseStart_1220729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220881 : List Nat := [1, 2, 2, 1, 1, 5, 3, 3, 4]
def baseStart_1220881 : Nat := 118140960795 + 1220881 * 2 ^ 59
def prefixEnd_1220881 : Nat := 4983230072969 + 3 ^ 40 * 1220881 * 2
def baseEnd_1220881 : Nat := 139310838875987340260617

theorem tailTrace_1220881 : CollatzResearch.WordTrace tailWord_1220881 prefixEnd_1220881 139310838875987340260617 := by
  unfold tailWord_1220881
  simp only [CollatzResearch.WordTrace]
  refine ⟨44529188289964121719590497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29686125526642747813060331 44529188289964121719590497)
  ·
    refine ⟨33396891217473091289692873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44529188289964121719590497 33396891217473091289692873)
    ·
      refine ⟨25047668413104818467269655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33396891217473091289692873 25047668413104818467269655)
      ·
        refine ⟨37571502619657227700904483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25047668413104818467269655 37571502619657227700904483)
        ·
          refine ⟨56357253929485841551356725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37571502619657227700904483 56357253929485841551356725)
          ·
            refine ⟨5283492555889297645439693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56357253929485841551356725 5283492555889297645439693)
            ·
              refine ⟨1981309708458486617039885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5283492555889297645439693 1981309708458486617039885)
              ·
                refine ⟨742991140671932481389957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1981309708458486617039885 742991140671932481389957)
                ·
                  refine ⟨139310838875987340260617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 742991140671932481389957 139310838875987340260617)
                  ·
                    rfl

theorem cell22_1220881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 4].length) (baseStart_1220881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220881 prefixEnd_1220881 := by exact prefixLift 1220881
  have htrace : WordTrace (prefixWord ++ tailWord_1220881) baseStart_1220881 baseEnd_1220881 := by
    simpa [prefixWord, tailWord_1220881, baseEnd_1220881] using wordTrace_append hprefix tailTrace_1220881
  have hstable : (prefixWord ++ tailWord_1220881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220881).length < 2 ^ (prefixWord ++ tailWord_1220881).sum := by decide
  have hdescent : baseEnd_1220881 < baseStart_1220881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220896 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 4, 3]
def baseStart_1220896 : Nat := 118140960795 + 1220896 * 2 ^ 59
def prefixEnd_1220896 : Nat := 4983230072969 + 3 ^ 40 * 1220896 * 2
def baseEnd_1220896 : Nat := 417937651434506981656805

theorem tailTrace_1220896 : CollatzResearch.WordTrace tailWord_1220896 prefixEnd_1220896 417937651434506981656805 := by
  unfold tailWord_1220896
  simp only [CollatzResearch.WordTrace]
  refine ⟨22264867692454889640693271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29686490256606519520924361 22264867692454889640693271)
  ·
    refine ⟨33397301538682334461039907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22264867692454889640693271 33397301538682334461039907)
    ·
      refine ⟨50095952308023501691559861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33397301538682334461039907 50095952308023501691559861)
      ·
        refine ⟨4696495528877203283583737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50095952308023501691559861 4696495528877203283583737)
        ·
          refine ⟨3522371646657902462687803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4696495528877203283583737 3522371646657902462687803)
          ·
            refine ⟨5283557469986853694031705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3522371646657902462687803 5283557469986853694031705)
            ·
              refine ⟨3962668102490140270523779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5283557469986853694031705 3962668102490140270523779)
              ·
                refine ⟨5944002153735210405785669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3962668102490140270523779 5944002153735210405785669)
                ·
                  refine ⟨1114500403825351951084813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5944002153735210405785669 1114500403825351951084813)
                  ·
                    refine ⟨417937651434506981656805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1114500403825351951084813 417937651434506981656805)
                    ·
                      rfl

theorem cell22_1220896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 4, 3].length) (baseStart_1220896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220896 prefixEnd_1220896 := by exact prefixLift 1220896
  have htrace : WordTrace (prefixWord ++ tailWord_1220896) baseStart_1220896 baseEnd_1220896 := by
    simpa [prefixWord, tailWord_1220896, baseEnd_1220896] using wordTrace_append hprefix tailTrace_1220896
  have hstable : (prefixWord ++ tailWord_1220896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220896).length < 2 ^ (prefixWord ++ tailWord_1220896).sum := by decide
  have hdescent : baseEnd_1220896 < baseStart_1220896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220913 : List Nat := [1, 2, 2, 3, 4, 1, 1, 3, 2, 3]
def baseStart_1220913 : Nat := 118140960795 + 1220913 * 2 ^ 59
def prefixEnd_1220913 : Nat := 4983230072969 + 3 ^ 40 * 1220913 * 2
def baseEnd_1220913 : Nat := 417943470881924603981753

theorem tailTrace_1220913 : CollatzResearch.WordTrace tailWord_1220913 prefixEnd_1220913 417943470881924603981753 := by
  unfold tailWord_1220913
  simp only [CollatzResearch.WordTrace]
  refine ⟨44530355425848191184755393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29686903617232127456503595 44530355425848191184755393)
  ·
    refine ⟨33397766569386143388566545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44530355425848191184755393 33397766569386143388566545)
    ·
      refine ⟨25048324927039607541424909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33397766569386143388566545 25048324927039607541424909)
      ·
        refine ⟨9393121847639852828034341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25048324927039607541424909 9393121847639852828034341)
        ·
          refine ⟨1761210346432472405256439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9393121847639852828034341 1761210346432472405256439)
          ·
            refine ⟨2641815519648708607884659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761210346432472405256439 2641815519648708607884659)
            ·
              refine ⟨3962723279473062911826989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641815519648708607884659 3962723279473062911826989)
              ·
                refine ⟨1486021229802398591935121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3962723279473062911826989 1486021229802398591935121)
                ·
                  refine ⟨1114515922351798943951341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1486021229802398591935121 1114515922351798943951341)
                  ·
                    refine ⟨417943470881924603981753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1114515922351798943951341 417943470881924603981753)
                    ·
                      rfl

theorem cell22_1220913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_1220913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220913 prefixEnd_1220913 := by exact prefixLift 1220913
  have htrace : WordTrace (prefixWord ++ tailWord_1220913) baseStart_1220913 baseEnd_1220913 := by
    simpa [prefixWord, tailWord_1220913, baseEnd_1220913] using wordTrace_append hprefix tailTrace_1220913
  have hstable : (prefixWord ++ tailWord_1220913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220913).length < 2 ^ (prefixWord ++ tailWord_1220913).sum := by decide
  have hdescent : baseEnd_1220913 < baseStart_1220913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220969 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 2, 5]
def baseStart_1220969 : Nat := 118140960795 + 1220969 * 2 ^ 59
def prefixEnd_1220969 : Nat := 4983230072969 + 3 ^ 40 * 1220969 * 2
def baseEnd_1220969 : Nat := 417962640826359124581581

theorem tailTrace_1220969 : CollatzResearch.WordTrace tailWord_1220969 prefixEnd_1220969 417962640826359124581581 := by
  unfold tailWord_1220969
  simp only [CollatzResearch.WordTrace]
  refine ⟨44532397913645312748793961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29688265275763541832529307 44532397913645312748793961)
  ·
    refine ⟨33399298435233984561595471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44532397913645312748793961 33399298435233984561595471)
    ·
      refine ⟨50098947652850976842393207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33399298435233984561595471 50098947652850976842393207)
      ·
        refine ⟨75148421479276465263589811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50098947652850976842393207 75148421479276465263589811)
        ·
          refine ⟨112722632218914697895384717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75148421479276465263589811 112722632218914697895384717)
          ·
            refine ⟨42270987082093011710769269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112722632218914697895384717 42270987082093011710769269)
            ·
              refine ⟨3962905038946219847884619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42270987082093011710769269 3962905038946219847884619)
              ·
                refine ⟨5944357558419329771826929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3962905038946219847884619 5944357558419329771826929)
                ·
                  refine ⟨4458268168814497328870197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5944357558419329771826929 4458268168814497328870197)
                  ·
                    refine ⟨417962640826359124581581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4458268168814497328870197 417962640826359124581581)
                    ·
                      rfl

theorem cell22_1220969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_1220969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220969 prefixEnd_1220969 := by exact prefixLift 1220969
  have htrace : WordTrace (prefixWord ++ tailWord_1220969) baseStart_1220969 baseEnd_1220969 := by
    simpa [prefixWord, tailWord_1220969, baseEnd_1220969] using wordTrace_append hprefix tailTrace_1220969
  have hstable : (prefixWord ++ tailWord_1220969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220969).length < 2 ^ (prefixWord ++ tailWord_1220969).sum := by decide
  have hdescent : baseEnd_1220969 < baseStart_1220969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220999 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 8]
def baseStart_1220999 : Nat := 118140960795 + 1220999 * 2 ^ 59
def prefixEnd_1220999 : Nat := 4983230072969 + 3 ^ 40 * 1220999 * 2
def baseEnd_1220999 : Nat := 139324303479816348777163

theorem tailTrace_1220999 : CollatzResearch.WordTrace tailWord_1220999 prefixEnd_1220999 139324303479816348777163 := by
  unfold tailWord_1220999
  simp only [CollatzResearch.WordTrace]
  refine ⟨44533492103536627872386051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29688994735691085248257367 44533492103536627872386051)
  ·
    refine ⟨66800238155304941808579077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44533492103536627872386051 66800238155304941808579077)
    ·
      refine ⟨12525044654119676589108577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66800238155304941808579077 12525044654119676589108577)
      ·
        refine ⟨9393783490589757441831433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12525044654119676589108577 9393783490589757441831433)
        ·
          refine ⟨7045337617942318081373575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9393783490589757441831433 7045337617942318081373575)
          ·
            refine ⟨10568006426913477122060363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7045337617942318081373575 10568006426913477122060363)
            ·
              refine ⟨15852009640370215683090545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10568006426913477122060363 15852009640370215683090545)
              ·
                refine ⟨11889007230277661762317909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15852009640370215683090545 11889007230277661762317909)
                ·
                  refine ⟨139324303479816348777163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11889007230277661762317909 139324303479816348777163)
                  ·
                    rfl

theorem cell22_1220999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 8].length) (baseStart_1220999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1220999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1220999 prefixEnd_1220999 := by exact prefixLift 1220999
  have htrace : WordTrace (prefixWord ++ tailWord_1220999) baseStart_1220999 baseEnd_1220999 := by
    simpa [prefixWord, tailWord_1220999, baseEnd_1220999] using wordTrace_append hprefix tailTrace_1220999
  have hstable : (prefixWord ++ tailWord_1220999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220999).length < 2 ^ (prefixWord ++ tailWord_1220999).sum := by decide
  have hdescent : baseEnd_1220999 < baseStart_1220999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221016 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 6]
def baseStart_1221016 : Nat := 118140960795 + 1221016 * 2 ^ 59
def prefixEnd_1221016 : Nat := 4983230072969 + 3 ^ 40 * 1221016 * 2
def baseEnd_1221016 : Nat := 139326243295622222885479

theorem tailTrace_1221016 : CollatzResearch.WordTrace tailWord_1221016 prefixEnd_1221016 139326243295622222885479 := by
  unfold tailWord_1221016
  simp only [CollatzResearch.WordTrace]
  refine ⟨22267056072237519887877451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29689408096316693183836601 22267056072237519887877451)
  ·
    refine ⟨33400584108356279831816177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22267056072237519887877451 33400584108356279831816177)
    ·
      refine ⟨25050438081267209873862133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33400584108356279831816177 25050438081267209873862133)
      ·
        refine ⟨2348478570118800925674575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25050438081267209873862133 2348478570118800925674575)
        ·
          refine ⟨3522717855178201388511863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2348478570118800925674575 3522717855178201388511863)
          ·
            refine ⟨5284076782767302082767795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3522717855178201388511863 5284076782767302082767795)
            ·
              refine ⟨7926115174150953124151693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5284076782767302082767795 7926115174150953124151693)
              ·
                refine ⟨2972293190306607421556885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7926115174150953124151693 2972293190306607421556885)
                ·
                  refine ⟨139326243295622222885479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2972293190306607421556885 139326243295622222885479)
                  ·
                    rfl

theorem cell22_1221016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 6].length) (baseStart_1221016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221016 prefixEnd_1221016 := by exact prefixLift 1221016
  have htrace : WordTrace (prefixWord ++ tailWord_1221016) baseStart_1221016 baseEnd_1221016 := by
    simpa [prefixWord, tailWord_1221016, baseEnd_1221016] using wordTrace_append hprefix tailTrace_1221016
  have hstable : (prefixWord ++ tailWord_1221016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221016).length < 2 ^ (prefixWord ++ tailWord_1221016).sum := by decide
  have hdescent : baseEnd_1221016 < baseStart_1221016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221029 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_1221029 : Nat := 118140960795 + 1221029 * 2 ^ 59
def prefixEnd_1221029 : Nat := 4983230072969 + 3 ^ 40 * 1221029 * 2
def baseEnd_1221029 : Nat := 417983180052538968081397

theorem tailTrace_1221029 : CollatzResearch.WordTrace tailWord_1221029 prefixEnd_1221029 417983180052538968081397 := by
  unfold tailWord_1221029
  simp only [CollatzResearch.WordTrace]
  refine ⟨44534586293427942995978141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29689724195618628663985427 44534586293427942995978141)
  ·
    refine ⟨16700469860035478623491803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44534586293427942995978141 16700469860035478623491803)
    ·
      refine ⟨25050704790053217935237705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16700469860035478623491803 25050704790053217935237705)
      ·
        refine ⟨18788028592539913451428279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25050704790053217935237705 18788028592539913451428279)
        ·
          refine ⟨28182042888809870177142419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18788028592539913451428279 28182042888809870177142419)
          ·
            refine ⟨42273064333214805265713629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28182042888809870177142419 42273064333214805265713629)
            ·
              refine ⟨15852399124955551974642611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42273064333214805265713629 15852399124955551974642611)
              ·
                refine ⟨23778598687433327961963917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15852399124955551974642611 23778598687433327961963917)
                ·
                  refine ⟨8916974507787497985736469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23778598687433327961963917 8916974507787497985736469)
                  ·
                    refine ⟨417983180052538968081397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8916974507787497985736469 417983180052538968081397)
                    ·
                      rfl

theorem cell22_1221029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_1221029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221029 prefixEnd_1221029 := by exact prefixLift 1221029
  have htrace : WordTrace (prefixWord ++ tailWord_1221029) baseStart_1221029 baseEnd_1221029 := by
    simpa [prefixWord, tailWord_1221029, baseEnd_1221029] using wordTrace_append hprefix tailTrace_1221029
  have hstable : (prefixWord ++ tailWord_1221029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221029).length < 2 ^ (prefixWord ++ tailWord_1221029).sum := by decide
  have hdescent : baseEnd_1221029 < baseStart_1221029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221078 : List Nat := [5, 2, 1, 1, 1, 1, 4, 7]
def baseStart_1221078 : Nat := 118140960795 + 1221078 * 2 ^ 59
def prefixEnd_1221078 : Nat := 4983230072969 + 3 ^ 40 * 1221078 * 2
def baseEnd_1221078 : Nat := 46444439305991019289583

theorem tailTrace_1221078 : CollatzResearch.WordTrace tailWord_1221078 prefixEnd_1221078 46444439305991019289583 := by
  unfold tailWord_1221078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783523341890651522781993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29690915646833616243007925 2783523341890651522781993)
  ·
    refine ⟨2087642506417988642086495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2783523341890651522781993 2087642506417988642086495)
    ·
      refine ⟨3131463759626982963129743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2087642506417988642086495 3131463759626982963129743)
      ·
        refine ⟨4697195639440474444694615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3131463759626982963129743 4697195639440474444694615)
        ·
          refine ⟨7045793459160711667041923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4697195639440474444694615 7045793459160711667041923)
          ·
            refine ⟨10568690188741067500562885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7045793459160711667041923 10568690188741067500562885)
            ·
              refine ⟨1981629410388950156355541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10568690188741067500562885 1981629410388950156355541)
              ·
                refine ⟨46444439305991019289583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1981629410388950156355541 46444439305991019289583)
                ·
                  rfl

theorem cell22_1221078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_1221078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221078 prefixEnd_1221078 := by exact prefixLift 1221078
  have htrace : WordTrace (prefixWord ++ tailWord_1221078) baseStart_1221078 baseEnd_1221078 := by
    simpa [prefixWord, tailWord_1221078, baseEnd_1221078] using wordTrace_append hprefix tailTrace_1221078
  have hstable : (prefixWord ++ tailWord_1221078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221078).length < 2 ^ (prefixWord ++ tailWord_1221078).sum := by decide
  have hdescent : baseEnd_1221078 < baseStart_1221078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221127 : List Nat := [1, 1, 4, 3, 3, 1, 1, 4, 1, 3]
def baseStart_1221127 : Nat := 118140960795 + 1221127 * 2 ^ 59
def prefixEnd_1221127 : Nat := 4983230072969 + 3 ^ 40 * 1221127 * 2
def baseEnd_1221127 : Nat := 418016727455299379131097

theorem tailTrace_1221127 : CollatzResearch.WordTrace tailWord_1221127 prefixEnd_1221127 418016727455299379131097 := by
  unfold tailWord_1221127
  simp only [CollatzResearch.WordTrace]
  refine ⟨44538160647072905733045635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29692107098048603822030423 44538160647072905733045635)
  ·
    refine ⟨66807240970609358599568453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44538160647072905733045635 66807240970609358599568453)
    ·
      refine ⟨12526357681989254737419085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66807240970609358599568453 12526357681989254737419085)
      ·
        refine ⟨4697384130745970526532157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12526357681989254737419085 4697384130745970526532157)
        ·
          refine ⟨1761519049029738947449559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4697384130745970526532157 1761519049029738947449559)
          ·
            refine ⟨2642278573544608421174339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761519049029738947449559 2642278573544608421174339)
            ·
              refine ⟨3963417860316912631761509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2642278573544608421174339 3963417860316912631761509)
              ·
                refine ⟨743140848809421118455283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3963417860316912631761509 743140848809421118455283)
                ·
                  refine ⟨1114711273214131677682925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 743140848809421118455283 1114711273214131677682925)
                  ·
                    refine ⟨418016727455299379131097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1114711273214131677682925 418016727455299379131097)
                    ·
                      rfl

theorem cell22_1221127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_1221127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221127 prefixEnd_1221127 := by exact prefixLift 1221127
  have htrace : WordTrace (prefixWord ++ tailWord_1221127) baseStart_1221127 baseEnd_1221127 := by
    simpa [prefixWord, tailWord_1221127, baseEnd_1221127] using wordTrace_append hprefix tailTrace_1221127
  have hstable : (prefixWord ++ tailWord_1221127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221127).length < 2 ^ (prefixWord ++ tailWord_1221127).sum := by decide
  have hdescent : baseEnd_1221127 < baseStart_1221127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221140 : List Nat := [2, 4, 3, 1, 1, 1, 2, 3, 5]
def baseStart_1221140 : Nat := 118140960795 + 1221140 * 2 ^ 59
def prefixEnd_1221140 : Nat := 4983230072969 + 3 ^ 40 * 1221140 * 2
def baseEnd_1221140 : Nat := 139340392540323892852019

theorem tailTrace_1221140 : CollatzResearch.WordTrace tailWord_1221140 prefixEnd_1221140 139340392540323892852019 := by
  unfold tailWord_1221140
  simp only [CollatzResearch.WordTrace]
  refine ⟨22269317398012904476634437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29692423197350539302179249 22269317398012904476634437)
  ·
    refine ⟨4175497012127419589368957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22269317398012904476634437 4175497012127419589368957)
    ·
      refine ⟨1565811379547782346013359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4175497012127419589368957 1565811379547782346013359)
      ·
        refine ⟨2348717069321673519020039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1565811379547782346013359 2348717069321673519020039)
        ·
          refine ⟨3523075603982510278530059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2348717069321673519020039 3523075603982510278530059)
          ·
            refine ⟨5284613405973765417795089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3523075603982510278530059 5284613405973765417795089)
            ·
              refine ⟨3963460054480324063346317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5284613405973765417795089 3963460054480324063346317)
              ·
                refine ⟨1486297520430121523754869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3963460054480324063346317 1486297520430121523754869)
                ·
                  refine ⟨139340392540323892852019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1486297520430121523754869 139340392540323892852019)
                  ·
                    rfl

theorem cell22_1221140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_1221140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221140 prefixEnd_1221140 := by exact prefixLift 1221140
  have htrace : WordTrace (prefixWord ++ tailWord_1221140) baseStart_1221140 baseEnd_1221140 := by
    simpa [prefixWord, tailWord_1221140, baseEnd_1221140] using wordTrace_append hprefix tailTrace_1221140
  have hstable : (prefixWord ++ tailWord_1221140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221140).length < 2 ^ (prefixWord ++ tailWord_1221140).sum := by decide
  have hdescent : baseEnd_1221140 < baseStart_1221140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221153 : List Nat := [1, 2, 3, 2, 2, 1, 2, 4, 1, 4]
def baseStart_1221153 : Nat := 118140960795 + 1221153 * 2 ^ 59
def prefixEnd_1221153 : Nat := 4983230072969 + 3 ^ 40 * 1221153 * 2
def baseEnd_1221153 : Nat := 418025627786643977981017

theorem tailTrace_1221153 : CollatzResearch.WordTrace tailWord_1221153 prefixEnd_1221153 418025627786643977981017 := by
  unfold tailWord_1221153
  simp only [CollatzResearch.WordTrace]
  refine ⟨44539108944978712173492113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29692739296652474782328075 44539108944978712173492113)
  ·
    refine ⟨33404331708734034130119085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44539108944978712173492113 33404331708734034130119085)
    ·
      refine ⟨12526624390775262798794657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33404331708734034130119085 12526624390775262798794657)
      ·
        refine ⟨9394968293081447099095993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12526624390775262798794657 9394968293081447099095993)
        ·
          refine ⟨7046226219811085324321995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9394968293081447099095993 7046226219811085324321995)
          ·
            refine ⟨10569339329716627986482993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7046226219811085324321995 10569339329716627986482993)
            ·
              refine ⟨7927004497287470989862245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10569339329716627986482993 7927004497287470989862245)
              ·
                refine ⟨1486313343241400810599171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7927004497287470989862245 1486313343241400810599171)
                ·
                  refine ⟨2229470014862101215898757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486313343241400810599171 2229470014862101215898757)
                  ·
                    refine ⟨418025627786643977981017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2229470014862101215898757 418025627786643977981017)
                    ·
                      rfl

theorem cell22_1221153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_1221153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221153 prefixEnd_1221153 := by exact prefixLift 1221153
  have htrace : WordTrace (prefixWord ++ tailWord_1221153) baseStart_1221153 baseEnd_1221153 := by
    simpa [prefixWord, tailWord_1221153, baseEnd_1221153] using wordTrace_append hprefix tailTrace_1221153
  have hstable : (prefixWord ++ tailWord_1221153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221153).length < 2 ^ (prefixWord ++ tailWord_1221153).sum := by decide
  have hdescent : baseEnd_1221153 < baseStart_1221153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221168 : List Nat := [2, 1, 1, 1, 2, 3, 3, 5, 4]
def baseStart_1221168 : Nat := 118140960795 + 1221168 * 2 ^ 59
def prefixEnd_1221168 : Nat := 4983230072969 + 3 ^ 40 * 1221168 * 2
def baseEnd_1221168 : Nat := 139343587531062979618657

theorem tailTrace_1221168 : CollatzResearch.WordTrace tailWord_1221168 prefixEnd_1221168 139343587531062979618657 := by
  unfold tailWord_1221168
  simp only [CollatzResearch.WordTrace]
  refine ⟨22269828019962184867644079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29693104026616246490192105 22269828019962184867644079)
  ·
    refine ⟨33404742029943277301466119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22269828019962184867644079 33404742029943277301466119)
    ·
      refine ⟨50107113044914915952199179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33404742029943277301466119 50107113044914915952199179)
      ·
        refine ⟨75160669567372373928298769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50107113044914915952199179 75160669567372373928298769)
        ·
          refine ⟨56370502175529280446224077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75160669567372373928298769 56370502175529280446224077)
          ·
            refine ⟨21138938315823480167334029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56370502175529280446224077 21138938315823480167334029)
            ·
              refine ⟨7927101868433805062750261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21138938315823480167334029 7927101868433805062750261)
              ·
                refine ⟨743165800165669224632837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7927101868433805062750261 743165800165669224632837)
                ·
                  refine ⟨139343587531062979618657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 743165800165669224632837 139343587531062979618657)
                  ·
                    rfl

theorem cell22_1221168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 4].length) (baseStart_1221168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221168 prefixEnd_1221168 := by exact prefixLift 1221168
  have htrace : WordTrace (prefixWord ++ tailWord_1221168) baseStart_1221168 baseEnd_1221168 := by
    simpa [prefixWord, tailWord_1221168, baseEnd_1221168] using wordTrace_append hprefix tailTrace_1221168
  have hstable : (prefixWord ++ tailWord_1221168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221168).length < 2 ^ (prefixWord ++ tailWord_1221168).sum := by decide
  have hdescent : baseEnd_1221168 < baseStart_1221168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221170 : List Nat := [3, 2, 1, 1, 2, 1, 6, 1, 1, 4]
def baseStart_1221170 : Nat := 118140960795 + 1221170 * 2 ^ 59
def prefixEnd_1221170 : Nat := 4983230072969 + 3 ^ 40 * 1221170 * 2
def baseEnd_1221170 : Nat := 418031447234061600305965

theorem tailTrace_1221170 : CollatzResearch.WordTrace tailWord_1221170 prefixEnd_1221170 418031447234061600305965 := by
  unfold tailWord_1221170
  simp only [CollatzResearch.WordTrace]
  refine ⟨11134932246479281019215241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29693152657278082717907309 11134932246479281019215241)
  ·
    refine ⟨8351199184859460764411431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11134932246479281019215241 8351199184859460764411431)
    ·
      refine ⟨12526798777289191146617147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8351199184859460764411431 12526798777289191146617147)
      ·
        refine ⟨18790198165933786719925721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12526798777289191146617147 18790198165933786719925721)
        ·
          refine ⟨14092648624450340039944291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18790198165933786719925721 14092648624450340039944291)
          ·
            refine ⟨21138972936675510059916437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14092648624450340039944291 21138972936675510059916437)
            ·
              refine ⟨990889356406664534058583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21138972936675510059916437 990889356406664534058583)
              ·
                refine ⟨1486334034609996801087875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990889356406664534058583 1486334034609996801087875)
                ·
                  refine ⟨2229501051914995201631813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486334034609996801087875 2229501051914995201631813)
                  ·
                    refine ⟨418031447234061600305965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2229501051914995201631813 418031447234061600305965)
                    ·
                      rfl

theorem cell22_1221170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_1221170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221170 prefixEnd_1221170 := by exact prefixLift 1221170
  have htrace : WordTrace (prefixWord ++ tailWord_1221170) baseStart_1221170 baseEnd_1221170 := by
    simpa [prefixWord, tailWord_1221170, baseEnd_1221170] using wordTrace_append hprefix tailTrace_1221170
  have hstable : (prefixWord ++ tailWord_1221170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221170).length < 2 ^ (prefixWord ++ tailWord_1221170).sum := by decide
  have hdescent : baseEnd_1221170 < baseStart_1221170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221183 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 4, 3]
def baseStart_1221183 : Nat := 118140960795 + 1221183 * 2 ^ 59
def prefixEnd_1221183 : Nat := 4983230072969 + 3 ^ 40 * 1221183 * 2
def baseEnd_1221183 : Nat := 418035897399733899730925

theorem tailTrace_1221183 : CollatzResearch.WordTrace tailWord_1221183 prefixEnd_1221183 418035897399733899730925 := by
  unfold tailWord_1221183
  simp only [CollatzResearch.WordTrace]
  refine ⟨44540203134870027297084203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29693468756580018198056135 44540203134870027297084203)
  ·
    refine ⟨66810304702305040945626305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44540203134870027297084203 66810304702305040945626305)
    ·
      refine ⟨50107728526728780709219729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66810304702305040945626305 50107728526728780709219729)
      ·
        refine ⟨37580796395046585531914797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50107728526728780709219729 37580796395046585531914797)
        ·
          refine ⟨14092798648142469574468049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37580796395046585531914797 14092798648142469574468049)
          ·
            refine ⟨10569598986106852180851037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14092798648142469574468049 10569598986106852180851037)
            ·
              refine ⟨3963599619790069567819139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10569598986106852180851037 3963599619790069567819139)
              ·
                refine ⟨5945399429685104351728709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3963599619790069567819139 5945399429685104351728709)
                ·
                  refine ⟨1114762393065957065949133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5945399429685104351728709 1114762393065957065949133)
                  ·
                    refine ⟨418035897399733899730925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1114762393065957065949133 418035897399733899730925)
                    ·
                      rfl

theorem cell22_1221183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 3].length) (baseStart_1221183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221183 prefixEnd_1221183 := by exact prefixLift 1221183
  have htrace : WordTrace (prefixWord ++ tailWord_1221183) baseStart_1221183 baseEnd_1221183 := by
    simpa [prefixWord, tailWord_1221183, baseEnd_1221183] using wordTrace_append hprefix tailTrace_1221183
  have hstable : (prefixWord ++ tailWord_1221183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221183).length < 2 ^ (prefixWord ++ tailWord_1221183).sum := by decide
  have hdescent : baseEnd_1221183 < baseStart_1221183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221185 : List Nat := [1, 2, 5, 1, 1, 2, 2, 4, 4]
def baseStart_1221185 : Nat := 118140960795 + 1221185 * 2 ^ 59
def prefixEnd_1221185 : Nat := 4983230072969 + 3 ^ 40 * 1221185 * 2
def baseEnd_1221185 : Nat := 139345527346868853726973

theorem tailTrace_1221185 : CollatzResearch.WordTrace tailWord_1221185 prefixEnd_1221185 139345527346868853726973 := by
  unfold tailWord_1221185
  simp only [CollatzResearch.WordTrace]
  refine ⟨44540276080862781638657009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29693517387241854425771339 44540276080862781638657009)
  ·
    refine ⟨33405207060647086228992757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44540276080862781638657009 33405207060647086228992757)
    ·
      refine ⟨3131738161935664333968071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33405207060647086228992757 3131738161935664333968071)
      ·
        refine ⟨4697607242903496500952107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3131738161935664333968071 4697607242903496500952107)
        ·
          refine ⟨7046410864355244751428161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4697607242903496500952107 7046410864355244751428161)
          ·
            refine ⟨5284808148266433563571121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7046410864355244751428161 5284808148266433563571121)
            ·
              refine ⟨3963606111199825172678341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5284808148266433563571121 3963606111199825172678341)
              ·
                refine ⟨743176145849967219877189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3963606111199825172678341 743176145849967219877189)
                ·
                  refine ⟨139345527346868853726973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 743176145849967219877189 139345527346868853726973)
                  ·
                    rfl

theorem cell22_1221185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 4].length) (baseStart_1221185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221185 prefixEnd_1221185 := by exact prefixLift 1221185
  have htrace : WordTrace (prefixWord ++ tailWord_1221185) baseStart_1221185 baseEnd_1221185 := by
    simpa [prefixWord, tailWord_1221185, baseEnd_1221185] using wordTrace_append hprefix tailTrace_1221185
  have hstable : (prefixWord ++ tailWord_1221185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221185).length < 2 ^ (prefixWord ++ tailWord_1221185).sum := by decide
  have hdescent : baseEnd_1221185 < baseStart_1221185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221196 : List Nat := [2, 2, 1, 3, 1, 2, 2, 9]
def baseStart_1221196 : Nat := 118140960795 + 1221196 * 2 ^ 59
def prefixEnd_1221196 : Nat := 4983230072969 + 3 ^ 40 * 1221196 * 2
def baseEnd_1221196 : Nat := 46448927507267355461765

theorem tailTrace_1221196 : CollatzResearch.WordTrace tailWord_1221196 prefixEnd_1221196 46448927507267355461765 := by
  unfold tailWord_1221196
  simp only [CollatzResearch.WordTrace]
  refine ⟨22270338641911465258653721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29693784855881953678204961 22270338641911465258653721)
  ·
    refine ⟨16702753981433598943990291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22270338641911465258653721 16702753981433598943990291)
    ·
      refine ⟨25054130972150398415985437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16702753981433598943990291 25054130972150398415985437)
      ·
        refine ⟨9395299114556399405994539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25054130972150398415985437 9395299114556399405994539)
        ·
          refine ⟨14092948671834599108991809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9395299114556399405994539 14092948671834599108991809)
          ·
            refine ⟨10569711503875949331743857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14092948671834599108991809 10569711503875949331743857)
            ·
              refine ⟨7927283627906961998807893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10569711503875949331743857 7927283627906961998807893)
              ·
                refine ⟨46448927507267355461765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7927283627906961998807893 46448927507267355461765)
                ·
                  rfl

theorem cell22_1221196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 9].length) (baseStart_1221196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221196 prefixEnd_1221196 := by exact prefixLift 1221196
  have htrace : WordTrace (prefixWord ++ tailWord_1221196) baseStart_1221196 baseEnd_1221196 := by
    simpa [prefixWord, tailWord_1221196, baseEnd_1221196] using wordTrace_append hprefix tailTrace_1221196
  have hstable : (prefixWord ++ tailWord_1221196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221196).length < 2 ^ (prefixWord ++ tailWord_1221196).sum := by decide
  have hdescent : baseEnd_1221196 < baseStart_1221196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221228 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 5, 3]
def baseStart_1221228 : Nat := 118140960795 + 1221228 * 2 ^ 59
def prefixEnd_1221228 : Nat := 4983230072969 + 3 ^ 40 * 1221228 * 2
def baseEnd_1221228 : Nat := 418051301819368782355787

theorem tailTrace_1221228 : CollatzResearch.WordTrace tailWord_1221228 prefixEnd_1221228 418051301819368782355787 := by
  unfold tailWord_1221228
  simp only [CollatzResearch.WordTrace]
  refine ⟨22270922209853499991236169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29694562946471333321648225 22270922209853499991236169)
  ·
    refine ⟨16703191657390124993427127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22270922209853499991236169 16703191657390124993427127)
    ·
      refine ⟨25054787486085187490140691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16703191657390124993427127 25054787486085187490140691)
      ·
        refine ⟨37582181229127781235211037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25054787486085187490140691 37582181229127781235211037)
        ·
          refine ⟨14093317960922917963204139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37582181229127781235211037 14093317960922917963204139)
          ·
            refine ⟨21139976941384376944806209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14093317960922917963204139 21139976941384376944806209)
            ·
              refine ⟨15854982706038282708604657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21139976941384376944806209 15854982706038282708604657)
              ·
                refine ⟨11891237029528712031453493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15854982706038282708604657 11891237029528712031453493)
                ·
                  refine ⟨1114803471518316752948765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11891237029528712031453493 1114803471518316752948765)
                  ·
                    refine ⟨418051301819368782355787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1114803471518316752948765 418051301819368782355787)
                    ·
                      rfl

theorem cell22_1221228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_1221228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221228 prefixEnd_1221228 := by exact prefixLift 1221228
  have htrace : WordTrace (prefixWord ++ tailWord_1221228) baseStart_1221228 baseEnd_1221228 := by
    simpa [prefixWord, tailWord_1221228, baseEnd_1221228] using wordTrace_append hprefix tailTrace_1221228
  have hstable : (prefixWord ++ tailWord_1221228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221228).length < 2 ^ (prefixWord ++ tailWord_1221228).sum := by decide
  have hdescent : baseEnd_1221228 < baseStart_1221228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221348 : List Nat := [2, 3, 1, 1, 1, 5, 9]
def baseStart_1221348 : Nat := 118140960795 + 1221348 * 2 ^ 59
def prefixEnd_1221348 : Nat := 4983230072969 + 3 ^ 40 * 1221348 * 2
def baseEnd_1221348 : Nat := 15484902973026980346497

theorem tailTrace_1221348 : CollatzResearch.WordTrace tailWord_1221348 prefixEnd_1221348 15484902973026980346497 := by
  unfold tailWord_1221348
  simp only [CollatzResearch.WordTrace]
  refine ⟨22273110589636130238420349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29697480786181506984560465 22273110589636130238420349)
  ·
    refine ⟨8352416471113548839407631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22273110589636130238420349 8352416471113548839407631)
    ·
      refine ⟨12528624706670323259111447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8352416471113548839407631 12528624706670323259111447)
      ·
        refine ⟨18792937060005484888667171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12528624706670323259111447 18792937060005484888667171)
        ·
          refine ⟨28189405590008227333000757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18792937060005484888667171 28189405590008227333000757)
          ·
            refine ⟨2642756774063271312468821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28189405590008227333000757 2642756774063271312468821)
            ·
              refine ⟨15484902973026980346497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2642756774063271312468821 15484902973026980346497)
              ·
                rfl

theorem cell22_1221348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 9].length) (baseStart_1221348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221348 prefixEnd_1221348 := by exact prefixLift 1221348
  have htrace : WordTrace (prefixWord ++ tailWord_1221348) baseStart_1221348 baseEnd_1221348 := by
    simpa [prefixWord, tailWord_1221348, baseEnd_1221348] using wordTrace_append hprefix tailTrace_1221348
  have hstable : (prefixWord ++ tailWord_1221348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221348).length < 2 ^ (prefixWord ++ tailWord_1221348).sum := by decide
  have hdescent : baseEnd_1221348 < baseStart_1221348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221352 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 4, 3]
def baseStart_1221352 : Nat := 118140960795 + 1221352 * 2 ^ 59
def prefixEnd_1221352 : Nat := 4983230072969 + 3 ^ 40 * 1221352 * 2
def baseEnd_1221352 : Nat := 418093749553473792255407

theorem tailTrace_1221352 : CollatzResearch.WordTrace tailWord_1221352 prefixEnd_1221352 418093749553473792255407 := by
  unfold tailWord_1221352
  simp only [CollatzResearch.WordTrace]
  refine ⟨22273183535628884579993155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29697578047505179439990873 22273183535628884579993155)
  ·
    refine ⟨33409775303443326869989733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22273183535628884579993155 33409775303443326869989733)
    ·
      refine ⟨6264332869395623788123075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33409775303443326869989733 6264332869395623788123075)
      ·
        refine ⟨9396499304093435682184613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6264332869395623788123075 9396499304093435682184613)
        ·
          refine ⟨1761843619517519190409615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9396499304093435682184613 1761843619517519190409615)
          ·
            refine ⟨2642765429276278785614423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761843619517519190409615 2642765429276278785614423)
            ·
              refine ⟨3964148143914418178421635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2642765429276278785614423 3964148143914418178421635)
              ·
                refine ⟨5946222215871627267632453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964148143914418178421635 5946222215871627267632453)
                ·
                  refine ⟨1114916665475930112681085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5946222215871627267632453 1114916665475930112681085)
                  ·
                    refine ⟨418093749553473792255407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1114916665475930112681085 418093749553473792255407)
                    ·
                      rfl

theorem cell22_1221352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_1221352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221352 prefixEnd_1221352 := by exact prefixLift 1221352
  have htrace : WordTrace (prefixWord ++ tailWord_1221352) baseStart_1221352 baseEnd_1221352 := by
    simpa [prefixWord, tailWord_1221352, baseEnd_1221352] using wordTrace_append hprefix tailTrace_1221352
  have hstable : (prefixWord ++ tailWord_1221352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221352).length < 2 ^ (prefixWord ++ tailWord_1221352).sum := by decide
  have hdescent : baseEnd_1221352 < baseStart_1221352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221393 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 7]
def baseStart_1221393 : Nat := 118140960795 + 1221393 * 2 ^ 59
def prefixEnd_1221393 : Nat := 4983230072969 + 3 ^ 40 * 1221393 * 2
def baseEnd_1221393 : Nat := 139369261563787783993427

theorem tailTrace_1221393 : CollatzResearch.WordTrace tailWord_1221393 prefixEnd_1221393 139369261563787783993427 := by
  unfold tailWord_1221393
  simp only [CollatzResearch.WordTrace]
  refine ⟨44547862464109233162228833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29698574976072822108152555 44547862464109233162228833)
  ·
    refine ⟨33410896848081924871671625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44547862464109233162228833 33410896848081924871671625)
    ·
      refine ⟨25058172636061443653753719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33410896848081924871671625 25058172636061443653753719)
      ·
        refine ⟨37587258954092165480630579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25058172636061443653753719 37587258954092165480630579)
        ·
          refine ⟨56380888431138248220945869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37587258954092165480630579 56380888431138248220945869)
          ·
            refine ⟨21142833161676843082854701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56380888431138248220945869 21142833161676843082854701)
            ·
              refine ⟨7928562435628816156070513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21142833161676843082854701 7928562435628816156070513)
              ·
                refine ⟨5946421826721612117052885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7928562435628816156070513 5946421826721612117052885)
                ·
                  refine ⟨139369261563787783993427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5946421826721612117052885 139369261563787783993427)
                  ·
                    rfl

theorem cell22_1221393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_1221393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221393 prefixEnd_1221393 := by exact prefixLift 1221393
  have htrace : WordTrace (prefixWord ++ tailWord_1221393) baseStart_1221393 baseEnd_1221393 := by
    simpa [prefixWord, tailWord_1221393, baseEnd_1221393] using wordTrace_append hprefix tailTrace_1221393
  have hstable : (prefixWord ++ tailWord_1221393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221393).length < 2 ^ (prefixWord ++ tailWord_1221393).sum := by decide
  have hdescent : baseEnd_1221393 < baseStart_1221393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221410 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 7]
def baseStart_1221410 : Nat := 118140960795 + 1221410 * 2 ^ 59
def prefixEnd_1221410 : Nat := 4983230072969 + 3 ^ 40 * 1221410 * 2
def baseEnd_1221410 : Nat := 139371201379593658101743

theorem tailTrace_1221410 : CollatzResearch.WordTrace tailWord_1221410 prefixEnd_1221410 139371201379593658101743 := by
  unfold tailWord_1221410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11137120626261911266399421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29698988336698430043731789 11137120626261911266399421)
  ·
    refine ⟨4176420234848216724899783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11137120626261911266399421 4176420234848216724899783)
    ·
      refine ⟨6264630352272325087349675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4176420234848216724899783 6264630352272325087349675)
      ·
        refine ⟨9396945528408487631024513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6264630352272325087349675 9396945528408487631024513)
        ·
          refine ⟨7047709146306365723268385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9396945528408487631024513 7047709146306365723268385)
          ·
            refine ⟨5285781859729774292451289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7047709146306365723268385 5285781859729774292451289)
            ·
              refine ⟨3964336394797330719338467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5285781859729774292451289 3964336394797330719338467)
              ·
                refine ⟨5946504592195996079007701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964336394797330719338467 5946504592195996079007701)
                ·
                  refine ⟨139371201379593658101743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5946504592195996079007701 139371201379593658101743)
                  ·
                    rfl

theorem cell22_1221410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_1221410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221410 prefixEnd_1221410 := by exact prefixLift 1221410
  have htrace : WordTrace (prefixWord ++ tailWord_1221410) baseStart_1221410 baseEnd_1221410 := by
    simpa [prefixWord, tailWord_1221410, baseEnd_1221410] using wordTrace_append hprefix tailTrace_1221410
  have hstable : (prefixWord ++ tailWord_1221410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221410).length < 2 ^ (prefixWord ++ tailWord_1221410).sum := by decide
  have hdescent : baseEnd_1221410 < baseStart_1221410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221427 : List Nat := [1, 1, 1, 2, 6, 1, 4, 1, 5]
def baseStart_1221427 : Nat := 118140960795 + 1221427 * 2 ^ 59
def prefixEnd_1221427 : Nat := 4983230072969 + 3 ^ 40 * 1221427 * 2
def baseEnd_1221427 : Nat := 139373141195399532210059

theorem tailTrace_1221427 : CollatzResearch.WordTrace tailWord_1221427 prefixEnd_1221427 139373141195399532210059 := by
  unfold tailWord_1221427
  simp only [CollatzResearch.WordTrace]
  refine ⟨44549102545986056968966535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29699401697324037979311023 44549102545986056968966535)
  ·
    refine ⟨66823653818979085453449803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44549102545986056968966535 66823653818979085453449803)
    ·
      refine ⟨100235480728468628180174705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66823653818979085453449803 100235480728468628180174705)
      ·
        refine ⟨75176610546351471135131029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100235480728468628180174705 75176610546351471135131029)
        ·
          refine ⟨3523903619360225209459267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75176610546351471135131029 3523903619360225209459267)
          ·
            refine ⟨5285855429040337814188901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3523903619360225209459267 5285855429040337814188901)
            ·
              refine ⟨991097892945063340160419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5285855429040337814188901 991097892945063340160419)
              ·
                refine ⟨1486646839417595010240629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991097892945063340160419 1486646839417595010240629)
                ·
                  refine ⟨139373141195399532210059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1486646839417595010240629 139373141195399532210059)
                  ·
                    rfl

theorem cell22_1221427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 5].length) (baseStart_1221427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221427 prefixEnd_1221427 := by exact prefixLift 1221427
  have htrace : WordTrace (prefixWord ++ tailWord_1221427) baseStart_1221427 baseEnd_1221427 := by
    simpa [prefixWord, tailWord_1221427, baseEnd_1221427] using wordTrace_append hprefix tailTrace_1221427
  have hstable : (prefixWord ++ tailWord_1221427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221427).length < 2 ^ (prefixWord ++ tailWord_1221427).sum := by decide
  have hdescent : baseEnd_1221427 < baseStart_1221427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221472 : List Nat := [2, 1, 1, 3, 3, 1, 3, 4, 4]
def baseStart_1221472 : Nat := 118140960795 + 1221472 * 2 ^ 59
def prefixEnd_1221472 : Nat := 4983230072969 + 3 ^ 40 * 1221472 * 2
def baseEnd_1221472 : Nat := 139378276001944493085013

theorem tailTrace_1221472 : CollatzResearch.WordTrace tailWord_1221472 prefixEnd_1221472 139378276001944493085013 := by
  unfold tailWord_1221472
  simp only [CollatzResearch.WordTrace]
  refine ⟨22275371915411514827177335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29700495887215353102903113 22275371915411514827177335)
  ·
    refine ⟨33413057873117272240766003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22275371915411514827177335 33413057873117272240766003)
    ·
      refine ⟨50119586809675908361149005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33413057873117272240766003 50119586809675908361149005)
      ·
        refine ⟨18794845053628465635430877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50119586809675908361149005 18794845053628465635430877)
        ·
          refine ⟨7048066895110674613286579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18794845053628465635430877 7048066895110674613286579)
          ·
            refine ⟨10572100342666011919929869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7048066895110674613286579 10572100342666011919929869)
            ·
              refine ⟨3964537628499754469973701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10572100342666011919929869 3964537628499754469973701)
              ·
                refine ⟨743350805343703963120069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3964537628499754469973701 743350805343703963120069)
                ·
                  refine ⟨139378276001944493085013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 743350805343703963120069 139378276001944493085013)
                  ·
                    rfl

theorem cell22_1221472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 4].length) (baseStart_1221472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221472 prefixEnd_1221472 := by exact prefixLift 1221472
  have htrace : WordTrace (prefixWord ++ tailWord_1221472) baseStart_1221472 baseEnd_1221472 := by
    simpa [prefixWord, tailWord_1221472, baseEnd_1221472] using wordTrace_append hprefix tailTrace_1221472
  have hstable : (prefixWord ++ tailWord_1221472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221472).length < 2 ^ (prefixWord ++ tailWord_1221472).sum := by decide
  have hdescent : baseEnd_1221472 < baseStart_1221472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221485 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_1221485 : Nat := 118140960795 + 1221485 * 2 ^ 59
def prefixEnd_1221485 : Nat := 4983230072969 + 3 ^ 40 * 1221485 * 2
def baseEnd_1221485 : Nat := 418139278171505778679999

theorem tailTrace_1221485 : CollatzResearch.WordTrace tailWord_1221485 prefixEnd_1221485 418139278171505778679999 := by
  unfold tailWord_1221485
  simp only [CollatzResearch.WordTrace]
  refine ⟨44551217979775932874577909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29700811986517288583051939 44551217979775932874577909)
  ·
    refine ⟨4176676685603993706991679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44551217979775932874577909 4176676685603993706991679)
    ·
      refine ⟨6265015028405990560487519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4176676685603993706991679 6265015028405990560487519)
      ·
        refine ⟨9397522542608985840731279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6265015028405990560487519 9397522542608985840731279)
        ·
          refine ⟨14096283813913478761096919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9397522542608985840731279 14096283813913478761096919)
          ·
            refine ⟨21144425720870218141645379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14096283813913478761096919 21144425720870218141645379)
            ·
              refine ⟨31716638581305327212468069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21144425720870218141645379 31716638581305327212468069)
              ·
                refine ⟨5946869733994748852337763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31716638581305327212468069 5946869733994748852337763)
                ·
                  refine ⟨8920304600992123278506645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5946869733994748852337763 8920304600992123278506645)
                  ·
                    refine ⟨418139278171505778679999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8920304600992123278506645 418139278171505778679999)
                    ·
                      rfl

theorem cell22_1221485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_1221485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221485 prefixEnd_1221485 := by exact prefixLift 1221485
  have htrace : WordTrace (prefixWord ++ tailWord_1221485) baseStart_1221485 baseEnd_1221485 := by
    simpa [prefixWord, tailWord_1221485, baseEnd_1221485] using wordTrace_append hprefix tailTrace_1221485
  have hstable : (prefixWord ++ tailWord_1221485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221485).length < 2 ^ (prefixWord ++ tailWord_1221485).sum := by decide
  have hdescent : baseEnd_1221485 < baseStart_1221485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221634 : List Nat := [3, 4, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_1221634 : Nat := 118140960795 + 1221634 * 2 ^ 59
def prefixEnd_1221634 : Nat := 4983230072969 + 3 ^ 40 * 1221634 * 2
def baseEnd_1221634 : Nat := 418190283916519056704543

theorem tailTrace_1221634 : CollatzResearch.WordTrace tailWord_1221634 prefixEnd_1221634 418190283916519056704543 := by
  unfold tailWord_1221634
  simp only [CollatzResearch.WordTrace]
  refine ⟨11139163114059032830437989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29704434970824087547834637 11139163114059032830437989)
  ·
    refine ⟨2088593083886068655707123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11139163114059032830437989 2088593083886068655707123)
    ·
      refine ⟨3132889625829102983560685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2088593083886068655707123 3132889625829102983560685)
      ·
        refine ⟨1174833609685913618835257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3132889625829102983560685 1174833609685913618835257)
        ·
          refine ⟨881125207264435214126443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1174833609685913618835257 881125207264435214126443)
          ·
            refine ⟨1321687810896652821189665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881125207264435214126443 1321687810896652821189665)
            ·
              refine ⟨991265858172489615892249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1321687810896652821189665 991265858172489615892249)
              ·
                refine ⟨743449393629367211919187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 991265858172489615892249 743449393629367211919187)
                ·
                  refine ⟨1115174090444050817878781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 743449393629367211919187 1115174090444050817878781)
                  ·
                    refine ⟨418190283916519056704543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1115174090444050817878781 418190283916519056704543)
                    ·
                      rfl

theorem cell22_1221634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_1221634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221634 prefixEnd_1221634 := by exact prefixLift 1221634
  have htrace : WordTrace (prefixWord ++ tailWord_1221634) baseStart_1221634 baseEnd_1221634 := by
    simpa [prefixWord, tailWord_1221634, baseEnd_1221634] using wordTrace_append hprefix tailTrace_1221634
  have hstable : (prefixWord ++ tailWord_1221634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221634).length < 2 ^ (prefixWord ++ tailWord_1221634).sum := by decide
  have hdescent : baseEnd_1221634 < baseStart_1221634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221637 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_1221637 : Nat := 118140960795 + 1221637 * 2 ^ 59
def prefixEnd_1221637 : Nat := 4983230072969 + 3 ^ 40 * 1221637 * 2
def baseEnd_1221637 : Nat := 418191310877828048879533

theorem tailTrace_1221637 : CollatzResearch.WordTrace tailWord_1221637 prefixEnd_1221637 418191310877828048879533 := by
  unfold tailWord_1221637
  simp only [CollatzResearch.WordTrace]
  refine ⟨44556761875225262834111165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29704507916816841889407443 44556761875225262834111165)
  ·
    refine ⟨16708785703209473562791687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44556761875225262834111165 16708785703209473562791687)
    ·
      refine ⟨25063178554814210344187531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16708785703209473562791687 25063178554814210344187531)
      ·
        refine ⟨37594767832221315516281297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25063178554814210344187531 37594767832221315516281297)
        ·
          refine ⟨28196075874165986637210973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37594767832221315516281297 28196075874165986637210973)
          ·
            refine ⟨10573528452812244988954115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28196075874165986637210973 10573528452812244988954115)
            ·
              refine ⟨15860292679218367483431173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10573528452812244988954115 15860292679218367483431173)
              ·
                refine ⟨2973804877353443903143345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15860292679218367483431173 2973804877353443903143345)
                ·
                  refine ⟨2230353658015082927357509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2973804877353443903143345 2230353658015082927357509)
                  ·
                    refine ⟨418191310877828048879533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2230353658015082927357509 418191310877828048879533)
                    ·
                      rfl

theorem cell22_1221637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_1221637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221637 prefixEnd_1221637 := by exact prefixLift 1221637
  have htrace : WordTrace (prefixWord ++ tailWord_1221637) baseStart_1221637 baseEnd_1221637 := by
    simpa [prefixWord, tailWord_1221637, baseEnd_1221637] using wordTrace_append hprefix tailTrace_1221637
  have hstable : (prefixWord ++ tailWord_1221637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221637).length < 2 ^ (prefixWord ++ tailWord_1221637).sum := by decide
  have hdescent : baseEnd_1221637 < baseStart_1221637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221671 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1221671 : Nat := 118140960795 + 1221671 * 2 ^ 59
def prefixEnd_1221671 : Nat := 4983230072969 + 3 ^ 40 * 1221671 * 2
def baseEnd_1221671 : Nat := 418202949772663293529429

theorem tailTrace_1221671 : CollatzResearch.WordTrace tailWord_1221671 prefixEnd_1221671 418202949772663293529429 := by
  unfold tailWord_1221671
  simp only [CollatzResearch.WordTrace]
  refine ⟨44558001957102086640848867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29705334638068057760565911 44558001957102086640848867)
  ·
    refine ⟨66837002935653129961273301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44558001957102086640848867 66837002935653129961273301)
    ·
      refine ⟨1566492256304370233467343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 66837002935653129961273301 1566492256304370233467343)
      ·
        refine ⟨2349738384456555350201015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566492256304370233467343 2349738384456555350201015)
        ·
          refine ⟨3524607576684833025301523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2349738384456555350201015 3524607576684833025301523)
          ·
            refine ⟨5286911365027249537952285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524607576684833025301523 5286911365027249537952285)
            ·
              refine ⟨1982591761885218576732107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5286911365027249537952285 1982591761885218576732107)
              ·
                refine ⟨2973887642827827865098161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1982591761885218576732107 2973887642827827865098161)
                ·
                  refine ⟨2230415732120870898823621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2973887642827827865098161 2230415732120870898823621)
                  ·
                    refine ⟨418202949772663293529429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2230415732120870898823621 418202949772663293529429)
                    ·
                      rfl

theorem cell22_1221671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1221671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221671 prefixEnd_1221671 := by exact prefixLift 1221671
  have htrace : WordTrace (prefixWord ++ tailWord_1221671) baseStart_1221671 baseEnd_1221671 := by
    simpa [prefixWord, tailWord_1221671, baseEnd_1221671] using wordTrace_append hprefix tailTrace_1221671
  have hstable : (prefixWord ++ tailWord_1221671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221671).length < 2 ^ (prefixWord ++ tailWord_1221671).sum := by decide
  have hdescent : baseEnd_1221671 < baseStart_1221671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221701 : List Nat := [1, 3, 1, 1, 1, 3, 4, 4, 1, 3]
def baseStart_1221701 : Nat := 118140960795 + 1221701 * 2 ^ 59
def prefixEnd_1221701 : Nat := 4983230072969 + 3 ^ 40 * 1221701 * 2
def baseEnd_1221701 : Nat := 418213219385753215279337

theorem tailTrace_1221701 : CollatzResearch.WordTrace tailWord_1221701 prefixEnd_1221701 418213219385753215279337 := by
  unfold tailWord_1221701
  simp only [CollatzResearch.WordTrace]
  refine ⟨44559096146993401764440957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29706064097995601176293971 44559096146993401764440957)
  ·
    refine ⟨16709661055122525661665359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44559096146993401764440957 16709661055122525661665359)
    ·
      refine ⟨25064491582683788492498039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16709661055122525661665359 25064491582683788492498039)
      ·
        refine ⟨37596737374025682738747059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25064491582683788492498039 37596737374025682738747059)
        ·
          refine ⟨56395106061038524108120589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37596737374025682738747059 56395106061038524108120589)
          ·
            refine ⟨21148164772889446540545221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56395106061038524108120589 21148164772889446540545221)
            ·
              refine ⟨3965280894916771226352229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21148164772889446540545221 3965280894916771226352229)
              ·
                refine ⟨743490167796894604941043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3965280894916771226352229 743490167796894604941043)
                ·
                  refine ⟨1115235251695341907411565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 743490167796894604941043 1115235251695341907411565)
                  ·
                    refine ⟨418213219385753215279337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1115235251695341907411565 418213219385753215279337)
                    ·
                      rfl

theorem cell22_1221701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_1221701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221701 prefixEnd_1221701 := by exact prefixLift 1221701
  have htrace : WordTrace (prefixWord ++ tailWord_1221701) baseStart_1221701 baseEnd_1221701 := by
    simpa [prefixWord, tailWord_1221701, baseEnd_1221701] using wordTrace_append hprefix tailTrace_1221701
  have hstable : (prefixWord ++ tailWord_1221701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221701).length < 2 ^ (prefixWord ++ tailWord_1221701).sum := by decide
  have hdescent : baseEnd_1221701 < baseStart_1221701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221744 : List Nat := [2, 1, 1, 1, 5, 1, 1, 5, 1, 4]
def baseStart_1221744 : Nat := 118140960795 + 1221744 * 2 ^ 59
def prefixEnd_1221744 : Nat := 4983230072969 + 3 ^ 40 * 1221744 * 2
def baseEnd_1221744 : Nat := 418227939164515436454205

theorem tailTrace_1221744 : CollatzResearch.WordTrace tailWord_1221744 prefixEnd_1221744 418227939164515436454205 := by
  unfold tailWord_1221744
  simp only [CollatzResearch.WordTrace]
  refine ⟨22280332242918810054128143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29707109657225080072170857 22280332242918810054128143)
  ·
    refine ⟨33420498364378215081192215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22280332242918810054128143 33420498364378215081192215)
    ·
      refine ⟨50130747546567322621788323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33420498364378215081192215 50130747546567322621788323)
      ·
        refine ⟨75196121319850983932682485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50130747546567322621788323 75196121319850983932682485)
        ·
          refine ⟨7049636373736029743688983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75196121319850983932682485 7049636373736029743688983)
          ·
            refine ⟨10574454560604044615533475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7049636373736029743688983 10574454560604044615533475)
            ·
              refine ⟨15861681840906066923300213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10574454560604044615533475 15861681840906066923300213)
              ·
                refine ⟨1487032672584943774059395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15861681840906066923300213 1487032672584943774059395)
                ·
                  refine ⟨2230549008877415661089093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487032672584943774059395 2230549008877415661089093)
                  ·
                    refine ⟨418227939164515436454205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2230549008877415661089093 418227939164515436454205)
                    ·
                      rfl

theorem cell22_1221744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_1221744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221744 prefixEnd_1221744 := by exact prefixLift 1221744
  have htrace : WordTrace (prefixWord ++ tailWord_1221744) baseStart_1221744 baseEnd_1221744 := by
    simpa [prefixWord, tailWord_1221744, baseEnd_1221744] using wordTrace_append hprefix tailTrace_1221744
  have hstable : (prefixWord ++ tailWord_1221744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221744).length < 2 ^ (prefixWord ++ tailWord_1221744).sum := by decide
  have hdescent : baseEnd_1221744 < baseStart_1221744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221772 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_1221772 : Nat := 118140960795 + 1221772 * 2 ^ 59
def prefixEnd_1221772 : Nat := 4983230072969 + 3 ^ 40 * 1221772 * 2
def baseEnd_1221772 : Nat := 418237524136732696754119

theorem tailTrace_1221772 : CollatzResearch.WordTrace tailWord_1221772 prefixEnd_1221772 418237524136732696754119 := by
  unfold tailWord_1221772
  simp only [CollatzResearch.WordTrace]
  refine ⟨22280842864868090445137785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29707790486490787260183713 22280842864868090445137785)
  ·
    refine ⟨16710632148651067833853339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22280842864868090445137785 16710632148651067833853339)
    ·
      refine ⟨25065948222976601750780009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16710632148651067833853339 25065948222976601750780009)
      ·
        refine ⟨18799461167232451313085007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25065948222976601750780009 18799461167232451313085007)
        ·
          refine ⟨28199191750848676969627511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18799461167232451313085007 28199191750848676969627511)
          ·
            refine ⟨42298787626273015454441267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28199191750848676969627511 42298787626273015454441267)
            ·
              refine ⟨63448181439409523181661901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42298787626273015454441267 63448181439409523181661901)
              ·
                refine ⟨23793068039778571193123213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63448181439409523181661901 23793068039778571193123213)
                ·
                  refine ⟨8922400514916964197421205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23793068039778571193123213 8922400514916964197421205)
                  ·
                    refine ⟨418237524136732696754119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8922400514916964197421205 418237524136732696754119)
                    ·
                      rfl

theorem cell22_1221772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_1221772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221772 prefixEnd_1221772 := by exact prefixLift 1221772
  have htrace : WordTrace (prefixWord ++ tailWord_1221772) baseStart_1221772 baseEnd_1221772 := by
    simpa [prefixWord, tailWord_1221772, baseEnd_1221772] using wordTrace_append hprefix tailTrace_1221772
  have hstable : (prefixWord ++ tailWord_1221772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221772).length < 2 ^ (prefixWord ++ tailWord_1221772).sum := by decide
  have hdescent : baseEnd_1221772 < baseStart_1221772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221778 : List Nat := [3, 2, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_1221778 : Nat := 118140960795 + 1221778 * 2 ^ 59
def prefixEnd_1221778 : Nat := 4983230072969 + 3 ^ 40 * 1221778 * 2
def baseEnd_1221778 : Nat := 418239578059350681104101

theorem tailTrace_1221778 : CollatzResearch.WordTrace tailWord_1221778 prefixEnd_1221778 418239578059350681104101 := by
  unfold tailWord_1221778
  simp only [CollatzResearch.WordTrace]
  refine ⟨11140476141928610978748497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29707936378476295943329325 11140476141928610978748497)
  ·
    refine ⟨8355357106446458234061373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11140476141928610978748497 8355357106446458234061373)
    ·
      refine ⟨3133258914917421837773015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8355357106446458234061373 3133258914917421837773015)
      ·
        refine ⟨4699888372376132756659523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3133258914917421837773015 4699888372376132756659523)
        ·
          refine ⟨7049832558564199134989285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4699888372376132756659523 7049832558564199134989285)
          ·
            refine ⟨1321843604730787337810491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7049832558564199134989285 1321843604730787337810491)
            ·
              refine ⟨1982765407096181006715737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321843604730787337810491 1982765407096181006715737)
              ·
                refine ⟨1487074055322135755036803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1982765407096181006715737 1487074055322135755036803)
                ·
                  refine ⟨2230611082983203632555205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487074055322135755036803 2230611082983203632555205)
                  ·
                    refine ⟨418239578059350681104101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2230611082983203632555205 418239578059350681104101)
                    ·
                      rfl

theorem cell22_1221778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_1221778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221778 prefixEnd_1221778 := by exact prefixLift 1221778
  have htrace : WordTrace (prefixWord ++ tailWord_1221778) baseStart_1221778 baseEnd_1221778 := by
    simpa [prefixWord, tailWord_1221778, baseEnd_1221778] using wordTrace_append hprefix tailTrace_1221778
  have hstable : (prefixWord ++ tailWord_1221778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221778).length < 2 ^ (prefixWord ++ tailWord_1221778).sum := by decide
  have hdescent : baseEnd_1221778 < baseStart_1221778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221791 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 1, 5]
def baseStart_1221791 : Nat := 118140960795 + 1221791 * 2 ^ 59
def prefixEnd_1221791 : Nat := 4983230072969 + 3 ^ 40 * 1221791 * 2
def baseEnd_1221791 : Nat := 418244028225022980529061

theorem tailTrace_1221791 : CollatzResearch.WordTrace tailWord_1221791 prefixEnd_1221791 418244028225022980529061 := by
  unfold tailWord_1221791
  simp only [CollatzResearch.WordTrace]
  refine ⟨44562378716667347135217227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29708252477778231423478151 44562378716667347135217227)
  ·
    refine ⟨66843568075001020702825841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44562378716667347135217227 66843568075001020702825841)
    ·
      refine ⟨50132676056250765527119381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66843568075001020702825841 50132676056250765527119381)
      ·
        refine ⟨2349969190136754634083721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50132676056250765527119381 2349969190136754634083721)
        ·
          refine ⟨1762476892602565975562791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2349969190136754634083721 1762476892602565975562791)
          ·
            refine ⟨2643715338903848963344187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1762476892602565975562791 2643715338903848963344187)
            ·
              refine ⟨3965573008355773445016281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2643715338903848963344187 3965573008355773445016281)
              ·
                refine ⟨2974179756266830083762211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3965573008355773445016281 2974179756266830083762211)
                ·
                  refine ⟨4461269634400245125643317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2974179756266830083762211 4461269634400245125643317)
                  ·
                    refine ⟨418244028225022980529061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4461269634400245125643317 418244028225022980529061)
                    ·
                      rfl

theorem cell22_1221791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_1221791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221791 prefixEnd_1221791 := by exact prefixLift 1221791
  have htrace : WordTrace (prefixWord ++ tailWord_1221791) baseStart_1221791 baseEnd_1221791 := by
    simpa [prefixWord, tailWord_1221791, baseEnd_1221791] using wordTrace_append hprefix tailTrace_1221791
  have hstable : (prefixWord ++ tailWord_1221791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221791).length < 2 ^ (prefixWord ++ tailWord_1221791).sum := by decide
  have hdescent : baseEnd_1221791 < baseStart_1221791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221864 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 4, 5]
def baseStart_1221864 : Nat := 118140960795 + 1221864 * 2 ^ 59
def prefixEnd_1221864 : Nat := 4983230072969 + 3 ^ 40 * 1221864 * 2
def baseEnd_1221864 : Nat := 418269017616875123453837

theorem tailTrace_1221864 : CollatzResearch.WordTrace tailWord_1221864 prefixEnd_1221864 418269017616875123453837 := by
  unfold tailWord_1221864
  simp only [CollatzResearch.WordTrace]
  refine ⟨22282520622701440301312323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29710027496935253735083097 22282520622701440301312323)
  ·
    refine ⟨33423780934052160451968485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22282520622701440301312323 33423780934052160451968485)
    ·
      refine ⟨6266958925134780084744091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33423780934052160451968485 6266958925134780084744091)
      ·
        refine ⟨9400438387702170127116137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6266958925134780084744091 9400438387702170127116137)
        ·
          refine ⟨7050328790776627595337103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9400438387702170127116137 7050328790776627595337103)
          ·
            refine ⟨10575493186164941393005655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7050328790776627595337103 10575493186164941393005655)
            ·
              refine ⟨15863239779247412089508483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10575493186164941393005655 15863239779247412089508483)
              ·
                refine ⟨23794859668871118134262725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15863239779247412089508483 23794859668871118134262725)
                ·
                  refine ⟨4461536187913334650174261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23794859668871118134262725 4461536187913334650174261)
                  ·
                    refine ⟨418269017616875123453837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4461536187913334650174261 418269017616875123453837)
                    ·
                      rfl

theorem cell22_1221864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_1221864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221864 prefixEnd_1221864 := by exact prefixLift 1221864
  have htrace : WordTrace (prefixWord ++ tailWord_1221864) baseStart_1221864 baseEnd_1221864 := by
    simpa [prefixWord, tailWord_1221864, baseEnd_1221864] using wordTrace_append hprefix tailTrace_1221864
  have hstable : (prefixWord ++ tailWord_1221864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221864).length < 2 ^ (prefixWord ++ tailWord_1221864).sum := by decide
  have hdescent : baseEnd_1221864 < baseStart_1221864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221866 : List Nat := [3, 1, 3, 1, 1, 3, 3, 2, 5]
def baseStart_1221866 : Nat := 118140960795 + 1221866 * 2 ^ 59
def prefixEnd_1221866 : Nat := 4983230072969 + 3 ^ 40 * 1221866 * 2
def baseEnd_1221866 : Nat := 139423234085915928301277

theorem tailTrace_1221866 : CollatzResearch.WordTrace tailWord_1221866 prefixEnd_1221866 139423234085915928301277 := by
  unfold tailWord_1221866
  simp only [CollatzResearch.WordTrace]
  refine ⟨11141278547848908736049363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29710076127597089962798301 11141278547848908736049363)
  ·
    refine ⟨16711917821773363104074045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11141278547848908736049363 16711917821773363104074045)
    ·
      refine ⟨6266969183165011164027767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16711917821773363104074045 6266969183165011164027767)
      ·
        refine ⟨9400453774747516746041651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6266969183165011164027767 9400453774747516746041651)
        ·
          refine ⟨14100680662121275119062477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9400453774747516746041651 14100680662121275119062477)
          ·
            refine ⟨5287755248295478169648429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14100680662121275119062477 5287755248295478169648429)
            ·
              refine ⟨1982908218110804313618161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5287755248295478169648429 1982908218110804313618161)
              ·
                refine ⟨1487181163583103235213621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1982908218110804313618161 1487181163583103235213621)
                ·
                  refine ⟨139423234085915928301277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1487181163583103235213621 139423234085915928301277)
                  ·
                    rfl

theorem cell22_1221866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_1221866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221866 prefixEnd_1221866 := by exact prefixLift 1221866
  have htrace : WordTrace (prefixWord ++ tailWord_1221866) baseStart_1221866 baseEnd_1221866 := by
    simpa [prefixWord, tailWord_1221866, baseEnd_1221866] using wordTrace_append hprefix tailTrace_1221866
  have hstable : (prefixWord ++ tailWord_1221866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221866).length < 2 ^ (prefixWord ++ tailWord_1221866).sum := by decide
  have hdescent : baseEnd_1221866 < baseStart_1221866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221909 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_1221909 : Nat := 118140960795 + 1221909 * 2 ^ 59
def prefixEnd_1221909 : Nat := 4983230072969 + 3 ^ 40 * 1221909 * 2
def baseEnd_1221909 : Nat := 418284422036510006078699

theorem tailTrace_1221909 : CollatzResearch.WordTrace tailWord_1221909 prefixEnd_1221909 418284422036510006078699 := by
  unfold tailWord_1221909
  simp only [CollatzResearch.WordTrace]
  refine ⟨44566682530239853288012781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29711121686826568858675187 44566682530239853288012781)
  ·
    refine ⟨16712505948839944983004793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44566682530239853288012781 16712505948839944983004793)
    ·
      refine ⟨12534379461629958737253595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16712505948839944983004793 12534379461629958737253595)
      ·
        refine ⟨18801569192444938105880393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12534379461629958737253595 18801569192444938105880393)
        ·
          refine ⟨14101176894333703579410295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18801569192444938105880393 14101176894333703579410295)
          ·
            refine ⟨21151765341500555369115443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14101176894333703579410295 21151765341500555369115443)
            ·
              refine ⟨31727648012250833053673165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21151765341500555369115443 31727648012250833053673165)
              ·
                refine ⟨11897868004594062395127437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31727648012250833053673165 11897868004594062395127437)
                ·
                  refine ⟨4461700501722773398172789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11897868004594062395127437 4461700501722773398172789)
                  ·
                    refine ⟨418284422036510006078699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4461700501722773398172789 418284422036510006078699)
                    ·
                      rfl

theorem cell22_1221909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_1221909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221909 prefixEnd_1221909 := by exact prefixLift 1221909
  have htrace : WordTrace (prefixWord ++ tailWord_1221909) baseStart_1221909 baseEnd_1221909 := by
    simpa [prefixWord, tailWord_1221909, baseEnd_1221909] using wordTrace_append hprefix tailTrace_1221909
  have hstable : (prefixWord ++ tailWord_1221909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221909).length < 2 ^ (prefixWord ++ tailWord_1221909).sum := by decide
  have hdescent : baseEnd_1221909 < baseStart_1221909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221928 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 6]
def baseStart_1221928 : Nat := 118140960795 + 1221928 * 2 ^ 59
def prefixEnd_1221928 : Nat := 4983230072969 + 3 ^ 40 * 1221928 * 2
def baseEnd_1221928 : Nat := 139430308708266763284547

theorem tailTrace_1221928 : CollatzResearch.WordTrace tailWord_1221928 prefixEnd_1221928 139430308708266763284547 := by
  unfold tailWord_1221928
  simp only [CollatzResearch.WordTrace]
  refine ⟨22283687758585509766477219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29711583678114013021969625 22283687758585509766477219)
  ·
    refine ⟨33425531637878264649715829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22283687758585509766477219 33425531637878264649715829)
    ·
      refine ⟨3133643591051087310910859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33425531637878264649715829 3133643591051087310910859)
      ·
        refine ⟨4700465386576630966366289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3133643591051087310910859 4700465386576630966366289)
        ·
          refine ⟨3525349039932473224774717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4700465386576630966366289 3525349039932473224774717)
          ·
            refine ⟨1322005889974677459290519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3525349039932473224774717 1322005889974677459290519)
            ·
              refine ⟨1983008834962016188935779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322005889974677459290519 1983008834962016188935779)
              ·
                refine ⟨2974513252443024283403669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983008834962016188935779 2974513252443024283403669)
                ·
                  refine ⟨139430308708266763284547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2974513252443024283403669 139430308708266763284547)
                  ·
                    rfl

theorem cell22_1221928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 6].length) (baseStart_1221928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221928 prefixEnd_1221928 := by exact prefixLift 1221928
  have htrace : WordTrace (prefixWord ++ tailWord_1221928) baseStart_1221928 baseEnd_1221928 := by
    simpa [prefixWord, tailWord_1221928, baseEnd_1221928] using wordTrace_append hprefix tailTrace_1221928
  have hstable : (prefixWord ++ tailWord_1221928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221928).length < 2 ^ (prefixWord ++ tailWord_1221928).sum := by decide
  have hdescent : baseEnd_1221928 < baseStart_1221928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221939 : List Nat := [1, 1, 1, 2, 5, 2, 1, 9]
def baseStart_1221939 : Nat := 118140960795 + 1221939 * 2 ^ 59
def prefixEnd_1221939 : Nat := 4983230072969 + 3 ^ 40 * 1221939 * 2
def baseEnd_1221939 : Nat := 46477187961066658647623

theorem tailTrace_1221939 : CollatzResearch.WordTrace tailWord_1221939 prefixEnd_1221939 46477187961066658647623 := by
  unfold tailWord_1221939
  simp only [CollatzResearch.WordTrace]
  refine ⟨44567776720131168411604871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29711851146754112274403247 44567776720131168411604871)
  ·
    refine ⟨66851665080196752617407307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44567776720131168411604871 66851665080196752617407307)
    ·
      refine ⟨100277497620295128926110961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66851665080196752617407307 100277497620295128926110961)
      ·
        refine ⟨75208123215221346694583221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100277497620295128926110961 75208123215221346694583221)
        ·
          refine ⟨7050761551427001252617177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75208123215221346694583221 7050761551427001252617177)
          ·
            refine ⟨5288071163570250939462883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7050761551427001252617177 5288071163570250939462883)
            ·
              refine ⟨7932106745355376409194325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5288071163570250939462883 7932106745355376409194325)
              ·
                refine ⟨46477187961066658647623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7932106745355376409194325 46477187961066658647623)
                ·
                  rfl

theorem cell22_1221939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 9].length) (baseStart_1221939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221939 prefixEnd_1221939 := by exact prefixLift 1221939
  have htrace : WordTrace (prefixWord ++ tailWord_1221939) baseStart_1221939 baseEnd_1221939 := by
    simpa [prefixWord, tailWord_1221939, baseEnd_1221939] using wordTrace_append hprefix tailTrace_1221939
  have hstable : (prefixWord ++ tailWord_1221939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221939).length < 2 ^ (prefixWord ++ tailWord_1221939).sum := by decide
  have hdescent : baseEnd_1221939 < baseStart_1221939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221986 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1221986 : Nat := 118140960795 + 1221986 * 2 ^ 59
def prefixEnd_1221986 : Nat := 4983230072969 + 3 ^ 40 * 1221986 * 2
def baseEnd_1221986 : Nat := 418310780710107471903463

theorem tailTrace_1221986 : CollatzResearch.WordTrace tailWord_1221986 prefixEnd_1221986 418310780710107471903463 := by
  unfold tailWord_1221986
  simp only [CollatzResearch.WordTrace]
  refine ⟨11142372737740223859641453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29712993967307263625710541 11142372737740223859641453)
  ·
    refine ⟨4178389776652583947365545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11142372737740223859641453 4178389776652583947365545)
    ·
      refine ⟨3133792332489437960524159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4178389776652583947365545 3133792332489437960524159)
      ·
        refine ⟨4700688498734156940786239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3133792332489437960524159 4700688498734156940786239)
        ·
          refine ⟨7051032748101235411179359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4700688498734156940786239 7051032748101235411179359)
          ·
            refine ⟨10576549122151853116769039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7051032748101235411179359 10576549122151853116769039)
            ·
              refine ⟨15864823683227779675153559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10576549122151853116769039 15864823683227779675153559)
              ·
                refine ⟨23797235524841669512730339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15864823683227779675153559 23797235524841669512730339)
                ·
                  refine ⟨35695853287262504269095509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23797235524841669512730339 35695853287262504269095509)
                  ·
                    refine ⟨418310780710107471903463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35695853287262504269095509 418310780710107471903463)
                    ·
                      rfl

theorem cell22_1221986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1221986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1221986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1221986 prefixEnd_1221986 := by exact prefixLift 1221986
  have htrace : WordTrace (prefixWord ++ tailWord_1221986) baseStart_1221986 baseEnd_1221986 := by
    simpa [prefixWord, tailWord_1221986, baseEnd_1221986] using wordTrace_append hprefix tailTrace_1221986
  have hstable : (prefixWord ++ tailWord_1221986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221986).length < 2 ^ (prefixWord ++ tailWord_1221986).sum := by decide
  have hdescent : baseEnd_1221986 < baseStart_1221986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222001 : List Nat := [1, 2, 2, 2, 1, 2, 4, 3, 5]
def baseStart_1222001 : Nat := 118140960795 + 1222001 * 2 ^ 59
def prefixEnd_1222001 : Nat := 4983230072969 + 3 ^ 40 * 1222001 * 2
def baseEnd_1222001 : Nat := 139438638505550810926139

theorem tailTrace_1222001 : CollatzResearch.WordTrace tailWord_1222001 prefixEnd_1222001 139438638505550810926139 := by
  unfold tailWord_1222001
  simp only [CollatzResearch.WordTrace]
  refine ⟨44570038045906553000361857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29713358697271035333574571 44570038045906553000361857)
  ·
    refine ⟨33427528534429914750271393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44570038045906553000361857 33427528534429914750271393)
    ·
      refine ⟨25070646400822436062703545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33427528534429914750271393 25070646400822436062703545)
      ·
        refine ⟨18802984800616827047027659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25070646400822436062703545 18802984800616827047027659)
        ·
          refine ⟨28204477200925240570541489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18802984800616827047027659 28204477200925240570541489)
          ·
            refine ⟨21153357900693930427906117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28204477200925240570541489 21153357900693930427906117)
            ·
              refine ⟨3966254606380111955232397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21153357900693930427906117 3966254606380111955232397)
              ·
                refine ⟨1487345477392541983212149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3966254606380111955232397 1487345477392541983212149)
                ·
                  refine ⟨139438638505550810926139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1487345477392541983212149 139438638505550810926139)
                  ·
                    rfl

theorem cell22_1222001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 5].length) (baseStart_1222001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222001 prefixEnd_1222001 := by exact prefixLift 1222001
  have htrace : WordTrace (prefixWord ++ tailWord_1222001) baseStart_1222001 baseEnd_1222001 := by
    simpa [prefixWord, tailWord_1222001, baseEnd_1222001] using wordTrace_append hprefix tailTrace_1222001
  have hstable : (prefixWord ++ tailWord_1222001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222001).length < 2 ^ (prefixWord ++ tailWord_1222001).sum := by decide
  have hdescent : baseEnd_1222001 < baseStart_1222001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222005 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 3, 3]
def baseStart_1222005 : Nat := 118140960795 + 1222005 * 2 ^ 59
def prefixEnd_1222005 : Nat := 4983230072969 + 3 ^ 40 * 1222005 * 2
def baseEnd_1222005 : Nat := 418317284798397755678405

theorem tailTrace_1222005 : CollatzResearch.WordTrace tailWord_1222005 prefixEnd_1222005 418317284798397755678405 := by
  unfold tailWord_1222005
  simp only [CollatzResearch.WordTrace]
  refine ⟨44570183937892061683507469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29713455958594707789004979 44570183937892061683507469)
  ·
    refine ⟨16713818976709523131315301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44570183937892061683507469 16713818976709523131315301)
    ·
      refine ⟨3133841058133035587121619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16713818976709523131315301 3133841058133035587121619)
      ·
        refine ⟨4700761587199553380682429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3133841058133035587121619 4700761587199553380682429)
        ·
          refine ⟨1762785595199832517755911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4700761587199553380682429 1762785595199832517755911)
          ·
            refine ⟨2644178392799748776633867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1762785595199832517755911 2644178392799748776633867)
            ·
              refine ⟨3966267589199623164950801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644178392799748776633867 3966267589199623164950801)
              ·
                refine ⟨2974700691899717373713101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3966267589199623164950801 2974700691899717373713101)
                ·
                  refine ⟨1115512759462394015142413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2974700691899717373713101 1115512759462394015142413)
                  ·
                    refine ⟨418317284798397755678405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1115512759462394015142413 418317284798397755678405)
                    ·
                      rfl

theorem cell22_1222005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_1222005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222005 prefixEnd_1222005 := by exact prefixLift 1222005
  have htrace : WordTrace (prefixWord ++ tailWord_1222005) baseStart_1222005 baseEnd_1222005 := by
    simpa [prefixWord, tailWord_1222005, baseEnd_1222005] using wordTrace_append hprefix tailTrace_1222005
  have hstable : (prefixWord ++ tailWord_1222005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222005).length < 2 ^ (prefixWord ++ tailWord_1222005).sum := by decide
  have hdescent : baseEnd_1222005 < baseStart_1222005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222153 : List Nat := [1, 2, 1, 1, 3, 1, 6, 2, 5]
def baseStart_1222153 : Nat := 118140960795 + 1222153 * 2 ^ 59
def prefixEnd_1222153 : Nat := 4983230072969 + 3 ^ 40 * 1222153 * 2
def baseEnd_1222153 : Nat := 139455982740991567659317

theorem tailTrace_1222153 : CollatzResearch.WordTrace tailWord_1222153 prefixEnd_1222153 139455982740991567659317 := by
  unfold tailWord_1222153
  simp only [CollatzResearch.WordTrace]
  refine ⟨44575581941355882959895113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29717054627570588639930075 44575581941355882959895113)
  ·
    refine ⟨33431686456016912219921335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44575581941355882959895113 33431686456016912219921335)
    ·
      refine ⟨50147529684025368329882003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33431686456016912219921335 50147529684025368329882003)
      ·
        refine ⟨75221294526038052494823005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50147529684025368329882003 75221294526038052494823005)
        ·
          refine ⟨28207985447264269685558627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75221294526038052494823005 28207985447264269685558627)
          ·
            refine ⟨42311978170896404528337941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28207985447264269685558627 42311978170896404528337941)
            ·
              refine ⟨1983373976760768962265841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42311978170896404528337941 1983373976760768962265841)
              ·
                refine ⟨1487530482570576721699381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1983373976760768962265841 1487530482570576721699381)
                ·
                  refine ⟨139455982740991567659317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1487530482570576721699381 139455982740991567659317)
                  ·
                    rfl

theorem cell22_1222153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 5].length) (baseStart_1222153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222153 prefixEnd_1222153 := by exact prefixLift 1222153
  have htrace : WordTrace (prefixWord ++ tailWord_1222153) baseStart_1222153 baseEnd_1222153 := by
    simpa [prefixWord, tailWord_1222153, baseEnd_1222153] using wordTrace_append hprefix tailTrace_1222153
  have hstable : (prefixWord ++ tailWord_1222153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222153).length < 2 ^ (prefixWord ++ tailWord_1222153).sum := by decide
  have hdescent : baseEnd_1222153 < baseStart_1222153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222200 : List Nat := [2, 1, 2, 1, 4, 3, 1, 3, 1, 4]
def baseStart_1222200 : Nat := 118140960795 + 1222200 * 2 ^ 59
def prefixEnd_1222200 : Nat := 4983230072969 + 3 ^ 40 * 1222200 * 2
def baseEnd_1222200 : Nat := 418384037283482247052807

theorem tailTrace_1222200 : CollatzResearch.WordTrace tailWord_1222200 prefixEnd_1222200 418384037283482247052807 := by
  unfold tailWord_1222200
  simp only [CollatzResearch.WordTrace]
  refine ⟨22288648086092804993428027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29718197448123739991237369 22288648086092804993428027)
  ·
    refine ⟨33432972129139207490142041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22288648086092804993428027 33432972129139207490142041)
    ·
      refine ⟨25074729096854405617606531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33432972129139207490142041 25074729096854405617606531)
      ·
        refine ⟨37612093645281608426409797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25074729096854405617606531 37612093645281608426409797)
        ·
          refine ⟨7052267558490301579951837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37612093645281608426409797 7052267558490301579951837)
          ·
            refine ⟨2644600334433863092481939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7052267558490301579951837 2644600334433863092481939)
            ·
              refine ⟨3966900501650794638722909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644600334433863092481939 3966900501650794638722909)
              ·
                refine ⟨1487587688119047989521091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3966900501650794638722909 1487587688119047989521091)
                ·
                  refine ⟨2231381532178571984281637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487587688119047989521091 2231381532178571984281637)
                  ·
                    refine ⟨418384037283482247052807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2231381532178571984281637 418384037283482247052807)
                    ·
                      rfl

theorem cell22_1222200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_1222200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222200 prefixEnd_1222200 := by exact prefixLift 1222200
  have htrace : WordTrace (prefixWord ++ tailWord_1222200) baseStart_1222200 baseEnd_1222200 := by
    simpa [prefixWord, tailWord_1222200, baseEnd_1222200] using wordTrace_append hprefix tailTrace_1222200
  have hstable : (prefixWord ++ tailWord_1222200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222200).length < 2 ^ (prefixWord ++ tailWord_1222200).sum := by decide
  have hdescent : baseEnd_1222200 < baseStart_1222200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222215 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 6]
def baseStart_1222215 : Nat := 118140960795 + 1222215 * 2 ^ 59
def prefixEnd_1222215 : Nat := 4983230072969 + 3 ^ 40 * 1222215 * 2
def baseEnd_1222215 : Nat := 139463057363342402642587

theorem tailTrace_1222215 : CollatzResearch.WordTrace tailWord_1222215 prefixEnd_1222215 139463057363342402642587 := by
  unfold tailWord_1222215
  simp only [CollatzResearch.WordTrace]
  refine ⟨44577843267131267548652099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29718562178087511699101399 44577843267131267548652099)
  ·
    refine ⟨66866764900696901322978149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44577843267131267548652099 66866764900696901322978149)
    ·
      refine ⟨12537518418880668998058403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66866764900696901322978149 12537518418880668998058403)
      ·
        refine ⟨18806277628321003497087605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12537518418880668998058403 18806277628321003497087605)
        ·
          refine ⟨1763088527655094077851963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18806277628321003497087605 1763088527655094077851963)
          ·
            refine ⟨2644632791482641116777945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763088527655094077851963 2644632791482641116777945)
            ·
              refine ⟨1983474593611980837583459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2644632791482641116777945 1983474593611980837583459)
              ·
                refine ⟨2975211890417971256375189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983474593611980837583459 2975211890417971256375189)
                ·
                  refine ⟨139463057363342402642587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2975211890417971256375189 139463057363342402642587)
                  ·
                    rfl

theorem cell22_1222215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 6].length) (baseStart_1222215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222215 prefixEnd_1222215 := by exact prefixLift 1222215
  have htrace : WordTrace (prefixWord ++ tailWord_1222215) baseStart_1222215 baseEnd_1222215 := by
    simpa [prefixWord, tailWord_1222215, baseEnd_1222215] using wordTrace_append hprefix tailTrace_1222215
  have hstable : (prefixWord ++ tailWord_1222215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222215).length < 2 ^ (prefixWord ++ tailWord_1222215).sum := by decide
  have hdescent : baseEnd_1222215 < baseStart_1222215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222228 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1222228 : Nat := 118140960795 + 1222228 * 2 ^ 59
def prefixEnd_1222228 : Nat := 4983230072969 + 3 ^ 40 * 1222228 * 2
def baseEnd_1222228 : Nat := 418393622255699507352721

theorem tailTrace_1222228 : CollatzResearch.WordTrace tailWord_1222228 prefixEnd_1222228 418393622255699507352721 := by
  unfold tailWord_1222228
  simp only [CollatzResearch.WordTrace]
  refine ⟨22289158708042085384437669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29718878277389447179250225 22289158708042085384437669)
  ·
    refine ⟨4179217257757891009582063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22289158708042085384437669 4179217257757891009582063)
    ·
      refine ⟨6268825886636836514373095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4179217257757891009582063 6268825886636836514373095)
      ·
        refine ⟨9403238829955254771559643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6268825886636836514373095 9403238829955254771559643)
        ·
          refine ⟨14104858244932882157339465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9403238829955254771559643 14104858244932882157339465)
          ·
            refine ⟨10578643683699661618004599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14104858244932882157339465 10578643683699661618004599)
            ·
              refine ⟨15867965525549492427006899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10578643683699661618004599 15867965525549492427006899)
              ·
                refine ⟨23801948288324238640510349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15867965525549492427006899 23801948288324238640510349)
                ·
                  refine ⟨8925730608121589490191381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23801948288324238640510349 8925730608121589490191381)
                  ·
                    refine ⟨418393622255699507352721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8925730608121589490191381 418393622255699507352721)
                    ·
                      rfl

theorem cell22_1222228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1222228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222228 prefixEnd_1222228 := by exact prefixLift 1222228
  have htrace : WordTrace (prefixWord ++ tailWord_1222228) baseStart_1222228 baseEnd_1222228 := by
    simpa [prefixWord, tailWord_1222228, baseEnd_1222228] using wordTrace_append hprefix tailTrace_1222228
  have hstable : (prefixWord ++ tailWord_1222228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222228).length < 2 ^ (prefixWord ++ tailWord_1222228).sum := by decide
  have hdescent : baseEnd_1222228 < baseStart_1222228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222243 : List Nat := [1, 1, 1, 5, 1, 4, 1, 8]
def baseStart_1222243 : Nat := 118140960795 + 1222243 * 2 ^ 59
def prefixEnd_1222243 : Nat := 4983230072969 + 3 ^ 40 * 1222243 * 2
def baseEnd_1222243 : Nat := 46488750784693829803075

theorem tailTrace_1222243 : CollatzResearch.WordTrace tailWord_1222243 prefixEnd_1222243 46488750784693829803075 := by
  unfold tailWord_1222243
  simp only [CollatzResearch.WordTrace]
  refine ⟨44578864511029828330671383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29719243007353218887114255 44578864511029828330671383)
  ·
    refine ⟨66868296766544742496007075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44578864511029828330671383 66868296766544742496007075)
    ·
      refine ⟨100302445149817113744010613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66868296766544742496007075 100302445149817113744010613)
      ·
        refine ⟨9403354232795354413500995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100302445149817113744010613 9403354232795354413500995)
        ·
          refine ⟨14105031349193031620251493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9403354232795354413500995 14105031349193031620251493)
          ·
            refine ⟨2644693377973693428797155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14105031349193031620251493 2644693377973693428797155)
            ·
              refine ⟨3967040066960540143195733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644693377973693428797155 3967040066960540143195733)
              ·
                refine ⟨46488750784693829803075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3967040066960540143195733 46488750784693829803075)
                ·
                  rfl

theorem cell22_1222243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 8].length) (baseStart_1222243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222243 prefixEnd_1222243 := by exact prefixLift 1222243
  have htrace : WordTrace (prefixWord ++ tailWord_1222243) baseStart_1222243 baseEnd_1222243 := by
    simpa [prefixWord, tailWord_1222243, baseEnd_1222243] using wordTrace_append hprefix tailTrace_1222243
  have hstable : (prefixWord ++ tailWord_1222243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222243).length < 2 ^ (prefixWord ++ tailWord_1222243).sum := by decide
  have hdescent : baseEnd_1222243 < baseStart_1222243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222262 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_1222262 : Nat := 118140960795 + 1222262 * 2 ^ 59
def prefixEnd_1222262 : Nat := 4983230072969 + 3 ^ 40 * 1222262 * 2
def baseEnd_1222262 : Nat := 418405261150534752002617

theorem tailTrace_1222262 : CollatzResearch.WordTrace tailWord_1222262 prefixEnd_1222262 418405261150534752002617 := by
  unfold tailWord_1222262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2786222343622562160975815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29719704998640663050408693 2786222343622562160975815)
  ·
    refine ⟨4179333515433843241463723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2786222343622562160975815 4179333515433843241463723)
    ·
      refine ⟨6269000273150764862195585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4179333515433843241463723 6269000273150764862195585)
      ·
        refine ⟨4701750204863073646646689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6269000273150764862195585 4701750204863073646646689)
        ·
          refine ⟨3526312653647305234985017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4701750204863073646646689 3526312653647305234985017)
          ·
            refine ⟨2644734490235478926238763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3526312653647305234985017 2644734490235478926238763)
            ·
              refine ⟨3967101735353218389358145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644734490235478926238763 3967101735353218389358145)
              ·
                refine ⟨2975326301514913792018609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3967101735353218389358145 2975326301514913792018609)
                ·
                  refine ⟨2231494726136185344013957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2975326301514913792018609 2231494726136185344013957)
                  ·
                    refine ⟨418405261150534752002617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2231494726136185344013957 418405261150534752002617)
                    ·
                      rfl

theorem cell22_1222262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_1222262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222262 prefixEnd_1222262 := by exact prefixLift 1222262
  have htrace : WordTrace (prefixWord ++ tailWord_1222262) baseStart_1222262 baseEnd_1222262 := by
    simpa [prefixWord, tailWord_1222262, baseEnd_1222262] using wordTrace_append hprefix tailTrace_1222262
  have hstable : (prefixWord ++ tailWord_1222262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222262).length < 2 ^ (prefixWord ++ tailWord_1222262).sum := by decide
  have hdescent : baseEnd_1222262 < baseStart_1222262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222350 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_1222350 : Nat := 118140960795 + 1222350 * 2 ^ 59
def prefixEnd_1222350 : Nat := 4983230072969 + 3 ^ 40 * 1222350 * 2
def baseEnd_1222350 : Nat := 139478461782977285267449

theorem tailTrace_1222350 : CollatzResearch.WordTrace tailWord_1222350 prefixEnd_1222350 139478461782977285267449 := by
  unfold tailWord_1222350
  simp only [CollatzResearch.WordTrace]
  refine ⟨5572845890205273200602063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29721844747761457069877669 5572845890205273200602063)
  ·
    refine ⟨8359268835307909800903095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5572845890205273200602063 8359268835307909800903095)
    ·
      refine ⟨12538903252961864701354643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8359268835307909800903095 12538903252961864701354643)
      ·
        refine ⟨18808354879442797052031965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12538903252961864701354643 18808354879442797052031965)
        ·
          refine ⟨7053133079791048894511987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18808354879442797052031965 7053133079791048894511987)
          ·
            refine ⟨10579699619686573341767981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7053133079791048894511987 10579699619686573341767981)
            ·
              refine ⟨3967387357382465003162993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10579699619686573341767981 3967387357382465003162993)
              ·
                refine ⟨2975540518036848752372245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3967387357382465003162993 2975540518036848752372245)
                ·
                  refine ⟨139478461782977285267449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2975540518036848752372245 139478461782977285267449)
                  ·
                    rfl

theorem cell22_1222350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_1222350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222350 prefixEnd_1222350 := by exact prefixLift 1222350
  have htrace : WordTrace (prefixWord ++ tailWord_1222350) baseStart_1222350 baseEnd_1222350 := by
    simpa [prefixWord, tailWord_1222350, baseEnd_1222350] using wordTrace_append hprefix tailTrace_1222350
  have hstable : (prefixWord ++ tailWord_1222350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222350).length < 2 ^ (prefixWord ++ tailWord_1222350).sum := by decide
  have hdescent : baseEnd_1222350 < baseStart_1222350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222367 : List Nat := [1, 1, 2, 3, 2, 2, 4, 3, 4]
def baseStart_1222367 : Nat := 118140960795 + 1222367 * 2 ^ 59
def prefixEnd_1222367 : Nat := 4983230072969 + 3 ^ 40 * 1222367 * 2
def baseEnd_1222367 : Nat := 139480401598783159375765

theorem tailTrace_1222367 : CollatzResearch.WordTrace tailWord_1222367 prefixEnd_1222367 139480401598783159375765 := by
  unfold tailWord_1222367
  simp only [CollatzResearch.WordTrace]
  refine ⟨44583387162580597508185355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29722258108387065005456903 44583387162580597508185355)
  ·
    refine ⟨66875080743870896262278033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44583387162580597508185355 66875080743870896262278033)
    ·
      refine ⟨50156310557903172196708525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66875080743870896262278033 50156310557903172196708525)
      ·
        refine ⟨18808616459213689573765697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50156310557903172196708525 18808616459213689573765697)
        ·
          refine ⟨14106462344410267180324273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18808616459213689573765697 14106462344410267180324273)
          ·
            refine ⟨10579846758307700385243205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14106462344410267180324273 10579846758307700385243205)
            ·
              refine ⟨1983721267182693822233101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10579846758307700385243205 1983721267182693822233101)
              ·
                refine ⟨743895475193510183337413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1983721267182693822233101 743895475193510183337413)
                ·
                  refine ⟨139480401598783159375765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 743895475193510183337413 139480401598783159375765)
                  ·
                    rfl

theorem cell22_1222367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 4].length) (baseStart_1222367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222367 prefixEnd_1222367 := by exact prefixLift 1222367
  have htrace : WordTrace (prefixWord ++ tailWord_1222367) baseStart_1222367 baseEnd_1222367 := by
    simpa [prefixWord, tailWord_1222367, baseEnd_1222367] using wordTrace_append hprefix tailTrace_1222367
  have hstable : (prefixWord ++ tailWord_1222367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222367).length < 2 ^ (prefixWord ++ tailWord_1222367).sum := by decide
  have hdescent : baseEnd_1222367 < baseStart_1222367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222380 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_1222380 : Nat := 118140960795 + 1222380 * 2 ^ 59
def prefixEnd_1222380 : Nat := 4983230072969 + 3 ^ 40 * 1222380 * 2
def baseEnd_1222380 : Nat := 418445654962021777552255

theorem tailTrace_1222380 : CollatzResearch.WordTrace tailWord_1222380 prefixEnd_1222380 418445654962021777552255 := by
  unfold tailWord_1222380
  simp only [CollatzResearch.WordTrace]
  refine ⟨22291930655766750364204297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29722574207689000485605729 22291930655766750364204297)
  ·
    refine ⟨16718947991825062773153223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22291930655766750364204297 16718947991825062773153223)
    ·
      refine ⟨25078421987737594159729835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16718947991825062773153223 25078421987737594159729835)
      ·
        refine ⟨37617632981606391239594753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25078421987737594159729835 37617632981606391239594753)
        ·
          refine ⟨28213224736204793429696065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37617632981606391239594753 28213224736204793429696065)
          ·
            refine ⟨21159918552153595072272049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28213224736204793429696065 21159918552153595072272049)
            ·
              refine ⟨15869938914115196304204037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21159918552153595072272049 15869938914115196304204037)
              ·
                refine ⟨2975613546396599307038257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15869938914115196304204037 2975613546396599307038257)
                ·
                  refine ⟨2231710159797449480278693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2975613546396599307038257 2231710159797449480278693)
                  ·
                    refine ⟨418445654962021777552255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2231710159797449480278693 418445654962021777552255)
                    ·
                      rfl

theorem cell22_1222380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_1222380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222380 prefixEnd_1222380 := by exact prefixLift 1222380
  have htrace : WordTrace (prefixWord ++ tailWord_1222380) baseStart_1222380 baseEnd_1222380 := by
    simpa [prefixWord, tailWord_1222380, baseEnd_1222380] using wordTrace_append hprefix tailTrace_1222380
  have hstable : (prefixWord ++ tailWord_1222380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222380).length < 2 ^ (prefixWord ++ tailWord_1222380).sum := by decide
  have hdescent : baseEnd_1222380 < baseStart_1222380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222382 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_1222382 : Nat := 118140960795 + 1222382 * 2 ^ 59
def prefixEnd_1222382 : Nat := 4983230072969 + 3 ^ 40 * 1222382 * 2
def baseEnd_1222382 : Nat := 418446339602894439002249

theorem tailTrace_1222382 : CollatzResearch.WordTrace tailWord_1222382 prefixEnd_1222382 418446339602894439002249 := by
  unfold tailWord_1222382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5572991782190781883747675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29722622838350836713320933 5572991782190781883747675)
  ·
    refine ⟨8359487673286172825621513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5572991782190781883747675 8359487673286172825621513)
    ·
      refine ⟨6269615754964629619216135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8359487673286172825621513 6269615754964629619216135)
      ·
        refine ⟨9404423632446944428824203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6269615754964629619216135 9404423632446944428824203)
        ·
          refine ⟨14106635448670416643236305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9404423632446944428824203 14106635448670416643236305)
          ·
            refine ⟨10579976586502812482427229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14106635448670416643236305 10579976586502812482427229)
            ·
              refine ⟨3967491219938554680910211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10579976586502812482427229 3967491219938554680910211)
              ·
                refine ⟨5951236829907832021365317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3967491219938554680910211 5951236829907832021365317)
                ·
                  refine ⟨1115856905607718504005997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5951236829907832021365317 1115856905607718504005997)
                  ·
                    refine ⟨418446339602894439002249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1115856905607718504005997 418446339602894439002249)
                    ·
                      rfl

theorem cell22_1222382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_1222382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222382 prefixEnd_1222382 := by exact prefixLift 1222382
  have htrace : WordTrace (prefixWord ++ tailWord_1222382) baseStart_1222382 baseEnd_1222382 := by
    simpa [prefixWord, tailWord_1222382, baseEnd_1222382] using wordTrace_append hprefix tailTrace_1222382
  have hstable : (prefixWord ++ tailWord_1222382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222382).length < 2 ^ (prefixWord ++ tailWord_1222382).sum := by decide
  have hdescent : baseEnd_1222382 < baseStart_1222382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222444 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 3, 3]
def baseStart_1222444 : Nat := 118140960795 + 1222444 * 2 ^ 59
def prefixEnd_1222444 : Nat := 4983230072969 + 3 ^ 40 * 1222444 * 2
def baseEnd_1222444 : Nat := 418467563469946943952059

theorem tailTrace_1222444 : CollatzResearch.WordTrace tailWord_1222444 prefixEnd_1222444 418467563469946943952059 := by
  unfold tailWord_1222444
  simp only [CollatzResearch.WordTrace]
  refine ⟨22293097791650819829369193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29724130388867759772492257 22293097791650819829369193)
  ·
    refine ⟨16719823343738114872026895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22293097791650819829369193 16719823343738114872026895)
    ·
      refine ⟨25079735015607172308040343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16719823343738114872026895 25079735015607172308040343)
      ·
        refine ⟨37619602523410758462060515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25079735015607172308040343 37619602523410758462060515)
        ·
          refine ⟨56429403785116137693090773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37619602523410758462060515 56429403785116137693090773)
          ·
            refine ⟨1322564151213659477181815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 56429403785116137693090773 1322564151213659477181815)
            ·
              refine ⟨1983846226820489215772723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322564151213659477181815 1983846226820489215772723)
              ·
                refine ⟨2975769340230733823659085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983846226820489215772723 2975769340230733823659085)
                ·
                  refine ⟨1115913502586525183872157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2975769340230733823659085 1115913502586525183872157)
                  ·
                    refine ⟨418467563469946943952059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1115913502586525183872157 418467563469946943952059)
                    ·
                      rfl

theorem cell22_1222444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_1222444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222444 prefixEnd_1222444 := by exact prefixLift 1222444
  have htrace : WordTrace (prefixWord ++ tailWord_1222444) baseStart_1222444 baseEnd_1222444 := by
    simpa [prefixWord, tailWord_1222444, baseEnd_1222444] using wordTrace_append hprefix tailTrace_1222444
  have hstable : (prefixWord ++ tailWord_1222444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222444).length < 2 ^ (prefixWord ++ tailWord_1222444).sum := by decide
  have hdescent : baseEnd_1222444 < baseStart_1222444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222515 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 1, 6]
def baseStart_1222515 : Nat := 118140960795 + 1222515 * 2 ^ 59
def prefixEnd_1222515 : Nat := 4983230072969 + 3 ^ 40 * 1222515 * 2
def baseEnd_1222515 : Nat := 418491868220926425426841

theorem tailTrace_1222515 : CollatzResearch.WordTrace tailWord_1222515 prefixEnd_1222515 418491868220926425426841 := by
  unfold tailWord_1222515
  simp only [CollatzResearch.WordTrace]
  refine ⟨44588785166044418784572999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29725856777362945856381999 44588785166044418784572999)
  ·
    refine ⟨66883177749066628176859499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44588785166044418784572999 66883177749066628176859499)
    ·
      refine ⟨100324766623599942265289249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66883177749066628176859499 100324766623599942265289249)
      ·
        refine ⟨75243574967699956698966937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100324766623599942265289249 75243574967699956698966937)
        ·
          refine ⟨56432681225774967524225203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75243574967699956698966937 56432681225774967524225203)
          ·
            refine ⟨84649021838662451286337805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56432681225774967524225203 84649021838662451286337805)
            ·
              refine ⟨31743383189498419232376677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84649021838662451286337805 31743383189498419232376677)
              ·
                refine ⟨5951884348030953606070627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31743383189498419232376677 5951884348030953606070627)
                ·
                  refine ⟨8927826522046430409105941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5951884348030953606070627 8927826522046430409105941)
                  ·
                    refine ⟨418491868220926425426841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8927826522046430409105941 418491868220926425426841)
                    ·
                      rfl

theorem cell22_1222515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 6].length) (baseStart_1222515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222515 prefixEnd_1222515 := by exact prefixLift 1222515
  have htrace : WordTrace (prefixWord ++ tailWord_1222515) baseStart_1222515 baseEnd_1222515 := by
    simpa [prefixWord, tailWord_1222515, baseEnd_1222515] using wordTrace_append hprefix tailTrace_1222515
  have hstable : (prefixWord ++ tailWord_1222515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222515).length < 2 ^ (prefixWord ++ tailWord_1222515).sum := by decide
  have hdescent : baseEnd_1222515 < baseStart_1222515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222536 : List Nat := [2, 1, 3, 3, 3, 1, 2, 3, 4]
def baseStart_1222536 : Nat := 118140960795 + 1222536 * 2 ^ 59
def prefixEnd_1222536 : Nat := 4983230072969 + 3 ^ 40 * 1222536 * 2
def baseEnd_1222536 : Nat := 139499685650029790217259

theorem tailTrace_1222536 : CollatzResearch.WordTrace tailWord_1222536 prefixEnd_1222536 139499685650029790217259 := by
  unfold tailWord_1222536
  simp only [CollatzResearch.WordTrace]
  refine ⟨22294775549484169685543731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29726367399312226247391641 22294775549484169685543731)
  ·
    refine ⟨33442163324226254528315597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22294775549484169685543731 33442163324226254528315597)
    ·
      refine ⟨12540811246584845448118349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33442163324226254528315597 12540811246584845448118349)
      ·
        refine ⟨4702804217469317043044381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12540811246584845448118349 4702804217469317043044381)
        ·
          refine ⟨1763551581550993891141643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4702804217469317043044381 1763551581550993891141643)
          ·
            refine ⟨2645327372326490836712465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763551581550993891141643 2645327372326490836712465)
            ·
              refine ⟨1983995529244868127534349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2645327372326490836712465 1983995529244868127534349)
              ·
                refine ⟨743998323466825547825381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1983995529244868127534349 743998323466825547825381)
                ·
                  refine ⟨139499685650029790217259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 743998323466825547825381 139499685650029790217259)
                  ·
                    rfl

theorem cell22_1222536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 4].length) (baseStart_1222536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222536 prefixEnd_1222536 := by exact prefixLift 1222536
  have htrace : WordTrace (prefixWord ++ tailWord_1222536) baseStart_1222536 baseEnd_1222536 := by
    simpa [prefixWord, tailWord_1222536, baseEnd_1222536] using wordTrace_append hprefix tailTrace_1222536
  have hstable : (prefixWord ++ tailWord_1222536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222536).length < 2 ^ (prefixWord ++ tailWord_1222536).sum := by decide
  have hdescent : baseEnd_1222536 < baseStart_1222536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222538 : List Nat := [3, 1, 2, 4, 2, 2, 2, 1, 1, 4]
def baseStart_1222538 : Nat := 118140960795 + 1222538 * 2 ^ 59
def prefixEnd_1222538 : Nat := 4983230072969 + 3 ^ 40 * 1222538 * 2
def baseEnd_1222538 : Nat := 418499741590962032101771

theorem tailTrace_1222538 : CollatzResearch.WordTrace tailWord_1222538 prefixEnd_1222538 418499741590962032101771 := by
  unfold tailWord_1222538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11147406011240273428165067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29726416029974062475106845 11147406011240273428165067)
  ·
    refine ⟨16721109016860410142247601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11147406011240273428165067 16721109016860410142247601)
    ·
      refine ⟨12540831762645307606685701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16721109016860410142247601 12540831762645307606685701)
      ·
        refine ⟨2351405955495995176253569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12540831762645307606685701 2351405955495995176253569)
        ·
          refine ⟨1763554466621996382190177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2351405955495995176253569 1763554466621996382190177)
          ·
            refine ⟨1322665849966497286642633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1763554466621996382190177 1322665849966497286642633)
            ·
              refine ⟨991999387474872964981975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1322665849966497286642633 991999387474872964981975)
              ·
                refine ⟨1487999081212309447472963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991999387474872964981975 1487999081212309447472963)
                ·
                  refine ⟨2231998621818464171209445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1487999081212309447472963 2231998621818464171209445)
                  ·
                    refine ⟨418499741590962032101771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2231998621818464171209445 418499741590962032101771)
                    ·
                      rfl

theorem cell22_1222538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_1222538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222538 prefixEnd_1222538 := by exact prefixLift 1222538
  have htrace : WordTrace (prefixWord ++ tailWord_1222538) baseStart_1222538 baseEnd_1222538 := by
    simpa [prefixWord, tailWord_1222538, baseEnd_1222538] using wordTrace_append hprefix tailTrace_1222538
  have hstable : (prefixWord ++ tailWord_1222538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222538).length < 2 ^ (prefixWord ++ tailWord_1222538).sum := by decide
  have hdescent : baseEnd_1222538 < baseStart_1222538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222551 : List Nat := [1, 1, 3, 3, 1, 5, 1, 2, 2, 3]
def baseStart_1222551 : Nat := 118140960795 + 1222551 * 2 ^ 59
def prefixEnd_1222551 : Nat := 4983230072969 + 3 ^ 40 * 1222551 * 2
def baseEnd_1222551 : Nat := 418504191756634331526731

theorem tailTrace_1222551 : CollatzResearch.WordTrace tailWord_1222551 prefixEnd_1222551 418504191756634331526731 := by
  unfold tailWord_1222551
  simp only [CollatzResearch.WordTrace]
  refine ⟨44590098193913996932883507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29726732129275997955255671 44590098193913996932883507)
  ·
    refine ⟨66885147290870995399325261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44590098193913996932883507 66885147290870995399325261)
    ·
      refine ⟨25081930234076623274746973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66885147290870995399325261 25081930234076623274746973)
      ·
        refine ⟨9405723837778733728030115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25081930234076623274746973 9405723837778733728030115)
        ·
          refine ⟨14108585756668100592045173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9405723837778733728030115 14108585756668100592045173)
          ·
            refine ⟨1322679914687634430504235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14108585756668100592045173 1322679914687634430504235)
            ·
              refine ⟨1984019872031451645756353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322679914687634430504235 1984019872031451645756353)
              ·
                refine ⟨1488014904023588734317265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1984019872031451645756353 1488014904023588734317265)
                ·
                  refine ⟨1116011178017691550737949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1488014904023588734317265 1116011178017691550737949)
                  ·
                    refine ⟨418504191756634331526731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1116011178017691550737949 418504191756634331526731)
                    ·
                      rfl

theorem cell22_1222551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_1222551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222551 prefixEnd_1222551 := by exact prefixLift 1222551
  have htrace : WordTrace (prefixWord ++ tailWord_1222551) baseStart_1222551 baseEnd_1222551 := by
    simpa [prefixWord, tailWord_1222551, baseEnd_1222551] using wordTrace_append hprefix tailTrace_1222551
  have hstable : (prefixWord ++ tailWord_1222551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222551).length < 2 ^ (prefixWord ++ tailWord_1222551).sum := by decide
  have hdescent : baseEnd_1222551 < baseStart_1222551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222568 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1222568 : Nat := 118140960795 + 1222568 * 2 ^ 59
def prefixEnd_1222568 : Nat := 4983230072969 + 3 ^ 40 * 1222568 * 2
def baseEnd_1222568 : Nat := 418510011204051953851679

theorem tailTrace_1222568 : CollatzResearch.WordTrace tailWord_1222568 prefixEnd_1222568 418510011204051953851679 := by
  unfold tailWord_1222568
  simp only [CollatzResearch.WordTrace]
  refine ⟨22295359117426204418126179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29727145489901605890834905 22295359117426204418126179)
  ·
    refine ⟨33443038676139306627189269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22295359117426204418126179 33443038676139306627189269)
    ·
      refine ⟨1567642437944029998149497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33443038676139306627189269 1567642437944029998149497)
      ·
        refine ⟨1175731828458022498612123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1567642437944029998149497 1175731828458022498612123)
        ·
          refine ⟨1763597742687033747918185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175731828458022498612123 1763597742687033747918185)
          ·
            refine ⟨1322698307015275310938639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1763597742687033747918185 1322698307015275310938639)
            ·
              refine ⟨1984047460522912966407959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322698307015275310938639 1984047460522912966407959)
              ·
                refine ⟨2976071190784369449611939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984047460522912966407959 2976071190784369449611939)
                ·
                  refine ⟨4464106786176554174417909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2976071190784369449611939 4464106786176554174417909)
                  ·
                    refine ⟨418510011204051953851679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4464106786176554174417909 418510011204051953851679)
                    ·
                      rfl

theorem cell22_1222568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1222568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222568 prefixEnd_1222568 := by exact prefixLift 1222568
  have htrace : WordTrace (prefixWord ++ tailWord_1222568) baseStart_1222568 baseEnd_1222568 := by
    simpa [prefixWord, tailWord_1222568, baseEnd_1222568] using wordTrace_append hprefix tailTrace_1222568
  have hstable : (prefixWord ++ tailWord_1222568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222568).length < 2 ^ (prefixWord ++ tailWord_1222568).sum := by decide
  have hdescent : baseEnd_1222568 < baseStart_1222568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222714 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 7, 3]
def baseStart_1222714 : Nat := 118140960795 + 1222714 * 2 ^ 59
def prefixEnd_1222714 : Nat := 4983230072969 + 3 ^ 40 * 1222714 * 2
def baseEnd_1222714 : Nat := 418559989987756239701231

theorem tailTrace_1222714 : CollatzResearch.WordTrace tailWord_1222714 prefixEnd_1222714 418559989987756239701231 := by
  unfold tailWord_1222714
  simp only [CollatzResearch.WordTrace]
  refine ⟨11149010823080868942766799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29730695528215650514044797 11149010823080868942766799)
  ·
    refine ⟨16723516234621303414150199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11149010823080868942766799 16723516234621303414150199)
    ·
      refine ⟨25085274351931955121225299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16723516234621303414150199 25085274351931955121225299)
      ·
        refine ⟨37627911527897932681837949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25085274351931955121225299 37627911527897932681837949)
        ·
          refine ⟨14110466822961724755689231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37627911527897932681837949 14110466822961724755689231)
          ·
            refine ⟨21165700234442587133533847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14110466822961724755689231 21165700234442587133533847)
            ·
              refine ⟨31748550351663880700300771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21165700234442587133533847 31748550351663880700300771)
              ·
                refine ⟨47622825527495821050451157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31748550351663880700300771 47622825527495821050451157)
                ·
                  refine ⟨1116159973300683305869949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 47622825527495821050451157 1116159973300683305869949)
                  ·
                    refine ⟨418559989987756239701231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1116159973300683305869949 418559989987756239701231)
                    ·
                      rfl

theorem cell22_1222714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_1222714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222714 prefixEnd_1222714 := by exact prefixLift 1222714
  have htrace : WordTrace (prefixWord ++ tailWord_1222714) baseStart_1222714 baseEnd_1222714 := by
    simpa [prefixWord, tailWord_1222714, baseEnd_1222714] using wordTrace_append hprefix tailTrace_1222714
  have hstable : (prefixWord ++ tailWord_1222714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222714).length < 2 ^ (prefixWord ++ tailWord_1222714).sum := by decide
  have hdescent : baseEnd_1222714 < baseStart_1222714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222870 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1222870 : Nat := 118140960795 + 1222870 * 2 ^ 59
def prefixEnd_1222870 : Nat := 4983230072969 + 3 ^ 40 * 1222870 * 2
def baseEnd_1222870 : Nat := 418613391975823832800753

theorem tailTrace_1222870 : CollatzResearch.WordTrace tailWord_1222870 prefixEnd_1222870 418613391975823832800753 := by
  unfold tailWord_1222870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2787608317484894650859129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29734488719838876275830709 2787608317484894650859129)
  ·
    refine ⟨2090706238113670988144347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2787608317484894650859129 2090706238113670988144347)
    ·
      refine ⟨3136059357170506482216521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2090706238113670988144347 3136059357170506482216521)
      ·
        refine ⟨2352044517877879861662391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3136059357170506482216521 2352044517877879861662391)
        ·
          refine ⟨3528066776816819792493587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2352044517877879861662391 3528066776816819792493587)
          ·
            refine ⟨5292100165225229688740381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528066776816819792493587 5292100165225229688740381)
            ·
              refine ⟨1984537561959461133277643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5292100165225229688740381 1984537561959461133277643)
              ·
                refine ⟨2976806342939191699916465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984537561959461133277643 2976806342939191699916465)
                ·
                  refine ⟨2232604757204393774937349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2976806342939191699916465 2232604757204393774937349)
                  ·
                    refine ⟨418613391975823832800753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2232604757204393774937349 418613391975823832800753)
                    ·
                      rfl

theorem cell22_1222870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1222870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222870 prefixEnd_1222870 := by exact prefixLift 1222870
  have htrace : WordTrace (prefixWord ++ tailWord_1222870) baseStart_1222870 baseEnd_1222870 := by
    simpa [prefixWord, tailWord_1222870, baseEnd_1222870] using wordTrace_append hprefix tailTrace_1222870
  have hstable : (prefixWord ++ tailWord_1222870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222870).length < 2 ^ (prefixWord ++ tailWord_1222870).sum := by decide
  have hdescent : baseEnd_1222870 < baseStart_1222870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222879 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 7]
def baseStart_1222879 : Nat := 118140960795 + 1222879 * 2 ^ 59
def prefixEnd_1222879 : Nat := 4983230072969 + 3 ^ 40 * 1222879 * 2
def baseEnd_1222879 : Nat := 139538824286583603108575

theorem tailTrace_1222879 : CollatzResearch.WordTrace tailWord_1222879 prefixEnd_1222879 139538824286583603108575 := by
  unfold tailWord_1222879
  simp only [CollatzResearch.WordTrace]
  refine ⟨44602061336725708950823691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29734707557817139300549127 44602061336725708950823691)
  ·
    refine ⟨66903092005088563426235537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44602061336725708950823691 66903092005088563426235537)
    ·
      refine ⟨50177319003816422569676653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66903092005088563426235537 50177319003816422569676653)
      ·
        refine ⟨18816494626431158463628745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50177319003816422569676653 18816494626431158463628745)
        ·
          refine ⟨14112370969823368847721559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18816494626431158463628745 14112370969823368847721559)
          ·
            refine ⟨21168556454735053271582339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14112370969823368847721559 21168556454735053271582339)
            ·
              refine ⟨31752834682102579907373509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21168556454735053271582339 31752834682102579907373509)
              ·
                refine ⟨5953656502894233732632533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31752834682102579907373509 5953656502894233732632533)
                ·
                  refine ⟨139538824286583603108575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5953656502894233732632533 139538824286583603108575)
                  ·
                    rfl

theorem cell22_1222879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 7].length) (baseStart_1222879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222879 prefixEnd_1222879 := by exact prefixLift 1222879
  have htrace : WordTrace (prefixWord ++ tailWord_1222879) baseStart_1222879 baseEnd_1222879 := by
    simpa [prefixWord, tailWord_1222879, baseEnd_1222879] using wordTrace_append hprefix tailTrace_1222879
  have hstable : (prefixWord ++ tailWord_1222879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222879).length < 2 ^ (prefixWord ++ tailWord_1222879).sum := by decide
  have hdescent : baseEnd_1222879 < baseStart_1222879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222913 : List Nat := [1, 2, 4, 1, 1, 2, 5, 1, 5]
def baseStart_1222913 : Nat := 118140960795 + 1222913 * 2 ^ 59
def prefixEnd_1222913 : Nat := 4983230072969 + 3 ^ 40 * 1222913 * 2
def baseEnd_1222913 : Nat := 139542703918195351325207

theorem tailTrace_1222913 : CollatzResearch.WordTrace tailWord_1222913 prefixEnd_1222913 139542703918195351325207 := by
  unfold tailWord_1222913
  simp only [CollatzResearch.WordTrace]
  refine ⟨44603301418602532757561393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29735534279068355171707595 44603301418602532757561393)
  ·
    refine ⟨33452476063951899568171045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44603301418602532757561393 33452476063951899568171045)
    ·
      refine ⟨6272339261990981169032071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33452476063951899568171045 6272339261990981169032071)
      ·
        refine ⟨9408508892986471753548107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6272339261990981169032071 9408508892986471753548107)
        ·
          refine ⟨14112763339479707630322161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9408508892986471753548107 14112763339479707630322161)
          ·
            refine ⟨10584572504609780722741621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14112763339479707630322161 10584572504609780722741621)
            ·
              refine ⟨992303672307166942757027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10584572504609780722741621 992303672307166942757027)
              ·
                refine ⟨1488455508460750414135541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992303672307166942757027 1488455508460750414135541)
                ·
                  refine ⟨139542703918195351325207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1488455508460750414135541 139542703918195351325207)
                  ·
                    rfl

theorem cell22_1222913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 5].length) (baseStart_1222913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222913 prefixEnd_1222913 := by exact prefixLift 1222913
  have htrace : WordTrace (prefixWord ++ tailWord_1222913) baseStart_1222913 baseEnd_1222913 := by
    simpa [prefixWord, tailWord_1222913, baseEnd_1222913] using wordTrace_append hprefix tailTrace_1222913
  have hstable : (prefixWord ++ tailWord_1222913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222913).length < 2 ^ (prefixWord ++ tailWord_1222913).sum := by decide
  have hdescent : baseEnd_1222913 < baseStart_1222913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222943 : List Nat := [1, 1, 2, 4, 3, 1, 2, 3, 1, 4]
def baseStart_1222943 : Nat := 118140960795 + 1222943 * 2 ^ 59
def prefixEnd_1222943 : Nat := 4983230072969 + 3 ^ 40 * 1222943 * 2
def baseEnd_1222943 : Nat := 418638381367675975725529

theorem tailTrace_1222943 : CollatzResearch.WordTrace tailWord_1222943 prefixEnd_1222943 418638381367675975725529 := by
  unfold tailWord_1222943
  simp only [CollatzResearch.WordTrace]
  refine ⟨44604395608493847881153483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29736263738995898587435655 44604395608493847881153483)
  ·
    refine ⟨66906593412740771821730225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44604395608493847881153483 66906593412740771821730225)
    ·
      refine ⟨50179945059555578866297669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66906593412740771821730225 50179945059555578866297669)
      ·
        refine ⟨9408739698666671037430813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50179945059555578866297669 9408739698666671037430813)
        ·
          refine ⟨3528277387000001639036555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9408739698666671037430813 3528277387000001639036555)
          ·
            refine ⟨5292416080500002458554833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528277387000001639036555 5292416080500002458554833)
            ·
              refine ⟨3969312060375001843916125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5292416080500002458554833 3969312060375001843916125)
              ·
                refine ⟨1488492022640625691468547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3969312060375001843916125 1488492022640625691468547)
                ·
                  refine ⟨2232738033960938537202821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488492022640625691468547 2232738033960938537202821)
                  ·
                    refine ⟨418638381367675975725529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2232738033960938537202821 418638381367675975725529)
                    ·
                      rfl

theorem cell22_1222943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_1222943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222943 prefixEnd_1222943 := by exact prefixLift 1222943
  have htrace : WordTrace (prefixWord ++ tailWord_1222943) baseStart_1222943 baseEnd_1222943 := by
    simpa [prefixWord, tailWord_1222943, baseEnd_1222943] using wordTrace_append hprefix tailTrace_1222943
  have hstable : (prefixWord ++ tailWord_1222943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222943).length < 2 ^ (prefixWord ++ tailWord_1222943).sum := by decide
  have hdescent : baseEnd_1222943 < baseStart_1222943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222951 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1222951 : Nat := 118140960795 + 1222951 * 2 ^ 59
def prefixEnd_1222951 : Nat := 4983230072969 + 3 ^ 40 * 1222951 * 2
def baseEnd_1222951 : Nat := 418641119931166621525505

theorem tailTrace_1222951 : CollatzResearch.WordTrace tailWord_1222951 prefixEnd_1222951 418641119931166621525505 := by
  unfold tailWord_1222951
  simp only [CollatzResearch.WordTrace]
  refine ⟨44604687392464865247444707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29736458261643243498296471 44604687392464865247444707)
  ·
    refine ⟨66907031088697297871167061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44604687392464865247444707 66907031088697297871167061)
    ·
      refine ⟨784066770570671459427739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 66907031088697297871167061 784066770570671459427739)
      ·
        refine ⟨1176100155856007189141609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784066770570671459427739 1176100155856007189141609)
        ·
          refine ⟨882075116892005391856207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1176100155856007189141609 882075116892005391856207)
          ·
            refine ⟨1323112675338008087784311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882075116892005391856207 1323112675338008087784311)
            ·
              refine ⟨1984669013007012131676467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323112675338008087784311 1984669013007012131676467)
              ·
                refine ⟨2977003519510518197514701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984669013007012131676467 2977003519510518197514701)
                ·
                  refine ⟨1116376319816444324068013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2977003519510518197514701 1116376319816444324068013)
                  ·
                    refine ⟨418641119931166621525505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1116376319816444324068013 418641119931166621525505)
                    ·
                      rfl

theorem cell22_1222951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1222951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222951 prefixEnd_1222951 := by exact prefixLift 1222951
  have htrace : WordTrace (prefixWord ++ tailWord_1222951) baseStart_1222951 baseEnd_1222951 := by
    simpa [prefixWord, tailWord_1222951, baseEnd_1222951] using wordTrace_append hprefix tailTrace_1222951
  have hstable : (prefixWord ++ tailWord_1222951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222951).length < 2 ^ (prefixWord ++ tailWord_1222951).sum := by decide
  have hdescent : baseEnd_1222951 < baseStart_1222951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222977 : List Nat := [1, 2, 5, 2, 2, 2, 1, 2, 1, 4]
def baseStart_1222977 : Nat := 118140960795 + 1222977 * 2 ^ 59
def prefixEnd_1222977 : Nat := 4983230072969 + 3 ^ 40 * 1222977 * 2
def baseEnd_1222977 : Nat := 418650020262511220375425

theorem tailTrace_1222977 : CollatzResearch.WordTrace tailWord_1222977 prefixEnd_1222977 418650020262511220375425 := by
  unfold tailWord_1222977
  simp only [CollatzResearch.WordTrace]
  refine ⟨44605635690370671687891185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29737090460247114458594123 44605635690370671687891185)
  ·
    refine ⟨33454226767778003765918389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44605635690370671687891185 33454226767778003765918389)
    ·
      refine ⟨3136333759479187853054849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33454226767778003765918389 3136333759479187853054849)
      ·
        refine ⟨2352250319609390889791137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3136333759479187853054849 2352250319609390889791137)
        ·
          refine ⟨1764187739707043167343353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2352250319609390889791137 1764187739707043167343353)
          ·
            refine ⟨1323140804780282375507515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1764187739707043167343353 1323140804780282375507515)
            ·
              refine ⟨1984711207170423563261273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323140804780282375507515 1984711207170423563261273)
              ·
                refine ⟨1488533405377817672445955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1984711207170423563261273 1488533405377817672445955)
                ·
                  refine ⟨2232800108066726508668933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488533405377817672445955 2232800108066726508668933)
                  ·
                    refine ⟨418650020262511220375425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2232800108066726508668933 418650020262511220375425)
                    ·
                      rfl

theorem cell22_1222977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_1222977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222977 prefixEnd_1222977 := by exact prefixLift 1222977
  have htrace : WordTrace (prefixWord ++ tailWord_1222977) baseStart_1222977 baseEnd_1222977 := by
    simpa [prefixWord, tailWord_1222977, baseEnd_1222977] using wordTrace_append hprefix tailTrace_1222977
  have hstable : (prefixWord ++ tailWord_1222977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222977).length < 2 ^ (prefixWord ++ tailWord_1222977).sum := by decide
  have hdescent : baseEnd_1222977 < baseStart_1222977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222988 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 2, 4]
def baseStart_1222988 : Nat := 118140960795 + 1222988 * 2 ^ 59
def prefixEnd_1222988 : Nat := 4983230072969 + 3 ^ 40 * 1222988 * 2
def baseEnd_1222988 : Nat := 418653785787310858350391

theorem tailTrace_1222988 : CollatzResearch.WordTrace tailWord_1222988 prefixEnd_1222988 418653785787310858350391 := by
  unfold tailWord_1222988
  simp only [CollatzResearch.WordTrace]
  refine ⟨22303018446665410283270809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29737357928887213711027745 22303018446665410283270809)
  ·
    refine ⟨16727263834999057712453107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22303018446665410283270809 16727263834999057712453107)
    ·
      refine ⟨25090895752498586568679661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16727263834999057712453107 25090895752498586568679661)
      ·
        refine ⟨9409085907186969963254873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25090895752498586568679661 9409085907186969963254873)
        ·
          refine ⟨7056814430390227472441155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9409085907186969963254873 7056814430390227472441155)
          ·
            refine ⟨10585221645585341208661733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7056814430390227472441155 10585221645585341208661733)
            ·
              refine ⟨1984729058547251476624075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10585221645585341208661733 1984729058547251476624075)
              ·
                refine ⟨2977093587820877214936113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984729058547251476624075 2977093587820877214936113)
                ·
                  refine ⟨2232820190865657911202085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2977093587820877214936113 2232820190865657911202085)
                  ·
                    refine ⟨418653785787310858350391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2232820190865657911202085 418653785787310858350391)
                    ·
                      rfl

theorem cell22_1222988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_1222988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1222988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1222988 prefixEnd_1222988 := by exact prefixLift 1222988
  have htrace : WordTrace (prefixWord ++ tailWord_1222988) baseStart_1222988 baseEnd_1222988 := by
    simpa [prefixWord, tailWord_1222988, baseEnd_1222988] using wordTrace_append hprefix tailTrace_1222988
  have hstable : (prefixWord ++ tailWord_1222988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222988).length < 2 ^ (prefixWord ++ tailWord_1222988).sum := by decide
  have hdescent : baseEnd_1222988 < baseStart_1222988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223020 : List Nat := [2, 2, 1, 1, 7, 1, 1, 7]
def baseStart_1223020 : Nat := 118140960795 + 1223020 * 2 ^ 59
def prefixEnd_1223020 : Nat := 4983230072969 + 3 ^ 40 * 1223020 * 2
def baseEnd_1223020 : Nat := 46518304449030382394477

theorem tailTrace_1223020 : CollatzResearch.WordTrace tailWord_1223020 prefixEnd_1223020 46518304449030382394477 := by
  unfold tailWord_1223020
  simp only [CollatzResearch.WordTrace]
  refine ⟨22303602014607445015853257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29738136019476593354471009 22303602014607445015853257)
  ·
    refine ⟨16727701510955583761889943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22303602014607445015853257 16727701510955583761889943)
    ·
      refine ⟨25091552266433375642834915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16727701510955583761889943 25091552266433375642834915)
      ·
        refine ⟨37637328399650063464252373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25091552266433375642834915 37637328399650063464252373)
        ·
          refine ⟨882124884366798362443415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 37637328399650063464252373 882124884366798362443415)
          ·
            refine ⟨1323187326550197543665123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882124884366798362443415 1323187326550197543665123)
            ·
              refine ⟨1984780989825296315497685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323187326550197543665123 1984780989825296315497685)
              ·
                refine ⟨46518304449030382394477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1984780989825296315497685 46518304449030382394477)
                ·
                  rfl

theorem cell22_1223020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 7].length) (baseStart_1223020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223020 prefixEnd_1223020 := by exact prefixLift 1223020
  have htrace : WordTrace (prefixWord ++ tailWord_1223020) baseStart_1223020 baseEnd_1223020 := by
    simpa [prefixWord, tailWord_1223020, baseEnd_1223020] using wordTrace_append hprefix tailTrace_1223020
  have hstable : (prefixWord ++ tailWord_1223020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223020).length < 2 ^ (prefixWord ++ tailWord_1223020).sum := by decide
  have hdescent : baseEnd_1223020 < baseStart_1223020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223052 : List Nat := [2, 2, 1, 2, 1, 5, 2, 3, 1, 3]
def baseStart_1223052 : Nat := 118140960795 + 1223052 * 2 ^ 59
def prefixEnd_1223052 : Nat := 4983230072969 + 3 ^ 40 * 1223052 * 2
def baseEnd_1223052 : Nat := 418675694295236024750195

theorem tailTrace_1223052 : CollatzResearch.WordTrace tailWord_1223052 prefixEnd_1223052 418675694295236024750195 := by
  unfold tailWord_1223052
  simp only [CollatzResearch.WordTrace]
  refine ⟨22304185582549479748435705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29738914110065972997914273 22304185582549479748435705)
  ·
    refine ⟨16728139186912109811326779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22304185582549479748435705 16728139186912109811326779)
    ·
      refine ⟨25092208780368164716990169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16728139186912109811326779 25092208780368164716990169)
      ·
        refine ⟨18819156585276123537742627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25092208780368164716990169 18819156585276123537742627)
        ·
          refine ⟨28228734877914185306613941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18819156585276123537742627 28228734877914185306613941)
          ·
            refine ⟨2646443894804454872495057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28228734877914185306613941 2646443894804454872495057)
            ·
              refine ⟨1984832921103341154371293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2646443894804454872495057 1984832921103341154371293)
              ·
                refine ⟨744312345413752932889235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1984832921103341154371293 744312345413752932889235)
                ·
                  refine ⟨1116468518120629399333853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744312345413752932889235 1116468518120629399333853)
                  ·
                    refine ⟨418675694295236024750195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1116468518120629399333853 418675694295236024750195)
                    ·
                      rfl

theorem cell22_1223052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_1223052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223052 prefixEnd_1223052 := by exact prefixLift 1223052
  have htrace : WordTrace (prefixWord ++ tailWord_1223052) baseStart_1223052 baseEnd_1223052 := by
    simpa [prefixWord, tailWord_1223052, baseEnd_1223052] using wordTrace_append hprefix tailTrace_1223052
  have hstable : (prefixWord ++ tailWord_1223052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223052).length < 2 ^ (prefixWord ++ tailWord_1223052).sum := by decide
  have hdescent : baseEnd_1223052 < baseStart_1223052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223080 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1223080 : Nat := 118140960795 + 1223080 * 2 ^ 59
def prefixEnd_1223080 : Nat := 4983230072969 + 3 ^ 40 * 1223080 * 2
def baseEnd_1223080 : Nat := 418685279267453285050109

theorem tailTrace_1223080 : CollatzResearch.WordTrace tailWord_1223080 prefixEnd_1223080 418685279267453285050109 := by
  unfold tailWord_1223080
  simp only [CollatzResearch.WordTrace]
  refine ⟨22304696204498760139445347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29739594939331680185927129 22304696204498760139445347)
  ·
    refine ⟨33457044306748140209168021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22304696204498760139445347 33457044306748140209168021)
    ·
      refine ⟨1568298951878819072304751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33457044306748140209168021 1568298951878819072304751)
      ·
        refine ⟨2352448427818228608457127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1568298951878819072304751 2352448427818228608457127)
        ·
          refine ⟨3528672641727342912685691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2352448427818228608457127 3528672641727342912685691)
          ·
            refine ⟨5293008962591014369028537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528672641727342912685691 5293008962591014369028537)
            ·
              refine ⟨3969756721943260776771403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5293008962591014369028537 3969756721943260776771403)
              ·
                refine ⟨5954635082914891165157105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3969756721943260776771403 5954635082914891165157105)
                ·
                  refine ⟨4465976312186168373867829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5954635082914891165157105 4465976312186168373867829)
                  ·
                    refine ⟨418685279267453285050109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4465976312186168373867829 418685279267453285050109)
                    ·
                      rfl

theorem cell22_1223080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1223080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223080 prefixEnd_1223080 := by exact prefixLift 1223080
  have htrace : WordTrace (prefixWord ++ tailWord_1223080) baseStart_1223080 baseEnd_1223080 := by
    simpa [prefixWord, tailWord_1223080, baseEnd_1223080] using wordTrace_append hprefix tailTrace_1223080
  have hstable : (prefixWord ++ tailWord_1223080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223080).length < 2 ^ (prefixWord ++ tailWord_1223080).sum := by decide
  have hdescent : baseEnd_1223080 < baseStart_1223080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223095 : List Nat := [1, 1, 3, 1, 3, 4, 2, 2, 1, 4]
def baseStart_1223095 : Nat := 118140960795 + 1223095 * 2 ^ 59
def prefixEnd_1223095 : Nat := 4983230072969 + 3 ^ 40 * 1223095 * 2
def baseEnd_1223095 : Nat := 418690414073998245925063

theorem tailTrace_1223095 : CollatzResearch.WordTrace tailWord_1223095 prefixEnd_1223095 418690414073998245925063 := by
  unfold tailWord_1223095
  simp only [CollatzResearch.WordTrace]
  refine ⟨44609939503943177840686739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29739959669295451893791159 44609939503943177840686739)
  ·
    refine ⟨66914909255914766761030109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44609939503943177840686739 66914909255914766761030109)
    ·
      refine ⟨25093090970968037535386291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66914909255914766761030109 25093090970968037535386291)
      ·
        refine ⟨37639636456452056303079437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25093090970968037535386291 37639636456452056303079437)
        ·
          refine ⟨14114863671169521113654789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37639636456452056303079437 14114863671169521113654789)
          ·
            refine ⟨2646536938344285208810273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14114863671169521113654789 2646536938344285208810273)
            ·
              refine ⟨1984902703758213906607705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2646536938344285208810273 1984902703758213906607705)
              ·
                refine ⟨1488677027818660429955779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1984902703758213906607705 1488677027818660429955779)
                ·
                  refine ⟨2233015541727990644933669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1488677027818660429955779 2233015541727990644933669)
                  ·
                    refine ⟨418690414073998245925063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2233015541727990644933669 418690414073998245925063)
                    ·
                      rfl

theorem cell22_1223095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_1223095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223095 prefixEnd_1223095 := by exact prefixLift 1223095
  have htrace : WordTrace (prefixWord ++ tailWord_1223095) baseStart_1223095 baseEnd_1223095 := by
    simpa [prefixWord, tailWord_1223095, baseEnd_1223095] using wordTrace_append hprefix tailTrace_1223095
  have hstable : (prefixWord ++ tailWord_1223095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223095).length < 2 ^ (prefixWord ++ tailWord_1223095).sum := by decide
  have hdescent : baseEnd_1223095 < baseStart_1223095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223125 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 4, 3]
def baseStart_1223125 : Nat := 118140960795 + 1223125 * 2 ^ 59
def prefixEnd_1223125 : Nat := 4983230072969 + 3 ^ 40 * 1223125 * 2
def baseEnd_1223125 : Nat := 418700683687088167674971

theorem tailTrace_1223125 : CollatzResearch.WordTrace tailWord_1223125 prefixEnd_1223125 418700683687088167674971 := by
  unfold tailWord_1223125
  simp only [CollatzResearch.WordTrace]
  refine ⟨44611033693834492964278829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29740689129222995309519219 44611033693834492964278829)
  ·
    refine ⟨16729137635187934861604561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44611033693834492964278829 16729137635187934861604561)
    ·
      refine ⟨12546853226390951146203421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16729137635187934861604561 12546853226390951146203421)
      ·
        refine ⟨4705069959896606679826283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12546853226390951146203421 4705069959896606679826283)
        ·
          refine ⟨7057604939844910019739425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4705069959896606679826283 7057604939844910019739425)
          ·
            refine ⟨5293203704883682514804569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7057604939844910019739425 5293203704883682514804569)
            ·
              refine ⟨3969902778662761886103427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5293203704883682514804569 3969902778662761886103427)
              ·
                refine ⟨5954854167994142829155141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3969902778662761886103427 5954854167994142829155141)
                ·
                  refine ⟨1116535156498901780466589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5954854167994142829155141 1116535156498901780466589)
                  ·
                    refine ⟨418700683687088167674971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1116535156498901780466589 418700683687088167674971)
                    ·
                      rfl

theorem cell22_1223125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_1223125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223125 prefixEnd_1223125 := by exact prefixLift 1223125
  have htrace : WordTrace (prefixWord ++ tailWord_1223125) baseStart_1223125 baseEnd_1223125 := by
    simpa [prefixWord, tailWord_1223125, baseEnd_1223125] using wordTrace_append hprefix tailTrace_1223125
  have hstable : (prefixWord ++ tailWord_1223125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223125).length < 2 ^ (prefixWord ++ tailWord_1223125).sum := by decide
  have hdescent : baseEnd_1223125 < baseStart_1223125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223183 : List Nat := [1, 1, 2, 1, 1, 1, 2, 8, 5]
def baseStart_1223183 : Nat := 118140960795 + 1223183 * 2 ^ 59
def prefixEnd_1223183 : Nat := 4983230072969 + 3 ^ 40 * 1223183 * 2
def baseEnd_1223183 : Nat := 139573512757465116574931

theorem tailTrace_1223183 : CollatzResearch.WordTrace tailWord_1223183 prefixEnd_1223183 139573512757465116574931 := by
  unfold tailWord_1223183
  simp only [CollatzResearch.WordTrace]
  refine ⟨44613149127624368869890203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29742099418416245913260135 44613149127624368869890203)
  ·
    refine ⟨66919723691436553304835305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44613149127624368869890203 66919723691436553304835305)
    ·
      refine ⟨50189792768577414978626479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66919723691436553304835305 50189792768577414978626479)
      ·
        refine ⟨75284689152866122467939719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50189792768577414978626479 75284689152866122467939719)
        ·
          refine ⟨112927033729299183701909579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75284689152866122467939719 112927033729299183701909579)
          ·
            refine ⟨169390550593948775552864369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112927033729299183701909579 169390550593948775552864369)
            ·
              refine ⟨127042912945461581664648277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169390550593948775552864369 127042912945461581664648277)
              ·
                refine ⟨1488784136079627910132597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 127042912945461581664648277 1488784136079627910132597)
                ·
                  refine ⟨139573512757465116574931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1488784136079627910132597 139573512757465116574931)
                  ·
                    rfl

theorem cell22_1223183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 5].length) (baseStart_1223183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223183 prefixEnd_1223183 := by exact prefixLift 1223183
  have htrace : WordTrace (prefixWord ++ tailWord_1223183) baseStart_1223183 baseEnd_1223183 := by
    simpa [prefixWord, tailWord_1223183, baseEnd_1223183] using wordTrace_append hprefix tailTrace_1223183
  have hstable : (prefixWord ++ tailWord_1223183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223183).length < 2 ^ (prefixWord ++ tailWord_1223183).sum := by decide
  have hdescent : baseEnd_1223183 < baseStart_1223183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223187 : List Nat := [1, 1, 1, 2, 1, 5, 3, 4, 1, 3]
def baseStart_1223187 : Nat := 118140960795 + 1223187 * 2 ^ 59
def prefixEnd_1223187 : Nat := 4983230072969 + 3 ^ 40 * 1223187 * 2
def baseEnd_1223187 : Nat := 418721907554140672624781

theorem tailTrace_1223187 : CollatzResearch.WordTrace tailWord_1223187 prefixEnd_1223187 418721907554140672624781 := by
  unfold tailWord_1223187
  simp only [CollatzResearch.WordTrace]
  refine ⟨44613295019609877553035815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29742196679739918368690543 44613295019609877553035815)
  ·
    refine ⟨66919942529414816329553723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44613295019609877553035815 66919942529414816329553723)
    ·
      refine ⟨100379913794122224494330585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66919942529414816329553723 100379913794122224494330585)
      ·
        refine ⟨75284935345591668370747939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100379913794122224494330585 75284935345591668370747939)
        ·
          refine ⟨112927403018387502556121909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75284935345591668370747939 112927403018387502556121909)
          ·
            refine ⟨10586944032973828364636429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112927403018387502556121909 10586944032973828364636429)
            ·
              refine ⟨3970104012365185636738661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10586944032973828364636429 3970104012365185636738661)
              ·
                refine ⟨744394502318472306888499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3970104012365185636738661 744394502318472306888499)
                ·
                  refine ⟨1116591753477708460332749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744394502318472306888499 1116591753477708460332749)
                  ·
                    refine ⟨418721907554140672624781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1116591753477708460332749 418721907554140672624781)
                    ·
                      rfl

theorem cell22_1223187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 1, 3].length) (baseStart_1223187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223187 prefixEnd_1223187 := by exact prefixLift 1223187
  have htrace : WordTrace (prefixWord ++ tailWord_1223187) baseStart_1223187 baseEnd_1223187 := by
    simpa [prefixWord, tailWord_1223187, baseEnd_1223187] using wordTrace_append hprefix tailTrace_1223187
  have hstable : (prefixWord ++ tailWord_1223187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223187).length < 2 ^ (prefixWord ++ tailWord_1223187).sum := by decide
  have hdescent : baseEnd_1223187 < baseStart_1223187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223204 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_1223204 : Nat := 118140960795 + 1223204 * 2 ^ 59
def prefixEnd_1223204 : Nat := 4983230072969 + 3 ^ 40 * 1223204 * 2
def baseEnd_1223204 : Nat := 418727727001558294949729

theorem tailTrace_1223204 : CollatzResearch.WordTrace tailWord_1223204 prefixEnd_1223204 418727727001558294949729 := by
  unfold tailWord_1223204
  simp only [CollatzResearch.WordTrace]
  refine ⟨22306957530274144728202333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29742610040365526304269777 22306957530274144728202333)
  ·
    refine ⟨8365109073852804273075875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22306957530274144728202333 8365109073852804273075875)
    ·
      refine ⟨12547663610779206409613813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8365109073852804273075875 12547663610779206409613813)
      ·
        refine ⟨1176343463510550600901295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12547663610779206409613813 1176343463510550600901295)
        ·
          refine ⟨1764515195265825901351943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1176343463510550600901295 1764515195265825901351943)
          ·
            refine ⟨2646772792898738852027915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764515195265825901351943 2646772792898738852027915)
            ·
              refine ⟨3970159189348108278041873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2646772792898738852027915 3970159189348108278041873)
              ·
                refine ⟨2977619392011081208531405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3970159189348108278041873 2977619392011081208531405)
                ·
                  refine ⟨1116607272004155453199277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2977619392011081208531405 1116607272004155453199277)
                  ·
                    refine ⟨418727727001558294949729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1116607272004155453199277 418727727001558294949729)
                    ·
                      rfl

theorem cell22_1223204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_1223204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223204 prefixEnd_1223204 := by exact prefixLift 1223204
  have htrace : WordTrace (prefixWord ++ tailWord_1223204) baseStart_1223204 baseEnd_1223204 := by
    simpa [prefixWord, tailWord_1223204, baseEnd_1223204] using wordTrace_append hprefix tailTrace_1223204
  have hstable : (prefixWord ++ tailWord_1223204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223204).length < 2 ^ (prefixWord ++ tailWord_1223204).sum := by decide
  have hdescent : baseEnd_1223204 < baseStart_1223204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223243 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 3, 5]
def baseStart_1223243 : Nat := 118140960795 + 1223243 * 2 ^ 59
def prefixEnd_1223243 : Nat := 4983230072969 + 3 ^ 40 * 1223243 * 2
def baseEnd_1223243 : Nat := 418741077498575193224609

theorem tailTrace_1223243 : CollatzResearch.WordTrace tailWord_1223243 prefixEnd_1223243 418741077498575193224609 := by
  unfold tailWord_1223243
  simp only [CollatzResearch.WordTrace]
  refine ⟨44615337507406999117074383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29743558338271332744716255 44615337507406999117074383)
  ·
    refine ⟨66923006261110498675611575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44615337507406999117074383 66923006261110498675611575)
    ·
      refine ⟨100384509391665748013417363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66923006261110498675611575 100384509391665748013417363)
      ·
        refine ⟨150576764087498622020126045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100384509391665748013417363 150576764087498622020126045)
        ·
          refine ⟨56466286532811983257547267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150576764087498622020126045 56466286532811983257547267)
          ·
            refine ⟨84699429799217974886320901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56466286532811983257547267 84699429799217974886320901)
            ·
              refine ⟨15881143087353370291185169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84699429799217974886320901 15881143087353370291185169)
              ·
                refine ⟨11910857315515027718388877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15881143087353370291185169 11910857315515027718388877)
                ·
                  refine ⟨4466571493318135394395829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11910857315515027718388877 4466571493318135394395829)
                  ·
                    refine ⟨418741077498575193224609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4466571493318135394395829 418741077498575193224609)
                    ·
                      rfl

theorem cell22_1223243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 5].length) (baseStart_1223243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223243 prefixEnd_1223243 := by exact prefixLift 1223243
  have htrace : WordTrace (prefixWord ++ tailWord_1223243) baseStart_1223243 baseEnd_1223243 := by
    simpa [prefixWord, tailWord_1223243, baseEnd_1223243] using wordTrace_append hprefix tailTrace_1223243
  have hstable : (prefixWord ++ tailWord_1223243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223243).length < 2 ^ (prefixWord ++ tailWord_1223243).sum := by decide
  have hdescent : baseEnd_1223243 < baseStart_1223243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223277 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_1223277 : Nat := 118140960795 + 1223277 * 2 ^ 59
def prefixEnd_1223277 : Nat := 4983230072969 + 3 ^ 40 * 1223277 * 2
def baseEnd_1223277 : Nat := 418752716393410437874505

theorem tailTrace_1223277 : CollatzResearch.WordTrace tailWord_1223277 prefixEnd_1223277 418752716393410437874505 := by
  unfold tailWord_1223277
  simp only [CollatzResearch.WordTrace]
  refine ⟨44616577589283822923812085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29744385059522548615874723 44616577589283822923812085)
  ·
    refine ⟨4182804148995358399107383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44616577589283822923812085 4182804148995358399107383)
    ·
      refine ⟨6274206223493037598661075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4182804148995358399107383 6274206223493037598661075)
      ·
        refine ⟨9411309335239556397991613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6274206223493037598661075 9411309335239556397991613)
        ·
          refine ⟨3529241000714833649246855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9411309335239556397991613 3529241000714833649246855)
          ·
            refine ⟨5293861501072250473870283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3529241000714833649246855 5293861501072250473870283)
            ·
              refine ⟨7940792251608375710805425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5293861501072250473870283 7940792251608375710805425)
              ·
                refine ⟨5955594188706281783104069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7940792251608375710805425 5955594188706281783104069)
                ·
                  refine ⟨1116673910382427834332013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5955594188706281783104069 1116673910382427834332013)
                  ·
                    refine ⟨418752716393410437874505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1116673910382427834332013 418752716393410437874505)
                    ·
                      rfl

theorem cell22_1223277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_1223277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223277 prefixEnd_1223277 := by exact prefixLift 1223277
  have htrace : WordTrace (prefixWord ++ tailWord_1223277) baseStart_1223277 baseEnd_1223277 := by
    simpa [prefixWord, tailWord_1223277, baseEnd_1223277] using wordTrace_append hprefix tailTrace_1223277
  have hstable : (prefixWord ++ tailWord_1223277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223277).length < 2 ^ (prefixWord ++ tailWord_1223277).sum := by decide
  have hdescent : baseEnd_1223277 < baseStart_1223277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223288 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 1, 9]
def baseStart_1223288 : Nat := 118140960795 + 1223288 * 2 ^ 59
def prefixEnd_1223288 : Nat := 4983230072969 + 3 ^ 40 * 1223288 * 2
def baseEnd_1223288 : Nat := 418756481918210075849471

theorem tailTrace_1223288 : CollatzResearch.WordTrace tailWord_1223288 prefixEnd_1223288 418756481918210075849471 := by
  unfold tailWord_1223288
  simp only [CollatzResearch.WordTrace]
  refine ⟨22308489396121985901231259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29744652528162647868308345 22308489396121985901231259)
  ·
    refine ⟨33462734094182978851846889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22308489396121985901231259 33462734094182978851846889)
    ·
      refine ⟨25097050570637234138885167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33462734094182978851846889 25097050570637234138885167)
      ·
        refine ⟨37645575855955851208327751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25097050570637234138885167 37645575855955851208327751)
        ·
          refine ⟨56468363783933776812491627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37645575855955851208327751 56468363783933776812491627)
          ·
            refine ⟨84702545675900665218737441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56468363783933776812491627 84702545675900665218737441)
            ·
              refine ⟨63526909256925498914053081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84702545675900665218737441 63526909256925498914053081)
              ·
                refine ⟨47645181942694124185539811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63526909256925498914053081 47645181942694124185539811)
                ·
                  refine ⟨71467772914041186278309717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47645181942694124185539811 71467772914041186278309717)
                  ·
                    refine ⟨418756481918210075849471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 71467772914041186278309717 418756481918210075849471)
                    ·
                      rfl

theorem cell22_1223288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_1223288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223288 prefixEnd_1223288 := by exact prefixLift 1223288
  have htrace : WordTrace (prefixWord ++ tailWord_1223288) baseStart_1223288 baseEnd_1223288 := by
    simpa [prefixWord, tailWord_1223288, baseEnd_1223288] using wordTrace_append hprefix tailTrace_1223288
  have hstable : (prefixWord ++ tailWord_1223288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223288).length < 2 ^ (prefixWord ++ tailWord_1223288).sum := by decide
  have hdescent : baseEnd_1223288 < baseStart_1223288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223414 : List Nat := [5, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_1223414 : Nat := 118140960795 + 1223414 * 2 ^ 59
def prefixEnd_1223414 : Nat := 4983230072969 + 3 ^ 40 * 1223414 * 2
def baseEnd_1223414 : Nat := 139599871431062582399695

theorem tailTrace_1223414 : CollatzResearch.WordTrace tailWord_1223414 prefixEnd_1223414 139599871431062582399695 := by
  unfold tailWord_1223414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2788848399361718457596831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29747716259858330214366197 2788848399361718457596831)
  ·
    refine ⟨4183272599042577686395247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2788848399361718457596831 4183272599042577686395247)
    ·
      refine ⟨6274908898563866529592871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4183272599042577686395247 6274908898563866529592871)
      ·
        refine ⟨9412363347845799794389307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6274908898563866529592871 9412363347845799794389307)
        ·
          refine ⟨14118545021768699691583961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9412363347845799794389307 14118545021768699691583961)
          ·
            refine ⟨10588908766326524768687971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14118545021768699691583961 10588908766326524768687971)
            ·
              refine ⟨15883363149489787153031957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10588908766326524768687971 15883363149489787153031957)
              ·
                refine ⟨744532647632333772798373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15883363149489787153031957 744532647632333772798373)
                ·
                  refine ⟨139599871431062582399695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 744532647632333772798373 139599871431062582399695)
                  ·
                    rfl

theorem cell22_1223414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_1223414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223414 prefixEnd_1223414 := by exact prefixLift 1223414
  have htrace : WordTrace (prefixWord ++ tailWord_1223414) baseStart_1223414 baseEnd_1223414 := by
    simpa [prefixWord, tailWord_1223414, baseEnd_1223414] using wordTrace_append hprefix tailTrace_1223414
  have hstable : (prefixWord ++ tailWord_1223414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223414).length < 2 ^ (prefixWord ++ tailWord_1223414).sum := by decide
  have hdescent : baseEnd_1223414 < baseStart_1223414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223425 : List Nat := [1, 2, 4, 1, 1, 1, 1, 11]
def baseStart_1223425 : Nat := 118140960795 + 1223425 * 2 ^ 59
def prefixEnd_1223425 : Nat := 4983230072969 + 3 ^ 40 * 1223425 * 2
def baseEnd_1223425 : Nat := 46533708868665265019339

theorem tailTrace_1223425 : CollatzResearch.WordTrace tailWord_1223425 prefixEnd_1223425 46533708868665265019339 := by
  unfold tailWord_1223425
  simp only [CollatzResearch.WordTrace]
  refine ⟨44621975592747644200199729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29747983728498429466799819 44621975592747644200199729)
  ·
    refine ⟨33466481694560733150149797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44621975592747644200199729 33466481694560733150149797)
    ·
      refine ⟨6274965317730137465653087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33466481694560733150149797 6274965317730137465653087)
      ·
        refine ⟨9412447976595206198479631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6274965317730137465653087 9412447976595206198479631)
        ·
          refine ⟨14118671964892809297719447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9412447976595206198479631 14118671964892809297719447)
          ·
            refine ⟨21178007947339213946579171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14118671964892809297719447 21178007947339213946579171)
            ·
              refine ⟨31767011921008820919868757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21178007947339213946579171 31767011921008820919868757)
              ·
                refine ⟨46533708868665265019339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 31767011921008820919868757 46533708868665265019339)
                ·
                  rfl

theorem cell22_1223425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 11].length) (baseStart_1223425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223425 prefixEnd_1223425 := by exact prefixLift 1223425
  have htrace : WordTrace (prefixWord ++ tailWord_1223425) baseStart_1223425 baseEnd_1223425 := by
    simpa [prefixWord, tailWord_1223425, baseEnd_1223425] using wordTrace_append hprefix tailTrace_1223425
  have hstable : (prefixWord ++ tailWord_1223425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223425).length < 2 ^ (prefixWord ++ tailWord_1223425).sum := by decide
  have hdescent : baseEnd_1223425 < baseStart_1223425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223532 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 6]
def baseStart_1223532 : Nat := 118140960795 + 1223532 * 2 ^ 59
def prefixEnd_1223532 : Nat := 4983230072969 + 3 ^ 40 * 1223532 * 2
def baseEnd_1223532 : Nat := 139613336034891590916241

theorem tailTrace_1223532 : CollatzResearch.WordTrace tailWord_1223532 prefixEnd_1223532 139613336034891590916241 := by
  unfold tailWord_1223532
  simp only [CollatzResearch.WordTrace]
  refine ⟨22312939101680000737172425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29750585468906667649563233 22312939101680000737172425)
  ·
    refine ⟨16734704326260000552879319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22312939101680000737172425 16734704326260000552879319)
    ·
      refine ⟨25102056489390000829318979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16734704326260000552879319 25102056489390000829318979)
      ·
        refine ⟨37653084734085001243978469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25102056489390000829318979 37653084734085001243978469)
        ·
          refine ⟨7059953387640937733245963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37653084734085001243978469 7059953387640937733245963)
          ·
            refine ⟨10589930081461406599868945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7059953387640937733245963 10589930081461406599868945)
            ·
              refine ⟨7942447561096054949901709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10589930081461406599868945 7942447561096054949901709)
              ·
                refine ⟨2978417835411020606213141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7942447561096054949901709 2978417835411020606213141)
                ·
                  refine ⟨139613336034891590916241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2978417835411020606213141 139613336034891590916241)
                  ·
                    rfl

theorem cell22_1223532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_1223532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223532 prefixEnd_1223532 := by exact prefixLift 1223532
  have htrace : WordTrace (prefixWord ++ tailWord_1223532) baseStart_1223532 baseEnd_1223532 := by
    simpa [prefixWord, tailWord_1223532, baseEnd_1223532] using wordTrace_append hprefix tailTrace_1223532
  have hstable : (prefixWord ++ tailWord_1223532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223532).length < 2 ^ (prefixWord ++ tailWord_1223532).sum := by decide
  have hdescent : baseEnd_1223532 < baseStart_1223532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223547 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 1, 5]
def baseStart_1223547 : Nat := 118140960795 + 1223547 * 2 ^ 59
def prefixEnd_1223547 : Nat := 4983230072969 + 3 ^ 40 * 1223547 * 2
def baseEnd_1223547 : Nat := 418845142911219733623677

theorem tailTrace_1223547 : CollatzResearch.WordTrace tailWord_1223547 prefixEnd_1223547 418845142911219733623677 := by
  unfold tailWord_1223547
  simp only [CollatzResearch.WordTrace]
  refine ⟨44626425298305659036140895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29750950198870439357427263 44626425298305659036140895)
  ·
    refine ⟨66939637947458488554211343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44626425298305659036140895 66939637947458488554211343)
    ·
      refine ⟨100409456921187732831317015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66939637947458488554211343 100409456921187732831317015)
      ·
        refine ⟨150614185381781599246975523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100409456921187732831317015 150614185381781599246975523)
        ·
          refine ⟨225921278072672398870463285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150614185381781599246975523 225921278072672398870463285)
          ·
            refine ⟨21180119819313037394105933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 225921278072672398870463285 21180119819313037394105933)
            ·
              refine ⟨7942544932242389022789725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21180119819313037394105933 7942544932242389022789725)
              ·
                refine ⟨2978454349590895883546147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7942544932242389022789725 2978454349590895883546147)
                ·
                  refine ⟨4467681524386343825319221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2978454349590895883546147 4467681524386343825319221)
                  ·
                    refine ⟨418845142911219733623677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4467681524386343825319221 418845142911219733623677)
                    ·
                      rfl

theorem cell22_1223547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 5].length) (baseStart_1223547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223547 prefixEnd_1223547 := by exact prefixLift 1223547
  have htrace : WordTrace (prefixWord ++ tailWord_1223547) baseStart_1223547 baseEnd_1223547 := by
    simpa [prefixWord, tailWord_1223547, baseEnd_1223547] using wordTrace_append hprefix tailTrace_1223547
  have hstable : (prefixWord ++ tailWord_1223547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223547).length < 2 ^ (prefixWord ++ tailWord_1223547).sum := by decide
  have hdescent : baseEnd_1223547 < baseStart_1223547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223607 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 2, 6]
def baseStart_1223607 : Nat := 118140960795 + 1223607 * 2 ^ 59
def prefixEnd_1223607 : Nat := 4983230072969 + 3 ^ 40 * 1223607 * 2
def baseEnd_1223607 : Nat := 418865682137399577123493

theorem tailTrace_1223607 : CollatzResearch.WordTrace tailWord_1223607 prefixEnd_1223607 418865682137399577123493 := by
  unfold tailWord_1223607
  simp only [CollatzResearch.WordTrace]
  refine ⟨44628613678088289283325075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29752409118725526188883383 44628613678088289283325075)
  ·
    refine ⟨66942920517132433924987613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44628613678088289283325075 66942920517132433924987613)
    ·
      refine ⟨25103595193924662721870355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66942920517132433924987613 25103595193924662721870355)
      ·
        refine ⟨37655392790886994082805533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25103595193924662721870355 37655392790886994082805533)
        ·
          refine ⟨14120772296582622781052075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37655392790886994082805533 14120772296582622781052075)
          ·
            refine ⟨21181158444873934171578113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14120772296582622781052075 21181158444873934171578113)
            ·
              refine ⟨15885868833655450628683585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21181158444873934171578113 15885868833655450628683585)
              ·
                refine ⟨11914401625241587971512689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15885868833655450628683585 11914401625241587971512689)
                ·
                  refine ⟨8935801218931190978634517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11914401625241587971512689 8935801218931190978634517)
                  ·
                    refine ⟨418865682137399577123493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8935801218931190978634517 418865682137399577123493)
                    ·
                      rfl

theorem cell22_1223607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_1223607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223607 prefixEnd_1223607 := by exact prefixLift 1223607
  have htrace : WordTrace (prefixWord ++ tailWord_1223607) baseStart_1223607 baseEnd_1223607 := by
    simpa [prefixWord, tailWord_1223607, baseEnd_1223607] using wordTrace_append hprefix tailTrace_1223607
  have hstable : (prefixWord ++ tailWord_1223607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223607).length < 2 ^ (prefixWord ++ tailWord_1223607).sum := by decide
  have hdescent : baseEnd_1223607 < baseStart_1223607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223656 : List Nat := [2, 1, 4, 1, 1, 1, 6, 1, 5]
def baseStart_1223656 : Nat := 118140960795 + 1223656 * 2 ^ 59
def prefixEnd_1223656 : Nat := 4983230072969 + 3 ^ 40 * 1223656 * 2
def baseEnd_1223656 : Nat := 139627485279593260882781

theorem tailTrace_1223656 : CollatzResearch.WordTrace tailWord_1223656 prefixEnd_1223656 139627485279593260882781 := by
  unfold tailWord_1223656
  simp only [CollatzResearch.WordTrace]
  refine ⟨22315200427455385325929411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29753600569940513767905881 22315200427455385325929411)
  ·
    refine ⟨33472800641183077988894117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22315200427455385325929411 33472800641183077988894117)
    ·
      refine ⟨6276150120221827122917647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33472800641183077988894117 6276150120221827122917647)
      ·
        refine ⟨9414225180332740684376471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6276150120221827122917647 9414225180332740684376471)
        ·
          refine ⟨14121337770499111026564707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9414225180332740684376471 14121337770499111026564707)
          ·
            refine ⟨21182006655748666539847061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14121337770499111026564707 21182006655748666539847061)
            ·
              refine ⟨992906561988218744055331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21182006655748666539847061 992906561988218744055331)
              ·
                refine ⟨1489359842982328116082997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992906561988218744055331 1489359842982328116082997)
                ·
                  refine ⟨139627485279593260882781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1489359842982328116082997 139627485279593260882781)
                  ·
                    rfl

theorem cell22_1223656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 5].length) (baseStart_1223656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223656 prefixEnd_1223656 := by exact prefixLift 1223656
  have htrace : WordTrace (prefixWord ++ tailWord_1223656) baseStart_1223656 baseEnd_1223656 := by
    simpa [prefixWord, tailWord_1223656, baseEnd_1223656] using wordTrace_append hprefix tailTrace_1223656
  have hstable : (prefixWord ++ tailWord_1223656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223656).length < 2 ^ (prefixWord ++ tailWord_1223656).sum := by decide
  have hdescent : baseEnd_1223656 < baseStart_1223656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223716 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_1223716 : Nat := 118140960795 + 1223716 * 2 ^ 59
def prefixEnd_1223716 : Nat := 4983230072969 + 3 ^ 40 * 1223716 * 2
def baseEnd_1223716 : Nat := 418902995064959626148159

theorem tailTrace_1223716 : CollatzResearch.WordTrace tailWord_1223716 prefixEnd_1223716 418902995064959626148159 := by
  unfold tailWord_1223716
  simp only [CollatzResearch.WordTrace]
  refine ⟨22316294617346700449521501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29755059489795600599362001 22316294617346700449521501)
  ·
    refine ⟨8368610481505012668570563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22316294617346700449521501 8368610481505012668570563)
    ·
      refine ⟨12552915722257519002855845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8368610481505012668570563 12552915722257519002855845)
      ·
        refine ⟨2353671697923284813035471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12552915722257519002855845 2353671697923284813035471)
        ·
          refine ⟨3530507546884927219553207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353671697923284813035471 3530507546884927219553207)
          ·
            refine ⟨5295761320327390829329811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3530507546884927219553207 5295761320327390829329811)
            ·
              refine ⟨7943641980491086243994717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5295761320327390829329811 7943641980491086243994717)
              ·
                refine ⟨2978865742684157341498019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7943641980491086243994717 2978865742684157341498019)
                ·
                  refine ⟨4468298614026236012247029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2978865742684157341498019 4468298614026236012247029)
                  ·
                    refine ⟨418902995064959626148159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4468298614026236012247029 418902995064959626148159)
                    ·
                      rfl

theorem cell22_1223716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_1223716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223716 prefixEnd_1223716 := by exact prefixLift 1223716
  have htrace : WordTrace (prefixWord ++ tailWord_1223716) baseStart_1223716 baseEnd_1223716 := by
    simpa [prefixWord, tailWord_1223716, baseEnd_1223716] using wordTrace_append hprefix tailTrace_1223716
  have hstable : (prefixWord ++ tailWord_1223716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223716).length < 2 ^ (prefixWord ++ tailWord_1223716).sum := by decide
  have hdescent : baseEnd_1223716 < baseStart_1223716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223750 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_1223750 : Nat := 118140960795 + 1223750 * 2 ^ 59
def prefixEnd_1223750 : Nat := 4983230072969 + 3 ^ 40 * 1223750 * 2
def baseEnd_1223750 : Nat := 418914633959794870798055

theorem tailTrace_1223750 : CollatzResearch.WordTrace tailWord_1223750 prefixEnd_1223750 418914633959794870798055 := by
  unfold tailWord_1223750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1394807166142819522055647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29755886211046816470520469 1394807166142819522055647)
  ·
    refine ⟨2092210749214229283083471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1394807166142819522055647 2092210749214229283083471)
    ·
      refine ⟨3138316123821343924625207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2092210749214229283083471 3138316123821343924625207)
      ·
        refine ⟨4707474185732015886937811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3138316123821343924625207 4707474185732015886937811)
        ·
          refine ⟨7061211278598023830406717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4707474185732015886937811 7061211278598023830406717)
          ·
            refine ⟨2647954229474258936402519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7061211278598023830406717 2647954229474258936402519)
            ·
              refine ⟨3971931344211388404603779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647954229474258936402519 3971931344211388404603779)
              ·
                refine ⟨5957897016317082606905669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3971931344211388404603779 5957897016317082606905669)
                ·
                  refine ⟨1117105690559452988794813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5957897016317082606905669 1117105690559452988794813)
                  ·
                    refine ⟨418914633959794870798055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1117105690559452988794813 418914633959794870798055)
                    ·
                      rfl

theorem cell22_1223750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_1223750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223750 prefixEnd_1223750 := by exact prefixLift 1223750
  have htrace : WordTrace (prefixWord ++ tailWord_1223750) baseStart_1223750 baseEnd_1223750 := by
    simpa [prefixWord, tailWord_1223750, baseEnd_1223750] using wordTrace_append hprefix tailTrace_1223750
  have hstable : (prefixWord ++ tailWord_1223750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223750).length < 2 ^ (prefixWord ++ tailWord_1223750).sum := by decide
  have hdescent : baseEnd_1223750 < baseStart_1223750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223761 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 3, 3]
def baseStart_1223761 : Nat := 118140960795 + 1223761 * 2 ^ 59
def prefixEnd_1223761 : Nat := 4983230072969 + 3 ^ 40 * 1223761 * 2
def baseEnd_1223761 : Nat := 418918399484594508773021

theorem tailTrace_1223761 : CollatzResearch.WordTrace tailWord_1223761 prefixEnd_1223761 418918399484594508773021 := by
  unfold tailWord_1223761
  simp only [CollatzResearch.WordTrace]
  refine ⟨44634230519530373584431137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29756153679686915722954091 44634230519530373584431137)
  ·
    refine ⟨33475672889647780188323353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44634230519530373584431137 33475672889647780188323353)
    ·
      refine ⟨25106754667235835141242515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33475672889647780188323353 25106754667235835141242515)
      ·
        refine ⟨37660132000853752711863773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25106754667235835141242515 37660132000853752711863773)
        ·
          refine ⟨14122549500320157266948915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37660132000853752711863773 14122549500320157266948915)
          ·
            refine ⟨21183824250480235900423373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14122549500320157266948915 21183824250480235900423373)
            ·
              refine ⟨7943934093930088462658765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21183824250480235900423373 7943934093930088462658765)
              ·
                refine ⟨2978975285223783173497037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7943934093930088462658765 2978975285223783173497037)
                ·
                  refine ⟨1117115731958918690061389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2978975285223783173497037 1117115731958918690061389)
                  ·
                    refine ⟨418918399484594508773021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1117115731958918690061389 418918399484594508773021)
                    ·
                      rfl

theorem cell22_1223761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_1223761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223761 prefixEnd_1223761 := by exact prefixLift 1223761
  have htrace : WordTrace (prefixWord ++ tailWord_1223761) baseStart_1223761 baseEnd_1223761 := by
    simpa [prefixWord, tailWord_1223761, baseEnd_1223761] using wordTrace_append hprefix tailTrace_1223761
  have hstable : (prefixWord ++ tailWord_1223761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223761).length < 2 ^ (prefixWord ++ tailWord_1223761).sum := by decide
  have hdescent : baseEnd_1223761 < baseStart_1223761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223812 : List Nat := [2, 3, 2, 1, 2, 3, 3, 2, 1, 3]
def baseStart_1223812 : Nat := 118140960795 + 1223812 * 2 ^ 59
def prefixEnd_1223812 : Nat := 4983230072969 + 3 ^ 40 * 1223812 * 2
def baseEnd_1223812 : Nat := 418935857826847375747865

theorem tailTrace_1223812 : CollatzResearch.WordTrace tailWord_1223812 prefixEnd_1223812 418935857826847375747865 := by
  unfold tailWord_1223812
  simp only [CollatzResearch.WordTrace]
  refine ⟨22318045321172804647268845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29757393761563739529691793 22318045321172804647268845)
  ·
    refine ⟨8369266995439801742725817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22318045321172804647268845 8369266995439801742725817)
    ·
      refine ⟨6276950246579851307044363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8369266995439801742725817 6276950246579851307044363)
      ·
        refine ⟨9415425369869776960566545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6276950246579851307044363 9415425369869776960566545)
        ·
          refine ⟨7061569027402332720424909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9415425369869776960566545 7061569027402332720424909)
          ·
            refine ⟨2648088385275874770159341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7061569027402332720424909 2648088385275874770159341)
            ·
              refine ⟨993033144478453038809753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2648088385275874770159341 993033144478453038809753)
              ·
                refine ⟨744774858358839779107315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993033144478453038809753 744774858358839779107315)
                ·
                  refine ⟨1117162287538259668660973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744774858358839779107315 1117162287538259668660973)
                  ·
                    refine ⟨418935857826847375747865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1117162287538259668660973 418935857826847375747865)
                    ·
                      rfl

theorem cell22_1223812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_1223812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223812 prefixEnd_1223812 := by exact prefixLift 1223812
  have htrace : WordTrace (prefixWord ++ tailWord_1223812) baseStart_1223812 baseEnd_1223812 := by
    simpa [prefixWord, tailWord_1223812, baseEnd_1223812] using wordTrace_append hprefix tailTrace_1223812
  have hstable : (prefixWord ++ tailWord_1223812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223812).length < 2 ^ (prefixWord ++ tailWord_1223812).sum := by decide
  have hdescent : baseEnd_1223812 < baseStart_1223812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223870 : List Nat := [4, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_1223870 : Nat := 118140960795 + 1223870 * 2 ^ 59
def prefixEnd_1223870 : Nat := 4983230072969 + 3 ^ 40 * 1223870 * 2
def baseEnd_1223870 : Nat := 139651904137384852599229

theorem tailTrace_1223870 : CollatzResearch.WordTrace tailWord_1223870 prefixEnd_1223870 139651904137384852599229 := by
  unfold tailWord_1223870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5579775759516935650018633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29758804050756990133432709 5579775759516935650018633)
  ·
    refine ⟨4184831819637701737513975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5579775759516935650018633 4184831819637701737513975)
    ·
      refine ⟨6277247729456552606270963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4184831819637701737513975 6277247729456552606270963)
      ·
        refine ⟨9415871594184828909406445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6277247729456552606270963 9415871594184828909406445)
        ·
          refine ⟨3530951847819310841027417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9415871594184828909406445 3530951847819310841027417)
          ·
            refine ⟨2648213885864483130770563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530951847819310841027417 2648213885864483130770563)
            ·
              refine ⟨3972320828796724696155845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2648213885864483130770563 3972320828796724696155845)
              ·
                refine ⟨744810155399385880529221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3972320828796724696155845 744810155399385880529221)
                ·
                  refine ⟨139651904137384852599229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 744810155399385880529221 139651904137384852599229)
                  ·
                    rfl

theorem cell22_1223870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_1223870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223870 prefixEnd_1223870 := by exact prefixLift 1223870
  have htrace : WordTrace (prefixWord ++ tailWord_1223870) baseStart_1223870 baseEnd_1223870 := by
    simpa [prefixWord, tailWord_1223870, baseEnd_1223870] using wordTrace_append hprefix tailTrace_1223870
  have hstable : (prefixWord ++ tailWord_1223870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223870).length < 2 ^ (prefixWord ++ tailWord_1223870).sum := by decide
  have hdescent : baseEnd_1223870 < baseStart_1223870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223930 : List Nat := [3, 1, 1, 1, 1, 4, 1, 6, 1, 3]
def baseStart_1223930 : Nat := 118140960795 + 1223930 * 2 ^ 59
def prefixEnd_1223930 : Nat := 4983230072969 + 3 ^ 40 * 1223930 * 2
def baseEnd_1223930 : Nat := 418976251638334401297503

theorem tailTrace_1223930 : CollatzResearch.WordTrace tailWord_1223930 prefixEnd_1223930 418976251638334401297503 := by
  unfold tailWord_1223930
  simp only [CollatzResearch.WordTrace]
  refine ⟨11160098613979528861833311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29760262970612076964888829 11160098613979528861833311)
  ·
    refine ⟨16740147920969293292749967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11160098613979528861833311 16740147920969293292749967)
    ·
      refine ⟨25110221881453939939124951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16740147920969293292749967 25110221881453939939124951)
      ·
        refine ⟨37665332822180909908687427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25110221881453939939124951 37665332822180909908687427)
        ·
          refine ⟨56497999233271364863031141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37665332822180909908687427 56497999233271364863031141)
          ·
            refine ⟨10593374856238380911818339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56497999233271364863031141 10593374856238380911818339)
            ·
              refine ⟨15890062284357571367727509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10593374856238380911818339 15890062284357571367727509)
              ·
                refine ⟨744846669579261157862227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15890062284357571367727509 744846669579261157862227)
                ·
                  refine ⟨1117270004368891736793341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744846669579261157862227 1117270004368891736793341)
                  ·
                    refine ⟨418976251638334401297503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1117270004368891736793341 418976251638334401297503)
                    ·
                      rfl

theorem cell22_1223930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_1223930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223930 prefixEnd_1223930 := by exact prefixLift 1223930
  have htrace : WordTrace (prefixWord ++ tailWord_1223930) baseStart_1223930 baseEnd_1223930 := by
    simpa [prefixWord, tailWord_1223930, baseEnd_1223930] using wordTrace_append hprefix tailTrace_1223930
  have hstable : (prefixWord ++ tailWord_1223930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223930).length < 2 ^ (prefixWord ++ tailWord_1223930).sum := by decide
  have hdescent : baseEnd_1223930 < baseStart_1223930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223941 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_1223941 : Nat := 118140960795 + 1223941 * 2 ^ 59
def prefixEnd_1223941 : Nat := 4983230072969 + 3 ^ 40 * 1223941 * 2
def baseEnd_1223941 : Nat := 418980017163134039272469

theorem tailTrace_1223941 : CollatzResearch.WordTrace tailWord_1223941 prefixEnd_1223941 418980017163134039272469 := by
  unfold tailWord_1223941
  simp only [CollatzResearch.WordTrace]
  refine ⟨44640795658878264325983677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29760530439252176217322451 44640795658878264325983677)
  ·
    refine ⟨16740298372079349122243879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44640795658878264325983677 16740298372079349122243879)
    ·
      refine ⟨25110447558119023683365819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16740298372079349122243879 25110447558119023683365819)
      ·
        refine ⟨37665671337178535525048729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25110447558119023683365819 37665671337178535525048729)
        ·
          refine ⟨28249253502883901643786547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37665671337178535525048729 28249253502883901643786547)
          ·
            refine ⟨42373880254325852465679821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28249253502883901643786547 42373880254325852465679821)
            ·
              refine ⟨15890205095372194674629933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42373880254325852465679821 15890205095372194674629933)
              ·
                refine ⟨5958826910764573002986225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15890205095372194674629933 5958826910764573002986225)
                ·
                  refine ⟨4469120183073429752239669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5958826910764573002986225 4469120183073429752239669)
                  ·
                    refine ⟨418980017163134039272469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4469120183073429752239669 418980017163134039272469)
                    ·
                      rfl

theorem cell22_1223941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_1223941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223941 prefixEnd_1223941 := by exact prefixLift 1223941
  have htrace : WordTrace (prefixWord ++ tailWord_1223941) baseStart_1223941 baseEnd_1223941 := by
    simpa [prefixWord, tailWord_1223941, baseEnd_1223941] using wordTrace_append hprefix tailTrace_1223941
  have hstable : (prefixWord ++ tailWord_1223941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223941).length < 2 ^ (prefixWord ++ tailWord_1223941).sum := by decide
  have hdescent : baseEnd_1223941 < baseStart_1223941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223981 : List Nat := [1, 5, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1223981 : Nat := 118140960795 + 1223981 * 2 ^ 59
def prefixEnd_1223981 : Nat := 4983230072969 + 3 ^ 40 * 1223981 * 2
def baseEnd_1223981 : Nat := 418993709980587268272347

theorem tailTrace_1223981 : CollatzResearch.WordTrace tailWord_1223981 prefixEnd_1223981 418993709980587268272347 := by
  unfold tailWord_1223981
  simp only [CollatzResearch.WordTrace]
  refine ⟨44642254578733351157439797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29761503052488900771626531 44642254578733351157439797)
  ·
    refine ⟨4185211366756251671009981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44642254578733351157439797 4185211366756251671009981)
    ·
      refine ⟨1569454262533594376628743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4185211366756251671009981 1569454262533594376628743)
      ·
        refine ⟨2354181393800391564943115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1569454262533594376628743 2354181393800391564943115)
        ·
          refine ⟨3531272090700587347414673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2354181393800391564943115 3531272090700587347414673)
          ·
            refine ⟨2648454068025440510561005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3531272090700587347414673 2648454068025440510561005)
            ·
              refine ⟨993170275509540191460377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2648454068025440510561005 993170275509540191460377)
              ·
                refine ⟨744877706632155143595283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993170275509540191460377 744877706632155143595283)
                ·
                  refine ⟨1117316559948232715392925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744877706632155143595283 1117316559948232715392925)
                  ·
                    refine ⟨418993709980587268272347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1117316559948232715392925 418993709980587268272347)
                    ·
                      rfl

theorem cell22_1223981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1223981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1223981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1223981 prefixEnd_1223981 := by exact prefixLift 1223981
  have htrace : WordTrace (prefixWord ++ tailWord_1223981) baseStart_1223981 baseEnd_1223981 := by
    simpa [prefixWord, tailWord_1223981, baseEnd_1223981] using wordTrace_append hprefix tailTrace_1223981
  have hstable : (prefixWord ++ tailWord_1223981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223981).length < 2 ^ (prefixWord ++ tailWord_1223981).sum := by decide
  have hdescent : baseEnd_1223981 < baseStart_1223981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224016 : List Nat := [2, 1, 1, 1, 1, 5, 1, 10]
def baseStart_1224016 : Nat := 118140960795 + 1224016 * 2 ^ 59
def prefixEnd_1224016 : Nat := 4983230072969 + 3 ^ 40 * 1224016 * 2
def baseEnd_1224016 : Nat := 46556187910650982627471

theorem tailTrace_1224016 : CollatzResearch.WordTrace tailWord_1224016 prefixEnd_1224016 46556187910650982627471 := by
  unfold tailWord_1224016
  simp only [CollatzResearch.WordTrace]
  refine ⟨22321765566803276067481951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29762354089071034756642601 22321765566803276067481951)
  ·
    refine ⟨33482648350204914101222927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22321765566803276067481951 33482648350204914101222927)
    ·
      refine ⟨50223972525307371151834391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33482648350204914101222927 50223972525307371151834391)
      ·
        refine ⟨75335958787961056727751587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50223972525307371151834391 75335958787961056727751587)
        ·
          refine ⟨113003938181941585091627381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75335958787961056727751587 113003938181941585091627381)
          ·
            refine ⟨10594119204557023602340067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113003938181941585091627381 10594119204557023602340067)
            ·
              refine ⟨15891178806835535403510101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10594119204557023602340067 15891178806835535403510101)
              ·
                refine ⟨46556187910650982627471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15891178806835535403510101 46556187910650982627471)
                ·
                  rfl

theorem cell22_1224016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 10].length) (baseStart_1224016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224016 prefixEnd_1224016 := by exact prefixLift 1224016
  have htrace : WordTrace (prefixWord ++ tailWord_1224016) baseStart_1224016 baseEnd_1224016 := by
    simpa [prefixWord, tailWord_1224016, baseEnd_1224016] using wordTrace_append hprefix tailTrace_1224016
  have hstable : (prefixWord ++ tailWord_1224016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224016).length < 2 ^ (prefixWord ++ tailWord_1224016).sum := by decide
  have hdescent : baseEnd_1224016 < baseStart_1224016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224039 : List Nat := [1, 1, 5, 1, 4, 2, 2, 2, 4]
def baseStart_1224039 : Nat := 118140960795 + 1224039 * 2 ^ 59
def prefixEnd_1224039 : Nat := 4983230072969 + 3 ^ 40 * 1224039 * 2
def baseEnd_1224039 : Nat := 139671188188631483440723

theorem tailTrace_1224039 : CollatzResearch.WordTrace tailWord_1224039 prefixEnd_1224039 139671188188631483440723 := by
  unfold tailWord_1224039
  simp only [CollatzResearch.WordTrace]
  refine ⟨44644370012523227063051171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29762913341682151375367447 44644370012523227063051171)
  ·
    refine ⟨66966555018784840594576757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44644370012523227063051171 66966555018784840594576757)
    ·
      refine ⟨6278114533011078805741571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66966555018784840594576757 6278114533011078805741571)
      ·
        refine ⟨9417171799516618208612357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6278114533011078805741571 9417171799516618208612357)
        ·
          refine ⟨1765719712409365914114817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9417171799516618208612357 1765719712409365914114817)
          ·
            refine ⟨1324289784307024435586113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1765719712409365914114817 1324289784307024435586113)
            ·
              refine ⟨993217338230268326689585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1324289784307024435586113 993217338230268326689585)
              ·
                refine ⟨744913003672701245017189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993217338230268326689585 744913003672701245017189)
                ·
                  refine ⟨139671188188631483440723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 744913003672701245017189 139671188188631483440723)
                  ·
                    rfl

theorem cell22_1224039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 4].length) (baseStart_1224039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224039 prefixEnd_1224039 := by exact prefixLift 1224039
  have htrace : WordTrace (prefixWord ++ tailWord_1224039) baseStart_1224039 baseEnd_1224039 := by
    simpa [prefixWord, tailWord_1224039, baseEnd_1224039] using wordTrace_append hprefix tailTrace_1224039
  have hstable : (prefixWord ++ tailWord_1224039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224039).length < 2 ^ (prefixWord ++ tailWord_1224039).sum := by decide
  have hdescent : baseEnd_1224039 < baseStart_1224039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224095 : List Nat := [1, 1, 2, 5, 1, 2, 3, 2, 5]
def baseStart_1224095 : Nat := 118140960795 + 1224095 * 2 ^ 59
def prefixEnd_1224095 : Nat := 4983230072969 + 3 ^ 40 * 1224095 * 2
def baseEnd_1224095 : Nat := 139677578170109656973999

theorem tailTrace_1224095 : CollatzResearch.WordTrace tailWord_1224095 prefixEnd_1224095 139677578170109656973999 := by
  unfold tailWord_1224095
  simp only [CollatzResearch.WordTrace]
  refine ⟨44646412500320348627089739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29764275000213565751393159 44646412500320348627089739)
  ·
    refine ⟨66969618750480522940634609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44646412500320348627089739 66969618750480522940634609)
    ·
      refine ⟨50227214062860392205475957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66969618750480522940634609 50227214062860392205475957)
      ·
        refine ⟨4708801318393161769263371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50227214062860392205475957 4708801318393161769263371)
        ·
          refine ⟨7063201977589742653895057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4708801318393161769263371 7063201977589742653895057)
          ·
            refine ⟨5297401483192306990421293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7063201977589742653895057 5297401483192306990421293)
            ·
              refine ⟨1986525556197115121407985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5297401483192306990421293 1986525556197115121407985)
              ·
                refine ⟨1489894167147836341055989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1986525556197115121407985 1489894167147836341055989)
                ·
                  refine ⟨139677578170109656973999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1489894167147836341055989 139677578170109656973999)
                  ·
                    rfl

theorem cell22_1224095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 5].length) (baseStart_1224095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224095 prefixEnd_1224095 := by exact prefixLift 1224095
  have htrace : WordTrace (prefixWord ++ tailWord_1224095) baseStart_1224095 baseEnd_1224095 := by
    simpa [prefixWord, tailWord_1224095, baseEnd_1224095] using wordTrace_append hprefix tailTrace_1224095
  have hstable : (prefixWord ++ tailWord_1224095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224095).length < 2 ^ (prefixWord ++ tailWord_1224095).sum := by decide
  have hdescent : baseEnd_1224095 < baseStart_1224095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224108 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_1224108 : Nat := 118140960795 + 1224108 * 2 ^ 59
def prefixEnd_1224108 : Nat := 4983230072969 + 3 ^ 40 * 1224108 * 2
def baseEnd_1224108 : Nat := 419037184676001270346957

theorem tailTrace_1224108 : CollatzResearch.WordTrace tailWord_1224108 prefixEnd_1224108 419037184676001270346957 := by
  unfold tailWord_1224108
  simp only [CollatzResearch.WordTrace]
  refine ⟨22323443324636625923656489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29764591099515501231541985 22323443324636625923656489)
  ·
    refine ⟨16742582493477469442742367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22323443324636625923656489 16742582493477469442742367)
    ·
      refine ⟨25113873740216204164113551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16742582493477469442742367 25113873740216204164113551)
      ·
        refine ⟨37670810610324306246170327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25113873740216204164113551 37670810610324306246170327)
        ·
          refine ⟨56506215915486459369255491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37670810610324306246170327 56506215915486459369255491)
          ·
            refine ⟨84759323873229689053883237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56506215915486459369255491 84759323873229689053883237)
            ·
              refine ⟨15892373226230566697603107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84759323873229689053883237 15892373226230566697603107)
              ·
                refine ⟨23838559839345850046404661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15892373226230566697603107 23838559839345850046404661)
                ·
                  refine ⟨2234864984938673441850437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23838559839345850046404661 2234864984938673441850437)
                  ·
                    refine ⟨419037184676001270346957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2234864984938673441850437 419037184676001270346957)
                    ·
                      rfl

theorem cell22_1224108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_1224108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224108 prefixEnd_1224108 := by exact prefixLift 1224108
  have htrace : WordTrace (prefixWord ++ tailWord_1224108) baseStart_1224108 baseEnd_1224108 := by
    simpa [prefixWord, tailWord_1224108, baseEnd_1224108] using wordTrace_append hprefix tailTrace_1224108
  have hstable : (prefixWord ++ tailWord_1224108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224108).length < 2 ^ (prefixWord ++ tailWord_1224108).sum := by decide
  have hdescent : baseEnd_1224108 < baseStart_1224108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224157 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 6]
def baseStart_1224157 : Nat := 118140960795 + 1224157 * 2 ^ 59
def prefixEnd_1224157 : Nat := 4983230072969 + 3 ^ 40 * 1224157 * 2
def baseEnd_1224157 : Nat := 139684652792460491957269

theorem tailTrace_1224157 : CollatzResearch.WordTrace tailWord_1224157 prefixEnd_1224157 139684652792460491957269 := by
  unfold tailWord_1224157
  simp only [CollatzResearch.WordTrace]
  refine ⟨44648673826095733215846725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29765782550730488810564483 44648673826095733215846725)
  ·
    refine ⟨8371626342392949977971261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44648673826095733215846725 8371626342392949977971261)
    ·
      refine ⟨3139359878397356241739223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8371626342392949977971261 3139359878397356241739223)
      ·
        refine ⟨4709039817596034362608835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3139359878397356241739223 4709039817596034362608835)
        ·
          refine ⟨7063559726394051543913253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4709039817596034362608835 7063559726394051543913253)
          ·
            refine ⟨1324417448698884664483735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7063559726394051543913253 1324417448698884664483735)
            ·
              refine ⟨1986626173048326996725603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1324417448698884664483735 1986626173048326996725603)
              ·
                refine ⟨2979939259572490495088405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1986626173048326996725603 2979939259572490495088405)
                ·
                  refine ⟨139684652792460491957269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2979939259572490495088405 139684652792460491957269)
                  ·
                    rfl

theorem cell22_1224157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_1224157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224157 prefixEnd_1224157 := by exact prefixLift 1224157
  have htrace : WordTrace (prefixWord ++ tailWord_1224157) baseStart_1224157 baseEnd_1224157 := by
    simpa [prefixWord, tailWord_1224157, baseEnd_1224157] using wordTrace_append hprefix tailTrace_1224157
  have hstable : (prefixWord ++ tailWord_1224157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224157).length < 2 ^ (prefixWord ++ tailWord_1224157).sum := by decide
  have hdescent : baseEnd_1224157 < baseStart_1224157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224305 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 6, 4]
def baseStart_1224305 : Nat := 118140960795 + 1224305 * 2 ^ 59
def prefixEnd_1224305 : Nat := 4983230072969 + 3 ^ 40 * 1224305 * 2
def baseEnd_1224305 : Nat := 419104621801958423171353

theorem tailTrace_1224305 : CollatzResearch.WordTrace tailWord_1224305 prefixEnd_1224305 419104621801958423171353 := by
  unfold tailWord_1224305
  simp only [CollatzResearch.WordTrace]
  refine ⟨44654071829559554492234369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29769381219706369661489579 44654071829559554492234369)
  ·
    refine ⟨33490553872169665869175777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44654071829559554492234369 33490553872169665869175777)
    ·
      refine ⟨25117915404127249401881833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33490553872169665869175777 25117915404127249401881833)
      ·
        refine ⟨18838436553095437051411375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25117915404127249401881833 18838436553095437051411375)
        ·
          refine ⟨28257654829643155577117063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18838436553095437051411375 28257654829643155577117063)
          ·
            refine ⟨42386482244464733365675595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28257654829643155577117063 42386482244464733365675595)
            ·
              refine ⟨63579723366697100048513393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42386482244464733365675595 63579723366697100048513393)
              ·
                refine ⟨47684792525022825036385045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63579723366697100048513393 47684792525022825036385045)
                ·
                  refine ⟨2235224649610444923580549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47684792525022825036385045 2235224649610444923580549)
                  ·
                    refine ⟨419104621801958423171353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2235224649610444923580549 419104621801958423171353)
                    ·
                      rfl

theorem cell22_1224305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_1224305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224305 prefixEnd_1224305 := by exact prefixLift 1224305
  have htrace : WordTrace (prefixWord ++ tailWord_1224305) baseStart_1224305 baseEnd_1224305 := by
    simpa [prefixWord, tailWord_1224305, baseEnd_1224305] using wordTrace_append hprefix tailTrace_1224305
  have hstable : (prefixWord ++ tailWord_1224305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224305).length < 2 ^ (prefixWord ++ tailWord_1224305).sum := by decide
  have hdescent : baseEnd_1224305 < baseStart_1224305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224444 : List Nat := [2, 2, 2, 1, 3, 1, 1, 6, 4]
def baseStart_1224444 : Nat := 118140960795 + 1224444 * 2 ^ 59
def prefixEnd_1224444 : Nat := 4983230072969 + 3 ^ 40 * 1224444 * 2
def baseEnd_1224444 : Nat := 139717401447536131315309

theorem tailTrace_1224444 : CollatzResearch.WordTrace tailWord_1224444 prefixEnd_1224444 139717401447536131315309 := by
  unfold tailWord_1224444
  simp only [CollatzResearch.WordTrace]
  refine ⟨22329570788027990615772193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29772761050703987487696257 22329570788027990615772193)
  ·
    refine ⟨16747178091020992961829145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22329570788027990615772193 16747178091020992961829145)
    ·
      refine ⟨12560383568265744721371859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16747178091020992961829145 12560383568265744721371859)
      ·
        refine ⟨18840575352398617082057789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12560383568265744721371859 18840575352398617082057789)
        ·
          refine ⟨7065215757149481405771671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18840575352398617082057789 7065215757149481405771671)
          ·
            refine ⟨10597823635724222108657507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7065215757149481405771671 10597823635724222108657507)
            ·
              refine ⟨15896735453586333162986261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10597823635724222108657507 15896735453586333162986261)
              ·
                refine ⟨745159474386859367014981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15896735453586333162986261 745159474386859367014981)
                ·
                  refine ⟨139717401447536131315309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 745159474386859367014981 139717401447536131315309)
                  ·
                    rfl

theorem cell22_1224444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_1224444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224444 prefixEnd_1224444 := by exact prefixLift 1224444
  have htrace : WordTrace (prefixWord ++ tailWord_1224444) baseStart_1224444 baseEnd_1224444 := by
    simpa [prefixWord, tailWord_1224444, baseEnd_1224444] using wordTrace_append hprefix tailTrace_1224444
  have hstable : (prefixWord ++ tailWord_1224444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224444).length < 2 ^ (prefixWord ++ tailWord_1224444).sum := by decide
  have hdescent : baseEnd_1224444 < baseStart_1224444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224459 : List Nat := [1, 1, 1, 1, 5, 1, 2, 5, 2, 3]
def baseStart_1224459 : Nat := 118140960795 + 1224459 * 2 ^ 59
def prefixEnd_1224459 : Nat := 4983230072969 + 3 ^ 40 * 1224459 * 2
def baseEnd_1224459 : Nat := 419157339149153354820881

theorem tailTrace_1224459 : CollatzResearch.WordTrace tailWord_1224459 prefixEnd_1224459 419157339149153354820881 := by
  unfold tailWord_1224459
  simp only [CollatzResearch.WordTrace]
  refine ⟨44659688671001638793340431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29773125780667759195560287 44659688671001638793340431)
  ·
    refine ⟨66989533006502458190010647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44659688671001638793340431 66989533006502458190010647)
    ·
      refine ⟨100484299509753687285015971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66989533006502458190010647 100484299509753687285015971)
      ·
        refine ⟨150726449264630530927523957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100484299509753687285015971 150726449264630530927523957)
        ·
          refine ⟨14130604618559112274455371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150726449264630530927523957 14130604618559112274455371)
          ·
            refine ⟨21195906927838668411683057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14130604618559112274455371 21195906927838668411683057)
            ·
              refine ⟨15896930195879001308762293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21195906927838668411683057 15896930195879001308762293)
              ·
                refine ⟨1490337205863656372696465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15896930195879001308762293 1490337205863656372696465)
                ·
                  refine ⟨1117752904397742279522349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1490337205863656372696465 1117752904397742279522349)
                  ·
                    refine ⟨419157339149153354820881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1117752904397742279522349 419157339149153354820881)
                    ·
                      rfl

theorem cell22_1224459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 3].length) (baseStart_1224459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224459 prefixEnd_1224459 := by exact prefixLift 1224459
  have htrace : WordTrace (prefixWord ++ tailWord_1224459) baseStart_1224459 baseEnd_1224459 := by
    simpa [prefixWord, tailWord_1224459, baseEnd_1224459] using wordTrace_append hprefix tailTrace_1224459
  have hstable : (prefixWord ++ tailWord_1224459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224459).length < 2 ^ (prefixWord ++ tailWord_1224459).sum := by decide
  have hdescent : baseEnd_1224459 < baseStart_1224459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224510 : List Nat := [4, 2, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_1224510 : Nat := 118140960795 + 1224510 * 2 ^ 59
def prefixEnd_1224510 : Nat := 4983230072969 + 3 ^ 40 * 1224510 * 2
def baseEnd_1224510 : Nat := 419174797491406221795725

theorem tailTrace_1224510 : CollatzResearch.WordTrace tailWord_1224510 prefixEnd_1224510 419174797491406221795725 := by
  unfold tailWord_1224510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5582693599227109312930873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29774365862544583002297989 5582693599227109312930873)
  ·
    refine ⟨4187020199420331984698155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5582693599227109312930873 4187020199420331984698155)
    ·
      refine ⟨6280530299130497977047233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4187020199420331984698155 6280530299130497977047233)
      ·
        refine ⟨4710397724347873482785425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6280530299130497977047233 4710397724347873482785425)
        ·
          refine ⟨3532798293260905112089069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4710397724347873482785425 3532798293260905112089069)
          ·
            refine ⟨1324799359972839417033401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3532798293260905112089069 1324799359972839417033401)
            ·
              refine ⟨993599519979629562775051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1324799359972839417033401 993599519979629562775051)
              ·
                refine ⟨1490399279969444344162577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 993599519979629562775051 1490399279969444344162577)
                ·
                  refine ⟨1117799459977083258121933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1490399279969444344162577 1117799459977083258121933)
                  ·
                    refine ⟨419174797491406221795725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1117799459977083258121933 419174797491406221795725)
                    ·
                      rfl

theorem cell22_1224510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_1224510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224510 prefixEnd_1224510 := by exact prefixLift 1224510
  have htrace : WordTrace (prefixWord ++ tailWord_1224510) baseStart_1224510 baseEnd_1224510 := by
    simpa [prefixWord, tailWord_1224510, baseEnd_1224510] using wordTrace_append hprefix tailTrace_1224510
  have hstable : (prefixWord ++ tailWord_1224510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224510).length < 2 ^ (prefixWord ++ tailWord_1224510).sum := by decide
  have hdescent : baseEnd_1224510 < baseStart_1224510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224579 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 6]
def baseStart_1224579 : Nat := 118140960795 + 1224579 * 2 ^ 59
def prefixEnd_1224579 : Nat := 4983230072969 + 3 ^ 40 * 1224579 * 2
def baseEnd_1224579 : Nat := 139732805867171013940171

theorem tailTrace_1224579 : CollatzResearch.WordTrace tailWord_1224579 prefixEnd_1224579 139732805867171013940171 := by
  unfold tailWord_1224579
  simp only [CollatzResearch.WordTrace]
  refine ⟨44664065430566899287708791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29776043620377932858472527 44664065430566899287708791)
  ·
    refine ⟨66996098145850348931563187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44664065430566899287708791 66996098145850348931563187)
    ·
      refine ⟨100494147218775523397344781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66996098145850348931563187 100494147218775523397344781)
      ·
        refine ⟨37685305207040821274004293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100494147218775523397344781 37685305207040821274004293)
        ·
          refine ⟨7065994726320153988875805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37685305207040821274004293 7065994726320153988875805)
          ·
            refine ⟨2649748022370057745828427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7065994726320153988875805 2649748022370057745828427)
            ·
              refine ⟨3974622033555086618742641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649748022370057745828427 3974622033555086618742641)
              ·
                refine ⟨2980966525166314964056981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3974622033555086618742641 2980966525166314964056981)
                ·
                  refine ⟨139732805867171013940171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2980966525166314964056981 139732805867171013940171)
                  ·
                    rfl

theorem cell22_1224579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 6].length) (baseStart_1224579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224579 prefixEnd_1224579 := by exact prefixLift 1224579
  have htrace : WordTrace (prefixWord ++ tailWord_1224579) baseStart_1224579 baseEnd_1224579 := by
    simpa [prefixWord, tailWord_1224579, baseEnd_1224579] using wordTrace_append hprefix tailTrace_1224579
  have hstable : (prefixWord ++ tailWord_1224579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224579).length < 2 ^ (prefixWord ++ tailWord_1224579).sum := by decide
  have hdescent : baseEnd_1224579 < baseStart_1224579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224658 : List Nat := [3, 2, 2, 3, 3, 1, 8]
def baseStart_1224658 : Nat := 118140960795 + 1224658 * 2 ^ 59
def prefixEnd_1224658 : Nat := 4983230072969 + 3 ^ 40 * 1224658 * 2
def baseEnd_1224658 : Nat := 15526868922814191447973

theorem tailTrace_1224658 : CollatzResearch.WordTrace tailWord_1224658 prefixEnd_1224658 15526868922814191447973 := by
  unfold tailWord_1224658
  simp only [CollatzResearch.WordTrace]
  refine ⟨11166736699320173944958657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29777964531520463853223085 11166736699320173944958657)
  ·
    refine ⟨8375052524490130458718993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11166736699320173944958657 8375052524490130458718993)
    ·
      refine ⟨6281289393367597844039245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8375052524490130458718993 6281289393367597844039245)
      ·
        refine ⟨2355483522512849191514717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6281289393367597844039245 2355483522512849191514717)
        ·
          refine ⟨883306320942318446818019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2355483522512849191514717 883306320942318446818019)
          ·
            refine ⟨1324959481413477670227029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883306320942318446818019 1324959481413477670227029)
            ·
              refine ⟨15526868922814191447973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1324959481413477670227029 15526868922814191447973)
              ·
                rfl

theorem cell22_1224658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 8].length) (baseStart_1224658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224658 prefixEnd_1224658 := by exact prefixLift 1224658
  have htrace : WordTrace (prefixWord ++ tailWord_1224658) baseStart_1224658 baseEnd_1224658 := by
    simpa [prefixWord, tailWord_1224658, baseEnd_1224658] using wordTrace_append hprefix tailTrace_1224658
  have hstable : (prefixWord ++ tailWord_1224658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224658).length < 2 ^ (prefixWord ++ tailWord_1224658).sum := by decide
  have hdescent : baseEnd_1224658 < baseStart_1224658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224673 : List Nat := [1, 2, 3, 1, 2, 1, 2, 6, 1, 3]
def baseStart_1224673 : Nat := 118140960795 + 1224673 * 2 ^ 59
def prefixEnd_1224673 : Nat := 4983230072969 + 3 ^ 40 * 1224673 * 2
def baseEnd_1224673 : Nat := 419230595722528129970225

theorem tailTrace_1224673 : CollatzResearch.WordTrace tailWord_1224673 prefixEnd_1224673 419230595722528129970225 := by
  unfold tailWord_1224673
  simp only [CollatzResearch.WordTrace]
  refine ⟨44667493892226353341630673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29778329261484235561087115 44667493892226353341630673)
  ·
    refine ⟨33500620419169765006223005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44667493892226353341630673 33500620419169765006223005)
    ·
      refine ⟨12562732657188661877333627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33500620419169765006223005 12562732657188661877333627)
      ·
        refine ⟨18844098985782992816000441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12562732657188661877333627 18844098985782992816000441)
        ·
          refine ⟨14133074239337244612000331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18844098985782992816000441 14133074239337244612000331)
          ·
            refine ⟨21199611359005866918000497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14133074239337244612000331 21199611359005866918000497)
            ·
              refine ⟨15899708519254400188500373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21199611359005866918000497 15899708519254400188500373)
              ·
                refine ⟨745298836840050008835955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15899708519254400188500373 745298836840050008835955)
                ·
                  refine ⟨1117948255260075013253933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745298836840050008835955 1117948255260075013253933)
                  ·
                    refine ⟨419230595722528129970225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1117948255260075013253933 419230595722528129970225)
                    ·
                      rfl

theorem cell22_1224673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_1224673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224673 prefixEnd_1224673 := by exact prefixLift 1224673
  have htrace : WordTrace (prefixWord ++ tailWord_1224673) baseStart_1224673 baseEnd_1224673 := by
    simpa [prefixWord, tailWord_1224673, baseEnd_1224673] using wordTrace_append hprefix tailTrace_1224673
  have hstable : (prefixWord ++ tailWord_1224673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224673).length < 2 ^ (prefixWord ++ tailWord_1224673).sum := by decide
  have hdescent : baseEnd_1224673 < baseStart_1224673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224684 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_1224684 : Nat := 118140960795 + 1224684 * 2 ^ 59
def prefixEnd_1224684 : Nat := 4983230072969 + 3 ^ 40 * 1224684 * 2
def baseEnd_1224684 : Nat := 419234361247327767945191

theorem tailTrace_1224684 : CollatzResearch.WordTrace tailWord_1224684 prefixEnd_1224684 419234361247327767945191 := by
  unfold tailWord_1224684
  simp only [CollatzResearch.WordTrace]
  refine ⟨22333947547593251110140553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29778596730124334813520737 22333947547593251110140553)
  ·
    refine ⟨16750460660694938332605415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22333947547593251110140553 16750460660694938332605415)
    ·
      refine ⟨25125690991042407498908123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16750460660694938332605415 25125690991042407498908123)
      ·
        refine ⟨37688536486563611248362185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25125690991042407498908123 37688536486563611248362185)
        ·
          refine ⟨28266402364922708436271639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37688536486563611248362185 28266402364922708436271639)
          ·
            refine ⟨42399603547384062654407459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28266402364922708436271639 42399603547384062654407459)
            ·
              refine ⟨63599405321076093981611189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42399603547384062654407459 63599405321076093981611189)
              ·
                refine ⟨5962444248850883810776049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63599405321076093981611189 5962444248850883810776049)
                ·
                  refine ⟨4471833186638162858082037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5962444248850883810776049 4471833186638162858082037)
                  ·
                    refine ⟨419234361247327767945191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4471833186638162858082037 419234361247327767945191)
                    ·
                      rfl

theorem cell22_1224684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_1224684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224684 prefixEnd_1224684 := by exact prefixLift 1224684
  have htrace : WordTrace (prefixWord ++ tailWord_1224684) baseStart_1224684 baseEnd_1224684 := by
    simpa [prefixWord, tailWord_1224684, baseEnd_1224684] using wordTrace_append hprefix tailTrace_1224684
  have hstable : (prefixWord ++ tailWord_1224684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224684).length < 2 ^ (prefixWord ++ tailWord_1224684).sum := by decide
  have hdescent : baseEnd_1224684 < baseStart_1224684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224724 : List Nat := [2, 4, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1224724 : Nat := 118140960795 + 1224724 * 2 ^ 59
def prefixEnd_1224724 : Nat := 4983230072969 + 3 ^ 40 * 1224724 * 2
def baseEnd_1224724 : Nat := 419248054064780996945069

theorem tailTrace_1224724 : CollatzResearch.WordTrace tailWord_1224724 prefixEnd_1224724 419248054064780996945069 := by
  unfold tailWord_1224724
  simp only [CollatzResearch.WordTrace]
  refine ⟨22334677007520794525868613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29779569343361059367824817 22334677007520794525868613)
  ·
    refine ⟨4187751938910148973600365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22334677007520794525868613 4187751938910148973600365)
    ·
      refine ⟨1570406977091305865100137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4187751938910148973600365 1570406977091305865100137)
      ·
        refine ⟨1177805232818479398825103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1570406977091305865100137 1177805232818479398825103)
        ·
          refine ⟨1766707849227719098237655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1177805232818479398825103 1766707849227719098237655)
          ·
            refine ⟨2650061773841578647356483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766707849227719098237655 2650061773841578647356483)
            ·
              refine ⟨3975092660762367971034725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2650061773841578647356483 3975092660762367971034725)
              ·
                refine ⟨745329873892943994569011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3975092660762367971034725 745329873892943994569011)
                ·
                  refine ⟨1117994810839415991853517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745329873892943994569011 1117994810839415991853517)
                  ·
                    refine ⟨419248054064780996945069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1117994810839415991853517 419248054064780996945069)
                    ·
                      rfl

theorem cell22_1224724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1224724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224724 prefixEnd_1224724 := by exact prefixLift 1224724
  have htrace : WordTrace (prefixWord ++ tailWord_1224724) baseStart_1224724 baseEnd_1224724 := by
    simpa [prefixWord, tailWord_1224724, baseEnd_1224724] using wordTrace_append hprefix tailTrace_1224724
  have hstable : (prefixWord ++ tailWord_1224724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224724).length < 2 ^ (prefixWord ++ tailWord_1224724).sum := by decide
  have hdescent : baseEnd_1224724 < baseStart_1224724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224729 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 5, 5]
def baseStart_1224729 : Nat := 118140960795 + 1224729 * 2 ^ 59
def prefixEnd_1224729 : Nat := 4983230072969 + 3 ^ 40 * 1224729 * 2
def baseEnd_1224729 : Nat := 419249765666962650570053

theorem tailTrace_1224729 : CollatzResearch.WordTrace tailWord_1224729 prefixEnd_1224729 419249765666962650570053 := by
  unfold tailWord_1224729
  simp only [CollatzResearch.WordTrace]
  refine ⟨44669536380023474905669241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29779690920015649937112827 44669536380023474905669241)
  ·
    refine ⟨33502152285017606179251931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44669536380023474905669241 33502152285017606179251931)
    ·
      refine ⟨50253228427526409268877897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33502152285017606179251931 50253228427526409268877897)
      ·
        refine ⟨37689921320644806951658423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50253228427526409268877897 37689921320644806951658423)
        ·
          refine ⟨56534881980967210427487635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37689921320644806951658423 56534881980967210427487635)
          ·
            refine ⟨84802322971450815641231453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56534881980967210427487635 84802322971450815641231453)
            ·
              refine ⟨31800871114294055865461795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84802322971450815641231453 31800871114294055865461795)
              ·
                refine ⟨47701306671441083798192693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31800871114294055865461795 47701306671441083798192693)
                ·
                  refine ⟨4471997500447601606080565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47701306671441083798192693 4471997500447601606080565)
                  ·
                    refine ⟨419249765666962650570053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4471997500447601606080565 419249765666962650570053)
                    ·
                      rfl

theorem cell22_1224729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_1224729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224729 prefixEnd_1224729 := by exact prefixLift 1224729
  have htrace : WordTrace (prefixWord ++ tailWord_1224729) baseStart_1224729 baseEnd_1224729 := by
    simpa [prefixWord, tailWord_1224729, baseEnd_1224729] using wordTrace_append hprefix tailTrace_1224729
  have hstable : (prefixWord ++ tailWord_1224729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224729).length < 2 ^ (prefixWord ++ tailWord_1224729).sum := by decide
  have hdescent : baseEnd_1224729 < baseStart_1224729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224759 : List Nat := [1, 1, 3, 1, 2, 2, 2, 10]
def baseStart_1224759 : Nat := 118140960795 + 1224759 * 2 ^ 59
def prefixEnd_1224759 : Nat := 4983230072969 + 3 ^ 40 * 1224759 * 2
def baseEnd_1224759 : Nat := 46584448364450285813329

theorem tailTrace_1224759 : CollatzResearch.WordTrace tailWord_1224759 prefixEnd_1224759 46584448364450285813329 := by
  unfold tailWord_1224759
  simp only [CollatzResearch.WordTrace]
  refine ⟨44670630569914790029261331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29780420379943193352840887 44670630569914790029261331)
  ·
    refine ⟨67005945854872185043891997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44670630569914790029261331 67005945854872185043891997)
    ·
      refine ⟨25127229695577069391459499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67005945854872185043891997 25127229695577069391459499)
      ·
        refine ⟨37690844543365604087189249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25127229695577069391459499 37690844543365604087189249)
        ·
          refine ⟨28268133407524203065391937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37690844543365604087189249 28268133407524203065391937)
          ·
            refine ⟨21201100055643152299043953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28268133407524203065391937 21201100055643152299043953)
            ·
              refine ⟨15900825041732364224282965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21201100055643152299043953 15900825041732364224282965)
              ·
                refine ⟨46584448364450285813329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15900825041732364224282965 46584448364450285813329)
                ·
                  rfl

theorem cell22_1224759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 10].length) (baseStart_1224759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224759 prefixEnd_1224759 := by exact prefixLift 1224759
  have htrace : WordTrace (prefixWord ++ tailWord_1224759) baseStart_1224759 baseEnd_1224759 := by
    simpa [prefixWord, tailWord_1224759, baseEnd_1224759] using wordTrace_append hprefix tailTrace_1224759
  have hstable : (prefixWord ++ tailWord_1224759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224759).length < 2 ^ (prefixWord ++ tailWord_1224759).sum := by decide
  have hdescent : baseEnd_1224759 < baseStart_1224759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224810 : List Nat := [3, 1, 3, 2, 3, 2, 2, 6]
def baseStart_1224810 : Nat := 118140960795 + 1224810 * 2 ^ 59
def prefixEnd_1224810 : Nat := 4983230072969 + 3 ^ 40 * 1224810 * 2
def baseEnd_1224810 : Nat := 46586388180256159921645

theorem tailTrace_1224810 : CollatzResearch.WordTrace tailWord_1224810 prefixEnd_1224810 46586388180256159921645 := by
  unfold tailWord_1224810
  simp only [CollatzResearch.WordTrace]
  refine ⟨11168122673182506434841971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29781660461820017159578589 11168122673182506434841971)
  ·
    refine ⟨16752184009773759652262957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11168122673182506434841971 16752184009773759652262957)
    ·
      refine ⟨6282069003665159869598609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16752184009773759652262957 6282069003665159869598609)
      ·
        refine ⟨4711551752748869902198957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6282069003665159869598609 4711551752748869902198957)
        ·
          refine ⟨1766831907280826213324609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4711551752748869902198957 1766831907280826213324609)
          ·
            refine ⟨1325123930460619659993457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1766831907280826213324609 1325123930460619659993457)
            ·
              refine ⟨993842947845464744995093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1325123930460619659993457 993842947845464744995093)
              ·
                refine ⟨46586388180256159921645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 993842947845464744995093 46586388180256159921645)
                ·
                  rfl

theorem cell22_1224810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 6].length) (baseStart_1224810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224810 prefixEnd_1224810 := by exact prefixLift 1224810
  have htrace : WordTrace (prefixWord ++ tailWord_1224810) baseStart_1224810 baseEnd_1224810 := by
    simpa [prefixWord, tailWord_1224810, baseEnd_1224810] using wordTrace_append hprefix tailTrace_1224810
  have hstable : (prefixWord ++ tailWord_1224810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224810).length < 2 ^ (prefixWord ++ tailWord_1224810).sum := by decide
  have hdescent : baseEnd_1224810 < baseStart_1224810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224851 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 3, 4]
def baseStart_1224851 : Nat := 118140960795 + 1224851 * 2 ^ 59
def prefixEnd_1224851 : Nat := 4983230072969 + 3 ^ 40 * 1224851 * 2
def baseEnd_1224851 : Nat := 419291528760194999019679

theorem tailTrace_1224851 : CollatzResearch.WordTrace tailWord_1224851 prefixEnd_1224851 419291528760194999019679 := by
  unfold tailWord_1224851
  simp only [CollatzResearch.WordTrace]
  refine ⟨44673986085581489741610407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29782657390387659827740271 44673986085581489741610407)
  ·
    refine ⟨67010979128372234612415611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44673986085581489741610407 67010979128372234612415611)
    ·
      refine ⟨100516468692558351918623417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67010979128372234612415611 100516468692558351918623417)
      ·
        refine ⟨75387351519418763938967563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100516468692558351918623417 75387351519418763938967563)
        ·
          refine ⟨113081027279128145908451345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75387351519418763938967563 113081027279128145908451345)
          ·
            refine ⟨84810770459346109431338509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113081027279128145908451345 84810770459346109431338509)
            ·
              refine ⟨31804038922254791036751941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84810770459346109431338509 31804038922254791036751941)
              ·
                refine ⟨5963257297922773319390989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31804038922254791036751941 5963257297922773319390989)
                ·
                  refine ⟨2236221486721039994771621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5963257297922773319390989 2236221486721039994771621)
                  ·
                    refine ⟨419291528760194999019679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2236221486721039994771621 419291528760194999019679)
                    ·
                      rfl

theorem cell22_1224851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 4].length) (baseStart_1224851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224851 prefixEnd_1224851 := by exact prefixLift 1224851
  have htrace : WordTrace (prefixWord ++ tailWord_1224851) baseStart_1224851 baseEnd_1224851 := by
    simpa [prefixWord, tailWord_1224851, baseEnd_1224851] using wordTrace_append hprefix tailTrace_1224851
  have hstable : (prefixWord ++ tailWord_1224851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224851).length < 2 ^ (prefixWord ++ tailWord_1224851).sum := by decide
  have hdescent : baseEnd_1224851 < baseStart_1224851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224883 : List Nat := [1, 1, 1, 2, 3, 2, 1, 7, 4]
def baseStart_1224883 : Nat := 118140960795 + 1224883 * 2 ^ 59
def prefixEnd_1224883 : Nat := 4983230072969 + 3 ^ 40 * 1224883 * 2
def baseEnd_1224883 : Nat := 139767494338052527406527

theorem tailTrace_1224883 : CollatzResearch.WordTrace tailWord_1224883 prefixEnd_1224883 139767494338052527406527 := by
  unfold tailWord_1224883
  simp only [CollatzResearch.WordTrace]
  refine ⟨44675153221465559206775303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29783435480977039471183535 44675153221465559206775303)
  ·
    refine ⟨67012729832198338810162955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44675153221465559206775303 67012729832198338810162955)
    ·
      refine ⟨100519094748297508215244433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67012729832198338810162955 100519094748297508215244433)
      ·
        refine ⟨75389321061223131161433325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100519094748297508215244433 75389321061223131161433325)
        ·
          refine ⟨28270995397958674185537497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75389321061223131161433325 28270995397958674185537497)
          ·
            refine ⟨21203246548469005639153123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28270995397958674185537497 21203246548469005639153123)
            ·
              refine ⟨31804869822703508458729685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21203246548469005639153123 31804869822703508458729685)
              ·
                refine ⟨745426636469613479501477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31804869822703508458729685 745426636469613479501477)
                ·
                  refine ⟨139767494338052527406527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 745426636469613479501477 139767494338052527406527)
                  ·
                    rfl

theorem cell22_1224883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 7, 4].length) (baseStart_1224883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224883 prefixEnd_1224883 := by exact prefixLift 1224883
  have htrace : WordTrace (prefixWord ++ tailWord_1224883) baseStart_1224883 baseEnd_1224883 := by
    simpa [prefixWord, tailWord_1224883, baseEnd_1224883] using wordTrace_append hprefix tailTrace_1224883
  have hstable : (prefixWord ++ tailWord_1224883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224883).length < 2 ^ (prefixWord ++ tailWord_1224883).sum := by decide
  have hdescent : baseEnd_1224883 < baseStart_1224883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224928 : List Nat := [2, 1, 1, 3, 1, 3, 5, 6]
def baseStart_1224928 : Nat := 118140960795 + 1224928 * 2 ^ 59
def prefixEnd_1224928 : Nat := 4983230072969 + 3 ^ 40 * 1224928 * 2
def baseEnd_1224928 : Nat := 46590876381532496093827

theorem tailTrace_1224928 : CollatzResearch.WordTrace tailWord_1224928 prefixEnd_1224928 46590876381532496093827 := by
  unfold tailWord_1224928
  simp only [CollatzResearch.WordTrace]
  refine ⟨22338397253151265946081719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29784529670868354594775625 22338397253151265946081719)
  ·
    refine ⟨33507595879726898919122579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22338397253151265946081719 33507595879726898919122579)
    ·
      refine ⟨50261393819590348378683869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33507595879726898919122579 50261393819590348378683869)
      ·
        refine ⟨18848022682346380642006451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50261393819590348378683869 18848022682346380642006451)
        ·
          refine ⟨28272034023519570963009677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18848022682346380642006451 28272034023519570963009677)
          ·
            refine ⟨10602012758819839111128629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28272034023519570963009677 10602012758819839111128629)
            ·
              refine ⟨993938696139359916668309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10602012758819839111128629 993938696139359916668309)
              ·
                refine ⟨46590876381532496093827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 993938696139359916668309 46590876381532496093827)
                ·
                  rfl

theorem cell22_1224928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 6].length) (baseStart_1224928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224928 prefixEnd_1224928 := by exact prefixLift 1224928
  have htrace : WordTrace (prefixWord ++ tailWord_1224928) baseStart_1224928 baseEnd_1224928 := by
    simpa [prefixWord, tailWord_1224928, baseEnd_1224928] using wordTrace_append hprefix tailTrace_1224928
  have hstable : (prefixWord ++ tailWord_1224928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224928).length < 2 ^ (prefixWord ++ tailWord_1224928).sum := by decide
  have hdescent : baseEnd_1224928 < baseStart_1224928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224994 : List Nat := [3, 3, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_1224994 : Nat := 118140960795 + 1224994 * 2 ^ 59
def prefixEnd_1224994 : Nat := 4983230072969 + 3 ^ 40 * 1224994 * 2
def baseEnd_1224994 : Nat := 419340480582590292694241

theorem tailTrace_1224994 : CollatzResearch.WordTrace tailWord_1224994 prefixEnd_1224994 419340480582590292694241 := by
  unfold tailWord_1224994
  simp only [CollatzResearch.WordTrace]
  refine ⟨11169800431015856291016509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29786134482708950109377357 11169800431015856291016509)
  ·
    refine ⟨4188675161630946109131191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11169800431015856291016509 4188675161630946109131191)
    ·
      refine ⟨6283012742446419163696787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4188675161630946109131191 6283012742446419163696787)
      ·
        refine ⟨9424519113669628745545181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6283012742446419163696787 9424519113669628745545181)
        ·
          refine ⟨3534194667626110779579443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9424519113669628745545181 3534194667626110779579443)
          ·
            refine ⟨5301292001439166169369165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534194667626110779579443 5301292001439166169369165)
            ·
              refine ⟨1987984500539687313513437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5301292001439166169369165 1987984500539687313513437)
              ·
                refine ⟨745494187702382742567539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1987984500539687313513437 745494187702382742567539)
                ·
                  refine ⟨1118241281553574113851309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745494187702382742567539 1118241281553574113851309)
                  ·
                    refine ⟨419340480582590292694241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1118241281553574113851309 419340480582590292694241)
                    ·
                      rfl

theorem cell22_1224994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_1224994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1224994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1224994 prefixEnd_1224994 := by exact prefixLift 1224994
  have htrace : WordTrace (prefixWord ++ tailWord_1224994) baseStart_1224994 baseEnd_1224994 := by
    simpa [prefixWord, tailWord_1224994, baseEnd_1224994] using wordTrace_append hprefix tailTrace_1224994
  have hstable : (prefixWord ++ tailWord_1224994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224994).length < 2 ^ (prefixWord ++ tailWord_1224994).sum := by decide
  have hdescent : baseEnd_1224994 < baseStart_1224994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225033 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 1, 5]
def baseStart_1225033 : Nat := 118140960795 + 1225033 * 2 ^ 59
def prefixEnd_1225033 : Nat := 4983230072969 + 3 ^ 40 * 1225033 * 2
def baseEnd_1225033 : Nat := 419353831079607190969121

theorem tailTrace_1225033 : CollatzResearch.WordTrace tailWord_1225033 prefixEnd_1225033 419353831079607190969121 := by
  unfold tailWord_1225033
  simp only [CollatzResearch.WordTrace]
  refine ⟨44680624170922134824735753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29787082780614756549823835 44680624170922134824735753)
  ·
    refine ⟨33510468128191601118551815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44680624170922134824735753 33510468128191601118551815)
    ·
      refine ⟨50265702192287401677827723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33510468128191601118551815 50265702192287401677827723)
      ·
        refine ⟨75398553288431102516741585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50265702192287401677827723 75398553288431102516741585)
        ·
          refine ⟨56548914966323326887556189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75398553288431102516741585 56548914966323326887556189)
          ·
            refine ⟨21205843112371247582833571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56548914966323326887556189 21205843112371247582833571)
            ·
              refine ⟨31808764668556871374250357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21205843112371247582833571 31808764668556871374250357)
              ·
                refine ⟨2982071687677206691335971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31808764668556871374250357 2982071687677206691335971)
                ·
                  refine ⟨4473107531515810037003957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2982071687677206691335971 4473107531515810037003957)
                  ·
                    refine ⟨419353831079607190969121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4473107531515810037003957 419353831079607190969121)
                    ·
                      rfl

theorem cell22_1225033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_1225033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225033 prefixEnd_1225033 := by exact prefixLift 1225033
  have htrace : WordTrace (prefixWord ++ tailWord_1225033) baseStart_1225033 baseEnd_1225033 := by
    simpa [prefixWord, tailWord_1225033, baseEnd_1225033] using wordTrace_append hprefix tailTrace_1225033
  have hstable : (prefixWord ++ tailWord_1225033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225033).length < 2 ^ (prefixWord ++ tailWord_1225033).sum := by decide
  have hdescent : baseEnd_1225033 < baseStart_1225033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225063 : List Nat := [1, 1, 5, 1, 3, 11]
def baseStart_1225063 : Nat := 118140960795 + 1225063 * 2 ^ 59
def prefixEnd_1225063 : Nat := 4983230072969 + 3 ^ 40 * 1225063 * 2
def baseEnd_1225063 : Nat := 5177334576453050774309

theorem tailTrace_1225063 : CollatzResearch.WordTrace tailWord_1225063 prefixEnd_1225063 5177334576453050774309 := by
  unfold tailWord_1225063
  simp only [CollatzResearch.WordTrace]
  refine ⟨44681718360813449948327843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29787812240542299965551895 44681718360813449948327843)
  ·
    refine ⟨67022577541220174922491765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44681718360813449948327843 67022577541220174922491765)
    ·
      refine ⟨6283366644489391398983603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67022577541220174922491765 6283366644489391398983603)
      ·
        refine ⟨9425049966734087098475405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6283366644489391398983603 9425049966734087098475405)
        ·
          refine ⟨3534393737525282661928277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9425049966734087098475405 3534393737525282661928277)
          ·
            refine ⟨5177334576453050774309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3534393737525282661928277 5177334576453050774309)
            ·
              rfl

theorem cell22_1225063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 11].length) (baseStart_1225063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225063 prefixEnd_1225063 := by exact prefixLift 1225063
  have htrace : WordTrace (prefixWord ++ tailWord_1225063) baseStart_1225063 baseEnd_1225063 := by
    simpa [prefixWord, tailWord_1225063, baseEnd_1225063] using wordTrace_append hprefix tailTrace_1225063
  have hstable : (prefixWord ++ tailWord_1225063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225063).length < 2 ^ (prefixWord ++ tailWord_1225063).sum := by decide
  have hdescent : baseEnd_1225063 < baseStart_1225063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225093 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_1225093 : Nat := 118140960795 + 1225093 * 2 ^ 59
def prefixEnd_1225093 : Nat := 4983230072969 + 3 ^ 40 * 1225093 * 2
def baseEnd_1225093 : Nat := 419374370305787034468937

theorem tailTrace_1225093 : CollatzResearch.WordTrace tailWord_1225093 prefixEnd_1225093 419374370305787034468937 := by
  unfold tailWord_1225093
  simp only [CollatzResearch.WordTrace]
  refine ⟨44682812550704765071919933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29788541700469843381279955 44682812550704765071919933)
  ·
    refine ⟨16756054706514286901969975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44682812550704765071919933 16756054706514286901969975)
    ·
      refine ⟨25134082059771430352954963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16756054706514286901969975 25134082059771430352954963)
      ·
        refine ⟨37701123089657145529432445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25134082059771430352954963 37701123089657145529432445)
        ·
          refine ⟨14137921158621429573537167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37701123089657145529432445 14137921158621429573537167)
          ·
            refine ⟨21206881737932144360305751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14137921158621429573537167 21206881737932144360305751)
            ·
              refine ⟨31810322606898216540458627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21206881737932144360305751 31810322606898216540458627)
              ·
                refine ⟨47715483910347324810687941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31810322606898216540458627 47715483910347324810687941)
                ·
                  refine ⟨8946653233190123402003989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47715483910347324810687941 8946653233190123402003989)
                  ·
                    refine ⟨419374370305787034468937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8946653233190123402003989 419374370305787034468937)
                    ·
                      rfl

theorem cell22_1225093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_1225093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225093 prefixEnd_1225093 := by exact prefixLift 1225093
  have htrace : WordTrace (prefixWord ++ tailWord_1225093) baseStart_1225093 baseEnd_1225093 := by
    simpa [prefixWord, tailWord_1225093, baseEnd_1225093] using wordTrace_append hprefix tailTrace_1225093
  have hstable : (prefixWord ++ tailWord_1225093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225093).length < 2 ^ (prefixWord ++ tailWord_1225093).sum := by decide
  have hdescent : baseEnd_1225093 < baseStart_1225093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225200 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 4, 4]
def baseStart_1225200 : Nat := 118140960795 + 1225200 * 2 ^ 59
def prefixEnd_1225200 : Nat := 4983230072969 + 3 ^ 40 * 1225200 * 2
def baseEnd_1225200 : Nat := 419410998592474422043609

theorem tailTrace_1225200 : CollatzResearch.WordTrace tailWord_1225200 prefixEnd_1225200 419410998592474422043609 := by
  unfold tailWord_1225200
  simp only [CollatzResearch.WordTrace]
  refine ⟨22343357580658561173032527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29791143440878081564043369 22343357580658561173032527)
  ·
    refine ⟨33515036370987841759548791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22343357580658561173032527 33515036370987841759548791)
    ·
      refine ⟨50272554556481762639323187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33515036370987841759548791 50272554556481762639323187)
      ·
        refine ⟨75408831834722643958984781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50272554556481762639323187 75408831834722643958984781)
        ·
          refine ⟨28278311938020991484619293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75408831834722643958984781 28278311938020991484619293)
          ·
            refine ⟨10604366976757871806732235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28278311938020991484619293 10604366976757871806732235)
            ·
              refine ⟨15906550465136807710098353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10604366976757871806732235 15906550465136807710098353)
              ·
                refine ⟨11929912848852605782573765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15906550465136807710098353 11929912848852605782573765)
                ·
                  refine ⟨2236858659159863584232581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11929912848852605782573765 2236858659159863584232581)
                  ·
                    refine ⟨419410998592474422043609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2236858659159863584232581 419410998592474422043609)
                    ·
                      rfl

theorem cell22_1225200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_1225200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225200 prefixEnd_1225200 := by exact prefixLift 1225200
  have htrace : WordTrace (prefixWord ++ tailWord_1225200) baseStart_1225200 baseEnd_1225200 := by
    simpa [prefixWord, tailWord_1225200, baseEnd_1225200] using wordTrace_append hprefix tailTrace_1225200
  have hstable : (prefixWord ++ tailWord_1225200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225200).length < 2 ^ (prefixWord ++ tailWord_1225200).sum := by decide
  have hdescent : baseEnd_1225200 < baseStart_1225200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225217 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 2, 4]
def baseStart_1225217 : Nat := 118140960795 + 1225217 * 2 ^ 59
def prefixEnd_1225217 : Nat := 4983230072969 + 3 ^ 40 * 1225217 * 2
def baseEnd_1225217 : Nat := 419416818039892044368557

theorem tailTrace_1225217 : CollatzResearch.WordTrace tailWord_1225217 prefixEnd_1225217 419416818039892044368557 := by
  unfold tailWord_1225217
  simp only [CollatzResearch.WordTrace]
  refine ⟨44687335202255534249433905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29791556801503689499622603 44687335202255534249433905)
  ·
    refine ⟨33515501401691650687075429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44687335202255534249433905 33515501401691650687075429)
    ·
      refine ⟨6284156512817184503826643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33515501401691650687075429 6284156512817184503826643)
      ·
        refine ⟨9426234769225776755739965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6284156512817184503826643 9426234769225776755739965)
        ·
          refine ⟨3534838038459666283402487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9426234769225776755739965 3534838038459666283402487)
          ·
            refine ⟨5302257057689499425103731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534838038459666283402487 5302257057689499425103731)
            ·
              refine ⟨7953385586534249137655597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5302257057689499425103731 7953385586534249137655597)
              ·
                refine ⟨2982519594950343426620849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7953385586534249137655597 2982519594950343426620849)
                ·
                  refine ⟨2236889696212757569965637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2982519594950343426620849 2236889696212757569965637)
                  ·
                    refine ⟨419416818039892044368557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2236889696212757569965637 419416818039892044368557)
                    ·
                      rfl

theorem cell22_1225217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_1225217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225217 prefixEnd_1225217 := by exact prefixLift 1225217
  have htrace : WordTrace (prefixWord ++ tailWord_1225217) baseStart_1225217 baseEnd_1225217 := by
    simpa [prefixWord, tailWord_1225217, baseEnd_1225217] using wordTrace_append hprefix tailTrace_1225217
  have hstable : (prefixWord ++ tailWord_1225217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225217).length < 2 ^ (prefixWord ++ tailWord_1225217).sum := by decide
  have hdescent : baseEnd_1225217 < baseStart_1225217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225236 : List Nat := [2, 4, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1225236 : Nat := 118140960795 + 1225236 * 2 ^ 59
def prefixEnd_1225236 : Nat := 4983230072969 + 3 ^ 40 * 1225236 * 2
def baseEnd_1225236 : Nat := 419423322128182328143499

theorem tailTrace_1225236 : CollatzResearch.WordTrace tailWord_1225236 prefixEnd_1225236 419423322128182328143499 := by
  unfold tailWord_1225236
  simp only [CollatzResearch.WordTrace]
  refine ⟨22344014094593350247187781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29792018792791133662917041 22344014094593350247187781)
  ·
    refine ⟨4189502642736253171347709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22344014094593350247187781 4189502642736253171347709)
    ·
      refine ⟨1571063491026094939255391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4189502642736253171347709 1571063491026094939255391)
      ·
        refine ⟨2356595236539142408883087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1571063491026094939255391 2356595236539142408883087)
        ·
          refine ⟨3534892854808713613324631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356595236539142408883087 3534892854808713613324631)
          ·
            refine ⟨5302339282213070419986947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534892854808713613324631 5302339282213070419986947)
            ·
              refine ⟨7953508923319605629980421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5302339282213070419986947 7953508923319605629980421)
              ·
                refine ⟨1491282923122426055621329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7953508923319605629980421 1491282923122426055621329)
                ·
                  refine ⟨1118462192341819541715997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1491282923122426055621329 1118462192341819541715997)
                  ·
                    refine ⟨419423322128182328143499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1118462192341819541715997 419423322128182328143499)
                    ·
                      rfl

theorem cell22_1225236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1225236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225236 prefixEnd_1225236 := by exact prefixLift 1225236
  have htrace : WordTrace (prefixWord ++ tailWord_1225236) baseStart_1225236 baseEnd_1225236 := by
    simpa [prefixWord, tailWord_1225236, baseEnd_1225236] using wordTrace_append hprefix tailTrace_1225236
  have hstable : (prefixWord ++ tailWord_1225236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225236).length < 2 ^ (prefixWord ++ tailWord_1225236).sum := by decide
  have hdescent : baseEnd_1225236 < baseStart_1225236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225247 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 3, 3]
def baseStart_1225247 : Nat := 118140960795 + 1225247 * 2 ^ 59
def prefixEnd_1225247 : Nat := 4983230072969 + 3 ^ 40 * 1225247 * 2
def baseEnd_1225247 : Nat := 419427087652981966118465

theorem tailTrace_1225247 : CollatzResearch.WordTrace tailWord_1225247 prefixEnd_1225247 419427087652981966118465 := by
  unfold tailWord_1225247
  simp only [CollatzResearch.WordTrace]
  refine ⟨44688429392146849373025995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29792286261431232915350663 44688429392146849373025995)
  ·
    refine ⟨67032644088220274059538993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44688429392146849373025995 67032644088220274059538993)
    ·
      refine ⟨50274483066165205544654245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67032644088220274059538993 50274483066165205544654245)
      ·
        refine ⟨9426465574905976039622671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50274483066165205544654245 9426465574905976039622671)
        ·
          refine ⟨14139698362358964059434007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9426465574905976039622671 14139698362358964059434007)
          ·
            refine ⟨21209547543538446089151011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14139698362358964059434007 21209547543538446089151011)
            ·
              refine ⟨31814321315307669133726517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21209547543538446089151011 31814321315307669133726517)
              ·
                refine ⟨2982592623310093981286861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31814321315307669133726517 2982592623310093981286861)
                ·
                  refine ⟨1118472233741285242982573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2982592623310093981286861 1118472233741285242982573)
                  ·
                    refine ⟨419427087652981966118465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1118472233741285242982573 419427087652981966118465)
                    ·
                      rfl

theorem cell22_1225247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 3].length) (baseStart_1225247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225247 prefixEnd_1225247 := by exact prefixLift 1225247
  have htrace : WordTrace (prefixWord ++ tailWord_1225247) baseStart_1225247 baseEnd_1225247 := by
    simpa [prefixWord, tailWord_1225247, baseEnd_1225247] using wordTrace_append hprefix tailTrace_1225247
  have hstable : (prefixWord ++ tailWord_1225247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225247).length < 2 ^ (prefixWord ++ tailWord_1225247).sum := by decide
  have hdescent : baseEnd_1225247 < baseStart_1225247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225268 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_1225268 : Nat := 118140960795 + 1225268 * 2 ^ 59
def prefixEnd_1225268 : Nat := 4983230072969 + 3 ^ 40 * 1225268 * 2
def baseEnd_1225268 : Nat := 419434276382144911343401

theorem tailTrace_1225268 : CollatzResearch.WordTrace tailWord_1225268 prefixEnd_1225268 419434276382144911343401 := by
  unfold tailWord_1225268
  simp only [CollatzResearch.WordTrace]
  refine ⟨22344597662535384979770229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29792796883380513306360305 22344597662535384979770229)
  ·
    refine ⟨2094806030862692341853459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22344597662535384979770229 2094806030862692341853459)
    ·
      refine ⟨3142209046294038512780189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2094806030862692341853459 3142209046294038512780189)
      ·
        refine ⟨1178328392360264442292571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3142209046294038512780189 1178328392360264442292571)
        ·
          refine ⟨1767492588540396663438857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1178328392360264442292571 1767492588540396663438857)
          ·
            refine ⟨1325619441405297497579143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1767492588540396663438857 1325619441405297497579143)
            ·
              refine ⟨1988429162107946246368715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1325619441405297497579143 1988429162107946246368715)
              ·
                refine ⟨2982643743161919369553073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1988429162107946246368715 2982643743161919369553073)
                ·
                  refine ⟨2236982807371439527164805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2982643743161919369553073 2236982807371439527164805)
                  ·
                    refine ⟨419434276382144911343401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2236982807371439527164805 419434276382144911343401)
                    ·
                      rfl

theorem cell22_1225268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_1225268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225268 prefixEnd_1225268 := by exact prefixLift 1225268
  have htrace : WordTrace (prefixWord ++ tailWord_1225268) baseStart_1225268 baseEnd_1225268 := by
    simpa [prefixWord, tailWord_1225268, baseEnd_1225268] using wordTrace_append hprefix tailTrace_1225268
  have hstable : (prefixWord ++ tailWord_1225268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225268).length < 2 ^ (prefixWord ++ tailWord_1225268).sum := by decide
  have hdescent : baseEnd_1225268 < baseStart_1225268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225281 : List Nat := [1, 2, 5, 1, 1, 2, 1, 5, 1, 3]
def baseStart_1225281 : Nat := 118140960795 + 1225281 * 2 ^ 59
def prefixEnd_1225281 : Nat := 4983230072969 + 3 ^ 40 * 1225281 * 2
def baseEnd_1225281 : Nat := 419438726547817210768361

theorem tailTrace_1225281 : CollatzResearch.WordTrace tailWord_1225281 prefixEnd_1225281 419438726547817210768361 := by
  unfold tailWord_1225281
  simp only [CollatzResearch.WordTrace]
  refine ⟨44689669474023673179763697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29793112982682448786509131 44689669474023673179763697)
  ·
    refine ⟨33517252105517754884822773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44689669474023673179763697 33517252105517754884822773)
    ·
      refine ⟨3142242384892289520452135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33517252105517754884822773 3142242384892289520452135)
      ·
        refine ⟨4713363577338434280678203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3142242384892289520452135 4713363577338434280678203)
        ·
          refine ⟨7070045366007651421017305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4713363577338434280678203 7070045366007651421017305)
          ·
            refine ⟨5302534024505738565762979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7070045366007651421017305 5302534024505738565762979)
            ·
              refine ⟨7953801036758607848644469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5302534024505738565762979 7953801036758607848644469)
              ·
                refine ⟨745668847196119485810419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7953801036758607848644469 745668847196119485810419)
                ·
                  refine ⟨1118503270794179228715629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745668847196119485810419 1118503270794179228715629)
                  ·
                    refine ⟨419438726547817210768361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1118503270794179228715629 419438726547817210768361)
                    ·
                      rfl

theorem cell22_1225281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_1225281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225281 prefixEnd_1225281 := by exact prefixLift 1225281
  have htrace : WordTrace (prefixWord ++ tailWord_1225281) baseStart_1225281 baseEnd_1225281 := by
    simpa [prefixWord, tailWord_1225281, baseEnd_1225281] using wordTrace_append hprefix tailTrace_1225281
  have hstable : (prefixWord ++ tailWord_1225281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225281).length < 2 ^ (prefixWord ++ tailWord_1225281).sum := by decide
  have hdescent : baseEnd_1225281 < baseStart_1225281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225322 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 6]
def baseStart_1225322 : Nat := 118140960795 + 1225322 * 2 ^ 59
def prefixEnd_1225322 : Nat := 4983230072969 + 3 ^ 40 * 1225322 * 2
def baseEnd_1225322 : Nat := 139817587228568923497745

theorem tailTrace_1225322 : CollatzResearch.WordTrace tailWord_1225322 prefixEnd_1225322 139817587228568923497745 := by
  unfold tailWord_1225322
  simp only [CollatzResearch.WordTrace]
  refine ⟨11172791216718784295501555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29794109911250091454670813 11172791216718784295501555)
  ·
    refine ⟨16759186825078176443252333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11172791216718784295501555 16759186825078176443252333)
    ·
      refine ⟨6284695059404316166219625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16759186825078176443252333 6284695059404316166219625)
      ·
        refine ⟨4713521294553237124664719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6284695059404316166219625 4713521294553237124664719)
        ·
          refine ⟨7070281941829855686997079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4713521294553237124664719 7070281941829855686997079)
          ·
            refine ⟨10605422912744783530495619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7070281941829855686997079 10605422912744783530495619)
            ·
              refine ⟨15908134369117175295743429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10605422912744783530495619 15908134369117175295743429)
              ·
                refine ⟨2982775194209470367951893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15908134369117175295743429 2982775194209470367951893)
                ·
                  refine ⟨139817587228568923497745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2982775194209470367951893 139817587228568923497745)
                  ·
                    rfl

theorem cell22_1225322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_1225322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225322 prefixEnd_1225322 := by exact prefixLift 1225322
  have htrace : WordTrace (prefixWord ++ tailWord_1225322) baseStart_1225322 baseEnd_1225322 := by
    simpa [prefixWord, tailWord_1225322, baseEnd_1225322] using wordTrace_append hprefix tailTrace_1225322
  have hstable : (prefixWord ++ tailWord_1225322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225322).length < 2 ^ (prefixWord ++ tailWord_1225322).sum := by decide
  have hdescent : baseEnd_1225322 < baseStart_1225322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225367 : List Nat := [1, 1, 3, 3, 2, 1, 4, 7]
def baseStart_1225367 : Nat := 118140960795 + 1225367 * 2 ^ 59
def prefixEnd_1225367 : Nat := 4983230072969 + 3 ^ 40 * 1225367 * 2
def baseEnd_1225367 : Nat := 46607574011704628124233

theorem tailTrace_1225367 : CollatzResearch.WordTrace tailWord_1225367 prefixEnd_1225367 46607574011704628124233 := by
  unfold tailWord_1225367
  simp only [CollatzResearch.WordTrace]
  refine ⟨44692806151712109867394355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29795204101141406578262903 44692806151712109867394355)
  ·
    refine ⟨67039209227568164801091533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44692806151712109867394355 67039209227568164801091533)
    ·
      refine ⟨25139703460338061800409325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67039209227568164801091533 25139703460338061800409325)
      ·
        refine ⟨9427388797626773175153497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25139703460338061800409325 9427388797626773175153497)
        ·
          refine ⟨7070541598220079881365123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9427388797626773175153497 7070541598220079881365123)
          ·
            refine ⟨10605812397330119822047685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7070541598220079881365123 10605812397330119822047685)
            ·
              refine ⟨1988589824499397466633941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10605812397330119822047685 1988589824499397466633941)
              ·
                refine ⟨46607574011704628124233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1988589824499397466633941 46607574011704628124233)
                ·
                  rfl

theorem cell22_1225367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 7].length) (baseStart_1225367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225367 prefixEnd_1225367 := by exact prefixLift 1225367
  have htrace : WordTrace (prefixWord ++ tailWord_1225367) baseStart_1225367 baseEnd_1225367 := by
    simpa [prefixWord, tailWord_1225367, baseEnd_1225367] using wordTrace_append hprefix tailTrace_1225367
  have hstable : (prefixWord ++ tailWord_1225367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225367).length < 2 ^ (prefixWord ++ tailWord_1225367).sum := by decide
  have hdescent : baseEnd_1225367 < baseStart_1225367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225457 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 8]
def baseStart_1225457 : Nat := 118140960795 + 1225457 * 2 ^ 59
def prefixEnd_1225457 : Nat := 4983230072969 + 3 ^ 40 * 1225457 * 2
def baseEnd_1225457 : Nat := 139832991648203806122607

theorem tailTrace_1225457 : CollatzResearch.WordTrace tailWord_1225457 prefixEnd_1225457 139832991648203806122607 := by
  unfold tailWord_1225457
  simp only [CollatzResearch.WordTrace]
  refine ⟨44696088721386055238170625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29797392480924036825447083 44696088721386055238170625)
  ·
    refine ⟨33522066541039541428627969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44696088721386055238170625 33522066541039541428627969)
    ·
      refine ⟨25141549905779656071470977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33522066541039541428627969 25141549905779656071470977)
      ·
        refine ⟨18856162429334742053603233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25141549905779656071470977 18856162429334742053603233)
        ·
          refine ⟨14142121822001056540202425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18856162429334742053603233 14142121822001056540202425)
          ·
            refine ⟨10606591366500792405151819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14142121822001056540202425 10606591366500792405151819)
            ·
              refine ⟨15909887049751188607727729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10606591366500792405151819 15909887049751188607727729)
              ·
                refine ⟨11932415287313391455795797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15909887049751188607727729 11932415287313391455795797)
                ·
                  refine ⟨139832991648203806122607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11932415287313391455795797 139832991648203806122607)
                  ·
                    rfl

theorem cell22_1225457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_1225457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225457 prefixEnd_1225457 := by exact prefixLift 1225457
  have htrace : WordTrace (prefixWord ++ tailWord_1225457) baseStart_1225457 baseEnd_1225457 := by
    simpa [prefixWord, tailWord_1225457, baseEnd_1225457] using wordTrace_append hprefix tailTrace_1225457
  have hstable : (prefixWord ++ tailWord_1225457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225457).length < 2 ^ (prefixWord ++ tailWord_1225457).sum := by decide
  have hdescent : baseEnd_1225457 < baseStart_1225457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225487 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 3, 6]
def baseStart_1225487 : Nat := 118140960795 + 1225487 * 2 ^ 59
def prefixEnd_1225487 : Nat := 4983230072969 + 3 ^ 40 * 1225487 * 2
def baseEnd_1225487 : Nat := 419509244557701340117729

theorem tailTrace_1225487 : CollatzResearch.WordTrace tailWord_1225487 prefixEnd_1225487 419509244557701340117729 := by
  unfold tailWord_1225487
  simp only [CollatzResearch.WordTrace]
  refine ⟨44697182911277370361762715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29798121940851580241175143 44697182911277370361762715)
  ·
    refine ⟨67045774366916055542644073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44697182911277370361762715 67045774366916055542644073)
    ·
      refine ⟨50284330775187041656983055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67045774366916055542644073 50284330775187041656983055)
      ·
        refine ⟨75426496162780562485474583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50284330775187041656983055 75426496162780562485474583)
        ·
          refine ⟨113139744244170843728211875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75426496162780562485474583 113139744244170843728211875)
          ·
            refine ⟨169709616366256265592317813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113139744244170843728211875 169709616366256265592317813)
            ·
              refine ⟨15910276534336524899279795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 169709616366256265592317813 15910276534336524899279795)
              ·
                refine ⟨23865414801504787348919693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15910276534336524899279795 23865414801504787348919693)
                ·
                  refine ⟨8949530550564295255844885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23865414801504787348919693 8949530550564295255844885)
                  ·
                    refine ⟨419509244557701340117729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8949530550564295255844885 419509244557701340117729)
                    ·
                      rfl

theorem cell22_1225487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_1225487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225487 prefixEnd_1225487 := by exact prefixLift 1225487
  have htrace : WordTrace (prefixWord ++ tailWord_1225487) baseStart_1225487 baseEnd_1225487 := by
    simpa [prefixWord, tailWord_1225487, baseEnd_1225487] using wordTrace_append hprefix tailTrace_1225487
  have hstable : (prefixWord ++ tailWord_1225487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225487).length < 2 ^ (prefixWord ++ tailWord_1225487).sum := by decide
  have hdescent : baseEnd_1225487 < baseStart_1225487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225489 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 1, 5]
def baseStart_1225489 : Nat := 118140960795 + 1225489 * 2 ^ 59
def prefixEnd_1225489 : Nat := 4983230072969 + 3 ^ 40 * 1225489 * 2
def baseEnd_1225489 : Nat := 419509929198574001567723

theorem tailTrace_1225489 : CollatzResearch.WordTrace tailWord_1225489 prefixEnd_1225489 419509929198574001567723 := by
  unfold tailWord_1225489
  simp only [CollatzResearch.WordTrace]
  refine ⟨44697255857270124703335521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29798170571513416468890347 44697255857270124703335521)
  ·
    refine ⟨33522941892952593527501641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44697255857270124703335521 33522941892952593527501641)
    ·
      refine ⟨25142206419714445145626231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33522941892952593527501641 25142206419714445145626231)
      ·
        refine ⟨37713309629571667718439347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25142206419714445145626231 37713309629571667718439347)
        ·
          refine ⟨56569964444357501577659021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37713309629571667718439347 56569964444357501577659021)
          ·
            refine ⟨21213736666634063091622133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56569964444357501577659021 21213736666634063091622133)
            ·
              refine ⟨1988787812496943414839575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21213736666634063091622133 1988787812496943414839575)
              ·
                refine ⟨2983181718745415122259363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1988787812496943414839575 2983181718745415122259363)
                ·
                  refine ⟨4474772578118122683389045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983181718745415122259363 4474772578118122683389045)
                  ·
                    refine ⟨419509929198574001567723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4474772578118122683389045 419509929198574001567723)
                    ·
                      rfl

theorem cell22_1225489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_1225489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225489 prefixEnd_1225489 := by exact prefixLift 1225489
  have htrace : WordTrace (prefixWord ++ tailWord_1225489) baseStart_1225489 baseEnd_1225489 := by
    simpa [prefixWord, tailWord_1225489, baseEnd_1225489] using wordTrace_append hprefix tailTrace_1225489
  have hstable : (prefixWord ++ tailWord_1225489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225489).length < 2 ^ (prefixWord ++ tailWord_1225489).sum := by decide
  have hdescent : baseEnd_1225489 < baseStart_1225489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225504 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 1, 6]
def baseStart_1225504 : Nat := 118140960795 + 1225504 * 2 ^ 59
def prefixEnd_1225504 : Nat := 4983230072969 + 3 ^ 40 * 1225504 * 2
def baseEnd_1225504 : Nat := 419515064005118962442677

theorem tailTrace_1225504 : CollatzResearch.WordTrace tailWord_1225504 prefixEnd_1225504 419515064005118962442677 := by
  unfold tailWord_1225504
  simp only [CollatzResearch.WordTrace]
  refine ⟨22348901476107891132565783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29798535301477188176754377 22348901476107891132565783)
  ·
    refine ⟨33523352214161836698848675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22348901476107891132565783 33523352214161836698848675)
    ·
      refine ⟨50285028321242755048273013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33523352214161836698848675 50285028321242755048273013)
      ·
        refine ⟨4714221405116508285775595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50285028321242755048273013 4714221405116508285775595)
        ·
          refine ⟨7071332107674762428663393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4714221405116508285775595 7071332107674762428663393)
          ·
            refine ⟨5303499080756071821497545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7071332107674762428663393 5303499080756071821497545)
            ·
              refine ⟨3977624310567053866123159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5303499080756071821497545 3977624310567053866123159)
              ·
                refine ⟨5966436465850580799184739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3977624310567053866123159 5966436465850580799184739)
                ·
                  refine ⟨8949654698775871198777109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5966436465850580799184739 8949654698775871198777109)
                  ·
                    refine ⟨419515064005118962442677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8949654698775871198777109 419515064005118962442677)
                    ·
                      rfl

theorem cell22_1225504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_1225504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225504 prefixEnd_1225504 := by exact prefixLift 1225504
  have htrace : WordTrace (prefixWord ++ tailWord_1225504) baseStart_1225504 baseEnd_1225504 := by
    simpa [prefixWord, tailWord_1225504, baseEnd_1225504] using wordTrace_append hprefix tailTrace_1225504
  have hstable : (prefixWord ++ tailWord_1225504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225504).length < 2 ^ (prefixWord ++ tailWord_1225504).sum := by decide
  have hdescent : baseEnd_1225504 < baseStart_1225504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225506 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_1225506 : Nat := 118140960795 + 1225506 * 2 ^ 59
def prefixEnd_1225506 : Nat := 4983230072969 + 3 ^ 40 * 1225506 * 2
def baseEnd_1225506 : Nat := 419515748645991623892671

theorem tailTrace_1225506 : CollatzResearch.WordTrace tailWord_1225506 prefixEnd_1225506 419515748645991623892671 := by
  unfold tailWord_1225506
  simp only [CollatzResearch.WordTrace]
  refine ⟨11174468974552134151676093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29798583932139024404469581 11174468974552134151676093)
  ·
    refine ⟨4190425865457050306878535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11174468974552134151676093 4190425865457050306878535)
    ·
      refine ⟨6285638798185575460317803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4190425865457050306878535 6285638798185575460317803)
      ·
        refine ⟨9428458197278363190476705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6285638798185575460317803 9428458197278363190476705)
        ·
          refine ⟨7071343647958772392857529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9428458197278363190476705 7071343647958772392857529)
          ·
            refine ⟨5303507735969079294643147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7071343647958772392857529 5303507735969079294643147)
            ·
              refine ⟨7955261603953618941964721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5303507735969079294643147 7955261603953618941964721)
              ·
                refine ⟨5966446202965214206473541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7955261603953618941964721 5966446202965214206473541)
                ·
                  refine ⟨1118708663055977663713789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5966446202965214206473541 1118708663055977663713789)
                  ·
                    refine ⟨419515748645991623892671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1118708663055977663713789 419515748645991623892671)
                    ·
                      rfl

theorem cell22_1225506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_1225506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225506 prefixEnd_1225506 := by exact prefixLift 1225506
  have htrace : WordTrace (prefixWord ++ tailWord_1225506) baseStart_1225506 baseEnd_1225506 := by
    simpa [prefixWord, tailWord_1225506, baseEnd_1225506] using wordTrace_append hprefix tailTrace_1225506
  have hstable : (prefixWord ++ tailWord_1225506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225506).length < 2 ^ (prefixWord ++ tailWord_1225506).sum := by decide
  have hdescent : baseEnd_1225506 < baseStart_1225506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225568 : List Nat := [2, 1, 1, 3, 3, 1, 2, 5, 1, 3]
def baseStart_1225568 : Nat := 118140960795 + 1225568 * 2 ^ 59
def prefixEnd_1225568 : Nat := 4983230072969 + 3 ^ 40 * 1225568 * 2
def baseEnd_1225568 : Nat := 419536972513044128842481

theorem tailTrace_1225568 : CollatzResearch.WordTrace tailWord_1225568 prefixEnd_1225568 419536972513044128842481 := by
  unfold tailWord_1225568
  simp only [CollatzResearch.WordTrace]
  refine ⟨22350068611991960597730679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29800091482655947463640905 22350068611991960597730679)
  ·
    refine ⟨33525102917987940896596019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22350068611991960597730679 33525102917987940896596019)
    ·
      refine ⟨50287654376981911344894029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33525102917987940896596019 50287654376981911344894029)
      ·
        refine ⟨18857870391368216754335261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50287654376981911344894029 18857870391368216754335261)
        ·
          refine ⟨7071701396763081282875723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18857870391368216754335261 7071701396763081282875723)
          ·
            refine ⟨10607552095144621924313585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7071701396763081282875723 10607552095144621924313585)
            ·
              refine ⟨7955664071358466443235189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10607552095144621924313585 7955664071358466443235189)
              ·
                refine ⟨745843506689856229053299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7955664071358466443235189 745843506689856229053299)
                ·
                  refine ⟨1118765260034784343579949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745843506689856229053299 1118765260034784343579949)
                  ·
                    refine ⟨419536972513044128842481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1118765260034784343579949 419536972513044128842481)
                    ·
                      rfl

theorem cell22_1225568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 1, 3].length) (baseStart_1225568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225568 prefixEnd_1225568 := by exact prefixLift 1225568
  have htrace : WordTrace (prefixWord ++ tailWord_1225568) baseStart_1225568 baseEnd_1225568 := by
    simpa [prefixWord, tailWord_1225568, baseEnd_1225568] using wordTrace_append hprefix tailTrace_1225568
  have hstable : (prefixWord ++ tailWord_1225568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225568).length < 2 ^ (prefixWord ++ tailWord_1225568).sum := by decide
  have hdescent : baseEnd_1225568 < baseStart_1225568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225585 : List Nat := [1, 2, 2, 2, 1, 4, 4, 2, 1, 3]
def baseStart_1225585 : Nat := 118140960795 + 1225585 * 2 ^ 59
def prefixEnd_1225585 : Nat := 4983230072969 + 3 ^ 40 * 1225585 * 2
def baseEnd_1225585 : Nat := 419542791960461751167429

theorem tailTrace_1225585 : CollatzResearch.WordTrace tailWord_1225585 prefixEnd_1225585 419542791960461751167429 := by
  unfold tailWord_1225585
  simp only [CollatzResearch.WordTrace]
  refine ⟨44700757264922333098830209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29800504843281555399220139 44700757264922333098830209)
  ·
    refine ⟨33525567948691749824122657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44700757264922333098830209 33525567948691749824122657)
    ·
      refine ⟨25144175961518812368091993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33525567948691749824122657 25144175961518812368091993)
      ·
        refine ⟨18858131971139109276068995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25144175961518812368091993 18858131971139109276068995)
        ·
          refine ⟨28287197956708663914103493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18858131971139109276068995 28287197956708663914103493)
          ·
            refine ⟨5303849616882874483894405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28287197956708663914103493 5303849616882874483894405)
            ·
              refine ⟨994471803165538965730201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5303849616882874483894405 994471803165538965730201)
              ·
                refine ⟨745853852374154224297651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 994471803165538965730201 745853852374154224297651)
                ·
                  refine ⟨1118780778561231336446477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745853852374154224297651 1118780778561231336446477)
                  ·
                    refine ⟨419542791960461751167429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1118780778561231336446477 419542791960461751167429)
                    ·
                      rfl

theorem cell22_1225585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_1225585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225585 prefixEnd_1225585 := by exact prefixLift 1225585
  have htrace : WordTrace (prefixWord ++ tailWord_1225585) baseStart_1225585 baseEnd_1225585 := by
    simpa [prefixWord, tailWord_1225585, baseEnd_1225585] using wordTrace_append hprefix tailTrace_1225585
  have hstable : (prefixWord ++ tailWord_1225585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225585).length < 2 ^ (prefixWord ++ tailWord_1225585).sum := by decide
  have hdescent : baseEnd_1225585 < baseStart_1225585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225602 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1225602 : Nat := 118140960795 + 1225602 * 2 ^ 59
def prefixEnd_1225602 : Nat := 4983230072969 + 3 ^ 40 * 1225602 * 2
def baseEnd_1225602 : Nat := 419548611407879373492377

theorem tailTrace_1225602 : CollatzResearch.WordTrace tailWord_1225602 prefixEnd_1225602 419548611407879373492377 := by
  unfold tailWord_1225602
  simp only [CollatzResearch.WordTrace]
  refine ⟨11175344326465186250549765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29800918203907163334799373 11175344326465186250549765)
  ·
    refine ⟨2095377061212222421978081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11175344326465186250549765 2095377061212222421978081)
    ·
      refine ⟨1571532795909166816483561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2095377061212222421978081 1571532795909166816483561)
      ·
        refine ⟨1178649596931875112362671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1571532795909166816483561 1178649596931875112362671)
        ·
          refine ⟨1767974395397812668544007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1178649596931875112362671 1767974395397812668544007)
          ·
            refine ⟨2651961593096719002816011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767974395397812668544007 2651961593096719002816011)
            ·
              refine ⟨3977942389645078504224017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2651961593096719002816011 3977942389645078504224017)
              ·
                refine ⟨2983456792233808878168013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3977942389645078504224017 2983456792233808878168013)
                ·
                  refine ⟨1118796297087678329313005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2983456792233808878168013 1118796297087678329313005)
                  ·
                    refine ⟨419548611407879373492377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1118796297087678329313005 419548611407879373492377)
                    ·
                      rfl

theorem cell22_1225602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1225602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225602 prefixEnd_1225602 := by exact prefixLift 1225602
  have htrace : WordTrace (prefixWord ++ tailWord_1225602) baseStart_1225602 baseEnd_1225602 := by
    simpa [prefixWord, tailWord_1225602, baseEnd_1225602] using wordTrace_append hprefix tailTrace_1225602
  have hstable : (prefixWord ++ tailWord_1225602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225602).length < 2 ^ (prefixWord ++ tailWord_1225602).sum := by decide
  have hdescent : baseEnd_1225602 < baseStart_1225602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225609 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 8]
def baseStart_1225609 : Nat := 118140960795 + 1225609 * 2 ^ 59
def prefixEnd_1225609 : Nat := 4983230072969 + 3 ^ 40 * 1225609 * 2
def baseEnd_1225609 : Nat := 139850335883644562855785

theorem tailTrace_1225609 : CollatzResearch.WordTrace tailWord_1225609 prefixEnd_1225609 139850335883644562855785 := by
  unfold tailWord_1225609
  simp only [CollatzResearch.WordTrace]
  refine ⟨44701632616835385197703881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29801088411223590131802587 44701632616835385197703881)
  ·
    refine ⟨33526224462626538898277911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44701632616835385197703881 33526224462626538898277911)
    ·
      refine ⟨50289336693939808347416867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33526224462626538898277911 50289336693939808347416867)
      ·
        refine ⟨75434005040909712521125301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50289336693939808347416867 75434005040909712521125301)
        ·
          refine ⟨7071937972585285548855497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75434005040909712521125301 7071937972585285548855497)
          ·
            refine ⟨5303953479438964161641623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7071937972585285548855497 5303953479438964161641623)
            ·
              refine ⟨7955930219158446242462435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5303953479438964161641623 7955930219158446242462435)
              ·
                refine ⟨11933895328737669363693653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7955930219158446242462435 11933895328737669363693653)
                ·
                  refine ⟨139850335883644562855785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11933895328737669363693653 139850335883644562855785)
                  ·
                    rfl

theorem cell22_1225609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_1225609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225609 prefixEnd_1225609 := by exact prefixLift 1225609
  have htrace : WordTrace (prefixWord ++ tailWord_1225609) baseStart_1225609 baseEnd_1225609 := by
    simpa [prefixWord, tailWord_1225609, baseEnd_1225609] using wordTrace_append hprefix tailTrace_1225609
  have hstable : (prefixWord ++ tailWord_1225609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225609).length < 2 ^ (prefixWord ++ tailWord_1225609).sum := by decide
  have hdescent : baseEnd_1225609 < baseStart_1225609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225641 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 4, 3]
def baseStart_1225641 : Nat := 118140960795 + 1225641 * 2 ^ 59
def prefixEnd_1225641 : Nat := 4983230072969 + 3 ^ 40 * 1225641 * 2
def baseEnd_1225641 : Nat := 419561961904896271767257

theorem tailTrace_1225641 : CollatzResearch.WordTrace tailWord_1225641 prefixEnd_1225641 419561961904896271767257 := by
  unfold tailWord_1225641
  simp only [CollatzResearch.WordTrace]
  refine ⟨44702799752719454662868777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29801866501812969775245851 44702799752719454662868777)
  ·
    refine ⟨33527099814539590997151583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44702799752719454662868777 33527099814539590997151583)
    ·
      refine ⟨50290649721809386495727375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33527099814539590997151583 50290649721809386495727375)
      ·
        refine ⟨75435974582714079743591063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50290649721809386495727375 75435974582714079743591063)
        ·
          refine ⟨113153961874071119615386595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75435974582714079743591063 113153961874071119615386595)
          ·
            refine ⟨169730942811106679423079893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113153961874071119615386595 169730942811106679423079893)
            ·
              refine ⟨3978068972135312798978435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 169730942811106679423079893 3978068972135312798978435)
              ·
                refine ⟨5967103458202969198467653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978068972135312798978435 5967103458202969198467653)
                ·
                  refine ⟨1118831898413056724712685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5967103458202969198467653 1118831898413056724712685)
                  ·
                    refine ⟨419561961904896271767257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1118831898413056724712685 419561961904896271767257)
                    ·
                      rfl

theorem cell22_1225641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 3].length) (baseStart_1225641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225641 prefixEnd_1225641 := by exact prefixLift 1225641
  have htrace : WordTrace (prefixWord ++ tailWord_1225641) baseStart_1225641 baseEnd_1225641 := by
    simpa [prefixWord, tailWord_1225641, baseEnd_1225641] using wordTrace_append hprefix tailTrace_1225641
  have hstable : (prefixWord ++ tailWord_1225641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225641).length < 2 ^ (prefixWord ++ tailWord_1225641).sum := by decide
  have hdescent : baseEnd_1225641 < baseStart_1225641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225670 : List Nat := [6, 1, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1225670 : Nat := 118140960795 + 1225670 * 2 ^ 59
def prefixEnd_1225670 : Nat := 4983230072969 + 3 ^ 40 * 1225670 * 2
def baseEnd_1225670 : Nat := 419571889197549862792169

theorem tailTrace_1225670 : CollatzResearch.WordTrace tailWord_1225670 prefixEnd_1225670 419571889197549862792169 := by
  unfold tailWord_1225670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1396995545925449769239827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29802571646409595077116309 1396995545925449769239827)
  ·
    refine ⟨2095493318888174653859741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1396995545925449769239827 2095493318888174653859741)
    ·
      refine ⟨785809994583065495197403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2095493318888174653859741 785809994583065495197403)
      ·
        refine ⟨1178714991874598242796105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785809994583065495197403 1178714991874598242796105)
        ·
          refine ⟨884036243905948682097079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1178714991874598242796105 884036243905948682097079)
          ·
            refine ⟨1326054365858923023145619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884036243905948682097079 1326054365858923023145619)
            ·
              refine ⟨1989081548788384534718429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1326054365858923023145619 1989081548788384534718429)
              ·
                refine ⟨745905580795644200519411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1989081548788384534718429 745905580795644200519411)
                ·
                  refine ⟨1118858371193466300779117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745905580795644200519411 1118858371193466300779117)
                  ·
                    refine ⟨419571889197549862792169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1118858371193466300779117 419571889197549862792169)
                    ·
                      rfl

theorem cell22_1225670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1225670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225670 prefixEnd_1225670 := by exact prefixLift 1225670
  have htrace : WordTrace (prefixWord ++ tailWord_1225670) baseStart_1225670 baseEnd_1225670 := by
    simpa [prefixWord, tailWord_1225670, baseEnd_1225670] using wordTrace_append hprefix tailTrace_1225670
  have hstable : (prefixWord ++ tailWord_1225670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225670).length < 2 ^ (prefixWord ++ tailWord_1225670).sum := by decide
  have hdescent : baseEnd_1225670 < baseStart_1225670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225671 : List Nat := [1, 1, 4, 1, 1, 2, 6, 6]
def baseStart_1225671 : Nat := 118140960795 + 1225671 * 2 ^ 59
def prefixEnd_1225671 : Nat := 4983230072969 + 3 ^ 40 * 1225671 * 2
def baseEnd_1225671 : Nat := 46619136835331799279685

theorem tailTrace_1225671 : CollatzResearch.WordTrace tailWord_1225671 prefixEnd_1225671 46619136835331799279685 := by
  unfold tailWord_1225671
  simp only [CollatzResearch.WordTrace]
  refine ⟨44703893942610769786460867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29802595961740513190973911 44703893942610769786460867)
  ·
    refine ⟨67055840913916154679691301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44703893942610769786460867 67055840913916154679691301)
    ·
      refine ⟨12572970171359279002442119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67055840913916154679691301 12572970171359279002442119)
      ·
        refine ⟨18859455257038918503663179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12572970171359279002442119 18859455257038918503663179)
        ·
          refine ⟨28289182885558377755494769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18859455257038918503663179 28289182885558377755494769)
          ·
            refine ⟨21216887164168783316621077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28289182885558377755494769 21216887164168783316621077)
            ·
              refine ⟨994541585820411717966613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21216887164168783316621077 994541585820411717966613)
              ·
                refine ⟨46619136835331799279685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 994541585820411717966613 46619136835331799279685)
                ·
                  rfl

theorem cell22_1225671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 6].length) (baseStart_1225671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225671 prefixEnd_1225671 := by exact prefixLift 1225671
  have htrace : WordTrace (prefixWord ++ tailWord_1225671) baseStart_1225671 baseEnd_1225671 := by
    simpa [prefixWord, tailWord_1225671, baseEnd_1225671] using wordTrace_append hprefix tailTrace_1225671
  have hstable : (prefixWord ++ tailWord_1225671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225671).length < 2 ^ (prefixWord ++ tailWord_1225671).sum := by decide
  have hdescent : baseEnd_1225671 < baseStart_1225671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225780 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1225780 : Nat := 118140960795 + 1225780 * 2 ^ 59
def prefixEnd_1225780 : Nat := 4983230072969 + 3 ^ 40 * 1225780 * 2
def baseEnd_1225780 : Nat := 419609544445546242541831

theorem tailTrace_1225780 : CollatzResearch.WordTrace tailWord_1225780 prefixEnd_1225780 419609544445546242541831 := by
  unfold tailWord_1225780
  simp only [CollatzResearch.WordTrace]
  refine ⟨22353934749607940701089397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29805246332810587601452529 22353934749607940701089397)
  ·
    refine ⟨2095681382775744440727131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22353934749607940701089397 2095681382775744440727131)
    ·
      refine ⟨3143522074163616661090697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2095681382775744440727131 3143522074163616661090697)
      ·
        refine ⟨2357641555622712495818023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3143522074163616661090697 2357641555622712495818023)
        ·
          refine ⟨3536462333434068743727035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2357641555622712495818023 3536462333434068743727035)
          ·
            refine ⟨5304693500151103115590553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3536462333434068743727035 5304693500151103115590553)
            ·
              refine ⟨3978520125113327336692915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5304693500151103115590553 3978520125113327336692915)
              ·
                refine ⟨5967780187669991005039373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978520125113327336692915 5967780187669991005039373)
                ·
                  refine ⟨2237917570376246626889765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5967780187669991005039373 2237917570376246626889765)
                  ·
                    refine ⟨419609544445546242541831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2237917570376246626889765 419609544445546242541831)
                    ·
                      rfl

theorem cell22_1225780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1225780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225780 prefixEnd_1225780 := by exact prefixLift 1225780
  have htrace : WordTrace (prefixWord ++ tailWord_1225780) baseStart_1225780 baseEnd_1225780 := by
    simpa [prefixWord, tailWord_1225780, baseEnd_1225780] using wordTrace_append hprefix tailTrace_1225780
  have hstable : (prefixWord ++ tailWord_1225780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225780).length < 2 ^ (prefixWord ++ tailWord_1225780).sum := by decide
  have hdescent : baseEnd_1225780 < baseStart_1225780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225806 : List Nat := [4, 1, 1, 1, 1, 3, 11]
def baseStart_1225806 : Nat := 118140960795 + 1225806 * 2 ^ 59
def prefixEnd_1225806 : Nat := 4983230072969 + 3 ^ 40 * 1225806 * 2
def baseEnd_1225806 : Nat := 15541423880625586718213

theorem tailTrace_1225806 : CollatzResearch.WordTrace tailWord_1225806 prefixEnd_1225806 15541423880625586718213 := by
  unfold tailWord_1225806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5588602224640210980328159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29805878531414458561750181 5588602224640210980328159)
  ·
    refine ⟨8382903336960316470492239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5588602224640210980328159 8382903336960316470492239)
    ·
      refine ⟨12574355005440474705738359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8382903336960316470492239 12574355005440474705738359)
      ·
        refine ⟨18861532508160712058607539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12574355005440474705738359 18861532508160712058607539)
        ·
          refine ⟨28292298762241068087911309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18861532508160712058607539 28292298762241068087911309)
          ·
            refine ⟨10609612035840400532966741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28292298762241068087911309 10609612035840400532966741)
            ·
              refine ⟨15541423880625586718213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10609612035840400532966741 15541423880625586718213)
              ·
                rfl

theorem cell22_1225806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 11].length) (baseStart_1225806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225806 prefixEnd_1225806 := by exact prefixLift 1225806
  have htrace : WordTrace (prefixWord ++ tailWord_1225806) baseStart_1225806 baseEnd_1225806 := by
    simpa [prefixWord, tailWord_1225806, baseEnd_1225806] using wordTrace_append hprefix tailTrace_1225806
  have hstable : (prefixWord ++ tailWord_1225806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225806).length < 2 ^ (prefixWord ++ tailWord_1225806).sum := by decide
  have hdescent : baseEnd_1225806 < baseStart_1225806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225810 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_1225810 : Nat := 118140960795 + 1225810 * 2 ^ 59
def prefixEnd_1225810 : Nat := 4983230072969 + 3 ^ 40 * 1225810 * 2
def baseEnd_1225810 : Nat := 419619814058636164291739

theorem tailTrace_1225810 : CollatzResearch.WordTrace tailWord_1225810 prefixEnd_1225810 419619814058636164291739 := by
  unfold tailWord_1225810
  simp only [CollatzResearch.WordTrace]
  refine ⟨11177240922276799131442721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29805975792738131017180589 11177240922276799131442721)
  ·
    refine ⟨8382930691707599348582041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11177240922276799131442721 8382930691707599348582041)
    ·
      refine ⟨6287198018780699511436531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8382930691707599348582041 6287198018780699511436531)
      ·
        refine ⟨9430797028171049267154797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6287198018780699511436531 9430797028171049267154797)
        ·
          refine ⟨3536548885564143475183049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9430797028171049267154797 3536548885564143475183049)
          ·
            refine ⟨2652411664173107606387287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3536548885564143475183049 2652411664173107606387287)
            ·
              refine ⟨3978617496259661409580931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2652411664173107606387287 3978617496259661409580931)
              ·
                refine ⟨5967926244389492114371397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978617496259661409580931 5967926244389492114371397)
                ·
                  refine ⟨1118986170823029771444637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5967926244389492114371397 1118986170823029771444637)
                  ·
                    refine ⟨419619814058636164291739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1118986170823029771444637 419619814058636164291739)
                    ·
                      rfl

theorem cell22_1225810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_1225810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225810 prefixEnd_1225810 := by exact prefixLift 1225810
  have htrace : WordTrace (prefixWord ++ tailWord_1225810) baseStart_1225810 baseEnd_1225810 := by
    simpa [prefixWord, tailWord_1225810, baseEnd_1225810] using wordTrace_append hprefix tailTrace_1225810
  have hstable : (prefixWord ++ tailWord_1225810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225810).length < 2 ^ (prefixWord ++ tailWord_1225810).sum := by decide
  have hdescent : baseEnd_1225810 < baseStart_1225810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225881 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 1, 10]
def baseStart_1225881 : Nat := 118140960795 + 1225881 * 2 ^ 59
def prefixEnd_1225881 : Nat := 4983230072969 + 3 ^ 40 * 1225881 * 2
def baseEnd_1225881 : Nat := 419644118809615645766521

theorem tailTrace_1225881 : CollatzResearch.WordTrace tailWord_1225881 prefixEnd_1225881 419644118809615645766521 := by
  unfold tailWord_1225881
  simp only [CollatzResearch.WordTrace]
  refine ⟨44711553271849975651605497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29807702181233317101070331 44711553271849975651605497)
  ·
    refine ⟨33533664953887481738704123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44711553271849975651605497 33533664953887481738704123)
    ·
      refine ⟨50300497430831222608056185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33533664953887481738704123 50300497430831222608056185)
      ·
        refine ⟨37725373073123416956042139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50300497430831222608056185 37725373073123416956042139)
        ·
          refine ⟨56588059609685125434063209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37725373073123416956042139 56588059609685125434063209)
          ·
            refine ⟨42441044707263844075547407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56588059609685125434063209 42441044707263844075547407)
            ·
              refine ⟨63661567060895766113321111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42441044707263844075547407 63661567060895766113321111)
              ·
                refine ⟨95492350591343649169981667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63661567060895766113321111 95492350591343649169981667)
                ·
                  refine ⟨143238525887015473754972501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95492350591343649169981667 143238525887015473754972501)
                  ·
                    refine ⟨419644118809615645766521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 143238525887015473754972501 419644118809615645766521)
                    ·
                      rfl

theorem cell22_1225881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_1225881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225881 prefixEnd_1225881 := by exact prefixLift 1225881
  have htrace : WordTrace (prefixWord ++ tailWord_1225881) baseStart_1225881 baseEnd_1225881 := by
    simpa [prefixWord, tailWord_1225881, baseEnd_1225881] using wordTrace_append hprefix tailTrace_1225881
  have hstable : (prefixWord ++ tailWord_1225881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225881).length < 2 ^ (prefixWord ++ tailWord_1225881).sum := by decide
  have hdescent : baseEnd_1225881 < baseStart_1225881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225943 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 4, 4]
def baseStart_1225943 : Nat := 118140960795 + 1225943 * 2 ^ 59
def prefixEnd_1225943 : Nat := 4983230072969 + 3 ^ 40 * 1225943 * 2
def baseEnd_1225943 : Nat := 419665342676668150716331

theorem tailTrace_1225943 : CollatzResearch.WordTrace tailWord_1225943 prefixEnd_1225943 419665342676668150716331 := by
  unfold tailWord_1225943
  simp only [CollatzResearch.WordTrace]
  refine ⟨44713814597625360240362483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29809209731750240160241655 44713814597625360240362483)
  ·
    refine ⟨67070721896438040360543725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44713814597625360240362483 67070721896438040360543725)
    ·
      refine ⟨25151520711164265135203897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67070721896438040360543725 25151520711164265135203897)
      ·
        refine ⟨18863640533373198851402923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25151520711164265135203897 18863640533373198851402923)
        ·
          refine ⟨28295460800059798277104385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18863640533373198851402923 28295460800059798277104385)
          ·
            refine ⟨21221595600044848707828289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28295460800059798277104385 21221595600044848707828289)
            ·
              refine ⟨15916196700033636530871217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21221595600044848707828289 15916196700033636530871217)
              ·
                refine ⟨11937147525025227398153413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15916196700033636530871217 11937147525025227398153413)
                ·
                  refine ⟨2238215160942230137153765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11937147525025227398153413 2238215160942230137153765)
                  ·
                    refine ⟨419665342676668150716331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2238215160942230137153765 419665342676668150716331)
                    ·
                      rfl

theorem cell22_1225943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_1225943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1225943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1225943 prefixEnd_1225943 := by exact prefixLift 1225943
  have htrace : WordTrace (prefixWord ++ tailWord_1225943) baseStart_1225943 baseEnd_1225943 := by
    simpa [prefixWord, tailWord_1225943, baseEnd_1225943] using wordTrace_append hprefix tailTrace_1225943
  have hstable : (prefixWord ++ tailWord_1225943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225943).length < 2 ^ (prefixWord ++ tailWord_1225943).sum := by decide
  have hdescent : baseEnd_1225943 < baseStart_1225943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226041 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 3, 3]
def baseStart_1226041 : Nat := 118140960795 + 1226041 * 2 ^ 59
def prefixEnd_1226041 : Nat := 4983230072969 + 3 ^ 40 * 1226041 * 2
def baseEnd_1226041 : Nat := 419698890079428561766031

theorem tailTrace_1226041 : CollatzResearch.WordTrace tailWord_1226041 prefixEnd_1226041 419698890079428561766031 := by
  unfold tailWord_1226041
  simp only [CollatzResearch.WordTrace]
  refine ⟨44717388951270322977429977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29811592634180215318286651 44717388951270322977429977)
  ·
    refine ⟨33538041713452742233072483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44717388951270322977429977 33538041713452742233072483)
    ·
      refine ⟨50307062570179113349608725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33538041713452742233072483 50307062570179113349608725)
      ·
        refine ⟨2358143557977145938262909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50307062570179113349608725 2358143557977145938262909)
        ·
          refine ⟨884303834241429726848591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2358143557977145938262909 884303834241429726848591)
          ·
            refine ⟨1326455751362144590272887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884303834241429726848591 1326455751362144590272887)
            ·
              refine ⟨1989683627043216885409331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1326455751362144590272887 1989683627043216885409331)
              ·
                refine ⟨2984525440564825328113997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989683627043216885409331 2984525440564825328113997)
                ·
                  refine ⟨1119197040211809498042749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2984525440564825328113997 1119197040211809498042749)
                  ·
                    refine ⟨419698890079428561766031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1119197040211809498042749 419698890079428561766031)
                    ·
                      rfl

theorem cell22_1226041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 3, 3].length) (baseStart_1226041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1226041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1226041 prefixEnd_1226041 := by exact prefixLift 1226041
  have htrace : WordTrace (prefixWord ++ tailWord_1226041) baseStart_1226041 baseEnd_1226041 := by
    simpa [prefixWord, tailWord_1226041, baseEnd_1226041] using wordTrace_append hprefix tailTrace_1226041
  have hstable : (prefixWord ++ tailWord_1226041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226041).length < 2 ^ (prefixWord ++ tailWord_1226041).sum := by decide
  have hdescent : baseEnd_1226041 < baseStart_1226041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
