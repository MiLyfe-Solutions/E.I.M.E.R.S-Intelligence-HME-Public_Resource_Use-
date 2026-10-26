import V185TrunkScan20Chunk007

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_48804 : List Nat := [2, 3, 1, 2, 2, 3, 2, 3, 2]
def baseStart_48804 : Nat := 118140960795 + 48804 * 2 ^ 59
def prefixEnd_48804 : Nat := 4983230072969 + 3 ^ 40 * 48804 * 2
def baseEnd_48804 : Nat := 22275475433006478067165

theorem tailTrace_48804 : CollatzResearch.WordTrace tailWord_48804 prefixEnd_48804 22275475433006478067165 := by
  unfold tailWord_48804
  simp only [CollatzResearch.WordTrace]
  refine ⟨890014057599458952360733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1186685410132611936480977 890014057599458952360733)
  ·
    refine ⟨333755271599797107135275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 890014057599458952360733 333755271599797107135275)
    ·
      refine ⟨500632907399695660702913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333755271599797107135275 500632907399695660702913)
      ·
        refine ⟨375474680549771745527185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500632907399695660702913 375474680549771745527185)
        ·
          refine ⟨281606010412328809145389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375474680549771745527185 281606010412328809145389)
          ·
            refine ⟨105602253904623303429521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281606010412328809145389 105602253904623303429521)
            ·
              refine ⟨79201690428467477572141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105602253904623303429521 79201690428467477572141)
              ·
                refine ⟨29700633910675304089553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79201690428467477572141 29700633910675304089553)
                ·
                  refine ⟨22275475433006478067165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29700633910675304089553 22275475433006478067165)
                  ·
                    rfl

theorem cell20_48804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_48804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48804 prefixEnd_48804 := by exact prefixLift 48804
  have htrace : WordTrace (prefixWord ++ tailWord_48804) baseStart_48804 baseEnd_48804 := by
    simpa [prefixWord, tailWord_48804, baseEnd_48804] using wordTrace_append hprefix tailTrace_48804
  have hstable : (prefixWord ++ tailWord_48804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48804).length < 2 ^ (prefixWord ++ tailWord_48804).sum := by decide
  have hdescent : baseEnd_48804 < baseStart_48804 := by decide
  rcases family_descends (prefixWord ++ tailWord_48804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48814 : List Nat := [4, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_48814 : Nat := 118140960795 + 48814 * 2 ^ 59
def prefixEnd_48814 : Nat := 4983230072969 + 3 ^ 40 * 48814 * 2
def baseEnd_48814 : Nat := 22280039705490887733791

theorem tailTrace_48814 : CollatzResearch.WordTrace tailWord_48814 prefixEnd_48814 22280039705490887733791 := by
  unfold tailWord_48814
  simp only [CollatzResearch.WordTrace]
  refine ⟨222549105645336201573187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1186928563441793075056997 222549105645336201573187)
  ·
    refine ⟨333823658468004302359781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222549105645336201573187 333823658468004302359781)
    ·
      refine ⟨62591935962750806692459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 333823658468004302359781 62591935962750806692459)
      ·
        refine ⟨93887903944126210038689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62591935962750806692459 93887903944126210038689)
        ·
          refine ⟨70415927958094657529017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93887903944126210038689 70415927958094657529017)
          ·
            refine ⟨52811945968570993146763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70415927958094657529017 52811945968570993146763)
            ·
              refine ⟨79217918952856489720145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52811945968570993146763 79217918952856489720145)
              ·
                refine ⟨59413439214642367290109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79217918952856489720145 59413439214642367290109)
                ·
                  refine ⟨22280039705490887733791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59413439214642367290109 22280039705490887733791)
                  ·
                    rfl

theorem cell20_48814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_48814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48814 prefixEnd_48814 := by exact prefixLift 48814
  have htrace : WordTrace (prefixWord ++ tailWord_48814) baseStart_48814 baseEnd_48814 := by
    simpa [prefixWord, tailWord_48814, baseEnd_48814] using wordTrace_append hprefix tailTrace_48814
  have hstable : (prefixWord ++ tailWord_48814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48814).length < 2 ^ (prefixWord ++ tailWord_48814).sum := by decide
  have hdescent : baseEnd_48814 < baseStart_48814 := by decide
  rcases family_descends (prefixWord ++ tailWord_48814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48825 : List Nat := [1, 2, 1, 4, 1, 1, 4, 4, 2]
def baseStart_48825 : Nat := 118140960795 + 48825 * 2 ^ 59
def prefixEnd_48825 : Nat := 4983230072969 + 3 ^ 40 * 48825 * 2
def baseEnd_48825 : Nat := 22285060405223738367079

theorem tailTrace_48825 : CollatzResearch.WordTrace tailWord_48825 prefixEnd_48825 22285060405223738367079 := by
  unfold tailWord_48825
  simp only [CollatzResearch.WordTrace]
  refine ⟨1780794048122838491235929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1187196032081892327490619 1780794048122838491235929)
  ·
    refine ⟨1335595536092128868426947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1780794048122838491235929 1335595536092128868426947)
    ·
      refine ⟨2003393304138193302640421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1335595536092128868426947 2003393304138193302640421)
      ·
        refine ⟨375636244525911244245079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2003393304138193302640421 375636244525911244245079)
        ·
          refine ⟨563454366788866866367619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375636244525911244245079 563454366788866866367619)
          ·
            refine ⟨845181550183300299551429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563454366788866866367619 845181550183300299551429)
            ·
              refine ⟨158471540659368806165893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 845181550183300299551429 158471540659368806165893)
              ·
                refine ⟨29713413873631651156105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158471540659368806165893 29713413873631651156105)
                ·
                  refine ⟨22285060405223738367079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29713413873631651156105 22285060405223738367079)
                  ·
                    rfl

theorem cell20_48825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 2].length) (baseStart_48825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48825 prefixEnd_48825 := by exact prefixLift 48825
  have htrace : WordTrace (prefixWord ++ tailWord_48825) baseStart_48825 baseEnd_48825 := by
    simpa [prefixWord, tailWord_48825, baseEnd_48825] using wordTrace_append hprefix tailTrace_48825
  have hstable : (prefixWord ++ tailWord_48825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48825).length < 2 ^ (prefixWord ++ tailWord_48825).sum := by decide
  have hdescent : baseEnd_48825 < baseStart_48825 := by decide
  rcases family_descends (prefixWord ++ tailWord_48825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48846 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_48846 : Nat := 118140960795 + 48846 * 2 ^ 59
def prefixEnd_48846 : Nat := 4983230072969 + 3 ^ 40 * 48846 * 2
def baseEnd_48846 : Nat := 22294645377440998666993

theorem tailTrace_48846 : CollatzResearch.WordTrace tailWord_48846 prefixEnd_48846 22294645377440998666993 := by
  unfold tailWord_48846
  simp only [CollatzResearch.WordTrace]
  refine ⟨222694997630844884718799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1187706654031172718500261 222694997630844884718799)
  ·
    refine ⟨334042496446267327078199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222694997630844884718799 334042496446267327078199)
    ·
      refine ⟨501063744669400990617299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334042496446267327078199 501063744669400990617299)
      ·
        refine ⟨751595617004101485925949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501063744669400990617299 751595617004101485925949)
        ·
          refine ⟨281848356376538057222231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 751595617004101485925949 281848356376538057222231)
          ·
            refine ⟨422772534564807085833347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281848356376538057222231 422772534564807085833347)
            ·
              refine ⟨634158801847210628750021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422772534564807085833347 634158801847210628750021)
              ·
                refine ⟨118904775346351992890629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 634158801847210628750021 118904775346351992890629)
                ·
                  refine ⟨22294645377440998666993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118904775346351992890629 22294645377440998666993)
                  ·
                    rfl

theorem cell20_48846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_48846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48846 prefixEnd_48846 := by exact prefixLift 48846
  have htrace : WordTrace (prefixWord ++ tailWord_48846) baseStart_48846 baseEnd_48846 := by
    simpa [prefixWord, tailWord_48846, baseEnd_48846] using wordTrace_append hprefix tailTrace_48846
  have hstable : (prefixWord ++ tailWord_48846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48846).length < 2 ^ (prefixWord ++ tailWord_48846).sum := by decide
  have hdescent : baseEnd_48846 < baseStart_48846 := by decide
  rcases family_descends (prefixWord ++ tailWord_48846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48877 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 5]
def baseStart_48877 : Nat := 118140960795 + 48877 * 2 ^ 59
def prefixEnd_48877 : Nat := 4983230072969 + 3 ^ 40 * 48877 * 2
def baseEnd_48877 : Nat := 22308794622142668633533

theorem tailTrace_48877 : CollatzResearch.WordTrace tailWord_48877 prefixEnd_48877 22308794622142668633533 := by
  unfold tailWord_48877
  simp only [CollatzResearch.WordTrace]
  refine ⟨1782690643934451372128885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1188460429289634248085923 1782690643934451372128885)
  ·
    refine ⟨167127247868854816137083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1782690643934451372128885 167127247868854816137083)
    ·
      refine ⟨250690871803282224205625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167127247868854816137083 250690871803282224205625)
      ·
        refine ⟨188018153852461668154219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250690871803282224205625 188018153852461668154219)
        ·
          refine ⟨282027230778692502231329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188018153852461668154219 282027230778692502231329)
          ·
            refine ⟨211520423084019376673497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282027230778692502231329 211520423084019376673497)
            ·
              refine ⟨158640317313014532505123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211520423084019376673497 158640317313014532505123)
              ·
                refine ⟨237960475969521798757685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158640317313014532505123 237960475969521798757685)
                ·
                  refine ⟨22308794622142668633533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 237960475969521798757685 22308794622142668633533)
                  ·
                    rfl

theorem cell20_48877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_48877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48877 prefixEnd_48877 := by exact prefixLift 48877
  have htrace : WordTrace (prefixWord ++ tailWord_48877) baseStart_48877 baseEnd_48877 := by
    simpa [prefixWord, tailWord_48877, baseEnd_48877] using wordTrace_append hprefix tailTrace_48877
  have hstable : (prefixWord ++ tailWord_48877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48877).length < 2 ^ (prefixWord ++ tailWord_48877).sum := by decide
  have hdescent : baseEnd_48877 < baseStart_48877 := by decide
  rcases family_descends (prefixWord ++ tailWord_48877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48905 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 6]
def baseStart_48905 : Nat := 118140960795 + 48905 * 2 ^ 59
def prefixEnd_48905 : Nat := 4983230072969 + 3 ^ 40 * 48905 * 2
def baseEnd_48905 : Nat := 22321574585099015700085

theorem tailTrace_48905 : CollatzResearch.WordTrace tailWord_48905 prefixEnd_48905 22321574585099015700085 := by
  unfold tailWord_48905
  simp only [CollatzResearch.WordTrace]
  refine ⟨1783711887833012154148169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1189141258555341436098779 1783711887833012154148169)
  ·
    refine ⟨1337783915874759115611127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1783711887833012154148169 1337783915874759115611127)
    ·
      refine ⟨2006675873812138673416691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337783915874759115611127 2006675873812138673416691)
      ·
        refine ⟨3010013810718208010125037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006675873812138673416691 3010013810718208010125037)
        ·
          refine ⟨1128755179019328003796889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3010013810718208010125037 1128755179019328003796889)
          ·
            refine ⟨846566384264496002847667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1128755179019328003796889 846566384264496002847667)
            ·
              refine ⟨1269849576396744004271501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846566384264496002847667 1269849576396744004271501)
              ·
                refine ⟨476193591148779001601813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1269849576396744004271501 476193591148779001601813)
                ·
                  refine ⟨22321574585099015700085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 476193591148779001601813 22321574585099015700085)
                  ·
                    rfl

theorem cell20_48905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_48905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48905 prefixEnd_48905 := by exact prefixLift 48905
  have htrace : WordTrace (prefixWord ++ tailWord_48905) baseStart_48905 baseEnd_48905 := by
    simpa [prefixWord, tailWord_48905, baseEnd_48905] using wordTrace_append hprefix tailTrace_48905
  have hstable : (prefixWord ++ tailWord_48905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48905).length < 2 ^ (prefixWord ++ tailWord_48905).sum := by decide
  have hdescent : baseEnd_48905 < baseStart_48905 := by decide
  rcases family_descends (prefixWord ++ tailWord_48905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48932 : List Nat := [2, 3, 1, 3, 2, 2, 2, 2, 3]
def baseStart_48932 : Nat := 118140960795 + 48932 * 2 ^ 59
def prefixEnd_48932 : Nat := 4983230072969 + 3 ^ 40 * 48932 * 2
def baseEnd_48932 : Nat := 22333898120806921799975

theorem tailTrace_48932 : CollatzResearch.WordTrace tailWord_48932 prefixEnd_48932 22333898120806921799975 := by
  unfold tailWord_48932
  simp only [CollatzResearch.WordTrace]
  refine ⟨892348329367597882690525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1189797772490130510254033 892348329367597882690525)
  ·
    refine ⟨334630623512849206008947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 892348329367597882690525 334630623512849206008947)
    ·
      refine ⟨501945935269273809013421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334630623512849206008947 501945935269273809013421)
      ·
        refine ⟨188229725725977678380033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 501945935269273809013421 188229725725977678380033)
        ·
          refine ⟨141172294294483258785025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188229725725977678380033 141172294294483258785025)
          ·
            refine ⟨105879220720862444088769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141172294294483258785025 105879220720862444088769)
            ·
              refine ⟨79409415540646833066577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105879220720862444088769 79409415540646833066577)
              ·
                refine ⟨59557061655485124799933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79409415540646833066577 59557061655485124799933)
                ·
                  refine ⟨22333898120806921799975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59557061655485124799933 22333898120806921799975)
                  ·
                    rfl

theorem cell20_48932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_48932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48932 prefixEnd_48932 := by exact prefixLift 48932
  have htrace : WordTrace (prefixWord ++ tailWord_48932) baseStart_48932 baseEnd_48932 := by
    simpa [prefixWord, tailWord_48932, baseEnd_48932] using wordTrace_append hprefix tailTrace_48932
  have hstable : (prefixWord ++ tailWord_48932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48932).length < 2 ^ (prefixWord ++ tailWord_48932).sum := by decide
  have hdescent : baseEnd_48932 < baseStart_48932 := by decide
  rcases family_descends (prefixWord ++ tailWord_48932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48942 : List Nat := [4, 1, 3, 2, 3, 1, 1, 5]
def baseStart_48942 : Nat := 118140960795 + 48942 * 2 ^ 59
def prefixEnd_48942 : Nat := 4983230072969 + 3 ^ 40 * 48942 * 2
def baseEnd_48942 : Nat := 7446154131097110488867

theorem tailTrace_48942 : CollatzResearch.WordTrace tailWord_48942 prefixEnd_48942 7446154131097110488867 := by
  unfold tailWord_48942
  simp only [CollatzResearch.WordTrace]
  refine ⟨223132673587370934155635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1190040925799311648830053 223132673587370934155635)
  ·
    refine ⟨334699010381056401233453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223132673587370934155635 334699010381056401233453)
    ·
      refine ⟨125512128892896150462545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334699010381056401233453 125512128892896150462545)
      ·
        refine ⟨94134096669672112846909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125512128892896150462545 94134096669672112846909)
        ·
          refine ⟨35300286251127042317591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94134096669672112846909 35300286251127042317591)
          ·
            refine ⟨52950429376690563476387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35300286251127042317591 52950429376690563476387)
            ·
              refine ⟨79425644065035845214581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52950429376690563476387 79425644065035845214581)
              ·
                refine ⟨7446154131097110488867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79425644065035845214581 7446154131097110488867)
                ·
                  rfl

theorem cell20_48942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_48942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48942 prefixEnd_48942 := by exact prefixLift 48942
  have htrace : WordTrace (prefixWord ++ tailWord_48942) baseStart_48942 baseEnd_48942 := by
    simpa [prefixWord, tailWord_48942, baseEnd_48942] using wordTrace_append hprefix tailTrace_48942
  have hstable : (prefixWord ++ tailWord_48942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48942).length < 2 ^ (prefixWord ++ tailWord_48942).sum := by decide
  have hdescent : baseEnd_48942 < baseStart_48942 := by decide
  rcases family_descends (prefixWord ++ tailWord_48942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48946 : List Nat := [3, 2, 1, 1, 3, 4, 1, 5]
def baseStart_48946 : Nat := 118140960795 + 48946 * 2 ^ 59
def prefixEnd_48946 : Nat := 4983230072969 + 3 ^ 40 * 48946 * 2
def baseEnd_48946 : Nat := 7446762700761698444417

theorem tailTrace_48946 : CollatzResearch.WordTrace tailWord_48946 prefixEnd_48946 7446762700761698444417 := by
  unfold tailWord_48946
  simp only [CollatzResearch.WordTrace]
  refine ⟨446301820171119039097673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1190138187122984104260461 446301820171119039097673)
  ·
    refine ⟨334726365128339279323255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 446301820171119039097673 334726365128339279323255)
    ·
      refine ⟨502089547692508918984883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334726365128339279323255 502089547692508918984883)
      ·
        refine ⟨753134321538763378477325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502089547692508918984883 753134321538763378477325)
        ·
          refine ⟨282425370577036266928997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 753134321538763378477325 282425370577036266928997)
          ·
            refine ⟨52954756983194300049187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 282425370577036266928997 52954756983194300049187)
            ·
              refine ⟨79432135474791450073781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52954756983194300049187 79432135474791450073781)
              ·
                refine ⟨7446762700761698444417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79432135474791450073781 7446762700761698444417)
                ·
                  rfl

theorem cell20_48946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_48946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48946 prefixEnd_48946 := by exact prefixLift 48946
  have htrace : WordTrace (prefixWord ++ tailWord_48946) baseStart_48946 baseEnd_48946 := by
    simpa [prefixWord, tailWord_48946, baseEnd_48946] using wordTrace_append hprefix tailTrace_48946
  have hstable : (prefixWord ++ tailWord_48946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48946).length < 2 ^ (prefixWord ++ tailWord_48946).sum := by decide
  have hdescent : baseEnd_48946 < baseStart_48946 := by decide
  rcases family_descends (prefixWord ++ tailWord_48946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48973 : List Nat := [1, 6, 1, 2, 1, 2, 2, 3, 2]
def baseStart_48973 : Nat := 118140960795 + 48973 * 2 ^ 59
def prefixEnd_48973 : Nat := 4983230072969 + 3 ^ 40 * 48973 * 2
def baseEnd_48973 : Nat := 22352611637993001433141

theorem tailTrace_48973 : CollatzResearch.WordTrace tailWord_48973 prefixEnd_48973 22352611637993001433141 := by
  unfold tailWord_48973
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786192051586659767623573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1190794701057773178415715 1786192051586659767623573)
  ·
    refine ⟨83727752418124676607355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1786192051586659767623573 83727752418124676607355)
    ·
      refine ⟨125591628627187014911033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83727752418124676607355 125591628627187014911033)
      ·
        refine ⟨94193721470390261183275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125591628627187014911033 94193721470390261183275)
        ·
          refine ⟨141290582205585391774913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94193721470390261183275 141290582205585391774913)
          ·
            refine ⟨105967936654189043831185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141290582205585391774913 105967936654189043831185)
            ·
              refine ⟨79475952490641782873389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105967936654189043831185 79475952490641782873389)
              ·
                refine ⟨29803482183990668577521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79475952490641782873389 29803482183990668577521)
                ·
                  refine ⟨22352611637993001433141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29803482183990668577521 22352611637993001433141)
                  ·
                    rfl

theorem cell20_48973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_48973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48973 prefixEnd_48973 := by exact prefixLift 48973
  have htrace : WordTrace (prefixWord ++ tailWord_48973) baseStart_48973 baseEnd_48973 := by
    simpa [prefixWord, tailWord_48973, baseEnd_48973] using wordTrace_append hprefix tailTrace_48973
  have hstable : (prefixWord ++ tailWord_48973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48973).length < 2 ^ (prefixWord ++ tailWord_48973).sum := by decide
  have hdescent : baseEnd_48973 < baseStart_48973 := by decide
  rcases family_descends (prefixWord ++ tailWord_48973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48977 : List Nat := [1, 2, 2, 1, 5, 1, 1, 5, 2]
def baseStart_48977 : Nat := 118140960795 + 48977 * 2 ^ 59
def prefixEnd_48977 : Nat := 4983230072969 + 3 ^ 40 * 48977 * 2
def baseEnd_48977 : Nat := 22354437346986765299791

theorem tailTrace_48977 : CollatzResearch.WordTrace tailWord_48977 prefixEnd_48977 22354437346986765299791 := by
  unfold tailWord_48977
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786337943572168450769185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1190891962381445633846123 1786337943572168450769185)
  ·
    refine ⟨1339753457679126338076889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1786337943572168450769185 1339753457679126338076889)
    ·
      refine ⟨1004815093259344753557667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1339753457679126338076889 1004815093259344753557667)
      ·
        refine ⟨1507222639889017130336501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004815093259344753557667 1507222639889017130336501)
        ·
          refine ⟨141302122489595355969047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1507222639889017130336501 141302122489595355969047)
          ·
            refine ⟨211953183734393033953571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141302122489595355969047 211953183734393033953571)
            ·
              refine ⟨317929775601589550930357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211953183734393033953571 317929775601589550930357)
              ·
                refine ⟨29805916462649020399721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 317929775601589550930357 29805916462649020399721)
                ·
                  refine ⟨22354437346986765299791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29805916462649020399721 22354437346986765299791)
                  ·
                    rfl

theorem cell20_48977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 2].length) (baseStart_48977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48977 prefixEnd_48977 := by exact prefixLift 48977
  have htrace : WordTrace (prefixWord ++ tailWord_48977) baseStart_48977 baseEnd_48977 := by
    simpa [prefixWord, tailWord_48977, baseEnd_48977] using wordTrace_append hprefix tailTrace_48977
  have hstable : (prefixWord ++ tailWord_48977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48977).length < 2 ^ (prefixWord ++ tailWord_48977).sum := by decide
  have hdescent : baseEnd_48977 < baseStart_48977 := by decide
  rcases family_descends (prefixWord ++ tailWord_48977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48991 : List Nat := [1, 1, 2, 3, 1, 4, 3, 2, 3]
def baseStart_48991 : Nat := 118140960795 + 48991 * 2 ^ 59
def prefixEnd_48991 : Nat := 4983230072969 + 3 ^ 40 * 48991 * 2
def baseEnd_48991 : Nat := 22360827328464938833067

theorem tailTrace_48991 : CollatzResearch.WordTrace tailWord_48991 prefixEnd_48991 22360827328464938833067 := by
  unfold tailWord_48991
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786848565521448841778827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1191232377014299227852551 1786848565521448841778827)
  ·
    refine ⟨2680272848282173262668241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1786848565521448841778827 2680272848282173262668241)
    ·
      refine ⟨2010204636211629947001181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2680272848282173262668241 2010204636211629947001181)
      ·
        refine ⟨753826738579361230125443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2010204636211629947001181 753826738579361230125443)
        ·
          refine ⟨1130740107869041845188165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753826738579361230125443 1130740107869041845188165)
          ·
            refine ⟨212013770225445345972781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1130740107869041845188165 212013770225445345972781)
            ·
              refine ⟨79505163834542004739793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212013770225445345972781 79505163834542004739793)
              ·
                refine ⟨59628872875906503554845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79505163834542004739793 59628872875906503554845)
                ·
                  refine ⟨22360827328464938833067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59628872875906503554845 22360827328464938833067)
                  ·
                    rfl

theorem cell20_48991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 3].length) (baseStart_48991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48991 prefixEnd_48991 := by exact prefixLift 48991
  have htrace : WordTrace (prefixWord ++ tailWord_48991) baseStart_48991 baseEnd_48991 := by
    simpa [prefixWord, tailWord_48991, baseEnd_48991] using wordTrace_append hprefix tailTrace_48991
  have hstable : (prefixWord ++ tailWord_48991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48991).length < 2 ^ (prefixWord ++ tailWord_48991).sum := by decide
  have hdescent : baseEnd_48991 < baseStart_48991 := by decide
  rcases family_descends (prefixWord ++ tailWord_48991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_48994 : List Nat := [3, 3, 2, 1, 2, 1, 2, 4, 2]
def baseStart_48994 : Nat := 118140960795 + 48994 * 2 ^ 59
def prefixEnd_48994 : Nat := 4983230072969 + 3 ^ 40 * 48994 * 2
def baseEnd_48994 : Nat := 22362196610210261733055

theorem tailTrace_48994 : CollatzResearch.WordTrace tailWord_48994 prefixEnd_48994 22362196610210261733055 := by
  unfold tailWord_48994
  simp only [CollatzResearch.WordTrace]
  refine ⟨446739496127645088534509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1191305323007053569425357 446739496127645088534509)
  ·
    refine ⟨167527311047866908200441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 446739496127645088534509 167527311047866908200441)
    ·
      refine ⟨125645483285900181150331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167527311047866908200441 125645483285900181150331)
      ·
        refine ⟨188468224928850271725497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125645483285900181150331 188468224928850271725497)
        ·
          refine ⟨141351168696637703794123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188468224928850271725497 141351168696637703794123)
          ·
            refine ⟨212026753044956555691185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141351168696637703794123 212026753044956555691185)
            ·
              refine ⟨159020064783717416768389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212026753044956555691185 159020064783717416768389)
              ·
                refine ⟨29816262146947015644073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159020064783717416768389 29816262146947015644073)
                ·
                  refine ⟨22362196610210261733055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29816262146947015644073 22362196610210261733055)
                  ·
                    rfl

theorem cell20_48994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_48994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_48994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_48994 prefixEnd_48994 := by exact prefixLift 48994
  have htrace : WordTrace (prefixWord ++ tailWord_48994) baseStart_48994 baseEnd_48994 := by
    simpa [prefixWord, tailWord_48994, baseEnd_48994] using wordTrace_append hprefix tailTrace_48994
  have hstable : (prefixWord ++ tailWord_48994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_48994).length < 2 ^ (prefixWord ++ tailWord_48994).sum := by decide
  have hdescent : baseEnd_48994 < baseStart_48994 := by decide
  rcases family_descends (prefixWord ++ tailWord_48994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49053 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 4]
def baseStart_49053 : Nat := 118140960795 + 49053 * 2 ^ 59
def prefixEnd_49053 : Nat := 4983230072969 + 3 ^ 40 * 49053 * 2
def baseEnd_49053 : Nat := 22389125817868278766147

theorem tailTrace_49053 : CollatzResearch.WordTrace tailWord_49053 prefixEnd_49053 22389125817868278766147 := by
  unfold tailWord_49053
  simp only [CollatzResearch.WordTrace]
  refine ⟨1789109891296833430535813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1192739927531222287023875 1789109891296833430535813)
  ·
    refine ⟨335458104618156268225465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1789109891296833430535813 335458104618156268225465)
    ·
      refine ⟨251593578463617201169099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335458104618156268225465 251593578463617201169099)
      ·
        refine ⟨377390367695425801753649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251593578463617201169099 377390367695425801753649)
        ·
          refine ⟨283042775771569351315237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377390367695425801753649 283042775771569351315237)
          ·
            refine ⟨53070520457169253371607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283042775771569351315237 53070520457169253371607)
            ·
              refine ⟨79605780685753880057411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53070520457169253371607 79605780685753880057411)
              ·
                refine ⟨119408671028630820086117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79605780685753880057411 119408671028630820086117)
                ·
                  refine ⟨22389125817868278766147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119408671028630820086117 22389125817868278766147)
                  ·
                    rfl

theorem cell20_49053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_49053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49053 prefixEnd_49053 := by exact prefixLift 49053
  have htrace : WordTrace (prefixWord ++ tailWord_49053) baseStart_49053 baseEnd_49053 := by
    simpa [prefixWord, tailWord_49053, baseEnd_49053] using wordTrace_append hprefix tailTrace_49053
  have hstable : (prefixWord ++ tailWord_49053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49053).length < 2 ^ (prefixWord ++ tailWord_49053).sum := by decide
  have hdescent : baseEnd_49053 < baseStart_49053 := by decide
  rcases family_descends (prefixWord ++ tailWord_49053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49063 : List Nat := [1, 1, 6, 1, 2, 3, 2, 1, 3]
def baseStart_49063 : Nat := 118140960795 + 49063 * 2 ^ 59
def prefixEnd_49063 : Nat := 4983230072969 + 3 ^ 40 * 49063 * 2
def baseEnd_49063 : Nat := 22393690090352688432773

theorem tailTrace_49063 : CollatzResearch.WordTrace tailWord_49063 prefixEnd_49063 22393690090352688432773 := by
  unfold tailWord_49063
  simp only [CollatzResearch.WordTrace]
  refine ⟨1789474621260605138399843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1192983080840403425599895 1789474621260605138399843)
  ·
    refine ⟨2684211931890907707599765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1789474621260605138399843 2684211931890907707599765)
    ·
      refine ⟨125822434307386298793739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2684211931890907707599765 125822434307386298793739)
      ·
        refine ⟨188733651461079448190609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125822434307386298793739 188733651461079448190609)
        ·
          refine ⟨141550238595809586142957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188733651461079448190609 141550238595809586142957)
          ·
            refine ⟨53081339473428594803609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141550238595809586142957 53081339473428594803609)
            ·
              refine ⟨39811004605071446102707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53081339473428594803609 39811004605071446102707)
              ·
                refine ⟨59716506907607169154061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39811004605071446102707 59716506907607169154061)
                ·
                  refine ⟨22393690090352688432773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59716506907607169154061 22393690090352688432773)
                  ·
                    rfl

theorem cell20_49063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 3].length) (baseStart_49063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49063 prefixEnd_49063 := by exact prefixLift 49063
  have htrace : WordTrace (prefixWord ++ tailWord_49063) baseStart_49063 baseEnd_49063 := by
    simpa [prefixWord, tailWord_49063, baseEnd_49063] using wordTrace_append hprefix tailTrace_49063
  have hstable : (prefixWord ++ tailWord_49063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49063).length < 2 ^ (prefixWord ++ tailWord_49063).sum := by decide
  have hdescent : baseEnd_49063 < baseStart_49063 := by decide
  rcases family_descends (prefixWord ++ tailWord_49063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49119 : List Nat := [1, 1, 2, 3, 4, 1, 3, 5]
def baseStart_49119 : Nat := 118140960795 + 49119 * 2 ^ 59
def prefixEnd_49119 : Nat := 4983230072969 + 3 ^ 40 * 49119 * 2
def baseEnd_49119 : Nat := 7473083338755127521959

theorem tailTrace_49119 : CollatzResearch.WordTrace tailWord_49119 prefixEnd_49119 7473083338755127521959 := by
  unfold tailWord_49119
  simp only [CollatzResearch.WordTrace]
  refine ⟨1791517109057726702438411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1194344739371817801625607 1791517109057726702438411)
  ·
    refine ⟨2687275663586590053657617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1791517109057726702438411 2687275663586590053657617)
    ·
      refine ⟨2015456747689942540243213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2687275663586590053657617 2015456747689942540243213)
      ·
        refine ⟨755796280383728452591205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2015456747689942540243213 755796280383728452591205)
        ·
          refine ⟨141711802571949084860851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 755796280383728452591205 141711802571949084860851)
          ·
            refine ⟨212567703857923627291277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141711802571949084860851 212567703857923627291277)
            ·
              refine ⟨79712888946721360234229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212567703857923627291277 79712888946721360234229)
              ·
                refine ⟨7473083338755127521959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79712888946721360234229 7473083338755127521959)
                ·
                  rfl

theorem cell20_49119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 5].length) (baseStart_49119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49119 prefixEnd_49119 := by exact prefixLift 49119
  have htrace : WordTrace (prefixWord ++ tailWord_49119) baseStart_49119 baseEnd_49119 := by
    simpa [prefixWord, tailWord_49119, baseEnd_49119] using wordTrace_append hprefix tailTrace_49119
  have hstable : (prefixWord ++ tailWord_49119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49119).length < 2 ^ (prefixWord ++ tailWord_49119).sum := by decide
  have hdescent : baseEnd_49119 < baseStart_49119 := by decide
  rcases family_descends (prefixWord ++ tailWord_49119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49156 : List Nat := [2, 3, 2, 4, 2, 1, 1, 2, 3]
def baseStart_49156 : Nat := 118140960795 + 49156 * 2 ^ 59
def prefixEnd_49156 : Nat := 4983230072969 + 3 ^ 40 * 49156 * 2
def baseEnd_49156 : Nat := 22436137824457698332393

theorem tailTrace_49156 : CollatzResearch.WordTrace tailWord_49156 prefixEnd_49156 22436137824457698332393 := by
  unfold tailWord_49156
  simp only [CollatzResearch.WordTrace]
  refine ⟨896433304961841010767661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1195244406615788014356881 896433304961841010767661)
  ·
    refine ⟨336162489360690379037873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 896433304961841010767661 336162489360690379037873)
    ·
      refine ⟨252121867020517784278405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336162489360690379037873 252121867020517784278405)
      ·
        refine ⟨47272850066347084552201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252121867020517784278405 47272850066347084552201)
        ·
          refine ⟨35454637549760313414151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47272850066347084552201 35454637549760313414151)
          ·
            refine ⟨53181956324640470121227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35454637549760313414151 53181956324640470121227)
            ·
              refine ⟨79772934486960705181841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53181956324640470121227 79772934486960705181841)
              ·
                refine ⟨59829700865220528886381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79772934486960705181841 59829700865220528886381)
                ·
                  refine ⟨22436137824457698332393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59829700865220528886381 22436137824457698332393)
                  ·
                    rfl

theorem cell20_49156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_49156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49156 prefixEnd_49156 := by exact prefixLift 49156
  have htrace : WordTrace (prefixWord ++ tailWord_49156) baseStart_49156 baseEnd_49156 := by
    simpa [prefixWord, tailWord_49156, baseEnd_49156] using wordTrace_append hprefix tailTrace_49156
  have hstable : (prefixWord ++ tailWord_49156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49156).length < 2 ^ (prefixWord ++ tailWord_49156).sum := by decide
  have hdescent : baseEnd_49156 < baseStart_49156 := by decide
  rcases family_descends (prefixWord ++ tailWord_49156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49164 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_49164 : Nat := 118140960795 + 49164 * 2 ^ 59
def prefixEnd_49164 : Nat := 4983230072969 + 3 ^ 40 * 49164 * 2
def baseEnd_49164 : Nat := 22439789242445226065693

theorem tailTrace_49164 : CollatzResearch.WordTrace tailWord_49164 prefixEnd_49164 22439789242445226065693 := by
  unfold tailWord_49164
  simp only [CollatzResearch.WordTrace]
  refine ⟨896579196947349693913273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1195438929263132925217697 896579196947349693913273)
  ·
    refine ⟨672434397710512270434955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 896579196947349693913273 672434397710512270434955)
    ·
      refine ⟨1008651596565768405652433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 672434397710512270434955 1008651596565768405652433)
      ·
        refine ⟨756488697424326304239325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1008651596565768405652433 756488697424326304239325)
        ·
          refine ⟨283683261534122364089747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 756488697424326304239325 283683261534122364089747)
          ·
            refine ⟨425524892301183546134621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283683261534122364089747 425524892301183546134621)
            ·
              refine ⟨159571834612943829800483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 425524892301183546134621 159571834612943829800483)
              ·
                refine ⟨239357751919415744700725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159571834612943829800483 239357751919415744700725)
                ·
                  refine ⟨22439789242445226065693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239357751919415744700725 22439789242445226065693)
                  ·
                    rfl

theorem cell20_49164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_49164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49164 prefixEnd_49164 := by exact prefixLift 49164
  have htrace : WordTrace (prefixWord ++ tailWord_49164) baseStart_49164 baseEnd_49164 := by
    simpa [prefixWord, tailWord_49164, baseEnd_49164] using wordTrace_append hprefix tailTrace_49164
  have hstable : (prefixWord ++ tailWord_49164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49164).length < 2 ^ (prefixWord ++ tailWord_49164).sum := by decide
  have hdescent : baseEnd_49164 < baseStart_49164 := by decide
  rcases family_descends (prefixWord ++ tailWord_49164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49171 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 4]
def baseStart_49171 : Nat := 118140960795 + 49171 * 2 ^ 59
def prefixEnd_49171 : Nat := 4983230072969 + 3 ^ 40 * 49171 * 2
def baseEnd_49171 : Nat := 22442984233184312832331

theorem tailTrace_49171 : CollatzResearch.WordTrace tailWord_49171 prefixEnd_49171 22442984233184312832331 := by
  unfold tailWord_49171
  simp only [CollatzResearch.WordTrace]
  refine ⟨1793413704869339583331367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1195609136579559722220911 1793413704869339583331367)
  ·
    refine ⟨2690120557304009374997051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1793413704869339583331367 2690120557304009374997051)
    ·
      refine ⟨4035180835956014062495577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2690120557304009374997051 4035180835956014062495577)
      ·
        refine ⟨3026385626967010546871683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4035180835956014062495577 3026385626967010546871683)
        ·
          refine ⟨4539578440450515820307525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3026385626967010546871683 4539578440450515820307525)
          ·
            refine ⟨851170957584471716307661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4539578440450515820307525 851170957584471716307661)
            ·
              refine ⟨319189109094176893615373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 851170957584471716307661 319189109094176893615373)
              ·
                refine ⟨119695915910316335105765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319189109094176893615373 119695915910316335105765)
                ·
                  refine ⟨22442984233184312832331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119695915910316335105765 22442984233184312832331)
                  ·
                    rfl

theorem cell20_49171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_49171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49171 prefixEnd_49171 := by exact prefixLift 49171
  have htrace : WordTrace (prefixWord ++ tailWord_49171) baseStart_49171 baseEnd_49171 := by
    simpa [prefixWord, tailWord_49171, baseEnd_49171] using wordTrace_append hprefix tailTrace_49171
  have hstable : (prefixWord ++ tailWord_49171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49171).length < 2 ^ (prefixWord ++ tailWord_49171).sum := by decide
  have hdescent : baseEnd_49171 < baseStart_49171 := by decide
  rcases family_descends (prefixWord ++ tailWord_49171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49202 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_49202 : Nat := 118140960795 + 49202 * 2 ^ 59
def prefixEnd_49202 : Nat := 4983230072969 + 3 ^ 40 * 49202 * 2
def baseEnd_49202 : Nat := 22457133477885982798871

theorem tailTrace_49202 : CollatzResearch.WordTrace tailWord_49202 prefixEnd_49202 22457133477885982798871 := by
  unfold tailWord_49202
  simp only [CollatzResearch.WordTrace]
  refine ⟨448636091939257969427465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1196362911838021251806573 448636091939257969427465)
  ·
    refine ⟨336477068954443477070599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 448636091939257969427465 336477068954443477070599)
    ·
      refine ⟨504715603431665215605899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336477068954443477070599 504715603431665215605899)
      ·
        refine ⟨757073405147497823408849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504715603431665215605899 757073405147497823408849)
        ·
          refine ⟨567805053860623367556637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 757073405147497823408849 567805053860623367556637)
          ·
            refine ⟨212926895197733762833739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 567805053860623367556637 212926895197733762833739)
            ·
              refine ⟨319390342796600644250609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212926895197733762833739 319390342796600644250609)
              ·
                refine ⟨239542757097450483187957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319390342796600644250609 239542757097450483187957)
                ·
                  refine ⟨22457133477885982798871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239542757097450483187957 22457133477885982798871)
                  ·
                    rfl

theorem cell20_49202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_49202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49202 prefixEnd_49202 := by exact prefixLift 49202
  have htrace : WordTrace (prefixWord ++ tailWord_49202) baseStart_49202 baseEnd_49202 := by
    simpa [prefixWord, tailWord_49202, baseEnd_49202] using wordTrace_append hprefix tailTrace_49202
  have hstable : (prefixWord ++ tailWord_49202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49202).length < 2 ^ (prefixWord ++ tailWord_49202).sum := by decide
  have hdescent : baseEnd_49202 < baseStart_49202 := by decide
  rcases family_descends (prefixWord ++ tailWord_49202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49205 : List Nat := [1, 3, 3, 1, 1, 1, 5, 3, 2]
def baseStart_49205 : Nat := 118140960795 + 49205 * 2 ^ 59
def prefixEnd_49205 : Nat := 4983230072969 + 3 ^ 40 * 49205 * 2
def baseEnd_49205 : Nat := 22458502759631305698859

theorem tailTrace_49205 : CollatzResearch.WordTrace tailWord_49205 prefixEnd_49205 22458502759631305698859 := by
  unfold tailWord_49205
  simp only [CollatzResearch.WordTrace]
  refine ⟨1794653786746163390069069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1196435857830775593379379 1794653786746163390069069)
  ·
    refine ⟨672995170029811271275901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1794653786746163390069069 672995170029811271275901)
    ·
      refine ⟨252373188761179226728463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 672995170029811271275901 252373188761179226728463)
      ·
        refine ⟨378559783141768840092695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252373188761179226728463 378559783141768840092695)
        ·
          refine ⟨567839674712653260139043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378559783141768840092695 567839674712653260139043)
          ·
            refine ⟨851759512068979890208565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567839674712653260139043 851759512068979890208565)
            ·
              refine ⟨79852454256466864707053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 851759512068979890208565 79852454256466864707053)
              ·
                refine ⟨29944670346175074265145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79852454256466864707053 29944670346175074265145)
                ·
                  refine ⟨22458502759631305698859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29944670346175074265145 22458502759631305698859)
                  ·
                    rfl

theorem cell20_49205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_49205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49205 prefixEnd_49205 := by exact prefixLift 49205
  have htrace : WordTrace (prefixWord ++ tailWord_49205) baseStart_49205 baseEnd_49205 := by
    simpa [prefixWord, tailWord_49205, baseEnd_49205] using wordTrace_append hprefix tailTrace_49205
  have hstable : (prefixWord ++ tailWord_49205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49205).length < 2 ^ (prefixWord ++ tailWord_49205).sum := by decide
  have hdescent : baseEnd_49205 < baseStart_49205 := by decide
  rcases family_descends (prefixWord ++ tailWord_49205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49216 : List Nat := [2, 1, 1, 2, 2, 4, 8]
def baseStart_49216 : Nat := 118140960795 + 49216 * 2 ^ 59
def prefixEnd_49216 : Nat := 4983230072969 + 3 ^ 40 * 49216 * 2
def baseEnd_49216 : Nat := 2495947051040461814683

theorem tailTrace_49216 : CollatzResearch.WordTrace tailWord_49216 prefixEnd_49216 2495947051040461814683 := by
  unfold tailWord_49216
  simp only [CollatzResearch.WordTrace]
  refine ⟨897527494853156134359751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1196703326470874845813001 897527494853156134359751)
  ·
    refine ⟨1346291242279734201539627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 897527494853156134359751 1346291242279734201539627)
    ·
      refine ⟨2019436863419601302309441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1346291242279734201539627 2019436863419601302309441)
      ·
        refine ⟨1514577647564700976732081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2019436863419601302309441 1514577647564700976732081)
        ·
          refine ⟨1135933235673525732549061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1514577647564700976732081 1135933235673525732549061)
          ·
            refine ⟨212987481688786074852949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1135933235673525732549061 212987481688786074852949)
            ·
              refine ⟨2495947051040461814683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 212987481688786074852949 2495947051040461814683)
              ·
                rfl

theorem cell20_49216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 8].length) (baseStart_49216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49216 prefixEnd_49216 := by exact prefixLift 49216
  have htrace : WordTrace (prefixWord ++ tailWord_49216) baseStart_49216 baseEnd_49216 := by
    simpa [prefixWord, tailWord_49216, baseEnd_49216] using wordTrace_append hprefix tailTrace_49216
  have hstable : (prefixWord ++ tailWord_49216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49216).length < 2 ^ (prefixWord ++ tailWord_49216).sum := by decide
  have hdescent : baseEnd_49216 < baseStart_49216 := by decide
  rcases family_descends (prefixWord ++ tailWord_49216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49288 : List Nat := [2, 1, 3, 4, 1, 3, 1, 5]
def baseStart_49288 : Nat := 118140960795 + 49288 * 2 ^ 59
def prefixEnd_49288 : Nat := 4983230072969 + 3 ^ 40 * 49288 * 2
def baseEnd_49288 : Nat := 7498795407083968643951

theorem tailTrace_49288 : CollatzResearch.WordTrace tailWord_49288 prefixEnd_49288 7498795407083968643951 := by
  unfold tailWord_49288
  simp only [CollatzResearch.WordTrace]
  refine ⟨898840522722734282670259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1198454030296979043560345 898840522722734282670259)
  ·
    refine ⟨1348260784084101424005389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 898840522722734282670259 1348260784084101424005389)
    ·
      refine ⟨505597794031538034002021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1348260784084101424005389 505597794031538034002021)
      ·
        refine ⟨94799586380913381375379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 505597794031538034002021 94799586380913381375379)
        ·
          refine ⟨142199379571370072063069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94799586380913381375379 142199379571370072063069)
          ·
            refine ⟨53324767339263777023651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142199379571370072063069 53324767339263777023651)
            ·
              refine ⟨79987151008895665535477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53324767339263777023651 79987151008895665535477)
              ·
                refine ⟨7498795407083968643951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79987151008895665535477 7498795407083968643951)
                ·
                  rfl

theorem cell20_49288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_49288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49288 prefixEnd_49288 := by exact prefixLift 49288
  have htrace : WordTrace (prefixWord ++ tailWord_49288) baseStart_49288 baseEnd_49288 := by
    simpa [prefixWord, tailWord_49288, baseEnd_49288] using wordTrace_append hprefix tailTrace_49288
  have hstable : (prefixWord ++ tailWord_49288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49288).length < 2 ^ (prefixWord ++ tailWord_49288).sum := by decide
  have hdescent : baseEnd_49288 < baseStart_49288 := by decide
  rcases family_descends (prefixWord ++ tailWord_49288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49299 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 7]
def baseStart_49299 : Nat := 118140960795 + 49299 * 2 ^ 59
def prefixEnd_49299 : Nat := 4983230072969 + 3 ^ 40 * 49299 * 2
def baseEnd_49299 : Nat := 22501406920984756565141

theorem tailTrace_49299 : CollatzResearch.WordTrace tailWord_49299 prefixEnd_49299 22501406920984756565141 := by
  unfold tailWord_49299
  simp only [CollatzResearch.WordTrace]
  refine ⟨1798082248405617443990951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1198721498937078295993967 1798082248405617443990951)
  ·
    refine ⟨2697123372608426165986427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1798082248405617443990951 2697123372608426165986427)
    ·
      refine ⟨4045685058912639248979641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2697123372608426165986427 4045685058912639248979641)
      ·
        refine ⟨3034263794184479436734731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4045685058912639248979641 3034263794184479436734731)
        ·
          refine ⟨4551395691276719155102097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034263794184479436734731 4551395691276719155102097)
          ·
            refine ⟨3413546768457539366326573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4551395691276719155102097 3413546768457539366326573)
            ·
              refine ⟨1280080038171577262372465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3413546768457539366326573 1280080038171577262372465)
              ·
                refine ⟨960060028628682946779349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280080038171577262372465 960060028628682946779349)
                ·
                  refine ⟨22501406920984756565141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 960060028628682946779349 22501406920984756565141)
                  ·
                    rfl

theorem cell20_49299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_49299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49299 prefixEnd_49299 := by exact prefixLift 49299
  have htrace : WordTrace (prefixWord ++ tailWord_49299) baseStart_49299 baseEnd_49299 := by
    simpa [prefixWord, tailWord_49299, baseEnd_49299] using wordTrace_append hprefix tailTrace_49299
  have hstable : (prefixWord ++ tailWord_49299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49299).length < 2 ^ (prefixWord ++ tailWord_49299).sum := by decide
  have hdescent : baseEnd_49299 < baseStart_49299 := by decide
  rcases family_descends (prefixWord ++ tailWord_49299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49329 : List Nat := [1, 2, 2, 5, 3, 1, 1, 2, 3]
def baseStart_49329 : Nat := 118140960795 + 49329 * 2 ^ 59
def prefixEnd_49329 : Nat := 4983230072969 + 3 ^ 40 * 49329 * 2
def baseEnd_49329 : Nat := 22515099738437985565019

theorem tailTrace_49329 : CollatzResearch.WordTrace tailWord_49329 prefixEnd_49329 22515099738437985565019 := by
  unfold tailWord_49329
  simp only [CollatzResearch.WordTrace]
  refine ⟨1799176438296932567583041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1199450958864621711722027 1799176438296932567583041)
  ·
    refine ⟨1349382328722699425687281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1799176438296932567583041 1349382328722699425687281)
    ·
      refine ⟨1012036746542024569265461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1349382328722699425687281 1012036746542024569265461)
      ·
        refine ⟨94878444988314803368637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1012036746542024569265461 94878444988314803368637)
        ·
          refine ⟨35579416870618051263239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94878444988314803368637 35579416870618051263239)
          ·
            refine ⟨53369125305927076894859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35579416870618051263239 53369125305927076894859)
            ·
              refine ⟨80053687958890615342289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53369125305927076894859 80053687958890615342289)
              ·
                refine ⟨60040265969167961506717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80053687958890615342289 60040265969167961506717)
                ·
                  refine ⟨22515099738437985565019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60040265969167961506717 22515099738437985565019)
                  ·
                    rfl

theorem cell20_49329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 3].length) (baseStart_49329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49329 prefixEnd_49329 := by exact prefixLift 49329
  have htrace : WordTrace (prefixWord ++ tailWord_49329) baseStart_49329 baseEnd_49329 := by
    simpa [prefixWord, tailWord_49329, baseEnd_49329] using wordTrace_append hprefix tailTrace_49329
  have hstable : (prefixWord ++ tailWord_49329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49329).length < 2 ^ (prefixWord ++ tailWord_49329).sum := by decide
  have hdescent : baseEnd_49329 < baseStart_49329 := by decide
  rcases family_descends (prefixWord ++ tailWord_49329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49330 : List Nat := [3, 2, 1, 1, 1, 3, 9]
def baseStart_49330 : Nat := 118140960795 + 49330 * 2 ^ 59
def prefixEnd_49330 : Nat := 4983230072969 + 3 ^ 40 * 49330 * 2
def baseEnd_49330 : Nat := 2501728462854047392409

theorem tailTrace_49330 : CollatzResearch.WordTrace tailWord_49330 prefixEnd_49330 2501728462854047392409 := by
  unfold tailWord_49330
  simp only [CollatzResearch.WordTrace]
  refine ⟨449803227823327434592361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1199475274195539825579629 449803227823327434592361)
  ·
    refine ⟨337352420867495575944271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 449803227823327434592361 337352420867495575944271)
    ·
      refine ⟨506028631301243363916407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337352420867495575944271 506028631301243363916407)
      ·
        refine ⟨759042946951865045874611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506028631301243363916407 759042946951865045874611)
        ·
          refine ⟨1138564420427797568811917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759042946951865045874611 1138564420427797568811917)
          ·
            refine ⟨426961657660424088304469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1138564420427797568811917 426961657660424088304469)
            ·
              refine ⟨2501728462854047392409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 426961657660424088304469 2501728462854047392409)
              ·
                rfl

theorem cell20_49330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 9].length) (baseStart_49330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49330 prefixEnd_49330 := by exact prefixLift 49330
  have htrace : WordTrace (prefixWord ++ tailWord_49330) baseStart_49330 baseEnd_49330 := by
    simpa [prefixWord, tailWord_49330, baseEnd_49330] using wordTrace_append hprefix tailTrace_49330
  have hstable : (prefixWord ++ tailWord_49330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49330).length < 2 ^ (prefixWord ++ tailWord_49330).sum := by decide
  have hdescent : baseEnd_49330 < baseStart_49330 := by decide
  rcases family_descends (prefixWord ++ tailWord_49330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49346 : List Nat := [3, 5, 1, 1, 1, 2, 3, 1, 3]
def baseStart_49346 : Nat := 118140960795 + 49346 * 2 ^ 59
def prefixEnd_49346 : Nat := 4983230072969 + 3 ^ 40 * 49346 * 2
def baseEnd_49346 : Nat := 22522859001661481998283

theorem tailTrace_49346 : CollatzResearch.WordTrace tailWord_49346 prefixEnd_49346 22522859001661481998283 := by
  unfold tailWord_49346
  simp only [CollatzResearch.WordTrace]
  refine ⟨449949119808836117737973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1199864319490229647301261 449949119808836117737973)
  ·
    refine ⟨42182729982078386037935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 449949119808836117737973 42182729982078386037935)
    ·
      refine ⟨63274094973117579056903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42182729982078386037935 63274094973117579056903)
      ·
        refine ⟨94911142459676368585355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63274094973117579056903 94911142459676368585355)
        ·
          refine ⟨142366713689514552878033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94911142459676368585355 142366713689514552878033)
          ·
            refine ⟨106775035267135914658525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142366713689514552878033 106775035267135914658525)
            ·
              refine ⟨40040638225175967996947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106775035267135914658525 40040638225175967996947)
              ·
                refine ⟨60060957337763951995421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40040638225175967996947 60060957337763951995421)
                ·
                  refine ⟨22522859001661481998283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60060957337763951995421 22522859001661481998283)
                  ·
                    rfl

theorem cell20_49346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_49346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49346 prefixEnd_49346 := by exact prefixLift 49346
  have htrace : WordTrace (prefixWord ++ tailWord_49346) baseStart_49346 baseEnd_49346 := by
    simpa [prefixWord, tailWord_49346, baseEnd_49346] using wordTrace_append hprefix tailTrace_49346
  have hstable : (prefixWord ++ tailWord_49346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49346).length < 2 ^ (prefixWord ++ tailWord_49346).sum := by decide
  have hdescent : baseEnd_49346 < baseStart_49346 := by decide
  rcases family_descends (prefixWord ++ tailWord_49346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49361 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 4]
def baseStart_49361 : Nat := 118140960795 + 49361 * 2 ^ 59
def prefixEnd_49361 : Nat := 4983230072969 + 3 ^ 40 * 49361 * 2
def baseEnd_49361 : Nat := 22529705410388096498221

theorem tailTrace_49361 : CollatzResearch.WordTrace tailWord_49361 prefixEnd_49361 22529705410388096498221 := by
  unfold tailWord_49361
  simp only [CollatzResearch.WordTrace]
  refine ⟨1800343574181002032747937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1200229049454001355165291 1800343574181002032747937)
  ·
    refine ⟨1350257680635751524560953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1800343574181002032747937 1350257680635751524560953)
    ·
      refine ⟨1012693260476813643420715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1350257680635751524560953 1012693260476813643420715)
      ·
        refine ⟨1519039890715220465131073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012693260476813643420715 1519039890715220465131073)
        ·
          refine ⟨1139279918036415348848305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1519039890715220465131073 1139279918036415348848305)
          ·
            refine ⟨854459938527311511636229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1139279918036415348848305 854459938527311511636229)
            ·
              refine ⟨160211238473870908431793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 854459938527311511636229 160211238473870908431793)
              ·
                refine ⟨120158428855403181323845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160211238473870908431793 120158428855403181323845)
                ·
                  refine ⟨22529705410388096498221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120158428855403181323845 22529705410388096498221)
                  ·
                    rfl

theorem cell20_49361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_49361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49361 prefixEnd_49361 := by exact prefixLift 49361
  have htrace : WordTrace (prefixWord ++ tailWord_49361) baseStart_49361 baseEnd_49361 := by
    simpa [prefixWord, tailWord_49361, baseEnd_49361] using wordTrace_append hprefix tailTrace_49361
  have hstable : (prefixWord ++ tailWord_49361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49361).length < 2 ^ (prefixWord ++ tailWord_49361).sum := by decide
  have hdescent : baseEnd_49361 < baseStart_49361 := by decide
  rcases family_descends (prefixWord ++ tailWord_49361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49395 : List Nat := [1, 1, 1, 2, 2, 4, 5, 2, 2]
def baseStart_49395 : Nat := 118140960795 + 49395 * 2 ^ 59
def prefixEnd_49395 : Nat := 4983230072969 + 3 ^ 40 * 49395 * 2
def baseEnd_49395 : Nat := 22545223936835089364749

theorem tailTrace_49395 : CollatzResearch.WordTrace tailWord_49395 prefixEnd_49395 22545223936835089364749 := by
  unfold tailWord_49395
  simp only [CollatzResearch.WordTrace]
  refine ⟨1801583656057825839485639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1201055770705217226323759 1801583656057825839485639)
  ·
    refine ⟨2702375484086738759228459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1801583656057825839485639 2702375484086738759228459)
    ·
      refine ⟨4053563226130108138842689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2702375484086738759228459 4053563226130108138842689)
      ·
        refine ⟨3040172419597581104132017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4053563226130108138842689 3040172419597581104132017)
        ·
          refine ⟨2280129314698185828099013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3040172419597581104132017 2280129314698185828099013)
          ·
            refine ⟨427524246505909842768565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2280129314698185828099013 427524246505909842768565)
            ·
              refine ⟨40080398109929047759553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 427524246505909842768565 40080398109929047759553)
              ·
                refine ⟨30060298582446785819665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40080398109929047759553 30060298582446785819665)
                ·
                  refine ⟨22545223936835089364749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30060298582446785819665 22545223936835089364749)
                  ·
                    rfl

theorem cell20_49395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 2].length) (baseStart_49395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49395 prefixEnd_49395 := by exact prefixLift 49395
  have htrace : WordTrace (prefixWord ++ tailWord_49395) baseStart_49395 baseEnd_49395 := by
    simpa [prefixWord, tailWord_49395, baseEnd_49395] using wordTrace_append hprefix tailTrace_49395
  have hstable : (prefixWord ++ tailWord_49395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49395).length < 2 ^ (prefixWord ++ tailWord_49395).sum := by decide
  have hdescent : baseEnd_49395 < baseStart_49395 := by decide
  rcases family_descends (prefixWord ++ tailWord_49395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49413 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 7]
def baseStart_49413 : Nat := 118140960795 + 49413 * 2 ^ 59
def prefixEnd_49413 : Nat := 4983230072969 + 3 ^ 40 * 49413 * 2
def baseEnd_49413 : Nat := 22553439627307026764675

theorem tailTrace_49413 : CollatzResearch.WordTrace tailWord_49413 prefixEnd_49413 22553439627307026764675 := by
  unfold tailWord_49413
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802240169992614913640893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1201493446661743275760595 1802240169992614913640893)
  ·
    refine ⟨675840063747230592615335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1802240169992614913640893 675840063747230592615335)
    ·
      refine ⟨1013760095620845888923003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 675840063747230592615335 1013760095620845888923003)
      ·
        refine ⟨1520640143431268833384505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1013760095620845888923003 1520640143431268833384505)
        ·
          refine ⟨1140480107573451625038379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1520640143431268833384505 1140480107573451625038379)
          ·
            refine ⟨1710720161360177437557569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140480107573451625038379 1710720161360177437557569)
            ·
              refine ⟨1283040121020133078168177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1710720161360177437557569 1283040121020133078168177)
              ·
                refine ⟨962280090765099808626133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283040121020133078168177 962280090765099808626133)
                ·
                  refine ⟨22553439627307026764675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 962280090765099808626133 22553439627307026764675)
                  ·
                    rfl

theorem cell20_49413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_49413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49413 prefixEnd_49413 := by exact prefixLift 49413
  have htrace : WordTrace (prefixWord ++ tailWord_49413) baseStart_49413 baseEnd_49413 := by
    simpa [prefixWord, tailWord_49413, baseEnd_49413] using wordTrace_append hprefix tailTrace_49413
  have hstable : (prefixWord ++ tailWord_49413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49413).length < 2 ^ (prefixWord ++ tailWord_49413).sum := by decide
  have hdescent : baseEnd_49413 < baseStart_49413 := by decide
  rcases family_descends (prefixWord ++ tailWord_49413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49444 : List Nat := [2, 3, 1, 3, 1, 10]
def baseStart_49444 : Nat := 118140960795 + 49444 * 2 ^ 59
def prefixEnd_49444 : Nat := 4983230072969 + 3 ^ 40 * 49444 * 2
def baseEnd_49444 : Nat := 835836624889210990045

theorem tailTrace_49444 : CollatzResearch.WordTrace tailWord_49444 prefixEnd_49444 835836624889210990045 := by
  unfold tailWord_49444
  simp only [CollatzResearch.WordTrace]
  refine ⟨901685416440153604009693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1202247221920204805346257 901685416440153604009693)
  ·
    refine ⟨338132031165057601503635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 901685416440153604009693 338132031165057601503635)
    ·
      refine ⟨507198046747586402255453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338132031165057601503635 507198046747586402255453)
      ·
        refine ⟨190199267530344900845795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 507198046747586402255453 190199267530344900845795)
        ·
          refine ⟨285298901295517351268693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190199267530344900845795 285298901295517351268693)
          ·
            refine ⟨835836624889210990045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 285298901295517351268693 835836624889210990045)
            ·
              rfl

theorem cell20_49444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 10].length) (baseStart_49444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49444 prefixEnd_49444 := by exact prefixLift 49444
  have htrace : WordTrace (prefixWord ++ tailWord_49444) baseStart_49444 baseEnd_49444 := by
    simpa [prefixWord, tailWord_49444, baseEnd_49444] using wordTrace_append hprefix tailTrace_49444
  have hstable : (prefixWord ++ tailWord_49444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49444).length < 2 ^ (prefixWord ++ tailWord_49444).sum := by decide
  have hdescent : baseEnd_49444 < baseStart_49444 := by decide
  rcases family_descends (prefixWord ++ tailWord_49444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49450 : List Nat := [3, 1, 4, 2, 2, 1, 1, 4, 2]
def baseStart_49450 : Nat := 118140960795 + 49450 * 2 ^ 59
def prefixEnd_49450 : Nat := 4983230072969 + 3 ^ 40 * 49450 * 2
def baseEnd_49450 : Nat := 22570327435499342531191

theorem tailTrace_49450 : CollatzResearch.WordTrace tailWord_49450 prefixEnd_49450 22570327435499342531191 := by
  unfold tailWord_49450
  simp only [CollatzResearch.WordTrace]
  refine ⟨450897417714642558184451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1202393113905713488491869 450897417714642558184451)
  ·
    refine ⟨676346126571963837276677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 450897417714642558184451 676346126571963837276677)
    ·
      refine ⟨126814898732243219489377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 676346126571963837276677 126814898732243219489377)
      ·
        refine ⟨95111174049182414617033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126814898732243219489377 95111174049182414617033)
        ·
          refine ⟨71333380536886810962775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95111174049182414617033 71333380536886810962775)
          ·
            refine ⟨107000070805330216444163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71333380536886810962775 107000070805330216444163)
            ·
              refine ⟨160500106207995324666245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107000070805330216444163 160500106207995324666245)
              ·
                refine ⟨30093769913999123374921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160500106207995324666245 30093769913999123374921)
                ·
                  refine ⟨22570327435499342531191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30093769913999123374921 22570327435499342531191)
                  ·
                    rfl

theorem cell20_49450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_49450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49450 prefixEnd_49450 := by exact prefixLift 49450
  have htrace : WordTrace (prefixWord ++ tailWord_49450) baseStart_49450 baseEnd_49450 := by
    simpa [prefixWord, tailWord_49450, baseEnd_49450] using wordTrace_append hprefix tailTrace_49450
  have hstable : (prefixWord ++ tailWord_49450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49450).length < 2 ^ (prefixWord ++ tailWord_49450).sum := by decide
  have hdescent : baseEnd_49450 < baseStart_49450 := by decide
  rcases family_descends (prefixWord ++ tailWord_49450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49468 : List Nat := [2, 2, 2, 2, 1, 2, 1, 5, 3]
def baseStart_49468 : Nat := 118140960795 + 49468 * 2 ^ 59
def prefixEnd_49468 : Nat := 4983230072969 + 3 ^ 40 * 49468 * 2
def baseEnd_49468 : Nat := 22578543125971279931117

theorem tailTrace_49468 : CollatzResearch.WordTrace tailWord_49468 prefixEnd_49468 22578543125971279931117 := by
  unfold tailWord_49468
  simp only [CollatzResearch.WordTrace]
  refine ⟨902123092396679653446529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1202830789862239537928705 902123092396679653446529)
  ·
    refine ⟨676592319297509740084897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 902123092396679653446529 676592319297509740084897)
    ·
      refine ⟨507444239473132305063673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 676592319297509740084897 507444239473132305063673)
      ·
        refine ⟨380583179604849228797755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507444239473132305063673 380583179604849228797755)
        ·
          refine ⟨570874769407273843196633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380583179604849228797755 570874769407273843196633)
          ·
            refine ⟨428156077055455382397475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 570874769407273843196633 428156077055455382397475)
            ·
              refine ⟨642234115583183073596213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428156077055455382397475 642234115583183073596213)
              ·
                refine ⟨60209448335923413149645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 642234115583183073596213 60209448335923413149645)
                ·
                  refine ⟨22578543125971279931117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60209448335923413149645 22578543125971279931117)
                  ·
                    rfl

theorem cell20_49468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_49468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49468 prefixEnd_49468 := by exact prefixLift 49468
  have htrace : WordTrace (prefixWord ++ tailWord_49468) baseStart_49468 baseEnd_49468 := by
    simpa [prefixWord, tailWord_49468, baseEnd_49468] using wordTrace_append hprefix tailTrace_49468
  have hstable : (prefixWord ++ tailWord_49468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49468).length < 2 ^ (prefixWord ++ tailWord_49468).sum := by decide
  have hdescent : baseEnd_49468 < baseStart_49468 := by decide
  rcases family_descends (prefixWord ++ tailWord_49468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49513 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 4]
def baseStart_49513 : Nat := 118140960795 + 49513 * 2 ^ 59
def prefixEnd_49513 : Nat := 4983230072969 + 3 ^ 40 * 49513 * 2
def baseEnd_49513 : Nat := 22599082352151123430933

theorem tailTrace_49513 : CollatzResearch.WordTrace tailWord_49513 prefixEnd_49513 22599082352151123430933 := by
  unfold tailWord_49513
  simp only [CollatzResearch.WordTrace]
  refine ⟨1805887469630331992281193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1203924979753554661520795 1805887469630331992281193)
  ·
    refine ⟨1354415602222748994210895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1805887469630331992281193 1354415602222748994210895)
    ·
      refine ⟨2031623403334123491316343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1354415602222748994210895 2031623403334123491316343)
      ·
        refine ⟨3047435105001185236974515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2031623403334123491316343 3047435105001185236974515)
        ·
          refine ⟨4571152657501777855461773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3047435105001185236974515 4571152657501777855461773)
          ·
            refine ⟨1714182246563166695798165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4571152657501777855461773 1714182246563166695798165)
            ·
              refine ⟨80352292807648438865539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1714182246563166695798165 80352292807648438865539)
              ·
                refine ⟨120528439211472658298309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80352292807648438865539 120528439211472658298309)
                ·
                  refine ⟨22599082352151123430933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120528439211472658298309 22599082352151123430933)
                  ·
                    rfl

theorem cell20_49513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_49513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49513 prefixEnd_49513 := by exact prefixLift 49513
  have htrace : WordTrace (prefixWord ++ tailWord_49513) baseStart_49513 baseEnd_49513 := by
    simpa [prefixWord, tailWord_49513, baseEnd_49513] using wordTrace_append hprefix tailTrace_49513
  have hstable : (prefixWord ++ tailWord_49513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49513).length < 2 ^ (prefixWord ++ tailWord_49513).sum := by decide
  have hdescent : baseEnd_49513 < baseStart_49513 := by decide
  rcases family_descends (prefixWord ++ tailWord_49513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49537 : List Nat := [1, 2, 4, 3, 1, 2, 1, 6]
def baseStart_49537 : Nat := 118140960795 + 49537 * 2 ^ 59
def prefixEnd_49537 : Nat := 4983230072969 + 3 ^ 40 * 49537 * 2
def baseEnd_49537 : Nat := 7536678868704568876945

theorem tailTrace_49537 : CollatzResearch.WordTrace tailWord_49537 prefixEnd_49537 7536678868704568876945 := by
  unfold tailWord_49537
  simp only [CollatzResearch.WordTrace]
  refine ⟨1806762821543384091154865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1204508547695589394103243 1806762821543384091154865)
  ·
    refine ⟨1355072116157538068366149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1806762821543384091154865 1355072116157538068366149)
    ·
      refine ⟨254076021779538387818653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1355072116157538068366149 254076021779538387818653)
      ·
        refine ⟨95278508167326895431995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254076021779538387818653 95278508167326895431995)
        ·
          refine ⟨142917762250990343147993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95278508167326895431995 142917762250990343147993)
          ·
            refine ⟨107188321688242757360995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142917762250990343147993 107188321688242757360995)
            ·
              refine ⟨160782482532364136041493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107188321688242757360995 160782482532364136041493)
              ·
                refine ⟨7536678868704568876945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160782482532364136041493 7536678868704568876945)
                ·
                  rfl

theorem cell20_49537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 6].length) (baseStart_49537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49537 prefixEnd_49537 := by exact prefixLift 49537
  have htrace : WordTrace (prefixWord ++ tailWord_49537) baseStart_49537 baseEnd_49537 := by
    simpa [prefixWord, tailWord_49537, baseEnd_49537] using wordTrace_append hprefix tailTrace_49537
  have hstable : (prefixWord ++ tailWord_49537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49537).length < 2 ^ (prefixWord ++ tailWord_49537).sum := by decide
  have hdescent : baseEnd_49537 < baseStart_49537 := by decide
  rcases family_descends (prefixWord ++ tailWord_49537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49547 : List Nat := [1, 1, 1, 1, 4, 6, 1, 3, 2]
def baseStart_49547 : Nat := 118140960795 + 49547 * 2 ^ 59
def prefixEnd_49547 : Nat := 4983230072969 + 3 ^ 40 * 49547 * 2
def baseEnd_49547 : Nat := 22614600878598116297461

theorem tailTrace_49547 : CollatzResearch.WordTrace tailWord_49547 prefixEnd_49547 22614600878598116297461 := by
  unfold tailWord_49547
  simp only [CollatzResearch.WordTrace]
  refine ⟨1807127551507155799018895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1204751701004770532679263 1807127551507155799018895)
  ·
    refine ⟨2710691327260733698528343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1807127551507155799018895 2710691327260733698528343)
    ·
      refine ⟨4066036990891100547792515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2710691327260733698528343 4066036990891100547792515)
      ·
        refine ⟨6099055486336650821688773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4066036990891100547792515 6099055486336650821688773)
        ·
          refine ⟨1143572903688122029066645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6099055486336650821688773 1143572903688122029066645)
          ·
            refine ⟨53604979860380720112499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1143572903688122029066645 53604979860380720112499)
            ·
              refine ⟨80407469790571080168749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53604979860380720112499 80407469790571080168749)
              ·
                refine ⟨30152801171464155063281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80407469790571080168749 30152801171464155063281)
                ·
                  refine ⟨22614600878598116297461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30152801171464155063281 22614600878598116297461)
                  ·
                    rfl

theorem cell20_49547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 2].length) (baseStart_49547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49547 prefixEnd_49547 := by exact prefixLift 49547
  have htrace : WordTrace (prefixWord ++ tailWord_49547) baseStart_49547 baseEnd_49547 := by
    simpa [prefixWord, tailWord_49547, baseEnd_49547] using wordTrace_append hprefix tailTrace_49547
  have hstable : (prefixWord ++ tailWord_49547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49547).length < 2 ^ (prefixWord ++ tailWord_49547).sum := by decide
  have hdescent : baseEnd_49547 < baseStart_49547 := by decide
  rcases family_descends (prefixWord ++ tailWord_49547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49568 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 4]
def baseStart_49568 : Nat := 118140960795 + 49568 * 2 ^ 59
def prefixEnd_49568 : Nat := 4983230072969 + 3 ^ 40 * 49568 * 2
def baseEnd_49568 : Nat := 22624185850815376597375

theorem tailTrace_49568 : CollatzResearch.WordTrace tailWord_49568 prefixEnd_49568 22624185850815376597375 := by
  unfold tailWord_49568
  simp only [CollatzResearch.WordTrace]
  refine ⟨903946742215538192766679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1205262322954050923688905 903946742215538192766679)
  ·
    refine ⟨1355920113323307289150019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 903946742215538192766679 1355920113323307289150019)
    ·
      refine ⟨2033880169984960933725029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1355920113323307289150019 2033880169984960933725029)
      ·
        refine ⟨381352531872180175073443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2033880169984960933725029 381352531872180175073443)
        ·
          refine ⟨572028797808270262610165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381352531872180175073443 572028797808270262610165)
          ·
            refine ⟨53627699794525337119703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 572028797808270262610165 53627699794525337119703)
            ·
              refine ⟨80441549691788005679555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53627699794525337119703 80441549691788005679555)
              ·
                refine ⟨120662324537682008519333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80441549691788005679555 120662324537682008519333)
                ·
                  refine ⟨22624185850815376597375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120662324537682008519333 22624185850815376597375)
                  ·
                    rfl

theorem cell20_49568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_49568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49568 prefixEnd_49568 := by exact prefixLift 49568
  have htrace : WordTrace (prefixWord ++ tailWord_49568) baseStart_49568 baseEnd_49568 := by
    simpa [prefixWord, tailWord_49568, baseEnd_49568] using wordTrace_append hprefix tailTrace_49568
  have hstable : (prefixWord ++ tailWord_49568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49568).length < 2 ^ (prefixWord ++ tailWord_49568).sum := by decide
  have hdescent : baseEnd_49568 < baseStart_49568 := by decide
  rcases family_descends (prefixWord ++ tailWord_49568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49575 : List Nat := [1, 1, 6, 1, 1, 3, 2, 5]
def baseStart_49575 : Nat := 118140960795 + 49575 * 2 ^ 59
def prefixEnd_49575 : Nat := 4983230072969 + 3 ^ 40 * 49575 * 2
def baseEnd_49575 : Nat := 7542460280518154454671

theorem tailTrace_49575 : CollatzResearch.WordTrace tailWord_49575 prefixEnd_49575 7542460280518154454671 := by
  unfold tailWord_49575
  simp only [CollatzResearch.WordTrace]
  refine ⟨1808148795405716581038179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1205432530270477720692119 1808148795405716581038179)
  ·
    refine ⟨2712223193108574871557269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1808148795405716581038179 2712223193108574871557269)
    ·
      refine ⟨127135462176964447104247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2712223193108574871557269 127135462176964447104247)
      ·
        refine ⟨190703193265446670656371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127135462176964447104247 190703193265446670656371)
        ·
          refine ⟨286054789898170005984557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190703193265446670656371 286054789898170005984557)
          ·
            refine ⟨107270546211813752244209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286054789898170005984557 107270546211813752244209)
            ·
              refine ⟨80452909658860314183157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107270546211813752244209 80452909658860314183157)
              ·
                refine ⟨7542460280518154454671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80452909658860314183157 7542460280518154454671)
                ·
                  rfl

theorem cell20_49575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 5].length) (baseStart_49575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49575 prefixEnd_49575 := by exact prefixLift 49575
  have htrace : WordTrace (prefixWord ++ tailWord_49575) baseStart_49575 baseEnd_49575 := by
    simpa [prefixWord, tailWord_49575, baseEnd_49575] using wordTrace_append hprefix tailTrace_49575
  have hstable : (prefixWord ++ tailWord_49575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49575).length < 2 ^ (prefixWord ++ tailWord_49575).sum := by decide
  have hdescent : baseEnd_49575 < baseStart_49575 := by decide
  rcases family_descends (prefixWord ++ tailWord_49575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49675 : List Nat := [1, 1, 1, 1, 7, 3, 1, 2, 3]
def baseStart_49675 : Nat := 118140960795 + 49675 * 2 ^ 59
def prefixEnd_49675 : Nat := 4983230072969 + 3 ^ 40 * 49675 * 2
def baseEnd_49675 : Nat := 22673023566398560030271

theorem tailTrace_49675 : CollatzResearch.WordTrace tailWord_49675 prefixEnd_49675 22673023566398560030271 := by
  unfold tailWord_49675
  simp only [CollatzResearch.WordTrace]
  refine ⟨1811796095043433659678479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1207864063362289106452319 1811796095043433659678479)
  ·
    refine ⟨2717694142565150489517719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1811796095043433659678479 2717694142565150489517719)
    ·
      refine ⟨4076541213847725734276579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2717694142565150489517719 4076541213847725734276579)
      ·
        refine ⟨6114811820771588601414869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4076541213847725734276579 6114811820771588601414869)
        ·
          refine ⟨143315902049334107845661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 6114811820771588601414869 143315902049334107845661)
          ·
            refine ⟨53743463268500290442123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143315902049334107845661 53743463268500290442123)
            ·
              refine ⟨80615194902750435663185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53743463268500290442123 80615194902750435663185)
              ·
                refine ⟨60461396177062826747389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80615194902750435663185 60461396177062826747389)
                ·
                  refine ⟨22673023566398560030271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60461396177062826747389 22673023566398560030271)
                  ·
                    rfl

theorem cell20_49675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 3].length) (baseStart_49675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49675 prefixEnd_49675 := by exact prefixLift 49675
  have htrace : WordTrace (prefixWord ++ tailWord_49675) baseStart_49675 baseEnd_49675 := by
    simpa [prefixWord, tailWord_49675, baseEnd_49675] using wordTrace_append hprefix tailTrace_49675
  have hstable : (prefixWord ++ tailWord_49675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49675).length < 2 ^ (prefixWord ++ tailWord_49675).sum := by decide
  have hdescent : baseEnd_49675 < baseStart_49675 := by decide
  rcases family_descends (prefixWord ++ tailWord_49675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49706 : List Nat := [3, 1, 4, 1, 1, 4, 2, 4]
def baseStart_49706 : Nat := 118140960795 + 49706 * 2 ^ 59
def prefixEnd_49706 : Nat := 4983230072969 + 3 ^ 40 * 49706 * 2
def baseEnd_49706 : Nat := 7562390937033409998937

theorem tailTrace_49706 : CollatzResearch.WordTrace tailWord_49706 prefixEnd_49706 7562390937033409998937 := by
  unfold tailWord_49706
  simp only [CollatzResearch.WordTrace]
  refine ⟨453231689482781488514243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1208617838620750636037981 453231689482781488514243)
  ·
    refine ⟨679847534224172232771365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 453231689482781488514243 679847534224172232771365)
    ·
      refine ⟨127471412667032293644631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 679847534224172232771365 127471412667032293644631)
      ·
        refine ⟨191207119000548440466947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127471412667032293644631 191207119000548440466947)
        ·
          refine ⟨286810678500822660700421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191207119000548440466947 286810678500822660700421)
          ·
            refine ⟨53777002218904248881329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 286810678500822660700421 53777002218904248881329)
            ·
              refine ⟨40332751664178186660997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53777002218904248881329 40332751664178186660997)
              ·
                refine ⟨7562390937033409998937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40332751664178186660997 7562390937033409998937)
                ·
                  rfl

theorem cell20_49706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_49706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49706 prefixEnd_49706 := by exact prefixLift 49706
  have htrace : WordTrace (prefixWord ++ tailWord_49706) baseStart_49706 baseEnd_49706 := by
    simpa [prefixWord, tailWord_49706, baseEnd_49706] using wordTrace_append hprefix tailTrace_49706
  have hstable : (prefixWord ++ tailWord_49706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49706).length < 2 ^ (prefixWord ++ tailWord_49706).sum := by decide
  have hdescent : baseEnd_49706 < baseStart_49706 := by decide
  rcases family_descends (prefixWord ++ tailWord_49706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49717 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 7]
def baseStart_49717 : Nat := 118140960795 + 49717 * 2 ^ 59
def prefixEnd_49717 : Nat := 4983230072969 + 3 ^ 40 * 49717 * 2
def baseEnd_49717 : Nat := 22692193510833080630099

theorem tailTrace_49717 : CollatzResearch.WordTrace tailWord_49717 prefixEnd_49717 22692193510833080630099 := by
  unfold tailWord_49717
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813327960891274832707405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1208885307260849888471603 1813327960891274832707405)
  ·
    refine ⟨679997985334228062265277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1813327960891274832707405 679997985334228062265277)
    ·
      refine ⟨254999244500335523349479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 679997985334228062265277 254999244500335523349479)
      ·
        refine ⟨382498866750503285024219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254999244500335523349479 382498866750503285024219)
        ·
          refine ⟨573748300125754927536329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382498866750503285024219 573748300125754927536329)
          ·
            refine ⟨430311225094316195652247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573748300125754927536329 430311225094316195652247)
            ·
              refine ⟨645466837641474293478371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430311225094316195652247 645466837641474293478371)
              ·
                refine ⟨968200256462211440217557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645466837641474293478371 968200256462211440217557)
                ·
                  refine ⟨22692193510833080630099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 968200256462211440217557 22692193510833080630099)
                  ·
                    rfl

theorem cell20_49717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_49717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49717 prefixEnd_49717 := by exact prefixLift 49717
  have htrace : WordTrace (prefixWord ++ tailWord_49717) baseStart_49717 baseEnd_49717 := by
    simpa [prefixWord, tailWord_49717, baseEnd_49717] using wordTrace_append hprefix tailTrace_49717
  have hstable : (prefixWord ++ tailWord_49717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49717).length < 2 ^ (prefixWord ++ tailWord_49717).sum := by decide
  have hdescent : baseEnd_49717 < baseStart_49717 := by decide
  rcases family_descends (prefixWord ++ tailWord_49717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49748 : List Nat := [2, 4, 1, 1, 1, 3, 1, 7]
def baseStart_49748 : Nat := 118140960795 + 49748 * 2 ^ 59
def prefixEnd_49748 : Nat := 4983230072969 + 3 ^ 40 * 49748 * 2
def baseEnd_49748 : Nat := 7568780918511583532213

theorem tailTrace_49748 : CollatzResearch.WordTrace tailWord_49748 prefixEnd_49748 7568780918511583532213 := by
  unfold tailWord_49748
  simp only [CollatzResearch.WordTrace]
  refine ⟨907229311889483563542949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1209639082519311418057265 907229311889483563542949)
  ·
    refine ⟨170105495979278168164303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 907229311889483563542949 170105495979278168164303)
    ·
      refine ⟨255158243968917252246455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170105495979278168164303 255158243968917252246455)
      ·
        refine ⟨382737365953375878369683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255158243968917252246455 382737365953375878369683)
        ·
          refine ⟨574106048930063817554525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382737365953375878369683 574106048930063817554525)
          ·
            refine ⟨215289768348773931582947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 574106048930063817554525 215289768348773931582947)
            ·
              refine ⟨322934652523160897374421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215289768348773931582947 322934652523160897374421)
              ·
                refine ⟨7568780918511583532213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 322934652523160897374421 7568780918511583532213)
                ·
                  rfl

theorem cell20_49748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_49748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49748 prefixEnd_49748 := by exact prefixLift 49748
  have htrace : WordTrace (prefixWord ++ tailWord_49748) baseStart_49748 baseEnd_49748 := by
    simpa [prefixWord, tailWord_49748, baseEnd_49748] using wordTrace_append hprefix tailTrace_49748
  have hstable : (prefixWord ++ tailWord_49748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49748).length < 2 ^ (prefixWord ++ tailWord_49748).sum := by decide
  have hdescent : baseEnd_49748 < baseStart_49748 := by decide
  rcases family_descends (prefixWord ++ tailWord_49748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49789 : List Nat := [1, 4, 1, 1, 5, 1, 2, 2, 3]
def baseStart_49789 : Nat := 118140960795 + 49789 * 2 ^ 59
def prefixEnd_49789 : Nat := 4983230072969 + 3 ^ 40 * 49789 * 2
def baseEnd_49789 : Nat := 22725056272720830229805

theorem tailTrace_49789 : CollatzResearch.WordTrace tailWord_49789 prefixEnd_49789 22725056272720830229805 := by
  unfold tailWord_49789
  simp only [CollatzResearch.WordTrace]
  refine ⟨1815954016630431129328421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1210636011086954086218947 1815954016630431129328421)
  ·
    refine ⟨340491378118205836749079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1815954016630431129328421 340491378118205836749079)
    ·
      refine ⟨510737067177308755123619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340491378118205836749079 510737067177308755123619)
      ·
        refine ⟨766105600765963132685429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510737067177308755123619 766105600765963132685429)
        ·
          refine ⟨71822400071809043689259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 766105600765963132685429 71822400071809043689259)
          ·
            refine ⟨107733600107713565533889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71822400071809043689259 107733600107713565533889)
            ·
              refine ⟨80800200080785174150417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107733600107713565533889 80800200080785174150417)
              ·
                refine ⟨60600150060588880612813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80800200080785174150417 60600150060588880612813)
                ·
                  refine ⟨22725056272720830229805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60600150060588880612813 22725056272720830229805)
                  ·
                    rfl

theorem cell20_49789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_49789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49789 prefixEnd_49789 := by exact prefixLift 49789
  have htrace : WordTrace (prefixWord ++ tailWord_49789) baseStart_49789 baseEnd_49789 := by
    simpa [prefixWord, tailWord_49789, baseEnd_49789] using wordTrace_append hprefix tailTrace_49789
  have hstable : (prefixWord ++ tailWord_49789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49789).length < 2 ^ (prefixWord ++ tailWord_49789).sum := by decide
  have hdescent : baseEnd_49789 < baseStart_49789 := by decide
  rcases family_descends (prefixWord ++ tailWord_49789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49841 : List Nat := [1, 2, 2, 6, 1, 1, 7]
def baseStart_49841 : Nat := 118140960795 + 49841 * 2 ^ 59
def prefixEnd_49841 : Nat := 4983230072969 + 3 ^ 40 * 49841 * 2
def baseEnd_49841 : Nat := 2527643387737751166251

theorem tailTrace_49841 : CollatzResearch.WordTrace tailWord_49841 prefixEnd_49841 2527643387737751166251 := by
  unfold tailWord_49841
  simp only [CollatzResearch.WordTrace]
  refine ⟨1817850612442044010221377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1211900408294696006814251 1817850612442044010221377)
  ·
    refine ⟨1363387959331533007666033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1817850612442044010221377 1363387959331533007666033)
    ·
      refine ⟨1022540969498649755749525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1363387959331533007666033 1022540969498649755749525)
      ·
        refine ⟨47931607945249207300759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1022540969498649755749525 47931607945249207300759)
        ·
          refine ⟨71897411917873810951139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47931607945249207300759 71897411917873810951139)
          ·
            refine ⟨107846117876810716426709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71897411917873810951139 107846117876810716426709)
            ·
              refine ⟨2527643387737751166251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 107846117876810716426709 2527643387737751166251)
              ·
                rfl

theorem cell20_49841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 7].length) (baseStart_49841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49841 prefixEnd_49841 := by exact prefixLift 49841
  have htrace : WordTrace (prefixWord ++ tailWord_49841) baseStart_49841 baseEnd_49841 := by
    simpa [prefixWord, tailWord_49841, baseEnd_49841] using wordTrace_append hprefix tailTrace_49841
  have hstable : (prefixWord ++ tailWord_49841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49841).length < 2 ^ (prefixWord ++ tailWord_49841).sum := by decide
  have hdescent : baseEnd_49841 < baseStart_49841 := by decide
  rcases family_descends (prefixWord ++ tailWord_49841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49855 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 4]
def baseStart_49855 : Nat := 118140960795 + 49855 * 2 ^ 59
def prefixEnd_49855 : Nat := 4983230072969 + 3 ^ 40 * 49855 * 2
def baseEnd_49855 : Nat := 22755180471117934029535

theorem tailTrace_49855 : CollatzResearch.WordTrace tailWord_49855 prefixEnd_49855 22755180471117934029535 := by
  unfold tailWord_49855
  simp only [CollatzResearch.WordTrace]
  refine ⟨1818361234391324401231019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1212240822927549600820679 1818361234391324401231019)
  ·
    refine ⟨2727541851586986601846529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1818361234391324401231019 2727541851586986601846529)
    ·
      refine ⟨2045656388690239951384897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2727541851586986601846529 2045656388690239951384897)
      ·
        refine ⟨1534242291517679963538673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2045656388690239951384897 1534242291517679963538673)
        ·
          refine ⟨1150681718638259972654005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1534242291517679963538673 1150681718638259972654005)
          ·
            refine ⟨107876411122336872436313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1150681718638259972654005 107876411122336872436313)
            ·
              refine ⟨80907308341752654327235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107876411122336872436313 80907308341752654327235)
              ·
                refine ⟨121360962512628981490853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80907308341752654327235 121360962512628981490853)
                ·
                  refine ⟨22755180471117934029535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121360962512628981490853 22755180471117934029535)
                  ·
                    rfl

theorem cell20_49855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_49855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49855 prefixEnd_49855 := by exact prefixLift 49855
  have htrace : WordTrace (prefixWord ++ tailWord_49855) baseStart_49855 baseEnd_49855 := by
    simpa [prefixWord, tailWord_49855, baseEnd_49855] using wordTrace_append hprefix tailTrace_49855
  have hstable : (prefixWord ++ tailWord_49855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49855).length < 2 ^ (prefixWord ++ tailWord_49855).sum := by decide
  have hdescent : baseEnd_49855 < baseStart_49855 := by decide
  rcases family_descends (prefixWord ++ tailWord_49855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49879 : List Nat := [1, 1, 3, 2, 1, 6, 2, 4]
def baseStart_49879 : Nat := 118140960795 + 49879 * 2 ^ 59
def prefixEnd_49879 : Nat := 4983230072969 + 3 ^ 40 * 49879 * 2
def baseEnd_49879 : Nat := 7588711575026839076479

theorem tailTrace_49879 : CollatzResearch.WordTrace tailWord_49879 prefixEnd_49879 7588711575026839076479 := by
  unfold tailWord_49879
  simp only [CollatzResearch.WordTrace]
  refine ⟨1819236586304376500104691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1212824390869584333403127 1819236586304376500104691)
  ·
    refine ⟨2728854879456564750157037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1819236586304376500104691 2728854879456564750157037)
    ·
      refine ⟨1023320579796211781308889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2728854879456564750157037 1023320579796211781308889)
      ·
        refine ⟨767490434847158835981667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1023320579796211781308889 767490434847158835981667)
        ·
          refine ⟨1151235652270738253972501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767490434847158835981667 1151235652270738253972501)
          ·
            refine ⟨53964171200190855654961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1151235652270738253972501 53964171200190855654961)
            ·
              refine ⟨40473128400143141741221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53964171200190855654961 40473128400143141741221)
              ·
                refine ⟨7588711575026839076479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40473128400143141741221 7588711575026839076479)
                ·
                  rfl

theorem cell20_49879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 4].length) (baseStart_49879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49879 prefixEnd_49879 := by exact prefixLift 49879
  have htrace : WordTrace (prefixWord ++ tailWord_49879) baseStart_49879 baseEnd_49879 := by
    simpa [prefixWord, tailWord_49879, baseEnd_49879] using wordTrace_append hprefix tailTrace_49879
  have hstable : (prefixWord ++ tailWord_49879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49879).length < 2 ^ (prefixWord ++ tailWord_49879).sum := by decide
  have hdescent : baseEnd_49879 < baseStart_49879 := by decide
  rcases family_descends (prefixWord ++ tailWord_49879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49889 : List Nat := [1, 2, 3, 1, 4, 3, 1, 3, 2]
def baseStart_49889 : Nat := 118140960795 + 49889 * 2 ^ 59
def prefixEnd_49889 : Nat := 4983230072969 + 3 ^ 40 * 49889 * 2
def baseEnd_49889 : Nat := 22770698997564926896063

theorem tailTrace_49889 : CollatzResearch.WordTrace tailWord_49889 prefixEnd_49889 22770698997564926896063 := by
  unfold tailWord_49889
  simp only [CollatzResearch.WordTrace]
  refine ⟨1819601316268148207968721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1213067544178765471979147 1819601316268148207968721)
  ·
    refine ⟨1364700987201111155976541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1819601316268148207968721 1364700987201111155976541)
    ·
      refine ⟨511762870200416683491203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1364700987201111155976541 511762870200416683491203)
      ·
        refine ⟨767644305300625025236805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511762870200416683491203 767644305300625025236805)
        ·
          refine ⟨143933307243867192231901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 767644305300625025236805 143933307243867192231901)
          ·
            refine ⟨53974990216450197086963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143933307243867192231901 53974990216450197086963)
            ·
              refine ⟨80962485324675295630445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53974990216450197086963 80962485324675295630445)
              ·
                refine ⟨30360931996753235861417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80962485324675295630445 30360931996753235861417)
                ·
                  refine ⟨22770698997564926896063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30360931996753235861417 22770698997564926896063)
                  ·
                    rfl

theorem cell20_49889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 2].length) (baseStart_49889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49889 prefixEnd_49889 := by exact prefixLift 49889
  have htrace : WordTrace (prefixWord ++ tailWord_49889) baseStart_49889 baseEnd_49889 := by
    simpa [prefixWord, tailWord_49889, baseEnd_49889] using wordTrace_append hprefix tailTrace_49889
  have hstable : (prefixWord ++ tailWord_49889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49889).length < 2 ^ (prefixWord ++ tailWord_49889).sum := by decide
  have hdescent : baseEnd_49889 < baseStart_49889 := by decide
  rcases family_descends (prefixWord ++ tailWord_49889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49907 : List Nat := [1, 1, 1, 2, 2, 3, 1, 6, 3]
def baseStart_49907 : Nat := 118140960795 + 49907 * 2 ^ 59
def prefixEnd_49907 : Nat := 4983230072969 + 3 ^ 40 * 49907 * 2
def baseEnd_49907 : Nat := 22778914688036864295989

theorem tailTrace_49907 : CollatzResearch.WordTrace tailWord_49907 prefixEnd_49907 22778914688036864295989 := by
  unfold tailWord_49907
  simp only [CollatzResearch.WordTrace]
  refine ⟨1820257830202937282123975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1213505220135291521415983 1820257830202937282123975)
  ·
    refine ⟨2730386745304405923185963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1820257830202937282123975 2730386745304405923185963)
    ·
      refine ⟨4095580117956608884778945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2730386745304405923185963 4095580117956608884778945)
      ·
        refine ⟨3071685088467456663584209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4095580117956608884778945 3071685088467456663584209)
        ·
          refine ⟨2303763816350592497688157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3071685088467456663584209 2303763816350592497688157)
          ·
            refine ⟨863911431131472186633059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2303763816350592497688157 863911431131472186633059)
            ·
              refine ⟨1295867146697208279949589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863911431131472186633059 1295867146697208279949589)
              ·
                refine ⟨60743772501431638122637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1295867146697208279949589 60743772501431638122637)
                ·
                  refine ⟨22778914688036864295989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60743772501431638122637 22778914688036864295989)
                  ·
                    rfl

theorem cell20_49907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 3].length) (baseStart_49907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49907 prefixEnd_49907 := by exact prefixLift 49907
  have htrace : WordTrace (prefixWord ++ tailWord_49907) baseStart_49907 baseEnd_49907 := by
    simpa [prefixWord, tailWord_49907, baseEnd_49907] using wordTrace_append hprefix tailTrace_49907
  have hstable : (prefixWord ++ tailWord_49907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49907).length < 2 ^ (prefixWord ++ tailWord_49907).sum := by decide
  have hdescent : baseEnd_49907 < baseStart_49907 := by decide
  rcases family_descends (prefixWord ++ tailWord_49907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49924 : List Nat := [2, 3, 2, 2, 1, 1, 3, 3, 3]
def baseStart_49924 : Nat := 118140960795 + 49924 * 2 ^ 59
def prefixEnd_49924 : Nat := 4983230072969 + 3 ^ 40 * 49924 * 2
def baseEnd_49924 : Nat := 22786673951260360729253

theorem tailTrace_49924 : CollatzResearch.WordTrace tailWord_49924 prefixEnd_49924 22786673951260360729253 := by
  unfold tailWord_49924
  simp only [CollatzResearch.WordTrace]
  refine ⟨910438935570674592746413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1213918580760899456995217 910438935570674592746413)
  ·
    refine ⟨341414600839002972279905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 910438935570674592746413 341414600839002972279905)
    ·
      refine ⟨256060950629252229209929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341414600839002972279905 256060950629252229209929)
      ·
        refine ⟨192045712971939171907447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256060950629252229209929 192045712971939171907447)
        ·
          refine ⟨288068569457908757861171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192045712971939171907447 288068569457908757861171)
          ·
            refine ⟨432102854186863136791757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288068569457908757861171 432102854186863136791757)
            ·
              refine ⟨162038570320073676296909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 432102854186863136791757 162038570320073676296909)
              ·
                refine ⟨60764463870027628611341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162038570320073676296909 60764463870027628611341)
                ·
                  refine ⟨22786673951260360729253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60764463870027628611341 22786673951260360729253)
                  ·
                    rfl

theorem cell20_49924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_49924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49924 prefixEnd_49924 := by exact prefixLift 49924
  have htrace : WordTrace (prefixWord ++ tailWord_49924) baseStart_49924 baseEnd_49924 := by
    simpa [prefixWord, tailWord_49924, baseEnd_49924] using wordTrace_append hprefix tailTrace_49924
  have hstable : (prefixWord ++ tailWord_49924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49924).length < 2 ^ (prefixWord ++ tailWord_49924).sum := by decide
  have hdescent : baseEnd_49924 < baseStart_49924 := by decide
  rcases family_descends (prefixWord ++ tailWord_49924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_49972 : List Nat := [2, 5, 1, 1, 3, 2, 1, 5]
def baseStart_49972 : Nat := 118140960795 + 49972 * 2 ^ 59
def prefixEnd_49972 : Nat := 4983230072969 + 3 ^ 40 * 49972 * 2
def baseEnd_49972 : Nat := 7602860819728509043019

theorem tailTrace_49972 : CollatzResearch.WordTrace tailWord_49972 prefixEnd_49972 7602860819728509043019 := by
  unfold tailWord_49972
  simp only [CollatzResearch.WordTrace]
  refine ⟨911314287483726691620085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1215085716644968922160113 911314287483726691620085)
  ·
    refine ⟨85435714451599377339383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 911314287483726691620085 85435714451599377339383)
    ·
      refine ⟨128153571677399066009075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85435714451599377339383 128153571677399066009075)
      ·
        refine ⟨192230357516098599013613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128153571677399066009075 192230357516098599013613)
        ·
          refine ⟨72086384068536974630105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192230357516098599013613 72086384068536974630105)
          ·
            refine ⟨54064788051402730972579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72086384068536974630105 54064788051402730972579)
            ·
              refine ⟨81097182077104096458869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54064788051402730972579 81097182077104096458869)
              ·
                refine ⟨7602860819728509043019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81097182077104096458869 7602860819728509043019)
                ·
                  rfl

theorem cell20_49972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_49972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_49972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_49972 prefixEnd_49972 := by exact prefixLift 49972
  have htrace : WordTrace (prefixWord ++ tailWord_49972) baseStart_49972 baseEnd_49972 := by
    simpa [prefixWord, tailWord_49972, baseEnd_49972] using wordTrace_append hprefix tailTrace_49972
  have hstable : (prefixWord ++ tailWord_49972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_49972).length < 2 ^ (prefixWord ++ tailWord_49972).sum := by decide
  have hdescent : baseEnd_49972 < baseStart_49972 := by decide
  rcases family_descends (prefixWord ++ tailWord_49972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50024 : List Nat := [2, 1, 4, 2, 1, 2, 2, 4, 2]
def baseStart_50024 : Nat := 118140960795 + 50024 * 2 ^ 59
def prefixEnd_50024 : Nat := 4983230072969 + 3 ^ 40 * 50024 * 2
def baseEnd_50024 : Nat := 22832316676104457395511

theorem tailTrace_50024 : CollatzResearch.WordTrace tailWord_50024 prefixEnd_50024 22832316676104457395511 := by
  unfold tailWord_50024
  simp only [CollatzResearch.WordTrace]
  refine ⟨912262585389533132066563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1216350113852710842755417 912262585389533132066563)
  ·
    refine ⟨1368393878084299698099845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 912262585389533132066563 1368393878084299698099845)
    ·
      refine ⟨256573852140806193393721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1368393878084299698099845 256573852140806193393721)
      ·
        refine ⟨192430389105604645045291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256573852140806193393721 192430389105604645045291)
        ·
          refine ⟨288645583658406967567937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192430389105604645045291 288645583658406967567937)
          ·
            refine ⟨216484187743805225675953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288645583658406967567937 216484187743805225675953)
            ·
              refine ⟨162363140807853919256965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216484187743805225675953 162363140807853919256965)
              ·
                refine ⟨30443088901472609860681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162363140807853919256965 30443088901472609860681)
                ·
                  refine ⟨22832316676104457395511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30443088901472609860681 22832316676104457395511)
                  ·
                    rfl

theorem cell20_50024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 2].length) (baseStart_50024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50024 prefixEnd_50024 := by exact prefixLift 50024
  have htrace : WordTrace (prefixWord ++ tailWord_50024) baseStart_50024 baseEnd_50024 := by
    simpa [prefixWord, tailWord_50024, baseEnd_50024] using wordTrace_append hprefix tailTrace_50024
  have hstable : (prefixWord ++ tailWord_50024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50024).length < 2 ^ (prefixWord ++ tailWord_50024).sum := by decide
  have hdescent : baseEnd_50024 < baseStart_50024 := by decide
  rcases family_descends (prefixWord ++ tailWord_50024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50079 : List Nat := [1, 1, 2, 5, 2, 2, 3, 2, 2]
def baseStart_50079 : Nat := 118140960795 + 50079 * 2 ^ 59
def prefixEnd_50079 : Nat := 4983230072969 + 3 ^ 40 * 50079 * 2
def baseEnd_50079 : Nat := 22857420174768710561953

theorem tailTrace_50079 : CollatzResearch.WordTrace tailWord_50079 prefixEnd_50079 22857420174768710561953 := by
  unfold tailWord_50079
  simp only [CollatzResearch.WordTrace]
  refine ⟨1826531185579810657385291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1217687457053207104923527 1826531185579810657385291)
  ·
    refine ⟨2739796778369715986077937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1826531185579810657385291 2739796778369715986077937)
    ·
      refine ⟨2054847583777286989558453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2739796778369715986077937 2054847583777286989558453)
      ·
        refine ⟨192641960979120655271105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2054847583777286989558453 192641960979120655271105)
        ·
          refine ⟨144481470734340491453329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192641960979120655271105 144481470734340491453329)
          ·
            refine ⟨108361103050755368589997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144481470734340491453329 108361103050755368589997)
            ·
              refine ⟨40635413644033263221249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108361103050755368589997 40635413644033263221249)
              ·
                refine ⟨30476560233024947415937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40635413644033263221249 30476560233024947415937)
                ·
                  refine ⟨22857420174768710561953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30476560233024947415937 22857420174768710561953)
                  ·
                    rfl

theorem cell20_50079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 2].length) (baseStart_50079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50079 prefixEnd_50079 := by exact prefixLift 50079
  have htrace : WordTrace (prefixWord ++ tailWord_50079) baseStart_50079 baseEnd_50079 := by
    simpa [prefixWord, tailWord_50079, baseEnd_50079] using wordTrace_append hprefix tailTrace_50079
  have hstable : (prefixWord ++ tailWord_50079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50079).length < 2 ^ (prefixWord ++ tailWord_50079).sum := by decide
  have hdescent : baseEnd_50079 < baseStart_50079 := by decide
  rcases family_descends (prefixWord ++ tailWord_50079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50083 : List Nat := [1, 1, 1, 4, 1, 2, 2, 6, 2]
def baseStart_50083 : Nat := 118140960795 + 50083 * 2 ^ 59
def prefixEnd_50083 : Nat := 4983230072969 + 3 ^ 40 * 50083 * 2
def baseEnd_50083 : Nat := 22859245883762474428603

theorem tailTrace_50083 : CollatzResearch.WordTrace tailWord_50083 prefixEnd_50083 22859245883762474428603 := by
  unfold tailWord_50083
  simp only [CollatzResearch.WordTrace]
  refine ⟨1826677077565319340530903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1217784718376879560353935 1826677077565319340530903)
  ·
    refine ⟨2740015616347979010796355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1826677077565319340530903 2740015616347979010796355)
    ·
      refine ⟨4110023424521968516194533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2740015616347979010796355 4110023424521968516194533)
      ·
        refine ⟨770629392097869096786475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4110023424521968516194533 770629392097869096786475)
        ·
          refine ⟨1155944088146803645179713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770629392097869096786475 1155944088146803645179713)
          ·
            refine ⟨866958066110102733884785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1155944088146803645179713 866958066110102733884785)
            ·
              refine ⟨650218549582577050413589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866958066110102733884785 650218549582577050413589)
              ·
                refine ⟨30478994511683299238137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 650218549582577050413589 30478994511683299238137)
                ·
                  refine ⟨22859245883762474428603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30478994511683299238137 22859245883762474428603)
                  ·
                    rfl

theorem cell20_50083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 2].length) (baseStart_50083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50083 prefixEnd_50083 := by exact prefixLift 50083
  have htrace : WordTrace (prefixWord ++ tailWord_50083) baseStart_50083 baseEnd_50083 := by
    simpa [prefixWord, tailWord_50083, baseEnd_50083] using wordTrace_append hprefix tailTrace_50083
  have hstable : (prefixWord ++ tailWord_50083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50083).length < 2 ^ (prefixWord ++ tailWord_50083).sum := by decide
  have hdescent : baseEnd_50083 < baseStart_50083 := by decide
  rcases family_descends (prefixWord ++ tailWord_50083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50134 : List Nat := [5, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_50134 : Nat := 118140960795 + 50134 * 2 ^ 59
def prefixEnd_50134 : Nat := 4983230072969 + 3 ^ 40 * 50134 * 2
def baseEnd_50134 : Nat := 22882523673432963728395

theorem tailTrace_50134 : CollatzResearch.WordTrace tailWord_50134 prefixEnd_50134 22882523673432963728395 := by
  unfold tailWord_50134
  simp only [CollatzResearch.WordTrace]
  refine ⟨114283575023784690664841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1219024800253703367091637 114283575023784690664841)
  ·
    refine ⟨85712681267838517998631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114283575023784690664841 85712681267838517998631)
    ·
      refine ⟨128569021901757776997947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85712681267838517998631 128569021901757776997947)
      ·
        refine ⟨192853532852636665496921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128569021901757776997947 192853532852636665496921)
        ·
          refine ⟨144640149639477499122691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192853532852636665496921 144640149639477499122691)
          ·
            refine ⟨216960224459216248684037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144640149639477499122691 216960224459216248684037)
            ·
              refine ⟨40680042086103046628257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216960224459216248684037 40680042086103046628257)
              ·
                refine ⟨30510031564577284971193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40680042086103046628257 30510031564577284971193)
                ·
                  refine ⟨22882523673432963728395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30510031564577284971193 22882523673432963728395)
                  ·
                    rfl

theorem cell20_50134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_50134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50134 prefixEnd_50134 := by exact prefixLift 50134
  have htrace : WordTrace (prefixWord ++ tailWord_50134) baseStart_50134 baseEnd_50134 := by
    simpa [prefixWord, tailWord_50134, baseEnd_50134] using wordTrace_append hprefix tailTrace_50134
  have hstable : (prefixWord ++ tailWord_50134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50134).length < 2 ^ (prefixWord ++ tailWord_50134).sum := by decide
  have hdescent : baseEnd_50134 < baseStart_50134 := by decide
  rcases family_descends (prefixWord ++ tailWord_50134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50138 : List Nat := [3, 1, 1, 2, 4, 2, 1, 4, 2]
def baseStart_50138 : Nat := 118140960795 + 50138 * 2 ^ 59
def prefixEnd_50138 : Nat := 4983230072969 + 3 ^ 40 * 50138 * 2
def baseEnd_50138 : Nat := 22884349382426727595045

theorem tailTrace_50138 : CollatzResearch.WordTrace tailWord_50138 prefixEnd_50138 22884349382426727595045 := by
  unfold tailWord_50138
  simp only [CollatzResearch.WordTrace]
  refine ⟨457170773091515933445767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1219122061577375822522045 457170773091515933445767)
  ·
    refine ⟨685756159637273900168651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 457170773091515933445767 685756159637273900168651)
    ·
      refine ⟨1028634239455910850252977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 685756159637273900168651 1028634239455910850252977)
      ·
        refine ⟨771475679591933137689733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1028634239455910850252977 771475679591933137689733)
        ·
          refine ⟨144651689923487463316825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 771475679591933137689733 144651689923487463316825)
          ·
            refine ⟨108488767442615597487619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144651689923487463316825 108488767442615597487619)
            ·
              refine ⟨162733151163923396231429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108488767442615597487619 162733151163923396231429)
              ·
                refine ⟨30512465843235636793393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162733151163923396231429 30512465843235636793393)
                ·
                  refine ⟨22884349382426727595045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30512465843235636793393 22884349382426727595045)
                  ·
                    rfl

theorem cell20_50138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_50138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50138 prefixEnd_50138 := by exact prefixLift 50138
  have htrace : WordTrace (prefixWord ++ tailWord_50138) baseStart_50138 baseEnd_50138 := by
    simpa [prefixWord, tailWord_50138, baseEnd_50138] using wordTrace_append hprefix tailTrace_50138
  have hstable : (prefixWord ++ tailWord_50138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50138).length < 2 ^ (prefixWord ++ tailWord_50138).sum := by decide
  have hdescent : baseEnd_50138 < baseStart_50138 := by decide
  rcases family_descends (prefixWord ++ tailWord_50138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50156 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_50156 : Nat := 118140960795 + 50156 * 2 ^ 59
def prefixEnd_50156 : Nat := 4983230072969 + 3 ^ 40 * 50156 * 2
def baseEnd_50156 : Nat := 22892565072898664994971

theorem tailTrace_50156 : CollatzResearch.WordTrace tailWord_50156 prefixEnd_50156 22892565072898664994971 := by
  unfold tailWord_50156
  simp only [CollatzResearch.WordTrace]
  refine ⟨914669803150426403969161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1219559737533901871958881 914669803150426403969161)
  ·
    refine ⟨686002352362819802976871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 914669803150426403969161 686002352362819802976871)
    ·
      refine ⟨1029003528544229704465307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 686002352362819802976871 1029003528544229704465307)
      ·
        refine ⟨1543505292816344556697961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029003528544229704465307 1543505292816344556697961)
        ·
          refine ⟨1157628969612258417523471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1543505292816344556697961 1157628969612258417523471)
          ·
            refine ⟨1736443454418387626285207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157628969612258417523471 1736443454418387626285207)
            ·
              refine ⟨2604665181627581439427811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736443454418387626285207 2604665181627581439427811)
              ·
                refine ⟨3906997772441372159141717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2604665181627581439427811 3906997772441372159141717)
                ·
                  refine ⟨22892565072898664994971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3906997772441372159141717 22892565072898664994971)
                  ·
                    rfl

theorem cell20_50156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_50156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50156 prefixEnd_50156 := by exact prefixLift 50156
  have htrace : WordTrace (prefixWord ++ tailWord_50156) baseStart_50156 baseEnd_50156 := by
    simpa [prefixWord, tailWord_50156, baseEnd_50156] using wordTrace_append hprefix tailTrace_50156
  have hstable : (prefixWord ++ tailWord_50156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50156).length < 2 ^ (prefixWord ++ tailWord_50156).sum := by decide
  have hdescent : baseEnd_50156 < baseStart_50156 := by decide
  rcases family_descends (prefixWord ++ tailWord_50156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50162 : List Nat := [3, 2, 1, 5, 1, 1, 3, 4]
def baseStart_50162 : Nat := 118140960795 + 50162 * 2 ^ 59
def prefixEnd_50162 : Nat := 4983230072969 + 3 ^ 40 * 50162 * 2
def baseEnd_50162 : Nat := 7631767878796436931649

theorem tailTrace_50162 : CollatzResearch.WordTrace tailWord_50162 prefixEnd_50162 7631767878796436931649 := by
  unfold tailWord_50162
  simp only [CollatzResearch.WordTrace]
  refine ⟨457389611069778958164185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1219705629519410555104493 457389611069778958164185)
  ·
    refine ⟨343042208302334218623139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 457389611069778958164185 343042208302334218623139)
    ·
      refine ⟨514563312453501327934709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343042208302334218623139 514563312453501327934709)
      ·
        refine ⟨48240310542515749493879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 514563312453501327934709 48240310542515749493879)
        ·
          refine ⟨72360465813773624240819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48240310542515749493879 72360465813773624240819)
          ·
            refine ⟨108540698720660436361229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72360465813773624240819 108540698720660436361229)
            ·
              refine ⟨40702762020247663635461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108540698720660436361229 40702762020247663635461)
              ·
                refine ⟨7631767878796436931649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40702762020247663635461 7631767878796436931649)
                ·
                  rfl

theorem cell20_50162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_50162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50162 prefixEnd_50162 := by exact prefixLift 50162
  have htrace : WordTrace (prefixWord ++ tailWord_50162) baseStart_50162 baseEnd_50162 := by
    simpa [prefixWord, tailWord_50162, baseEnd_50162] using wordTrace_append hprefix tailTrace_50162
  have hstable : (prefixWord ++ tailWord_50162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50162).length < 2 ^ (prefixWord ++ tailWord_50162).sum := by decide
  have hdescent : baseEnd_50162 < baseStart_50162 := by decide
  rcases family_descends (prefixWord ++ tailWord_50162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50187 : List Nat := [1, 1, 1, 1, 6, 3, 7]
def baseStart_50187 : Nat := 118140960795 + 50187 * 2 ^ 59
def prefixEnd_50187 : Nat := 4983230072969 + 3 ^ 40 * 50187 * 2
def baseEnd_50187 : Nat := 2545190479733370551279

theorem tailTrace_50187 : CollatzResearch.WordTrace tailWord_50187 prefixEnd_50187 2545190479733370551279 := by
  unfold tailWord_50187
  simp only [CollatzResearch.WordTrace]
  refine ⟨1830470269188545102316815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1220313512792363401544543 1830470269188545102316815)
  ·
    refine ⟨2745705403782817653475223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1830470269188545102316815 2745705403782817653475223)
    ·
      refine ⟨4118558105674226480212835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2745705403782817653475223 4118558105674226480212835)
      ·
        refine ⟨6177837158511339720319253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4118558105674226480212835 6177837158511339720319253)
        ·
          refine ⟨289586116805219049389965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6177837158511339720319253 289586116805219049389965)
          ·
            refine ⟨108594793801957143521237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289586116805219049389965 108594793801957143521237)
            ·
              refine ⟨2545190479733370551279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 108594793801957143521237 2545190479733370551279)
              ·
                rfl

theorem cell20_50187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 7].length) (baseStart_50187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50187 prefixEnd_50187 := by exact prefixLift 50187
  have htrace : WordTrace (prefixWord ++ tailWord_50187) baseStart_50187 baseEnd_50187 := by
    simpa [prefixWord, tailWord_50187, baseEnd_50187] using wordTrace_append hprefix tailTrace_50187
  have hstable : (prefixWord ++ tailWord_50187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50187).length < 2 ^ (prefixWord ++ tailWord_50187).sum := by decide
  have hdescent : baseEnd_50187 < baseStart_50187 := by decide
  rcases family_descends (prefixWord ++ tailWord_50187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50190 : List Nat := [4, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_50190 : Nat := 118140960795 + 50190 * 2 ^ 59
def prefixEnd_50190 : Nat := 4983230072969 + 3 ^ 40 * 50190 * 2
def baseEnd_50190 : Nat := 22908083599345657861499

theorem tailTrace_50190 : CollatzResearch.WordTrace tailWord_50190 prefixEnd_50190 22908083599345657861499 := by
  unfold tailWord_50190
  simp only [CollatzResearch.WordTrace]
  refine ⟨228822461022209576834503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1220386458785117743117349 228822461022209576834503)
  ·
    refine ⟨343233691533314365251755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228822461022209576834503 343233691533314365251755)
    ·
      refine ⟨514850537299971547877633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343233691533314365251755 514850537299971547877633)
      ·
        refine ⟨386137902974978660908225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514850537299971547877633 386137902974978660908225)
        ·
          refine ⟨289603427231233995681169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386137902974978660908225 289603427231233995681169)
          ·
            refine ⟨217202570423425496760877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289603427231233995681169 217202570423425496760877)
            ·
              refine ⟨81450963908784561285329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217202570423425496760877 81450963908784561285329)
              ·
                refine ⟨61088222931588420963997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81450963908784561285329 61088222931588420963997)
                ·
                  refine ⟨22908083599345657861499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61088222931588420963997 22908083599345657861499)
                  ·
                    rfl

theorem cell20_50190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_50190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50190 prefixEnd_50190 := by exact prefixLift 50190
  have htrace : WordTrace (prefixWord ++ tailWord_50190) baseStart_50190 baseEnd_50190 := by
    simpa [prefixWord, tailWord_50190, baseEnd_50190] using wordTrace_append hprefix tailTrace_50190
  have hstable : (prefixWord ++ tailWord_50190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50190).length < 2 ^ (prefixWord ++ tailWord_50190).sum := by decide
  have hdescent : baseEnd_50190 < baseStart_50190 := by decide
  rcases family_descends (prefixWord ++ tailWord_50190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50197 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 4]
def baseStart_50197 : Nat := 118140960795 + 50197 * 2 ^ 59
def prefixEnd_50197 : Nat := 4983230072969 + 3 ^ 40 * 50197 * 2
def baseEnd_50197 : Nat := 22911278590084744628137

theorem tailTrace_50197 : CollatzResearch.WordTrace tailWord_50197 prefixEnd_50197 22911278590084744628137 := by
  unfold tailWord_50197
  simp only [CollatzResearch.WordTrace]
  refine ⟨1830834999152316810180845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1220556666101544540120563 1830834999152316810180845)
  ·
    refine ⟨686563124682118803817817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1830834999152316810180845 686563124682118803817817)
    ·
      refine ⟨514922343511589102863363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 686563124682118803817817 514922343511589102863363)
      ·
        refine ⟨772383515267383654295045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514922343511589102863363 772383515267383654295045)
        ·
          refine ⟨144821909112634435180321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 772383515267383654295045 144821909112634435180321)
          ·
            refine ⟨108616431834475826385241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144821909112634435180321 108616431834475826385241)
            ·
              refine ⟨81462323875856869788931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108616431834475826385241 81462323875856869788931)
              ·
                refine ⟨122193485813785304683397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81462323875856869788931 122193485813785304683397)
                ·
                  refine ⟨22911278590084744628137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122193485813785304683397 22911278590084744628137)
                  ·
                    rfl

theorem cell20_50197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_50197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50197 prefixEnd_50197 := by exact prefixLift 50197
  have htrace : WordTrace (prefixWord ++ tailWord_50197) baseStart_50197 baseEnd_50197 := by
    simpa [prefixWord, tailWord_50197, baseEnd_50197] using wordTrace_append hprefix tailTrace_50197
  have hstable : (prefixWord ++ tailWord_50197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50197).length < 2 ^ (prefixWord ++ tailWord_50197).sum := by decide
  have hdescent : baseEnd_50197 < baseStart_50197 := by decide
  rcases family_descends (prefixWord ++ tailWord_50197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50225 : List Nat := [1, 2, 2, 3, 1, 2, 3, 6]
def baseStart_50225 : Nat := 118140960795 + 50225 * 2 ^ 59
def prefixEnd_50225 : Nat := 4983230072969 + 3 ^ 40 * 50225 * 2
def baseEnd_50225 : Nat := 7641352851013697231563

theorem tailTrace_50225 : CollatzResearch.WordTrace tailWord_50225 prefixEnd_50225 7641352851013697231563 := by
  unfold tailWord_50225
  simp only [CollatzResearch.WordTrace]
  refine ⟨1831856243050877592200129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1221237495367251728133419 1831856243050877592200129)
  ·
    refine ⟨1373892182288158194150097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1831856243050877592200129 1373892182288158194150097)
    ·
      refine ⟨1030419136716118645612573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1373892182288158194150097 1030419136716118645612573)
      ·
        refine ⟨386407176268544492104715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1030419136716118645612573 386407176268544492104715)
        ·
          refine ⟨579610764402816738157073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386407176268544492104715 579610764402816738157073)
          ·
            refine ⟨434708073302112553617805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579610764402816738157073 434708073302112553617805)
            ·
              refine ⟨163015527488292207606677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434708073302112553617805 163015527488292207606677)
              ·
                refine ⟨7641352851013697231563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 163015527488292207606677 7641352851013697231563)
                ·
                  rfl

theorem cell20_50225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 6].length) (baseStart_50225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50225 prefixEnd_50225 := by exact prefixLift 50225
  have htrace : WordTrace (prefixWord ++ tailWord_50225) baseStart_50225 baseEnd_50225 := by
    simpa [prefixWord, tailWord_50225, baseEnd_50225] using wordTrace_append hprefix tailTrace_50225
  have hstable : (prefixWord ++ tailWord_50225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50225).length < 2 ^ (prefixWord ++ tailWord_50225).sum := by decide
  have hdescent : baseEnd_50225 < baseStart_50225 := by decide
  rcases family_descends (prefixWord ++ tailWord_50225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50228 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 5]
def baseStart_50228 : Nat := 118140960795 + 50228 * 2 ^ 59
def prefixEnd_50228 : Nat := 4983230072969 + 3 ^ 40 * 50228 * 2
def baseEnd_50228 : Nat := 22925427834786414594677

theorem tailTrace_50228 : CollatzResearch.WordTrace tailWord_50228 prefixEnd_50228 22925427834786414594677 := by
  unfold tailWord_50228
  simp only [CollatzResearch.WordTrace]
  refine ⟨915982831020004552279669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1221310441360006069706225 915982831020004552279669)
  ·
    refine ⟨85873390408125426776219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 915982831020004552279669 85873390408125426776219)
    ·
      refine ⟨128810085612188140164329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85873390408125426776219 128810085612188140164329)
      ·
        refine ⟨96607564209141105123247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128810085612188140164329 96607564209141105123247)
        ·
          refine ⟨144911346313711657684871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96607564209141105123247 144911346313711657684871)
          ·
            refine ⟨217367019470567486527307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144911346313711657684871 217367019470567486527307)
            ·
              refine ⟨326050529205851229790961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217367019470567486527307 326050529205851229790961)
              ·
                refine ⟨244537896904388422343221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326050529205851229790961 244537896904388422343221)
                ·
                  refine ⟨22925427834786414594677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 244537896904388422343221 22925427834786414594677)
                  ·
                    rfl

theorem cell20_50228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_50228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50228 prefixEnd_50228 := by exact prefixLift 50228
  have htrace : WordTrace (prefixWord ++ tailWord_50228) baseStart_50228 baseEnd_50228 := by
    simpa [prefixWord, tailWord_50228, baseEnd_50228] using wordTrace_append hprefix tailTrace_50228
  have hstable : (prefixWord ++ tailWord_50228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50228).length < 2 ^ (prefixWord ++ tailWord_50228).sum := by decide
  have hdescent : baseEnd_50228 < baseStart_50228 := by decide
  rcases family_descends (prefixWord ++ tailWord_50228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50262 : List Nat := [5, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_50262 : Nat := 118140960795 + 50262 * 2 ^ 59
def prefixEnd_50262 : Nat := 4983230072969 + 3 ^ 40 * 50262 * 2
def baseEnd_50262 : Nat := 22940946361233407461205

theorem tailTrace_50262 : CollatzResearch.WordTrace tailWord_50262 prefixEnd_50262 22940946361233407461205 := by
  unfold tailWord_50262
  simp only [CollatzResearch.WordTrace]
  refine ⟨114575358994802056956065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1222137162611221940864693 114575358994802056956065)
  ·
    refine ⟨85931519246101542717049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114575358994802056956065 85931519246101542717049)
    ·
      refine ⟨64448639434576157037787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85931519246101542717049 64448639434576157037787)
      ·
        refine ⟨96672959151864235556681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64448639434576157037787 96672959151864235556681)
        ·
          refine ⟨72504719363898176667511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96672959151864235556681 72504719363898176667511)
          ·
            refine ⟨108757079045847265001267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72504719363898176667511 108757079045847265001267)
            ·
              refine ⟨163135618568770897501901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108757079045847265001267 163135618568770897501901)
              ·
                refine ⟨61175856963289086563213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163135618568770897501901 61175856963289086563213)
                ·
                  refine ⟨22940946361233407461205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61175856963289086563213 22940946361233407461205)
                  ·
                    rfl

theorem cell20_50262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_50262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50262 prefixEnd_50262 := by exact prefixLift 50262
  have htrace : WordTrace (prefixWord ++ tailWord_50262) baseStart_50262 baseEnd_50262 := by
    simpa [prefixWord, tailWord_50262, baseEnd_50262] using wordTrace_append hprefix tailTrace_50262
  have hstable : (prefixWord ++ tailWord_50262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50262).length < 2 ^ (prefixWord ++ tailWord_50262).sum := by decide
  have hdescent : baseEnd_50262 < baseStart_50262 := by decide
  rcases family_descends (prefixWord ++ tailWord_50262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50315 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 8]
def baseStart_50315 : Nat := 118140960795 + 50315 * 2 ^ 59
def prefixEnd_50315 : Nat := 4983230072969 + 3 ^ 40 * 50315 * 2
def baseEnd_50315 : Nat := 22965137005400778694321

theorem tailTrace_50315 : CollatzResearch.WordTrace tailWord_50315 prefixEnd_50315 22965137005400778694321 := by
  unfold tailWord_50315
  simp only [CollatzResearch.WordTrace]
  refine ⟨1835138812724822962976399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1223425875149881975317599 1835138812724822962976399)
  ·
    refine ⟨2752708219087234444464599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1835138812724822962976399 2752708219087234444464599)
    ·
      refine ⟨4129062328630851666696899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2752708219087234444464599 4129062328630851666696899)
      ·
        refine ⟨6193593492946277500045349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4129062328630851666696899 6193593492946277500045349)
        ·
          refine ⟨1161298779927427031258503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6193593492946277500045349 1161298779927427031258503)
          ·
            refine ⟨1741948169891140546887755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161298779927427031258503 1741948169891140546887755)
            ·
              refine ⟨2612922254836710820331633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741948169891140546887755 2612922254836710820331633)
              ·
                refine ⟨1959691691127533115248725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2612922254836710820331633 1959691691127533115248725)
                ·
                  refine ⟨22965137005400778694321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1959691691127533115248725 22965137005400778694321)
                  ·
                    rfl

theorem cell20_50315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_50315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50315 prefixEnd_50315 := by exact prefixLift 50315
  have htrace : WordTrace (prefixWord ++ tailWord_50315) baseStart_50315 baseEnd_50315 := by
    simpa [prefixWord, tailWord_50315, baseEnd_50315] using wordTrace_append hprefix tailTrace_50315
  have hstable : (prefixWord ++ tailWord_50315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50315).length < 2 ^ (prefixWord ++ tailWord_50315).sum := by decide
  have hdescent : baseEnd_50315 < baseStart_50315 := by decide
  rcases family_descends (prefixWord ++ tailWord_50315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50318 : List Nat := [4, 1, 1, 3, 2, 1, 3, 5]
def baseStart_50318 : Nat := 118140960795 + 50318 * 2 ^ 59
def prefixEnd_50318 : Nat := 4983230072969 + 3 ^ 40 * 50318 * 2
def baseEnd_50318 : Nat := 7655502095715367198103

theorem tailTrace_50318 : CollatzResearch.WordTrace tailWord_50318 prefixEnd_50318 7655502095715367198103 := by
  unfold tailWord_50318
  simp only [CollatzResearch.WordTrace]
  refine ⟨229406028964244309416951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1223498821142636316890405 229406028964244309416951)
  ·
    refine ⟨344109043446366464125427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229406028964244309416951 344109043446366464125427)
    ·
      refine ⟨516163565169549696188141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344109043446366464125427 516163565169549696188141)
      ·
        refine ⟨193561336938581136070553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 516163565169549696188141 193561336938581136070553)
        ·
          refine ⟨145171002703935852052915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193561336938581136070553 145171002703935852052915)
          ·
            refine ⟨217756504055903778079373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145171002703935852052915 217756504055903778079373)
            ·
              refine ⟨81658689020963916779765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217756504055903778079373 81658689020963916779765)
              ·
                refine ⟨7655502095715367198103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81658689020963916779765 7655502095715367198103)
                ·
                  rfl

theorem cell20_50318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_50318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50318 prefixEnd_50318 := by exact prefixLift 50318
  have htrace : WordTrace (prefixWord ++ tailWord_50318) baseStart_50318 baseEnd_50318 := by
    simpa [prefixWord, tailWord_50318, baseEnd_50318] using wordTrace_append hprefix tailTrace_50318
  have hstable : (prefixWord ++ tailWord_50318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50318).length < 2 ^ (prefixWord ++ tailWord_50318).sum := by decide
  have hdescent : baseEnd_50318 < baseStart_50318 := by decide
  rcases family_descends (prefixWord ++ tailWord_50318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50332 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_50332 : Nat := 118140960795 + 50332 * 2 ^ 59
def prefixEnd_50332 : Nat := 4983230072969 + 3 ^ 40 * 50332 * 2
def baseEnd_50332 : Nat := 22972896268624275127585

theorem tailTrace_50332 : CollatzResearch.WordTrace tailWord_50332 prefixEnd_50332 22972896268624275127585 := by
  unfold tailWord_50332
  simp only [CollatzResearch.WordTrace]
  refine ⟨917879426831617433172625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1223839235775489910896833 917879426831617433172625)
  ·
    refine ⟨688409570123713074879469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 917879426831617433172625 688409570123713074879469)
    ·
      refine ⟨258153588796392403079801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 688409570123713074879469 258153588796392403079801)
      ·
        refine ⟨193615191597294302309851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258153588796392403079801 193615191597294302309851)
        ·
          refine ⟨290422787395941453464777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193615191597294302309851 290422787395941453464777)
          ·
            refine ⟨217817090546956090098583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290422787395941453464777 217817090546956090098583)
            ·
              refine ⟨326725635820434135147875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217817090546956090098583 326725635820434135147875)
              ·
                refine ⟨490088453730651202721813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326725635820434135147875 490088453730651202721813)
                ·
                  refine ⟨22972896268624275127585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 490088453730651202721813 22972896268624275127585)
                  ·
                    rfl

theorem cell20_50332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_50332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50332 prefixEnd_50332 := by exact prefixLift 50332
  have htrace : WordTrace (prefixWord ++ tailWord_50332) baseStart_50332 baseEnd_50332 := by
    simpa [prefixWord, tailWord_50332, baseEnd_50332] using wordTrace_append hprefix tailTrace_50332
  have hstable : (prefixWord ++ tailWord_50332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50332).length < 2 ^ (prefixWord ++ tailWord_50332).sum := by decide
  have hdescent : baseEnd_50332 < baseStart_50332 := by decide
  rcases family_descends (prefixWord ++ tailWord_50332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50335 : List Nat := [1, 1, 2, 6, 2, 1, 3, 4]
def baseStart_50335 : Nat := 118140960795 + 50335 * 2 ^ 59
def prefixEnd_50335 : Nat := 4983230072969 + 3 ^ 40 * 50335 * 2
def baseEnd_50335 : Nat := 7658088516789866009191

theorem tailTrace_50335 : CollatzResearch.WordTrace tailWord_50335 prefixEnd_50335 7658088516789866009191 := by
  unfold tailWord_50335
  simp only [CollatzResearch.WordTrace]
  refine ⟨1835868272652366378704459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1223912181768244252469639 1835868272652366378704459)
  ·
    refine ⟨2753802408978549568056689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1835868272652366378704459 2753802408978549568056689)
    ·
      refine ⟨2065351806733912176042517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2753802408978549568056689 2065351806733912176042517)
      ·
        refine ⟨96813365940652133251993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2065351806733912176042517 96813365940652133251993)
        ·
          refine ⟨72610024455489099938995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96813365940652133251993 72610024455489099938995)
          ·
            refine ⟨108915036683233649908493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72610024455489099938995 108915036683233649908493)
            ·
              refine ⟨40843138756212618715685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108915036683233649908493 40843138756212618715685)
              ·
                refine ⟨7658088516789866009191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40843138756212618715685 7658088516789866009191)
                ·
                  rfl

theorem cell20_50335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 4].length) (baseStart_50335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50335 prefixEnd_50335 := by exact prefixLift 50335
  have htrace : WordTrace (prefixWord ++ tailWord_50335) baseStart_50335 baseEnd_50335 := by
    simpa [prefixWord, tailWord_50335, baseEnd_50335] using wordTrace_append hprefix tailTrace_50335
  have hstable : (prefixWord ++ tailWord_50335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50335).length < 2 ^ (prefixWord ++ tailWord_50335).sum := by decide
  have hdescent : baseEnd_50335 < baseStart_50335 := by decide
  rcases family_descends (prefixWord ++ tailWord_50335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50366 : List Nat := [4, 2, 1, 1, 3, 1, 2, 4, 2]
def baseStart_50366 : Nat := 118140960795 + 50366 * 2 ^ 59
def prefixEnd_50366 : Nat := 4983230072969 + 3 ^ 40 * 50366 * 2
def baseEnd_50366 : Nat := 22988414795071267994113

theorem tailTrace_50366 : CollatzResearch.WordTrace tailWord_50366 prefixEnd_50366 22988414795071267994113 := by
  unfold tailWord_50366
  simp only [CollatzResearch.WordTrace]
  refine ⟨229624866942507334135369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1224665957026705782055301 229624866942507334135369)
  ·
    refine ⟨172218650206880500601527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229624866942507334135369 172218650206880500601527)
    ·
      refine ⟨258327975310320750902291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172218650206880500601527 258327975310320750902291)
      ·
        refine ⟨387491962965481126353437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258327975310320750902291 387491962965481126353437)
        ·
          refine ⟨145309486112055422382539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387491962965481126353437 145309486112055422382539)
          ·
            refine ⟨217964229168083133573809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145309486112055422382539 217964229168083133573809)
            ·
              refine ⟨163473171876062350180357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217964229168083133573809 163473171876062350180357)
              ·
                refine ⟨30651219726761690658817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163473171876062350180357 30651219726761690658817)
                ·
                  refine ⟨22988414795071267994113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30651219726761690658817 22988414795071267994113)
                  ·
                    rfl

theorem cell20_50366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_50366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50366 prefixEnd_50366 := by exact prefixLift 50366
  have htrace : WordTrace (prefixWord ++ tailWord_50366) baseStart_50366 baseEnd_50366 := by
    simpa [prefixWord, tailWord_50366, baseEnd_50366] using wordTrace_append hprefix tailTrace_50366
  have hstable : (prefixWord ++ tailWord_50366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50366).length < 2 ^ (prefixWord ++ tailWord_50366).sum := by decide
  have hdescent : baseEnd_50366 < baseStart_50366 := by decide
  rcases family_descends (prefixWord ++ tailWord_50366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50460 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_50460 : Nat := 118140960795 + 50460 * 2 ^ 59
def prefixEnd_50460 : Nat := 4983230072969 + 3 ^ 40 * 50460 * 2
def baseEnd_50460 : Nat := 23031318956424718860395

theorem tailTrace_50460 : CollatzResearch.WordTrace tailWord_50460 prefixEnd_50460 23031318956424718860395 := by
  unfold tailWord_50460
  simp only [CollatzResearch.WordTrace]
  refine ⟨920213698599756363502417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1226951598133008484669889 920213698599756363502417)
  ·
    refine ⟨690160273949817272626813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 920213698599756363502417 690160273949817272626813)
    ·
      refine ⟨258810102731181477235055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 690160273949817272626813 258810102731181477235055)
      ·
        refine ⟨388215154096772215852583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258810102731181477235055 388215154096772215852583)
        ·
          refine ⟨582322731145158323778875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388215154096772215852583 582322731145158323778875)
          ·
            refine ⟨873484096717737485668313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582322731145158323778875 873484096717737485668313)
            ·
              refine ⟨655113072538303114251235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 873484096717737485668313 655113072538303114251235)
              ·
                refine ⟨982669608807454671376853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655113072538303114251235 982669608807454671376853)
                ·
                  refine ⟨23031318956424718860395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 982669608807454671376853 23031318956424718860395)
                  ·
                    rfl

theorem cell20_50460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_50460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50460 prefixEnd_50460 := by exact prefixLift 50460
  have htrace : WordTrace (prefixWord ++ tailWord_50460) baseStart_50460 baseEnd_50460 := by
    simpa [prefixWord, tailWord_50460, baseEnd_50460] using wordTrace_append hprefix tailTrace_50460
  have hstable : (prefixWord ++ tailWord_50460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50460).length < 2 ^ (prefixWord ++ tailWord_50460).sum := by decide
  have hdescent : baseEnd_50460 < baseStart_50460 := by decide
  rcases family_descends (prefixWord ++ tailWord_50460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50505 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 6]
def baseStart_50505 : Nat := 118140960795 + 50505 * 2 ^ 59
def prefixEnd_50505 : Nat := 4983230072969 + 3 ^ 40 * 50505 * 2
def baseEnd_50505 : Nat := 23051858182604562360211

theorem tailTrace_50505 : CollatzResearch.WordTrace tailWord_50505 prefixEnd_50505 23051858182604562360211 := by
  unfold tailWord_50505
  simp only [CollatzResearch.WordTrace]
  refine ⟨1842068682036485412392969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1228045788024323608261979 1842068682036485412392969)
  ·
    refine ⟨1381551511527364059294727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1842068682036485412392969 1381551511527364059294727)
    ·
      refine ⟨2072327267291046088942091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1381551511527364059294727 2072327267291046088942091)
      ·
        refine ⟨3108490900936569133413137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2072327267291046088942091 3108490900936569133413137)
        ·
          refine ⟨2331368175702426850059853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3108490900936569133413137 2331368175702426850059853)
          ·
            refine ⟨874263065888410068772445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2331368175702426850059853 874263065888410068772445)
            ·
              refine ⟨327848649708153775789667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 874263065888410068772445 327848649708153775789667)
              ·
                refine ⟨491772974562230663684501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327848649708153775789667 491772974562230663684501)
                ·
                  refine ⟨23051858182604562360211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 491772974562230663684501 23051858182604562360211)
                  ·
                    rfl

theorem cell20_50505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_50505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50505 prefixEnd_50505 := by exact prefixLift 50505
  have htrace : WordTrace (prefixWord ++ tailWord_50505) baseStart_50505 baseEnd_50505 := by
    simpa [prefixWord, tailWord_50505, baseEnd_50505] using wordTrace_append hprefix tailTrace_50505
  have hstable : (prefixWord ++ tailWord_50505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50505).length < 2 ^ (prefixWord ++ tailWord_50505).sum := by decide
  have hdescent : baseEnd_50505 < baseStart_50505 := by decide
  rcases family_descends (prefixWord ++ tailWord_50505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50508 : List Nat := [2, 2, 1, 3, 2, 3, 3, 4]
def baseStart_50508 : Nat := 118140960795 + 50508 * 2 ^ 59
def prefixEnd_50508 : Nat := 4983230072969 + 3 ^ 40 * 50508 * 2
def baseEnd_50508 : Nat := 7684409154783295086733

theorem tailTrace_50508 : CollatzResearch.WordTrace tailWord_50508 prefixEnd_50508 7684409154783295086733 := by
  unfold tailWord_50508
  simp only [CollatzResearch.WordTrace]
  refine ⟨921089050512808462376089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1228118734017077949834785 921089050512808462376089)
  ·
    refine ⟨690816787884606346782067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 921089050512808462376089 690816787884606346782067)
    ·
      refine ⟨1036225181826909520173101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 690816787884606346782067 1036225181826909520173101)
      ·
        refine ⟨388584443185091070064913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1036225181826909520173101 388584443185091070064913)
        ·
          refine ⟨291438332388818302548685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388584443185091070064913 291438332388818302548685)
          ·
            refine ⟨109289374645806863455757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291438332388818302548685 109289374645806863455757)
            ·
              refine ⟨40983515492177573795909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109289374645806863455757 40983515492177573795909)
              ·
                refine ⟨7684409154783295086733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40983515492177573795909 7684409154783295086733)
                ·
                  rfl

theorem cell20_50508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_50508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50508 prefixEnd_50508 := by exact prefixLift 50508
  have htrace : WordTrace (prefixWord ++ tailWord_50508) baseStart_50508 baseEnd_50508 := by
    simpa [prefixWord, tailWord_50508, baseEnd_50508] using wordTrace_append hprefix tailTrace_50508
  have hstable : (prefixWord ++ tailWord_50508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50508).length < 2 ^ (prefixWord ++ tailWord_50508).sum := by decide
  have hdescent : baseEnd_50508 < baseStart_50508 := by decide
  rcases family_descends (prefixWord ++ tailWord_50508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50532 : List Nat := [2, 3, 1, 1, 3, 4, 1, 2, 3]
def baseStart_50532 : Nat := 118140960795 + 50532 * 2 ^ 59
def prefixEnd_50532 : Nat := 4983230072969 + 3 ^ 40 * 50532 * 2
def baseEnd_50532 : Nat := 23064181718312468460101

theorem tailTrace_50532 : CollatzResearch.WordTrace tailWord_50532 prefixEnd_50532 23064181718312468460101 := by
  unfold tailWord_50532
  simp only [CollatzResearch.WordTrace]
  refine ⟨921526726469334511812925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1228702301959112682417233 921526726469334511812925)
  ·
    refine ⟨345572522426000441929847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 921526726469334511812925 345572522426000441929847)
    ·
      refine ⟨518358783639000662894771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345572522426000441929847 518358783639000662894771)
      ·
        refine ⟨777538175458500994342157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518358783639000662894771 777538175458500994342157)
        ·
          refine ⟨291576815796937872878309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 777538175458500994342157 291576815796937872878309)
          ·
            refine ⟨54670652961925851164683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291576815796937872878309 54670652961925851164683)
            ·
              refine ⟨82005979442888776747025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54670652961925851164683 82005979442888776747025)
              ·
                refine ⟨61504484582166582560269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82005979442888776747025 61504484582166582560269)
                ·
                  refine ⟨23064181718312468460101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61504484582166582560269 23064181718312468460101)
                  ·
                    rfl

theorem cell20_50532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_50532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50532 prefixEnd_50532 := by exact prefixLift 50532
  have htrace : WordTrace (prefixWord ++ tailWord_50532) baseStart_50532 baseEnd_50532 := by
    simpa [prefixWord, tailWord_50532, baseEnd_50532] using wordTrace_append hprefix tailTrace_50532
  have hstable : (prefixWord ++ tailWord_50532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50532).length < 2 ^ (prefixWord ++ tailWord_50532).sum := by decide
  have hdescent : baseEnd_50532 < baseStart_50532 := by decide
  rcases family_descends (prefixWord ++ tailWord_50532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50549 : List Nat := [1, 3, 4, 1, 3, 1, 3, 1, 3]
def baseStart_50549 : Nat := 118140960795 + 50549 * 2 ^ 59
def prefixEnd_50549 : Nat := 4983230072969 + 3 ^ 40 * 50549 * 2
def baseEnd_50549 : Nat := 23071940981535964893365

theorem tailTrace_50549 : CollatzResearch.WordTrace tailWord_50549 prefixEnd_50549 23071940981535964893365 := by
  unfold tailWord_50549
  simp only [CollatzResearch.WordTrace]
  refine ⟨1843673493877080926994701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1229115662584720617996467 1843673493877080926994701)
  ·
    refine ⟨691377560203905347623013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1843673493877080926994701 691377560203905347623013)
    ·
      refine ⟨129633292538232252679315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 691377560203905347623013 129633292538232252679315)
      ·
        refine ⟨194449938807348379018973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129633292538232252679315 194449938807348379018973)
        ·
          refine ⟨72918727052755642132115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194449938807348379018973 72918727052755642132115)
          ·
            refine ⟨109378090579133463198173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72918727052755642132115 109378090579133463198173)
            ·
              refine ⟨41016783967175048699315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109378090579133463198173 41016783967175048699315)
              ·
                refine ⟨61525175950762573048973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41016783967175048699315 61525175950762573048973)
                ·
                  refine ⟨23071940981535964893365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61525175950762573048973 23071940981535964893365)
                  ·
                    rfl

theorem cell20_50549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_50549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50549 prefixEnd_50549 := by exact prefixLift 50549
  have htrace : WordTrace (prefixWord ++ tailWord_50549) baseStart_50549 baseEnd_50549 := by
    simpa [prefixWord, tailWord_50549, baseEnd_50549] using wordTrace_append hprefix tailTrace_50549
  have hstable : (prefixWord ++ tailWord_50549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50549).length < 2 ^ (prefixWord ++ tailWord_50549).sum := by decide
  have hdescent : baseEnd_50549 < baseStart_50549 := by decide
  rcases family_descends (prefixWord ++ tailWord_50549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50567 : List Nat := [1, 1, 4, 2, 2, 3, 1, 6]
def baseStart_50567 : Nat := 118140960795 + 50567 * 2 ^ 59
def prefixEnd_50567 : Nat := 4983230072969 + 3 ^ 40 * 50567 * 2
def baseEnd_50567 : Nat := 7693385557335967431097

theorem tailTrace_50567 : CollatzResearch.WordTrace tailWord_50567 prefixEnd_50567 7693385557335967431097 := by
  unfold tailWord_50567
  simp only [CollatzResearch.WordTrace]
  refine ⟨1844330007811870001149955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1229553338541246667433303 1844330007811870001149955)
  ·
    refine ⟨2766495011717805001724933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1844330007811870001149955 2766495011717805001724933)
    ·
      refine ⟨518717814697088437823425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2766495011717805001724933 518717814697088437823425)
      ·
        refine ⟨389038361022816328367569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 518717814697088437823425 389038361022816328367569)
        ·
          refine ⟨291778770767112246275677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 389038361022816328367569 291778770767112246275677)
          ·
            refine ⟨109417039037667092353379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291778770767112246275677 109417039037667092353379)
            ·
              refine ⟨164125558556500638530069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109417039037667092353379 164125558556500638530069)
              ·
                refine ⟨7693385557335967431097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 164125558556500638530069 7693385557335967431097)
                ·
                  rfl

theorem cell20_50567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 6].length) (baseStart_50567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50567 prefixEnd_50567 := by exact prefixLift 50567
  have htrace : WordTrace (prefixWord ++ tailWord_50567) baseStart_50567 baseEnd_50567 := by
    simpa [prefixWord, tailWord_50567, baseEnd_50567] using wordTrace_append hprefix tailTrace_50567
  have hstable : (prefixWord ++ tailWord_50567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50567).length < 2 ^ (prefixWord ++ tailWord_50567).sum := by decide
  have hdescent : baseEnd_50567 < baseStart_50567 := by decide
  rcases family_descends (prefixWord ++ tailWord_50567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50581 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 6]
def baseStart_50581 : Nat := 118140960795 + 50581 * 2 ^ 59
def prefixEnd_50581 : Nat := 4983230072969 + 3 ^ 40 * 50581 * 2
def baseEnd_50581 : Nat := 23086546653486075826567

theorem tailTrace_50581 : CollatzResearch.WordTrace tailWord_50581 prefixEnd_50581 23086546653486075826567 := by
  unfold tailWord_50581
  simp only [CollatzResearch.WordTrace]
  refine ⟨1844840629761150392159597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1229893753174100261439731 1844840629761150392159597)
  ·
    refine ⟨691815236160431397059849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1844840629761150392159597 691815236160431397059849)
    ·
      refine ⟨518861427120323547794887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 691815236160431397059849 518861427120323547794887)
      ·
        refine ⟨778292140680485321692331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518861427120323547794887 778292140680485321692331)
        ·
          refine ⟨1167438211020727982538497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778292140680485321692331 1167438211020727982538497)
          ·
            refine ⟨875578658265545986903873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167438211020727982538497 875578658265545986903873)
            ·
              refine ⟨656683993699159490177905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875578658265545986903873 656683993699159490177905)
              ·
                refine ⟨492512995274369617633429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 656683993699159490177905 492512995274369617633429)
                ·
                  refine ⟨23086546653486075826567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 492512995274369617633429 23086546653486075826567)
                  ·
                    rfl

theorem cell20_50581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_50581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50581 prefixEnd_50581 := by exact prefixLift 50581
  have htrace : WordTrace (prefixWord ++ tailWord_50581) baseStart_50581 baseEnd_50581 := by
    simpa [prefixWord, tailWord_50581, baseEnd_50581] using wordTrace_append hprefix tailTrace_50581
  have hstable : (prefixWord ++ tailWord_50581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50581).length < 2 ^ (prefixWord ++ tailWord_50581).sum := by decide
  have hdescent : baseEnd_50581 < baseStart_50581 := by decide
  rcases family_descends (prefixWord ++ tailWord_50581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50584 : List Nat := [2, 1, 2, 5, 2, 2, 6]
def baseStart_50584 : Nat := 118140960795 + 50584 * 2 ^ 59
def prefixEnd_50584 : Nat := 4983230072969 + 3 ^ 40 * 50584 * 2
def baseEnd_50584 : Nat := 2565323992803488747395

theorem tailTrace_50584 : CollatzResearch.WordTrace tailWord_50584 prefixEnd_50584 2565323992803488747395 := by
  unfold tailWord_50584
  simp only [CollatzResearch.WordTrace]
  refine ⟨922475024375140952259403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1229966699166854603012537 922475024375140952259403)
  ·
    refine ⟨1383712536562711428389105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 922475024375140952259403 1383712536562711428389105)
    ·
      refine ⟨1037784402422033571291829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1383712536562711428389105 1037784402422033571291829)
      ·
        refine ⟨97292287727065647308609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1037784402422033571291829 97292287727065647308609)
        ·
          refine ⟨72969215795299235481457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97292287727065647308609 72969215795299235481457)
          ·
            refine ⟨54726911846474426611093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72969215795299235481457 54726911846474426611093)
            ·
              refine ⟨2565323992803488747395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54726911846474426611093 2565323992803488747395)
              ·
                rfl

theorem cell20_50584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 6].length) (baseStart_50584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50584 prefixEnd_50584 := by exact prefixLift 50584
  have htrace : WordTrace (prefixWord ++ tailWord_50584) baseStart_50584 baseEnd_50584 := by
    simpa [prefixWord, tailWord_50584, baseEnd_50584] using wordTrace_append hprefix tailTrace_50584
  have hstable : (prefixWord ++ tailWord_50584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50584).length < 2 ^ (prefixWord ++ tailWord_50584).sum := by decide
  have hdescent : baseEnd_50584 < baseStart_50584 := by decide
  rcases family_descends (prefixWord ++ tailWord_50584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50590 : List Nat := [4, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_50590 : Nat := 118140960795 + 50590 * 2 ^ 59
def prefixEnd_50590 : Nat := 4983230072969 + 3 ^ 40 * 50590 * 2
def baseEnd_50590 : Nat := 23090654498722044526531

theorem tailTrace_50590 : CollatzResearch.WordTrace tailWord_50590 prefixEnd_50590 23090654498722044526531 := by
  unfold tailWord_50590
  simp only [CollatzResearch.WordTrace]
  refine ⟨230646110841068116154653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1230112591152363286158149 230646110841068116154653)
  ·
    refine ⟨86492291565400543557995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 230646110841068116154653 86492291565400543557995)
    ·
      refine ⟨129738437348100815336993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86492291565400543557995 129738437348100815336993)
      ·
        refine ⟨97303828011075611502745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129738437348100815336993 97303828011075611502745)
        ·
          refine ⟨72977871008306708627059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97303828011075611502745 72977871008306708627059)
          ·
            refine ⟨109466806512460062940589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72977871008306708627059 109466806512460062940589)
            ·
              refine ⟨41050052442172523602721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109466806512460062940589 41050052442172523602721)
              ·
                refine ⟨30787539331629392702041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41050052442172523602721 30787539331629392702041)
                ·
                  refine ⟨23090654498722044526531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30787539331629392702041 23090654498722044526531)
                  ·
                    rfl

theorem cell20_50590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_50590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50590 prefixEnd_50590 := by exact prefixLift 50590
  have htrace : WordTrace (prefixWord ++ tailWord_50590) baseStart_50590 baseEnd_50590 := by
    simpa [prefixWord, tailWord_50590, baseEnd_50590] using wordTrace_append hprefix tailTrace_50590
  have hstable : (prefixWord ++ tailWord_50590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50590).length < 2 ^ (prefixWord ++ tailWord_50590).sum := by decide
  have hdescent : baseEnd_50590 < baseStart_50590 := by decide
  rcases family_descends (prefixWord ++ tailWord_50590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50646 : List Nat := [5, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_50646 : Nat := 118140960795 + 50646 * 2 ^ 59
def prefixEnd_50646 : Nat := 4983230072969 + 3 ^ 40 * 50646 * 2
def baseEnd_50646 : Nat := 23116214424634738659635

theorem tailTrace_50646 : CollatzResearch.WordTrace tailWord_50646 prefixEnd_50646 23116214424634738659635 := by
  unfold tailWord_50646
  simp only [CollatzResearch.WordTrace]
  refine ⟨115450710907854155829737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1231474249683777662183861 115450710907854155829737)
  ·
    refine ⟨86588033180890616872303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115450710907854155829737 86588033180890616872303)
    ·
      refine ⟨129882049771335925308455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86588033180890616872303 129882049771335925308455)
      ·
        refine ⟨194823074657003887962683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129882049771335925308455 194823074657003887962683)
        ·
          refine ⟨292234611985505831944025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194823074657003887962683 292234611985505831944025)
          ·
            refine ⟨219175958989129373958019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292234611985505831944025 219175958989129373958019)
            ·
              refine ⟨328763938483694060937029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219175958989129373958019 328763938483694060937029)
              ·
                refine ⟨61643238465692636425693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 328763938483694060937029 61643238465692636425693)
                ·
                  refine ⟨23116214424634738659635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61643238465692636425693 23116214424634738659635)
                  ·
                    rfl

theorem cell20_50646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_50646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50646 prefixEnd_50646 := by exact prefixLift 50646
  have htrace : WordTrace (prefixWord ++ tailWord_50646) baseStart_50646 baseEnd_50646 := by
    simpa [prefixWord, tailWord_50646, baseEnd_50646] using wordTrace_append hprefix tailTrace_50646
  have hstable : (prefixWord ++ tailWord_50646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50646).length < 2 ^ (prefixWord ++ tailWord_50646).sum := by decide
  have hdescent : baseEnd_50646 < baseStart_50646 := by decide
  rcases family_descends (prefixWord ++ tailWord_50646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50674 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_50674 : Nat := 118140960795 + 50674 * 2 ^ 59
def prefixEnd_50674 : Nat := 4983230072969 + 3 ^ 40 * 50674 * 2
def baseEnd_50674 : Nat := 23128994387591085726187

theorem tailTrace_50674 : CollatzResearch.WordTrace tailWord_50674 prefixEnd_50674 23128994387591085726187 := by
  unfold tailWord_50674
  simp only [CollatzResearch.WordTrace]
  refine ⟨462058154606056818823769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1232155078949484850196717 462058154606056818823769)
  ·
    refine ⟨346543615954542614117827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 462058154606056818823769 346543615954542614117827)
    ·
      refine ⟨519815423931813921176741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346543615954542614117827 519815423931813921176741)
      ·
        refine ⟨97465391987215110220639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 519815423931813921176741 97465391987215110220639)
        ·
          refine ⟨146198087980822665330959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97465391987215110220639 146198087980822665330959)
          ·
            refine ⟨219297131971233997996439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146198087980822665330959 219297131971233997996439)
            ·
              refine ⟨328945697956850996994659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219297131971233997996439 328945697956850996994659)
              ·
                refine ⟨493418546935276495491989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328945697956850996994659 493418546935276495491989)
                ·
                  refine ⟨23128994387591085726187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 493418546935276495491989 23128994387591085726187)
                  ·
                    rfl

theorem cell20_50674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_50674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50674 prefixEnd_50674 := by exact prefixLift 50674
  have htrace : WordTrace (prefixWord ++ tailWord_50674) baseStart_50674 baseEnd_50674 := by
    simpa [prefixWord, tailWord_50674, baseEnd_50674] using wordTrace_append hprefix tailTrace_50674
  have hstable : (prefixWord ++ tailWord_50674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50674).length < 2 ^ (prefixWord ++ tailWord_50674).sum := by decide
  have hdescent : baseEnd_50674 < baseStart_50674 := by decide
  rcases family_descends (prefixWord ++ tailWord_50674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50677 : List Nat := [1, 3, 5, 1, 1, 2, 3, 4]
def baseStart_50677 : Nat := 118140960795 + 50677 * 2 ^ 59
def prefixEnd_50677 : Nat := 4983230072969 + 3 ^ 40 * 50677 * 2
def baseEnd_50677 : Nat := 7710121223112136208725

theorem tailTrace_50677 : CollatzResearch.WordTrace tailWord_50677 prefixEnd_50677 7710121223112136208725 := by
  unfold tailWord_50677
  simp only [CollatzResearch.WordTrace]
  refine ⟨1848342037413358787654285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1232228024942239191769523 1848342037413358787654285)
  ·
    refine ⟨693128264030009545370357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1848342037413358787654285 693128264030009545370357)
    ·
      refine ⟨64980774752813394878471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 693128264030009545370357 64980774752813394878471)
      ·
        refine ⟨97471162129220092317707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64980774752813394878471 97471162129220092317707)
        ·
          refine ⟨146206743193830138476561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97471162129220092317707 146206743193830138476561)
          ·
            refine ⟨109655057395372603857421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146206743193830138476561 109655057395372603857421)
            ·
              refine ⟨41120646523264726446533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109655057395372603857421 41120646523264726446533)
              ·
                refine ⟨7710121223112136208725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41120646523264726446533 7710121223112136208725)
                ·
                  rfl

theorem cell20_50677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 4].length) (baseStart_50677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50677 prefixEnd_50677 := by exact prefixLift 50677
  have htrace : WordTrace (prefixWord ++ tailWord_50677) baseStart_50677 baseEnd_50677 := by
    simpa [prefixWord, tailWord_50677, baseEnd_50677] using wordTrace_append hprefix tailTrace_50677
  have hstable : (prefixWord ++ tailWord_50677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50677).length < 2 ^ (prefixWord ++ tailWord_50677).sum := by decide
  have hdescent : baseEnd_50677 < baseStart_50677 := by decide
  rcases family_descends (prefixWord ++ tailWord_50677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50694 : List Nat := [6, 2, 1, 1, 2, 1, 7]
def baseStart_50694 : Nat := 118140960795 + 50694 * 2 ^ 59
def prefixEnd_50694 : Nat := 4983230072969 + 3 ^ 40 * 50694 * 2
def baseEnd_50694 : Nat := 2570902548062211673271

theorem tailTrace_50694 : CollatzResearch.WordTrace tailWord_50694 prefixEnd_50694 2570902548062211673271 := by
  unfold tailWord_50694
  simp only [CollatzResearch.WordTrace]
  refine ⟨57780064948492834094473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1232641385567847127348757 57780064948492834094473)
  ·
    refine ⟨43335048711369625570855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57780064948492834094473 43335048711369625570855)
    ·
      refine ⟨65002573067054438356283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43335048711369625570855 65002573067054438356283)
      ·
        refine ⟨97503859600581657534425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65002573067054438356283 97503859600581657534425)
        ·
          refine ⟨73127894700436243150819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97503859600581657534425 73127894700436243150819)
          ·
            refine ⟨109691842050654364726229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73127894700436243150819 109691842050654364726229)
            ·
              refine ⟨2570902548062211673271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 109691842050654364726229 2570902548062211673271)
              ·
                rfl

theorem cell20_50694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 7].length) (baseStart_50694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50694 prefixEnd_50694 := by exact prefixLift 50694
  have htrace : WordTrace (prefixWord ++ tailWord_50694) baseStart_50694 baseEnd_50694 := by
    simpa [prefixWord, tailWord_50694, baseEnd_50694] using wordTrace_append hprefix tailTrace_50694
  have hstable : (prefixWord ++ tailWord_50694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50694).length < 2 ^ (prefixWord ++ tailWord_50694).sum := by decide
  have hdescent : baseEnd_50694 < baseStart_50694 := by decide
  rcases family_descends (prefixWord ++ tailWord_50694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50701 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 5]
def baseStart_50701 : Nat := 118140960795 + 50701 * 2 ^ 59
def prefixEnd_50701 : Nat := 4983230072969 + 3 ^ 40 * 50701 * 2
def baseEnd_50701 : Nat := 23141317923298991826077

theorem tailTrace_50701 : CollatzResearch.WordTrace tailWord_50701 prefixEnd_50701 23141317923298991826077 := by
  unfold tailWord_50701
  simp only [CollatzResearch.WordTrace]
  refine ⟨1849217389326410886527957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1232811592884273924351971 1849217389326410886527957)
  ·
    refine ⟨43341032562337755152999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 1849217389326410886527957 43341032562337755152999)
    ·
      refine ⟨65011548843506632729499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43341032562337755152999 65011548843506632729499)
      ·
        refine ⟨97517323265259949094249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65011548843506632729499 97517323265259949094249)
        ·
          refine ⟨73137992448944961820687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97517323265259949094249 73137992448944961820687)
          ·
            refine ⟨109706988673417442731031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73137992448944961820687 109706988673417442731031)
            ·
              refine ⟨164560483010126164096547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109706988673417442731031 164560483010126164096547)
              ·
                refine ⟨246840724515189246144821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164560483010126164096547 246840724515189246144821)
                ·
                  refine ⟨23141317923298991826077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 246840724515189246144821 23141317923298991826077)
                  ·
                    rfl

theorem cell20_50701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_50701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50701 prefixEnd_50701 := by exact prefixLift 50701
  have htrace : WordTrace (prefixWord ++ tailWord_50701) baseStart_50701 baseEnd_50701 := by
    simpa [prefixWord, tailWord_50701, baseEnd_50701] using wordTrace_append hprefix tailTrace_50701
  have hstable : (prefixWord ++ tailWord_50701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50701).length < 2 ^ (prefixWord ++ tailWord_50701).sum := by decide
  have hdescent : baseEnd_50701 < baseStart_50701 := by decide
  rcases family_descends (prefixWord ++ tailWord_50701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50708 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 4]
def baseStart_50708 : Nat := 118140960795 + 50708 * 2 ^ 59
def prefixEnd_50708 : Nat := 4983230072969 + 3 ^ 40 * 50708 * 2
def baseEnd_50708 : Nat := 23144512914038078592715

theorem tailTrace_50708 : CollatzResearch.WordTrace tailWord_50708 prefixEnd_50708 23144512914038078592715 := by
  unfold tailWord_50708
  simp only [CollatzResearch.WordTrace]
  refine ⟨924736350150525541016389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1232981800200700721355185 924736350150525541016389)
  ·
    refine ⟨173388065653223538940573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 924736350150525541016389 173388065653223538940573)
    ·
      refine ⟨65020524619958827102715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173388065653223538940573 65020524619958827102715)
      ·
        refine ⟨97530786929938240654073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65020524619958827102715 97530786929938240654073)
        ·
          refine ⟨73148090197453680490555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97530786929938240654073 73148090197453680490555)
          ·
            refine ⟨109722135296180520735833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73148090197453680490555 109722135296180520735833)
            ·
              refine ⟨82291601472135390551875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109722135296180520735833 82291601472135390551875)
              ·
                refine ⟨123437402208203085827813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82291601472135390551875 123437402208203085827813)
                ·
                  refine ⟨23144512914038078592715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123437402208203085827813 23144512914038078592715)
                  ·
                    rfl

theorem cell20_50708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_50708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50708 prefixEnd_50708 := by exact prefixLift 50708
  have htrace : WordTrace (prefixWord ++ tailWord_50708) baseStart_50708 baseEnd_50708 := by
    simpa [prefixWord, tailWord_50708, baseEnd_50708] using wordTrace_append hprefix tailTrace_50708
  have hstable : (prefixWord ++ tailWord_50708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50708).length < 2 ^ (prefixWord ++ tailWord_50708).sum := by decide
  have hdescent : baseEnd_50708 < baseStart_50708 := by decide
  rcases family_descends (prefixWord ++ tailWord_50708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50742 : List Nat := [5, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_50742 : Nat := 118140960795 + 50742 * 2 ^ 59
def prefixEnd_50742 : Nat := 4983230072969 + 3 ^ 40 * 50742 * 2
def baseEnd_50742 : Nat := 23160031440485071459243

theorem tailTrace_50742 : CollatzResearch.WordTrace tailWord_50742 prefixEnd_50742 23160031440485071459243 := by
  unfold tailWord_50742
  simp only [CollatzResearch.WordTrace]
  refine ⟨115669548886117180548155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1233808521451916592513653 115669548886117180548155)
  ·
    refine ⟨173504323329175770822233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115669548886117180548155 173504323329175770822233)
    ·
      refine ⟨130128242496881828116675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173504323329175770822233 130128242496881828116675)
      ·
        refine ⟨195192363745322742175013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130128242496881828116675 195192363745322742175013)
        ·
          refine ⟨36598568202248014157815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195192363745322742175013 36598568202248014157815)
          ·
            refine ⟨54897852303372021236723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36598568202248014157815 54897852303372021236723)
            ·
              refine ⟨82346778455058031855085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54897852303372021236723 82346778455058031855085)
              ·
                refine ⟨30880041920646761945657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82346778455058031855085 30880041920646761945657)
                ·
                  refine ⟨23160031440485071459243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30880041920646761945657 23160031440485071459243)
                  ·
                    rfl

theorem cell20_50742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_50742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50742 prefixEnd_50742 := by exact prefixLift 50742
  have htrace : WordTrace (prefixWord ++ tailWord_50742) baseStart_50742 baseEnd_50742 := by
    simpa [prefixWord, tailWord_50742, baseEnd_50742] using wordTrace_append hprefix tailTrace_50742
  have hstable : (prefixWord ++ tailWord_50742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50742).length < 2 ^ (prefixWord ++ tailWord_50742).sum := by decide
  have hdescent : baseEnd_50742 < baseStart_50742 := by decide
  rcases family_descends (prefixWord ++ tailWord_50742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50764 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_50764 : Nat := 118140960795 + 50764 * 2 ^ 59
def prefixEnd_50764 : Nat := 4983230072969 + 3 ^ 40 * 50764 * 2
def baseEnd_50764 : Nat := 23170072839950772725819

theorem tailTrace_50764 : CollatzResearch.WordTrace tailWord_50764 prefixEnd_50764 23170072839950772725819 := by
  unfold tailWord_50764
  simp only [CollatzResearch.WordTrace]
  refine ⟨925757594049086323035673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1234343458732115097380897 925757594049086323035673)
  ·
    refine ⟨694318195536814742276755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 925757594049086323035673 694318195536814742276755)
    ·
      refine ⟨1041477293305222113415133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 694318195536814742276755 1041477293305222113415133)
      ·
        refine ⟨390553984989458292530675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1041477293305222113415133 390553984989458292530675)
        ·
          refine ⟨585830977484187438796013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390553984989458292530675 585830977484187438796013)
          ·
            refine ⟨219686616556570289548505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 585830977484187438796013 219686616556570289548505)
            ·
              refine ⟨164764962417427717161379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219686616556570289548505 164764962417427717161379)
              ·
                refine ⟨247147443626141575742069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164764962417427717161379 247147443626141575742069)
                ·
                  refine ⟨23170072839950772725819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 247147443626141575742069 23170072839950772725819)
                  ·
                    rfl

theorem cell20_50764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_50764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50764 prefixEnd_50764 := by exact prefixLift 50764
  have htrace : WordTrace (prefixWord ++ tailWord_50764) baseStart_50764 baseEnd_50764 := by
    simpa [prefixWord, tailWord_50764, baseEnd_50764] using wordTrace_append hprefix tailTrace_50764
  have hstable : (prefixWord ++ tailWord_50764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50764).length < 2 ^ (prefixWord ++ tailWord_50764).sum := by decide
  have hdescent : baseEnd_50764 < baseStart_50764 := by decide
  rcases family_descends (prefixWord ++ tailWord_50764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50856 : List Nat := [2, 1, 7, 1, 1, 1, 2, 3, 2]
def baseStart_50856 : Nat := 118140960795 + 50856 * 2 ^ 59
def prefixEnd_50856 : Nat := 4983230072969 + 3 ^ 40 * 50856 * 2
def baseEnd_50856 : Nat := 23212064146807341658777

theorem tailTrace_50856 : CollatzResearch.WordTrace tailWord_50856 prefixEnd_50856 23212064146807341658777 := by
  unfold tailWord_50856
  simp only [CollatzResearch.WordTrace]
  refine ⟨927435351882436179210211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1236580469176581572280281 927435351882436179210211)
  ·
    refine ⟨1391153027823654268815317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 927435351882436179210211 1391153027823654268815317)
    ·
      refine ⟨32605149089616896925359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1391153027823654268815317 32605149089616896925359)
      ·
        refine ⟨48907723634425345388039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32605149089616896925359 48907723634425345388039)
        ·
          refine ⟨73361585451638018082059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48907723634425345388039 73361585451638018082059)
          ·
            refine ⟨110042378177457027123089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73361585451638018082059 110042378177457027123089)
            ·
              refine ⟨82531783633092770342317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110042378177457027123089 82531783633092770342317)
              ·
                refine ⟨30949418862409788878369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82531783633092770342317 30949418862409788878369)
                ·
                  refine ⟨23212064146807341658777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30949418862409788878369 23212064146807341658777)
                  ·
                    rfl

theorem cell20_50856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 2].length) (baseStart_50856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50856 prefixEnd_50856 := by exact prefixLift 50856
  have htrace : WordTrace (prefixWord ++ tailWord_50856) baseStart_50856 baseEnd_50856 := by
    simpa [prefixWord, tailWord_50856, baseEnd_50856] using wordTrace_append hprefix tailTrace_50856
  have hstable : (prefixWord ++ tailWord_50856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50856).length < 2 ^ (prefixWord ++ tailWord_50856).sum := by decide
  have hdescent : baseEnd_50856 < baseStart_50856 := by decide
  rcases family_descends (prefixWord ++ tailWord_50856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50864 : List Nat := [2, 1, 1, 1, 2, 1, 5, 5, 2]
def baseStart_50864 : Nat := 118140960795 + 50864 * 2 ^ 59
def prefixEnd_50864 : Nat := 4983230072969 + 3 ^ 40 * 50864 * 2
def baseEnd_50864 : Nat := 23215715564794869392077

theorem tailTrace_50864 : CollatzResearch.WordTrace tailWord_50864 prefixEnd_50864 23215715564794869392077 := by
  unfold tailWord_50864
  simp only [CollatzResearch.WordTrace]
  refine ⟨927581243867944862355823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1236774991823926483141097 927581243867944862355823)
  ·
    refine ⟨1391371865801917293533735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 927581243867944862355823 1391371865801917293533735)
    ·
      refine ⟨2087057798702875940300603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1391371865801917293533735 2087057798702875940300603)
      ·
        refine ⟨3130586698054313910450905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087057798702875940300603 3130586698054313910450905)
        ·
          refine ⟨2347940023540735432838179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3130586698054313910450905 2347940023540735432838179)
          ·
            refine ⟨3521910035311103149257269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2347940023540735432838179 3521910035311103149257269)
            ·
              refine ⟨330179065810415920242869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3521910035311103149257269 330179065810415920242869)
              ·
                refine ⟨30954287419726492522769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 330179065810415920242869 30954287419726492522769)
                ·
                  refine ⟨23215715564794869392077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30954287419726492522769 23215715564794869392077)
                  ·
                    rfl

theorem cell20_50864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 2].length) (baseStart_50864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50864 prefixEnd_50864 := by exact prefixLift 50864
  have htrace : WordTrace (prefixWord ++ tailWord_50864) baseStart_50864 baseEnd_50864 := by
    simpa [prefixWord, tailWord_50864, baseEnd_50864] using wordTrace_append hprefix tailTrace_50864
  have hstable : (prefixWord ++ tailWord_50864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50864).length < 2 ^ (prefixWord ++ tailWord_50864).sum := by decide
  have hdescent : baseEnd_50864 < baseStart_50864 := by decide
  rcases family_descends (prefixWord ++ tailWord_50864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50915 : List Nat := [1, 1, 1, 7, 3, 1, 1, 3, 2]
def baseStart_50915 : Nat := 118140960795 + 50915 * 2 ^ 59
def prefixEnd_50915 : Nat := 4983230072969 + 3 ^ 40 * 50915 * 2
def baseEnd_50915 : Nat := 23238993354465358691869

theorem tailTrace_50915 : CollatzResearch.WordTrace tailWord_50915 prefixEnd_50915 23238993354465358691869 := by
  unfold tailWord_50915
  simp only [CollatzResearch.WordTrace]
  refine ⟨1857022610551125434818199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1238015073700750289878799 1857022610551125434818199)
  ·
    refine ⟨2785533915826688152227299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1857022610551125434818199 2785533915826688152227299)
    ·
      refine ⟨4178300873740032228340949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2785533915826688152227299 4178300873740032228340949)
      ·
        refine ⟨97928926728282005351741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 4178300873740032228340949 97928926728282005351741)
        ·
          refine ⟨36723347523105752006903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97928926728282005351741 36723347523105752006903)
          ·
            refine ⟨55085021284658628010355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36723347523105752006903 55085021284658628010355)
            ·
              refine ⟨82627531926987942015533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55085021284658628010355 82627531926987942015533)
              ·
                refine ⟨30985324472620478255825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82627531926987942015533 30985324472620478255825)
                ·
                  refine ⟨23238993354465358691869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30985324472620478255825 23238993354465358691869)
                  ·
                    rfl

theorem cell20_50915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 2].length) (baseStart_50915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50915 prefixEnd_50915 := by exact prefixLift 50915
  have htrace : WordTrace (prefixWord ++ tailWord_50915) baseStart_50915 baseEnd_50915 := by
    simpa [prefixWord, tailWord_50915, baseEnd_50915] using wordTrace_append hprefix tailTrace_50915
  have hstable : (prefixWord ++ tailWord_50915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50915).length < 2 ^ (prefixWord ++ tailWord_50915).sum := by decide
  have hdescent : baseEnd_50915 < baseStart_50915 := by decide
  rcases family_descends (prefixWord ++ tailWord_50915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50932 : List Nat := [2, 6, 1, 1, 1, 2, 3, 2, 2]
def baseStart_50932 : Nat := 118140960795 + 50932 * 2 ^ 59
def prefixEnd_50932 : Nat := 4983230072969 + 3 ^ 40 * 50932 * 2
def baseEnd_50932 : Nat := 23246752617688855125133

theorem tailTrace_50932 : CollatzResearch.WordTrace tailWord_50932 prefixEnd_50932 23246752617688855125133 := by
  unfold tailWord_50932
  simp only [CollatzResearch.WordTrace]
  refine ⟨928821325744768669093525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1238428434326358225458033 928821325744768669093525)
  ·
    refine ⟨43538499644286031363759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 928821325744768669093525 43538499644286031363759)
    ·
      refine ⟨65307749466429047045639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43538499644286031363759 65307749466429047045639)
      ·
        refine ⟨97961624199643570568459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65307749466429047045639 97961624199643570568459)
        ·
          refine ⟨146942436299465355852689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97961624199643570568459 146942436299465355852689)
          ·
            refine ⟨110206827224599016889517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146942436299465355852689 110206827224599016889517)
            ·
              refine ⟨41327560209224631333569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110206827224599016889517 41327560209224631333569)
              ·
                refine ⟨30995670156918473500177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41327560209224631333569 30995670156918473500177)
                ·
                  refine ⟨23246752617688855125133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30995670156918473500177 23246752617688855125133)
                  ·
                    rfl

theorem cell20_50932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_50932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50932 prefixEnd_50932 := by exact prefixLift 50932
  have htrace : WordTrace (prefixWord ++ tailWord_50932) baseStart_50932 baseEnd_50932 := by
    simpa [prefixWord, tailWord_50932, baseEnd_50932] using wordTrace_append hprefix tailTrace_50932
  have hstable : (prefixWord ++ tailWord_50932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50932).length < 2 ^ (prefixWord ++ tailWord_50932).sum := by decide
  have hdescent : baseEnd_50932 < baseStart_50932 := by decide
  rcases family_descends (prefixWord ++ tailWord_50932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50968 : List Nat := [2, 1, 2, 3, 1, 1, 4, 6]
def baseStart_50968 : Nat := 118140960795 + 50968 * 2 ^ 59
def prefixEnd_50968 : Nat := 4983230072969 + 3 ^ 40 * 50968 * 2
def baseEnd_50968 : Nat := 7754394666210909974995

theorem tailTrace_50968 : CollatzResearch.WordTrace tailWord_50968 prefixEnd_50968 7754394666210909974995 := by
  unfold tailWord_50968
  simp only [CollatzResearch.WordTrace]
  refine ⟨929477839679557743248779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1239303786239410324331705 929477839679557743248779)
  ·
    refine ⟨1394216759519336614873169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 929477839679557743248779 1394216759519336614873169)
    ·
      refine ⟨1045662569639502461154877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1394216759519336614873169 1045662569639502461154877)
      ·
        refine ⟨392123463614813422933079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1045662569639502461154877 392123463614813422933079)
        ·
          refine ⟨588185195422220134399619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392123463614813422933079 588185195422220134399619)
          ·
            refine ⟨882277793133330201599429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588185195422220134399619 882277793133330201599429)
            ·
              refine ⟨165427086212499412799893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 882277793133330201599429 165427086212499412799893)
              ·
                refine ⟨7754394666210909974995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165427086212499412799893 7754394666210909974995)
                ·
                  rfl

theorem cell20_50968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_50968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50968 prefixEnd_50968 := by exact prefixLift 50968
  have htrace : WordTrace (prefixWord ++ tailWord_50968) baseStart_50968 baseEnd_50968 := by
    simpa [prefixWord, tailWord_50968, baseEnd_50968] using wordTrace_append hprefix tailTrace_50968
  have hstable : (prefixWord ++ tailWord_50968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50968).length < 2 ^ (prefixWord ++ tailWord_50968).sum := by decide
  have hdescent : baseEnd_50968 < baseStart_50968 := by decide
  rcases family_descends (prefixWord ++ tailWord_50968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_50995 : List Nat := [1, 1, 1, 2, 7, 1, 1, 4, 2]
def baseStart_50995 : Nat := 118140960795 + 50995 * 2 ^ 59
def prefixEnd_50995 : Nat := 4983230072969 + 3 ^ 40 * 50995 * 2
def baseEnd_50995 : Nat := 23275507534340636024875

theorem tailTrace_50995 : CollatzResearch.WordTrace tailWord_50995 prefixEnd_50995 23275507534340636024875 := by
  unfold tailWord_50995
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859940450261299097730439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1239960300174199398486959 1859940450261299097730439)
  ·
    refine ⟨2789910675391948646595659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1859940450261299097730439 2789910675391948646595659)
    ·
      refine ⟨4184866013087922969893489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2789910675391948646595659 4184866013087922969893489)
      ·
        refine ⟨3138649509815942227420117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4184866013087922969893489 3138649509815942227420117)
        ·
          refine ⟨73562097886311145955159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3138649509815942227420117 73562097886311145955159)
          ·
            refine ⟨110343146829466718932739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73562097886311145955159 110343146829466718932739)
            ·
              refine ⟨165514720244200078399109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110343146829466718932739 165514720244200078399109)
              ·
                refine ⟨31034010045787514699833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165514720244200078399109 31034010045787514699833)
                ·
                  refine ⟨23275507534340636024875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31034010045787514699833 23275507534340636024875)
                  ·
                    rfl

theorem cell20_50995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 2].length) (baseStart_50995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_50995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_50995 prefixEnd_50995 := by exact prefixLift 50995
  have htrace : WordTrace (prefixWord ++ tailWord_50995) baseStart_50995 baseEnd_50995 := by
    simpa [prefixWord, tailWord_50995, baseEnd_50995] using wordTrace_append hprefix tailTrace_50995
  have hstable : (prefixWord ++ tailWord_50995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_50995).length < 2 ^ (prefixWord ++ tailWord_50995).sum := by decide
  have hdescent : baseEnd_50995 < baseStart_50995 := by decide
  rcases family_descends (prefixWord ++ tailWord_50995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51054 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_51054 : Nat := 118140960795 + 51054 * 2 ^ 59
def prefixEnd_51054 : Nat := 4983230072969 + 3 ^ 40 * 51054 * 2
def baseEnd_51054 : Nat := 23302436741998653057967

theorem tailTrace_51054 : CollatzResearch.WordTrace tailWord_51054 prefixEnd_51054 23302436741998653057967 := by
  unfold tailWord_51054
  simp only [CollatzResearch.WordTrace]
  refine ⟨232761544630944021766027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1241394904698368116085477 232761544630944021766027)
  ·
    refine ⟨349142316946416032649041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232761544630944021766027 349142316946416032649041)
    ·
      refine ⟨261856737709812024486781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349142316946416032649041 261856737709812024486781)
      ·
        refine ⟨98196276641179509182543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261856737709812024486781 98196276641179509182543)
        ·
          refine ⟨147294414961769263773815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98196276641179509182543 147294414961769263773815)
          ·
            refine ⟨220941622442653895660723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147294414961769263773815 220941622442653895660723)
            ·
              refine ⟨331412433663980843491085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220941622442653895660723 331412433663980843491085)
              ·
                refine ⟨124279662623992816309157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331412433663980843491085 124279662623992816309157)
                ·
                  refine ⟨23302436741998653057967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124279662623992816309157 23302436741998653057967)
                  ·
                    rfl

theorem cell20_51054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_51054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51054 prefixEnd_51054 := by exact prefixLift 51054
  have htrace : WordTrace (prefixWord ++ tailWord_51054) baseStart_51054 baseEnd_51054 := by
    simpa [prefixWord, tailWord_51054, baseEnd_51054] using wordTrace_append hprefix tailTrace_51054
  have hstable : (prefixWord ++ tailWord_51054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51054).length < 2 ^ (prefixWord ++ tailWord_51054).sum := by decide
  have hdescent : baseEnd_51054 < baseStart_51054 := by decide
  rcases family_descends (prefixWord ++ tailWord_51054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51075 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 4]
def baseStart_51075 : Nat := 118140960795 + 51075 * 2 ^ 59
def prefixEnd_51075 : Nat := 4983230072969 + 3 ^ 40 * 51075 * 2
def baseEnd_51075 : Nat := 23312021714215913357881

theorem tailTrace_51075 : CollatzResearch.WordTrace tailWord_51075 prefixEnd_51075 23312021714215913357881 := by
  unfold tailWord_51075
  simp only [CollatzResearch.WordTrace]
  refine ⟨1862858289971472760642679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1241905526647648507095119 1862858289971472760642679)
  ·
    refine ⟨2794287434957209140964019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1862858289971472760642679 2794287434957209140964019)
    ·
      refine ⟨4191431152435813711446029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2794287434957209140964019 4191431152435813711446029)
      ·
        refine ⟨1571786682163430141792261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4191431152435813711446029 1571786682163430141792261)
        ·
          refine ⟨294710002905643151586049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1571786682163430141792261 294710002905643151586049)
          ·
            refine ⟨221032502179232363689537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294710002905643151586049 221032502179232363689537)
            ·
              refine ⟨165774376634424272767153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221032502179232363689537 165774376634424272767153)
              ·
                refine ⟨124330782475818204575365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165774376634424272767153 124330782475818204575365)
                ·
                  refine ⟨23312021714215913357881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124330782475818204575365 23312021714215913357881)
                  ·
                    rfl

theorem cell20_51075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_51075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51075 prefixEnd_51075 := by exact prefixLift 51075
  have htrace : WordTrace (prefixWord ++ tailWord_51075) baseStart_51075 baseEnd_51075 := by
    simpa [prefixWord, tailWord_51075, baseEnd_51075] using wordTrace_append hprefix tailTrace_51075
  have hstable : (prefixWord ++ tailWord_51075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51075).length < 2 ^ (prefixWord ++ tailWord_51075).sum := by decide
  have hdescent : baseEnd_51075 < baseStart_51075 := by decide
  rcases family_descends (prefixWord ++ tailWord_51075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51089 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 5]
def baseStart_51089 : Nat := 118140960795 + 51089 * 2 ^ 59
def prefixEnd_51089 : Nat := 4983230072969 + 3 ^ 40 * 51089 * 2
def baseEnd_51089 : Nat := 23318411695694086891157

theorem tailTrace_51089 : CollatzResearch.WordTrace tailWord_51089 prefixEnd_51089 23318411695694086891157 := by
  unfold tailWord_51089
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863368911920753151652321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1242245941280502101101547 1863368911920753151652321)
  ·
    refine ⟨1397526683940564863739241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1863368911920753151652321 1397526683940564863739241)
    ·
      refine ⟨1048145012955423647804431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1397526683940564863739241 1048145012955423647804431)
      ·
        refine ⟨1572217519433135471706647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048145012955423647804431 1572217519433135471706647)
        ·
          refine ⟨2358326279149703207559971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1572217519433135471706647 2358326279149703207559971)
          ·
            refine ⟨3537489418724554811339957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358326279149703207559971 3537489418724554811339957)
            ·
              refine ⟨331639633005427013563121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3537489418724554811339957 331639633005427013563121)
              ·
                refine ⟨248729724754070260172341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331639633005427013563121 248729724754070260172341)
                ·
                  refine ⟨23318411695694086891157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 248729724754070260172341 23318411695694086891157)
                  ·
                    rfl

theorem cell20_51089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_51089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51089 prefixEnd_51089 := by exact prefixLift 51089
  have htrace : WordTrace (prefixWord ++ tailWord_51089) baseStart_51089 baseEnd_51089 := by
    simpa [prefixWord, tailWord_51089, baseEnd_51089] using wordTrace_append hprefix tailTrace_51089
  have hstable : (prefixWord ++ tailWord_51089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51089).length < 2 ^ (prefixWord ++ tailWord_51089).sum := by decide
  have hdescent : baseEnd_51089 < baseStart_51089 := by decide
  rcases family_descends (prefixWord ++ tailWord_51089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51161 : List Nat := [1, 2, 1, 2, 6, 1, 2, 2, 3]
def baseStart_51161 : Nat := 118140960795 + 51161 * 2 ^ 59
def prefixEnd_51161 : Nat := 4983230072969 + 3 ^ 40 * 51161 * 2
def baseEnd_51161 : Nat := 23351274457581836490863

theorem tailTrace_51161 : CollatzResearch.WordTrace tailWord_51161 prefixEnd_51161 23351274457581836490863 := by
  unfold tailWord_51161
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865994967659909448273337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1243996645106606298848891 1865994967659909448273337)
  ·
    refine ⟨1399496225744932086205003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1865994967659909448273337 1399496225744932086205003)
    ·
      refine ⟨2099244338617398129307505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1399496225744932086205003 2099244338617398129307505)
      ·
        refine ⟨1574433253963048596980629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2099244338617398129307505 1574433253963048596980629)
        ·
          refine ⟨73801558779517902983467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1574433253963048596980629 73801558779517902983467)
          ·
            refine ⟨110702338169276854475201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73801558779517902983467 110702338169276854475201)
            ·
              refine ⟨83026753626957640856401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110702338169276854475201 83026753626957640856401)
              ·
                refine ⟨62270065220218230642301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83026753626957640856401 62270065220218230642301)
                ·
                  refine ⟨23351274457581836490863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62270065220218230642301 23351274457581836490863)
                  ·
                    rfl

theorem cell20_51161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_51161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51161 prefixEnd_51161 := by exact prefixLift 51161
  have htrace : WordTrace (prefixWord ++ tailWord_51161) baseStart_51161 baseEnd_51161 := by
    simpa [prefixWord, tailWord_51161, baseEnd_51161] using wordTrace_append hprefix tailTrace_51161
  have hstable : (prefixWord ++ tailWord_51161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51161).length < 2 ^ (prefixWord ++ tailWord_51161).sum := by decide
  have hdescent : baseEnd_51161 < baseStart_51161 := by decide
  rcases family_descends (prefixWord ++ tailWord_51161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51234 : List Nat := [3, 3, 1, 1, 1, 2, 2, 7]
def baseStart_51234 : Nat := 118140960795 + 51234 * 2 ^ 59
def prefixEnd_51234 : Nat := 4983230072969 + 3 ^ 40 * 51234 * 2
def baseEnd_51234 : Nat := 7794864548906009019077

theorem tailTrace_51234 : CollatzResearch.WordTrace tailWord_51234 prefixEnd_51234 7794864548906009019077 := by
  unfold tailWord_51234
  simp only [CollatzResearch.WordTrace]
  refine ⟨467164374098860728920189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1245771664263628610453837 467164374098860728920189)
  ·
    refine ⟨175186640287072773345071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 467164374098860728920189 175186640287072773345071)
    ·
      refine ⟨262779960430609160017607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175186640287072773345071 262779960430609160017607)
      ·
        refine ⟨394169940645913740026411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262779960430609160017607 394169940645913740026411)
        ·
          refine ⟨591254910968870610039617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394169940645913740026411 591254910968870610039617)
          ·
            refine ⟨443441183226652957529713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 591254910968870610039617 443441183226652957529713)
            ·
              refine ⟨332580887419989718147285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443441183226652957529713 332580887419989718147285)
              ·
                refine ⟨7794864548906009019077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 332580887419989718147285 7794864548906009019077)
                ·
                  rfl

theorem cell20_51234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_51234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51234 prefixEnd_51234 := by exact prefixLift 51234
  have htrace : WordTrace (prefixWord ++ tailWord_51234) baseStart_51234 baseEnd_51234 := by
    simpa [prefixWord, tailWord_51234, baseEnd_51234] using wordTrace_append hprefix tailTrace_51234
  have hstable : (prefixWord ++ tailWord_51234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51234).length < 2 ^ (prefixWord ++ tailWord_51234).sum := by decide
  have hdescent : baseEnd_51234 < baseStart_51234 := by decide
  rcases family_descends (prefixWord ++ tailWord_51234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51237 : List Nat := [1, 3, 1, 2, 2, 4, 3, 1, 3]
def baseStart_51237 : Nat := 118140960795 + 51237 * 2 ^ 59
def prefixEnd_51237 : Nat := 4983230072969 + 3 ^ 40 * 51237 * 2
def baseEnd_51237 : Nat := 23385962928463349957219

theorem tailTrace_51237 : CollatzResearch.WordTrace tailWord_51237 prefixEnd_51237 23385962928463349957219 := by
  unfold tailWord_51237
  simp only [CollatzResearch.WordTrace]
  refine ⟨1868766915384574428039965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1245844610256382952026643 1868766915384574428039965)
  ·
    refine ⟨700787593269215410514987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1868766915384574428039965 700787593269215410514987)
    ·
      refine ⟨1051181389903823115772481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 700787593269215410514987 1051181389903823115772481)
      ·
        refine ⟨788386042427867336829361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1051181389903823115772481 788386042427867336829361)
        ·
          refine ⟨591289531820900502622021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 788386042427867336829361 591289531820900502622021)
          ·
            refine ⟨110866787216418844241629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 591289531820900502622021 110866787216418844241629)
            ·
              refine ⟨41575045206157066590611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110866787216418844241629 41575045206157066590611)
              ·
                refine ⟨62362567809235599885917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41575045206157066590611 62362567809235599885917)
                ·
                  refine ⟨23385962928463349957219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62362567809235599885917 23385962928463349957219)
                  ·
                    rfl

theorem cell20_51237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_51237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51237 prefixEnd_51237 := by exact prefixLift 51237
  have htrace : WordTrace (prefixWord ++ tailWord_51237) baseStart_51237 baseEnd_51237 := by
    simpa [prefixWord, tailWord_51237, baseEnd_51237] using wordTrace_append hprefix tailTrace_51237
  have hstable : (prefixWord ++ tailWord_51237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51237).length < 2 ^ (prefixWord ++ tailWord_51237).sum := by decide
  have hdescent : baseEnd_51237 < baseStart_51237 := by decide
  rcases family_descends (prefixWord ++ tailWord_51237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51292 : List Nat := [2, 2, 4, 1, 1, 4, 2, 1, 3]
def baseStart_51292 : Nat := 118140960795 + 51292 * 2 ^ 59
def prefixEnd_51292 : Nat := 4983230072969 + 3 ^ 40 * 51292 * 2
def baseEnd_51292 : Nat := 23411066427127603123661

theorem tailTrace_51292 : CollatzResearch.WordTrace tailWord_51292 prefixEnd_51292 23411066427127603123661 := by
  unfold tailWord_51292
  simp only [CollatzResearch.WordTrace]
  refine ⟨935386465092659410646065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1247181953456879214194753 935386465092659410646065)
  ·
    refine ⟨701539848819494557984549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 935386465092659410646065 701539848819494557984549)
    ·
      refine ⟨131538721653655229622103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 701539848819494557984549 131538721653655229622103)
      ·
        refine ⟨197308082480482844433155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131538721653655229622103 197308082480482844433155)
        ·
          refine ⟨295962123720724266649733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197308082480482844433155 295962123720724266649733)
          ·
            refine ⟨55492898197635799996825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 295962123720724266649733 55492898197635799996825)
            ·
              refine ⟨41619673648226849997619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55492898197635799996825 41619673648226849997619)
              ·
                refine ⟨62429510472340274996429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41619673648226849997619 62429510472340274996429)
                ·
                  refine ⟨23411066427127603123661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62429510472340274996429 23411066427127603123661)
                  ·
                    rfl

theorem cell20_51292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_51292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51292 prefixEnd_51292 := by exact prefixLift 51292
  have htrace : WordTrace (prefixWord ++ tailWord_51292) baseStart_51292 baseEnd_51292 := by
    simpa [prefixWord, tailWord_51292, baseEnd_51292] using wordTrace_append hprefix tailTrace_51292
  have hstable : (prefixWord ++ tailWord_51292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51292).length < 2 ^ (prefixWord ++ tailWord_51292).sum := by decide
  have hdescent : baseEnd_51292 < baseStart_51292 := by decide
  rcases family_descends (prefixWord ++ tailWord_51292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51296 : List Nat := [2, 1, 1, 3, 2, 4, 1, 3, 3]
def baseStart_51296 : Nat := 118140960795 + 51296 * 2 ^ 59
def prefixEnd_51296 : Nat := 4983230072969 + 3 ^ 40 * 51296 * 2
def baseEnd_51296 : Nat := 23412892136121366990311

theorem tailTrace_51296 : CollatzResearch.WordTrace tailWord_51296 prefixEnd_51296 23412892136121366990311 := by
  unfold tailWord_51296
  simp only [CollatzResearch.WordTrace]
  refine ⟨935459411085413752218871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1247279214780551669625161 935459411085413752218871)
  ·
    refine ⟨1403189116628120628328307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 935459411085413752218871 1403189116628120628328307)
    ·
      refine ⟨2104783674942180942492461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1403189116628120628328307 2104783674942180942492461)
      ·
        refine ⟨789293878103317853434673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2104783674942180942492461 789293878103317853434673)
        ·
          refine ⟨591970408577488390076005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 789293878103317853434673 591970408577488390076005)
          ·
            refine ⟨110994451608279073139251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 591970408577488390076005 110994451608279073139251)
            ·
              refine ⟨166491677412418609708877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110994451608279073139251 166491677412418609708877)
              ·
                refine ⟨62434379029656978640829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166491677412418609708877 62434379029656978640829)
                ·
                  refine ⟨23412892136121366990311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62434379029656978640829 23412892136121366990311)
                  ·
                    rfl

theorem cell20_51296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_51296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51296 prefixEnd_51296 := by exact prefixLift 51296
  have htrace : WordTrace (prefixWord ++ tailWord_51296) baseStart_51296 baseEnd_51296 := by
    simpa [prefixWord, tailWord_51296, baseEnd_51296] using wordTrace_append hprefix tailTrace_51296
  have hstable : (prefixWord ++ tailWord_51296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51296).length < 2 ^ (prefixWord ++ tailWord_51296).sum := by decide
  have hdescent : baseEnd_51296 < baseStart_51296 := by decide
  rcases family_descends (prefixWord ++ tailWord_51296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51310 : List Nat := [4, 1, 2, 2, 1, 1, 1, 8]
def baseStart_51310 : Nat := 118140960795 + 51310 * 2 ^ 59
def prefixEnd_51310 : Nat := 4983230072969 + 3 ^ 40 * 51310 * 2
def baseEnd_51310 : Nat := 7806427372533180174529

theorem tailTrace_51310 : CollatzResearch.WordTrace tailWord_51310 prefixEnd_51310 7806427372533180174529 := by
  unfold tailWord_51310
  simp only [CollatzResearch.WordTrace]
  refine ⟨233928680515013486930923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1247619629413405263631589 233928680515013486930923)
  ·
    refine ⟨350893020772520230396385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233928680515013486930923 350893020772520230396385)
    ·
      refine ⟨263169765579390172797289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350893020772520230396385 263169765579390172797289)
      ·
        refine ⟨197377324184542629597967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263169765579390172797289 197377324184542629597967)
        ·
          refine ⟨296065986276813944396951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197377324184542629597967 296065986276813944396951)
          ·
            refine ⟨444098979415220916595427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296065986276813944396951 444098979415220916595427)
            ·
              refine ⟨666148469122831374893141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444098979415220916595427 666148469122831374893141)
              ·
                refine ⟨7806427372533180174529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 666148469122831374893141 7806427372533180174529)
                ·
                  rfl

theorem cell20_51310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_51310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51310 prefixEnd_51310 := by exact prefixLift 51310
  have htrace : WordTrace (prefixWord ++ tailWord_51310) baseStart_51310 baseEnd_51310 := by
    simpa [prefixWord, tailWord_51310, baseEnd_51310] using wordTrace_append hprefix tailTrace_51310
  have hstable : (prefixWord ++ tailWord_51310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51310).length < 2 ^ (prefixWord ++ tailWord_51310).sum := by decide
  have hdescent : baseEnd_51310 < baseStart_51310 := by decide
  rcases family_descends (prefixWord ++ tailWord_51310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51331 : List Nat := [1, 1, 1, 3, 3, 11]
def baseStart_51331 : Nat := 118140960795 + 51331 * 2 ^ 59
def prefixEnd_51331 : Nat := 4983230072969 + 3 ^ 40 * 51331 * 2
def baseEnd_51331 : Nat := 867735818141362993463

theorem tailTrace_51331 : CollatzResearch.WordTrace tailWord_51331 prefixEnd_51331 867735818141362993463 := by
  unfold tailWord_51331
  simp only [CollatzResearch.WordTrace]
  refine ⟨1872195377044028481961847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1248130251362685654641231 1872195377044028481961847)
  ·
    refine ⟨2808293065566042722942771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1872195377044028481961847 2808293065566042722942771)
    ·
      refine ⟨4212439598349064084414157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2808293065566042722942771 4212439598349064084414157)
      ·
        refine ⟨1579664849380899031655309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4212439598349064084414157 1579664849380899031655309)
        ·
          refine ⟨592374318517837136870741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1579664849380899031655309 592374318517837136870741)
          ·
            refine ⟨867735818141362993463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 592374318517837136870741 867735818141362993463)
            ·
              rfl

theorem cell20_51331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 11].length) (baseStart_51331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51331 prefixEnd_51331 := by exact prefixLift 51331
  have htrace : WordTrace (prefixWord ++ tailWord_51331) baseStart_51331 baseEnd_51331 := by
    simpa [prefixWord, tailWord_51331, baseEnd_51331] using wordTrace_append hprefix tailTrace_51331
  have hstable : (prefixWord ++ tailWord_51331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51331).length < 2 ^ (prefixWord ++ tailWord_51331).sum := by decide
  have hdescent : baseEnd_51331 < baseStart_51331 := by decide
  rcases family_descends (prefixWord ++ tailWord_51331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51355 : List Nat := [1, 1, 1, 1, 1, 1, 2, 9, 3]
def baseStart_51355 : Nat := 118140960795 + 51355 * 2 ^ 59
def prefixEnd_51355 : Nat := 4983230072969 + 3 ^ 40 * 51355 * 2
def baseEnd_51355 : Nat := 23439821343779384023403

theorem tailTrace_51355 : CollatzResearch.WordTrace tailWord_51355 prefixEnd_51355 23439821343779384023403 := by
  unfold tailWord_51355
  simp only [CollatzResearch.WordTrace]
  refine ⟨1873070728957080580835519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1248713819304720387223679 1873070728957080580835519)
  ·
    refine ⟨2809606093435620871253279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1873070728957080580835519 2809606093435620871253279)
    ·
      refine ⟨4214409140153431306879919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2809606093435620871253279 4214409140153431306879919)
      ·
        refine ⟨6321613710230146960319879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4214409140153431306879919 6321613710230146960319879)
        ·
          refine ⟨9482420565345220440479819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6321613710230146960319879 9482420565345220440479819)
          ·
            refine ⟨14223630848017830660719729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9482420565345220440479819 14223630848017830660719729)
            ·
              refine ⟨10667723136013372995539797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14223630848017830660719729 10667723136013372995539797)
              ·
                refine ⟨62506190250078357395741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10667723136013372995539797 62506190250078357395741)
                ·
                  refine ⟨23439821343779384023403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62506190250078357395741 23439821343779384023403)
                  ·
                    rfl

theorem cell20_51355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 3].length) (baseStart_51355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51355 prefixEnd_51355 := by exact prefixLift 51355
  have htrace : WordTrace (prefixWord ++ tailWord_51355) baseStart_51355 baseEnd_51355 := by
    simpa [prefixWord, tailWord_51355, baseEnd_51355] using wordTrace_append hprefix tailTrace_51355
  have hstable : (prefixWord ++ tailWord_51355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51355).length < 2 ^ (prefixWord ++ tailWord_51355).sum := by decide
  have hdescent : baseEnd_51355 < baseStart_51355 := by decide
  rcases family_descends (prefixWord ++ tailWord_51355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51396 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 4]
def baseStart_51396 : Nat := 118140960795 + 51396 * 2 ^ 59
def prefixEnd_51396 : Nat := 4983230072969 + 3 ^ 40 * 51396 * 2
def baseEnd_51396 : Nat := 23458534860965463656569

theorem tailTrace_51396 : CollatzResearch.WordTrace tailWord_51396 prefixEnd_51396 23458534860965463656569 := by
  unfold tailWord_51396
  simp only [CollatzResearch.WordTrace]
  refine ⟨937283060904272291539021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1249710747872363055385361 937283060904272291539021)
  ·
    refine ⟨351481147839102109327133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 937283060904272291539021 351481147839102109327133)
    ·
      refine ⟨131805430439663290997675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351481147839102109327133 131805430439663290997675)
      ·
        refine ⟨197708145659494936496513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131805430439663290997675 197708145659494936496513)
        ·
          refine ⟨148281109244621202372385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197708145659494936496513 148281109244621202372385)
          ·
            refine ⟨111210831933465901779289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148281109244621202372385 111210831933465901779289)
            ·
              refine ⟨83408123950099426334467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111210831933465901779289 83408123950099426334467)
              ·
                refine ⟨125112185925149139501701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83408123950099426334467 125112185925149139501701)
                ·
                  refine ⟨23458534860965463656569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125112185925149139501701 23458534860965463656569)
                  ·
                    rfl

theorem cell20_51396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_51396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51396 prefixEnd_51396 := by exact prefixLift 51396
  have htrace : WordTrace (prefixWord ++ tailWord_51396) baseStart_51396 baseEnd_51396 := by
    simpa [prefixWord, tailWord_51396, baseEnd_51396] using wordTrace_append hprefix tailTrace_51396
  have hstable : (prefixWord ++ tailWord_51396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51396).length < 2 ^ (prefixWord ++ tailWord_51396).sum := by decide
  have hdescent : baseEnd_51396 < baseStart_51396 := by decide
  rcases family_descends (prefixWord ++ tailWord_51396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51407 : List Nat := [1, 1, 2, 1, 1, 3, 4, 7]
def baseStart_51407 : Nat := 118140960795 + 51407 * 2 ^ 59
def prefixEnd_51407 : Nat := 4983230072969 + 3 ^ 40 * 51407 * 2
def baseEnd_51407 : Nat := 7821185186899438096619

theorem tailTrace_51407 : CollatzResearch.WordTrace tailWord_51407 prefixEnd_51407 7821185186899438096619 := by
  unfold tailWord_51407
  simp only [CollatzResearch.WordTrace]
  refine ⟨1874967324768693461728475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1249978216512462307818983 1874967324768693461728475)
  ·
    refine ⟨2812450987153040192592713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1874967324768693461728475 2812450987153040192592713)
    ·
      refine ⟨2109338240364780144444535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2812450987153040192592713 2109338240364780144444535)
      ·
        refine ⟨3164007360547170216666803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2109338240364780144444535 3164007360547170216666803)
        ·
          refine ⟨4746011040820755325000205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3164007360547170216666803 4746011040820755325000205)
          ·
            refine ⟨1779754140307783246875077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4746011040820755325000205 1779754140307783246875077)
            ·
              refine ⟨333703901307709358789077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1779754140307783246875077 333703901307709358789077)
              ·
                refine ⟨7821185186899438096619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 333703901307709358789077 7821185186899438096619)
                ·
                  rfl

theorem cell20_51407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_51407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51407 prefixEnd_51407 := by exact prefixLift 51407
  have htrace : WordTrace (prefixWord ++ tailWord_51407) baseStart_51407 baseEnd_51407 := by
    simpa [prefixWord, tailWord_51407, baseEnd_51407] using wordTrace_append hprefix tailTrace_51407
  have hstable : (prefixWord ++ tailWord_51407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51407).length < 2 ^ (prefixWord ++ tailWord_51407).sum := by decide
  have hdescent : baseEnd_51407 < baseStart_51407 := by decide
  rcases family_descends (prefixWord ++ tailWord_51407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51420 : List Nat := [2, 2, 5, 2, 1, 1, 1, 6]
def baseStart_51420 : Nat := 118140960795 + 51420 * 2 ^ 59
def prefixEnd_51420 : Nat := 4983230072969 + 3 ^ 40 * 51420 * 2
def baseEnd_51420 : Nat := 7823163038309348952157

theorem tailTrace_51420 : CollatzResearch.WordTrace tailWord_51420 prefixEnd_51420 7823163038309348952157 := by
  unfold tailWord_51420
  simp only [CollatzResearch.WordTrace]
  refine ⟨937720736860798340975857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1250294315814397787967809 937720736860798340975857)
  ·
    refine ⟨703290552645598755731893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 937720736860798340975857 703290552645598755731893)
    ·
      refine ⟨65933489310524883349865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 703290552645598755731893 65933489310524883349865)
      ·
        refine ⟨49450116982893662512399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65933489310524883349865 49450116982893662512399)
        ·
          refine ⟨74175175474340493768599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49450116982893662512399 74175175474340493768599)
          ·
            refine ⟨111262763211510740652899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74175175474340493768599 111262763211510740652899)
            ·
              refine ⟨166894144817266110979349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111262763211510740652899 166894144817266110979349)
              ·
                refine ⟨7823163038309348952157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 166894144817266110979349 7823163038309348952157)
                ·
                  rfl

theorem cell20_51420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_51420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51420 prefixEnd_51420 := by exact prefixLift 51420
  have htrace : WordTrace (prefixWord ++ tailWord_51420) baseStart_51420 baseEnd_51420 := by
    simpa [prefixWord, tailWord_51420, baseEnd_51420] using wordTrace_append hprefix tailTrace_51420
  have hstable : (prefixWord ++ tailWord_51420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51420).length < 2 ^ (prefixWord ++ tailWord_51420).sum := by decide
  have hdescent : baseEnd_51420 < baseStart_51420 := by decide
  rcases family_descends (prefixWord ++ tailWord_51420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51426 : List Nat := [3, 3, 4, 1, 1, 2, 1, 3, 2]
def baseStart_51426 : Nat := 118140960795 + 51426 * 2 ^ 59
def prefixEnd_51426 : Nat := 4983230072969 + 3 ^ 40 * 51426 * 2
def baseEnd_51426 : Nat := 23472227678418692656447

theorem tailTrace_51426 : CollatzResearch.WordTrace tailWord_51426 prefixEnd_51426 23472227678418692656447 := by
  unfold tailWord_51426
  simp only [CollatzResearch.WordTrace]
  refine ⟨468915077924964926667533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1250440207799906471113421 468915077924964926667533)
  ·
    refine ⟨175843154221861847500325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 468915077924964926667533 175843154221861847500325)
    ·
      refine ⟨32970591416599096406311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175843154221861847500325 32970591416599096406311)
      ·
        refine ⟨49455887124898644609467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32970591416599096406311 49455887124898644609467)
        ·
          refine ⟨74183830687347966914201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49455887124898644609467 74183830687347966914201)
          ·
            refine ⟨55637873015510975185651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74183830687347966914201 55637873015510975185651)
            ·
              refine ⟨83456809523266462778477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55637873015510975185651 83456809523266462778477)
              ·
                refine ⟨31296303571224923541929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83456809523266462778477 31296303571224923541929)
                ·
                  refine ⟨23472227678418692656447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31296303571224923541929 23472227678418692656447)
                  ·
                    rfl

theorem cell20_51426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_51426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51426 prefixEnd_51426 := by exact prefixLift 51426
  have htrace : WordTrace (prefixWord ++ tailWord_51426) baseStart_51426 baseEnd_51426 := by
    simpa [prefixWord, tailWord_51426, baseEnd_51426] using wordTrace_append hprefix tailTrace_51426
  have hstable : (prefixWord ++ tailWord_51426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51426).length < 2 ^ (prefixWord ++ tailWord_51426).sum := by decide
  have hdescent : baseEnd_51426 < baseStart_51426 := by decide
  rcases family_descends (prefixWord ++ tailWord_51426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51465 : List Nat := [1, 2, 1, 1, 3, 6, 2, 1, 3]
def baseStart_51465 : Nat := 118140960795 + 51465 * 2 ^ 59
def prefixEnd_51465 : Nat := 4983230072969 + 3 ^ 40 * 51465 * 2
def baseEnd_51465 : Nat := 23490028341107890356287

theorem tailTrace_51465 : CollatzResearch.WordTrace tailWord_51465 prefixEnd_51465 23490028341107890356287 := by
  unfold tailWord_51465
  simp only [CollatzResearch.WordTrace]
  refine ⟨1877082758558569367339849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1251388505705712911559899 1877082758558569367339849)
  ·
    refine ⟨1407812068918927025504887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1877082758558569367339849 1407812068918927025504887)
    ·
      refine ⟨2111718103378390538257331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407812068918927025504887 2111718103378390538257331)
      ·
        refine ⟨3167577155067585807385997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2111718103378390538257331 3167577155067585807385997)
        ·
          refine ⟨1187841433150344677769749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3167577155067585807385997 1187841433150344677769749)
          ·
            refine ⟨55680067178922406770457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1187841433150344677769749 55680067178922406770457)
            ·
              refine ⟨41760050384191805077843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55680067178922406770457 41760050384191805077843)
              ·
                refine ⟨62640075576287707616765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41760050384191805077843 62640075576287707616765)
                ·
                  refine ⟨23490028341107890356287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62640075576287707616765 23490028341107890356287)
                  ·
                    rfl

theorem cell20_51465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_51465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51465 prefixEnd_51465 := by exact prefixLift 51465
  have htrace : WordTrace (prefixWord ++ tailWord_51465) baseStart_51465 baseEnd_51465 := by
    simpa [prefixWord, tailWord_51465, baseEnd_51465] using wordTrace_append hprefix tailTrace_51465
  have hstable : (prefixWord ++ tailWord_51465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51465).length < 2 ^ (prefixWord ++ tailWord_51465).sum := by decide
  have hdescent : baseEnd_51465 < baseStart_51465 := by decide
  rcases family_descends (prefixWord ++ tailWord_51465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51483 : List Nat := [1, 1, 1, 1, 1, 1, 8, 6]
def baseStart_51483 : Nat := 118140960795 + 51483 * 2 ^ 59
def prefixEnd_51483 : Nat := 4983230072969 + 3 ^ 40 * 51483 * 2
def baseEnd_51483 : Nat := 7832748010526609252071

theorem tailTrace_51483 : CollatzResearch.WordTrace tailWord_51483 prefixEnd_51483 7832748010526609252071 := by
  unfold tailWord_51483
  simp only [CollatzResearch.WordTrace]
  refine ⟨1877739272493358441495103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1251826181662238960996735 1877739272493358441495103)
  ·
    refine ⟨2816608908740037662242655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1877739272493358441495103 2816608908740037662242655)
    ·
      refine ⟨4224913363110056493363983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2816608908740037662242655 4224913363110056493363983)
      ·
        refine ⟨6337370044665084740045975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4224913363110056493363983 6337370044665084740045975)
        ·
          refine ⟨9506055066997627110068963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6337370044665084740045975 9506055066997627110068963)
          ·
            refine ⟨14259082600496440665103445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9506055066997627110068963 14259082600496440665103445)
            ·
              refine ⟨167098624224567664044181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 14259082600496440665103445 167098624224567664044181)
              ·
                refine ⟨7832748010526609252071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167098624224567664044181 7832748010526609252071)
                ·
                  rfl

theorem cell20_51483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 6].length) (baseStart_51483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51483 prefixEnd_51483 := by exact prefixLift 51483
  have htrace : WordTrace (prefixWord ++ tailWord_51483) baseStart_51483 baseEnd_51483 := by
    simpa [prefixWord, tailWord_51483, baseEnd_51483] using wordTrace_append hprefix tailTrace_51483
  have hstable : (prefixWord ++ tailWord_51483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51483).length < 2 ^ (prefixWord ++ tailWord_51483).sum := by decide
  have hdescent : baseEnd_51483 < baseStart_51483 := by decide
  rcases family_descends (prefixWord ++ tailWord_51483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51502 : List Nat := [4, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_51502 : Nat := 118140960795 + 51502 * 2 ^ 59
def prefixEnd_51502 : Nat := 4983230072969 + 3 ^ 40 * 51502 * 2
def baseEnd_51502 : Nat := 23506916149300206122803

theorem tailTrace_51502 : CollatzResearch.WordTrace tailWord_51502 prefixEnd_51502 23506916149300206122803 := by
  unfold tailWord_51502
  simp only [CollatzResearch.WordTrace]
  refine ⟨234804032428065585804595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1252288172949683124291173 234804032428065585804595)
  ·
    refine ⟨352206048642098378706893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234804032428065585804595 352206048642098378706893)
    ·
      refine ⟨132077268240786892015085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352206048642098378706893 132077268240786892015085)
      ·
        refine ⟨49528975590295084505657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132077268240786892015085 49528975590295084505657)
        ·
          refine ⟨37146731692721313379243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49528975590295084505657 37146731692721313379243)
          ·
            refine ⟨55720097539081970068865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37146731692721313379243 55720097539081970068865)
            ·
              refine ⟨41790073154311477551649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55720097539081970068865 41790073154311477551649)
              ·
                refine ⟨31342554865733608163737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41790073154311477551649 31342554865733608163737)
                ·
                  refine ⟨23506916149300206122803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31342554865733608163737 23506916149300206122803)
                  ·
                    rfl

theorem cell20_51502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_51502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51502 prefixEnd_51502 := by exact prefixLift 51502
  have htrace : WordTrace (prefixWord ++ tailWord_51502) baseStart_51502 baseEnd_51502 := by
    simpa [prefixWord, tailWord_51502, baseEnd_51502] using wordTrace_append hprefix tailTrace_51502
  have hstable : (prefixWord ++ tailWord_51502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51502).length < 2 ^ (prefixWord ++ tailWord_51502).sum := by decide
  have hdescent : baseEnd_51502 < baseStart_51502 := by decide
  rcases family_descends (prefixWord ++ tailWord_51502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51506 : List Nat := [3, 2, 1, 1, 5, 2, 2, 2, 2]
def baseStart_51506 : Nat := 118140960795 + 51506 * 2 ^ 59
def prefixEnd_51506 : Nat := 4983230072969 + 3 ^ 40 * 51506 * 2
def baseEnd_51506 : Nat := 23508741858293969989453

theorem tailTrace_51506 : CollatzResearch.WordTrace tailWord_51506 prefixEnd_51506 23508741858293969989453 := by
  unfold tailWord_51506
  simp only [CollatzResearch.WordTrace]
  refine ⟨469644537852508342395593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1252385434273355579721581 469644537852508342395593)
  ·
    refine ⟨352233403389381256796695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 469644537852508342395593 352233403389381256796695)
    ·
      refine ⟨528350105084071885195043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352233403389381256796695 528350105084071885195043)
      ·
        refine ⟨792525157626107827792565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528350105084071885195043 792525157626107827792565)
        ·
          refine ⟨74299233527447608855553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 792525157626107827792565 74299233527447608855553)
          ·
            refine ⟨55724425145585706641665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74299233527447608855553 55724425145585706641665)
            ·
              refine ⟨41793318859189279981249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55724425145585706641665 41793318859189279981249)
              ·
                refine ⟨31344989144391959985937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41793318859189279981249 31344989144391959985937)
                ·
                  refine ⟨23508741858293969989453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31344989144391959985937 23508741858293969989453)
                  ·
                    rfl

theorem cell20_51506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_51506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51506 prefixEnd_51506 := by exact prefixLift 51506
  have htrace : WordTrace (prefixWord ++ tailWord_51506) baseStart_51506 baseEnd_51506 := by
    simpa [prefixWord, tailWord_51506, baseEnd_51506] using wordTrace_append hprefix tailTrace_51506
  have hstable : (prefixWord ++ tailWord_51506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51506).length < 2 ^ (prefixWord ++ tailWord_51506).sum := by decide
  have hdescent : baseEnd_51506 < baseStart_51506 := by decide
  rcases family_descends (prefixWord ++ tailWord_51506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51562 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_51562 : Nat := 118140960795 + 51562 * 2 ^ 59
def prefixEnd_51562 : Nat := 4983230072969 + 3 ^ 40 * 51562 * 2
def baseEnd_51562 : Nat := 23534301784206664122557

theorem tailTrace_51562 : CollatzResearch.WordTrace tailWord_51562 prefixEnd_51562 23534301784206664122557 := by
  unfold tailWord_51562
  simp only [CollatzResearch.WordTrace]
  refine ⟨470155159801788733405235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1253747092804769955747293 470155159801788733405235)
  ·
    refine ⟨705232739702683100107853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 470155159801788733405235 705232739702683100107853)
    ·
      refine ⟨264462277388506162540445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 705232739702683100107853 264462277388506162540445)
      ·
        refine ⟨99173354020689810952667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264462277388506162540445 99173354020689810952667)
        ·
          refine ⟨148760031031034716429001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99173354020689810952667 148760031031034716429001)
          ·
            refine ⟨111570023273276037321751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148760031031034716429001 111570023273276037321751)
            ·
              refine ⟨167355034909914055982627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111570023273276037321751 167355034909914055982627)
              ·
                refine ⟨251032552364871083973941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167355034909914055982627 251032552364871083973941)
                ·
                  refine ⟨23534301784206664122557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 251032552364871083973941 23534301784206664122557)
                  ·
                    rfl

theorem cell20_51562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_51562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51562 prefixEnd_51562 := by exact prefixLift 51562
  have htrace : WordTrace (prefixWord ++ tailWord_51562) baseStart_51562 baseEnd_51562 := by
    simpa [prefixWord, tailWord_51562, baseEnd_51562] using wordTrace_append hprefix tailTrace_51562
  have hstable : (prefixWord ++ tailWord_51562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51562).length < 2 ^ (prefixWord ++ tailWord_51562).sum := by decide
  have hdescent : baseEnd_51562 < baseStart_51562 := by decide
  rcases family_descends (prefixWord ++ tailWord_51562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51593 : List Nat := [1, 2, 1, 1, 6, 3, 2, 4]
def baseStart_51593 : Nat := 118140960795 + 51593 * 2 ^ 59
def prefixEnd_51593 : Nat := 4983230072969 + 3 ^ 40 * 51593 * 2
def baseEnd_51593 : Nat := 7849483676302778029699

theorem tailTrace_51593 : CollatzResearch.WordTrace tailWord_51593 prefixEnd_51593 7849483676302778029699 := by
  unfold tailWord_51593
  simp only [CollatzResearch.WordTrace]
  refine ⟨1881751302094847227999433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1254500868063231485332955 1881751302094847227999433)
  ·
    refine ⟨1411313476571135420999575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1881751302094847227999433 1411313476571135420999575)
    ·
      refine ⟨2116970214856703131499363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1411313476571135420999575 2116970214856703131499363)
      ·
        refine ⟨3175455322285054697249045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2116970214856703131499363 3175455322285054697249045)
        ·
          refine ⟨148849468232111938933549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3175455322285054697249045 148849468232111938933549)
          ·
            refine ⟨55818550587041977100081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148849468232111938933549 55818550587041977100081)
            ·
              refine ⟨41863912940281482825061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55818550587041977100081 41863912940281482825061)
              ·
                refine ⟨7849483676302778029699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41863912940281482825061 7849483676302778029699)
                ·
                  rfl

theorem cell20_51593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 4].length) (baseStart_51593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51593 prefixEnd_51593 := by exact prefixLift 51593
  have htrace : WordTrace (prefixWord ++ tailWord_51593) baseStart_51593 baseEnd_51593 := by
    simpa [prefixWord, tailWord_51593, baseEnd_51593] using wordTrace_append hprefix tailTrace_51593
  have hstable : (prefixWord ++ tailWord_51593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51593).length < 2 ^ (prefixWord ++ tailWord_51593).sum := by decide
  have hdescent : baseEnd_51593 < baseStart_51593 := by decide
  rcases family_descends (prefixWord ++ tailWord_51593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51606 : List Nat := [5, 3, 1, 2, 2, 1, 6]
def baseStart_51606 : Nat := 118140960795 + 51606 * 2 ^ 59
def prefixEnd_51606 : Nat := 4983230072969 + 3 ^ 40 * 51606 * 2
def baseEnd_51606 : Nat := 2617153842570896295079

theorem tailTrace_51606 : CollatzResearch.WordTrace tailWord_51606 prefixEnd_51606 2617153842570896295079 := by
  unfold tailWord_51606
  simp only [CollatzResearch.WordTrace]
  refine ⟨117639090690484403013917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1254816967365166965481781 117639090690484403013917)
  ·
    refine ⟨44114659008931651130219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117639090690484403013917 44114659008931651130219)
    ·
      refine ⟨66171988513397476695329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44114659008931651130219 66171988513397476695329)
      ·
        refine ⟨49628991385048107521497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66171988513397476695329 49628991385048107521497)
        ·
          refine ⟨37221743538786080641123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49628991385048107521497 37221743538786080641123)
          ·
            refine ⟨55832615308179120961685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37221743538786080641123 55832615308179120961685)
            ·
              refine ⟨2617153842570896295079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55832615308179120961685 2617153842570896295079)
              ·
                rfl

theorem cell20_51606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 6].length) (baseStart_51606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51606 prefixEnd_51606 := by exact prefixLift 51606
  have htrace : WordTrace (prefixWord ++ tailWord_51606) baseStart_51606 baseEnd_51606 := by
    simpa [prefixWord, tailWord_51606, baseEnd_51606] using wordTrace_append hprefix tailTrace_51606
  have hstable : (prefixWord ++ tailWord_51606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51606).length < 2 ^ (prefixWord ++ tailWord_51606).sum := by decide
  have hdescent : baseEnd_51606 < baseStart_51606 := by decide
  rcases family_descends (prefixWord ++ tailWord_51606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51621 : List Nat := [1, 3, 1, 2, 1, 1, 4, 4, 3]
def baseStart_51621 : Nat := 118140960795 + 51621 * 2 ^ 59
def prefixEnd_51621 : Nat := 4983230072969 + 3 ^ 40 * 51621 * 2
def baseEnd_51621 : Nat := 23561230991864681155649

theorem tailTrace_51621 : CollatzResearch.WordTrace tailWord_51621 prefixEnd_51621 23561230991864681155649 := by
  unfold tailWord_51621
  simp only [CollatzResearch.WordTrace]
  refine ⟨1882772545993408010018717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1255181697328938673345811 1882772545993408010018717)
  ·
    refine ⟨706039704747528003757019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1882772545993408010018717 706039704747528003757019)
    ·
      refine ⟨1059059557121292005635529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706039704747528003757019 1059059557121292005635529)
      ·
        refine ⟨794294667840969004226647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1059059557121292005635529 794294667840969004226647)
        ·
          refine ⟨1191442001761453506339971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794294667840969004226647 1191442001761453506339971)
          ·
            refine ⟨1787163002642180259509957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191442001761453506339971 1787163002642180259509957)
            ·
              refine ⟨335093062995408798658117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1787163002642180259509957 335093062995408798658117)
              ·
                refine ⟨62829949311639149748397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335093062995408798658117 62829949311639149748397)
                ·
                  refine ⟨23561230991864681155649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62829949311639149748397 23561230991864681155649)
                  ·
                    rfl

theorem cell20_51621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_51621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51621 prefixEnd_51621 := by exact prefixLift 51621
  have htrace : WordTrace (prefixWord ++ tailWord_51621) baseStart_51621 baseEnd_51621 := by
    simpa [prefixWord, tailWord_51621, baseEnd_51621] using wordTrace_append hprefix tailTrace_51621
  have hstable : (prefixWord ++ tailWord_51621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51621).length < 2 ^ (prefixWord ++ tailWord_51621).sum := by decide
  have hdescent : baseEnd_51621 < baseStart_51621 := by decide
  rcases family_descends (prefixWord ++ tailWord_51621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51624 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 4]
def baseStart_51624 : Nat := 118140960795 + 51624 * 2 ^ 59
def prefixEnd_51624 : Nat := 4983230072969 + 3 ^ 40 * 51624 * 2
def baseEnd_51624 : Nat := 23562600273610004055637

theorem tailTrace_51624 : CollatzResearch.WordTrace tailWord_51624 prefixEnd_51624 23562600273610004055637 := by
  unfold tailWord_51624
  simp only [CollatzResearch.WordTrace]
  refine ⟨941440982491269761188963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1255254643321693014918617 941440982491269761188963)
  ·
    refine ⟨1412161473736904641783445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 941440982491269761188963 1412161473736904641783445)
    ·
      refine ⟨66195069081417405083599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1412161473736904641783445 66195069081417405083599)
      ·
        refine ⟨99292603622126107625399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66195069081417405083599 99292603622126107625399)
        ·
          refine ⟨148938905433189161438099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99292603622126107625399 148938905433189161438099)
          ·
            refine ⟨223408358149783742157149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148938905433189161438099 223408358149783742157149)
            ·
              refine ⟨83778134306168903308931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223408358149783742157149 83778134306168903308931)
              ·
                refine ⟨125667201459253354963397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83778134306168903308931 125667201459253354963397)
                ·
                  refine ⟨23562600273610004055637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125667201459253354963397 23562600273610004055637)
                  ·
                    rfl

theorem cell20_51624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_51624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51624 prefixEnd_51624 := by exact prefixLift 51624
  have htrace : WordTrace (prefixWord ++ tailWord_51624) baseStart_51624 baseEnd_51624 := by
    simpa [prefixWord, tailWord_51624, baseEnd_51624] using wordTrace_append hprefix tailTrace_51624
  have hstable : (prefixWord ++ tailWord_51624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51624).length < 2 ^ (prefixWord ++ tailWord_51624).sum := by decide
  have hdescent : baseEnd_51624 < baseStart_51624 := by decide
  rcases family_descends (prefixWord ++ tailWord_51624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51679 : List Nat := [1, 1, 2, 3, 3, 4, 2, 2, 2]
def baseStart_51679 : Nat := 118140960795 + 51679 * 2 ^ 59
def prefixEnd_51679 : Nat := 4983230072969 + 3 ^ 40 * 51679 * 2
def baseEnd_51679 : Nat := 23587703772274257222079

theorem tailTrace_51679 : CollatzResearch.WordTrace tailWord_51679 prefixEnd_51679 23587703772274257222079 := by
  unfold tailWord_51679
  simp only [CollatzResearch.WordTrace]
  refine ⟨1884887979783283915630091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1256591986522189277086727 1884887979783283915630091)
  ·
    refine ⟨2827331969674925873445137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1884887979783283915630091 2827331969674925873445137)
    ·
      refine ⟨2120498977256194405083853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2827331969674925873445137 2120498977256194405083853)
      ·
        refine ⟨795187116471072901906445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2120498977256194405083853 795187116471072901906445)
        ·
          refine ⟨298195168676652338214917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 795187116471072901906445 298195168676652338214917)
          ·
            refine ⟨55911594126872313415297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 298195168676652338214917 55911594126872313415297)
            ·
              refine ⟨41933695595154235061473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55911594126872313415297 41933695595154235061473)
              ·
                refine ⟨31450271696365676296105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41933695595154235061473 31450271696365676296105)
                ·
                  refine ⟨23587703772274257222079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31450271696365676296105 23587703772274257222079)
                  ·
                    rfl

theorem cell20_51679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 2].length) (baseStart_51679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51679 prefixEnd_51679 := by exact prefixLift 51679
  have htrace : WordTrace (prefixWord ++ tailWord_51679) baseStart_51679 baseEnd_51679 := by
    simpa [prefixWord, tailWord_51679, baseEnd_51679] using wordTrace_append hprefix tailTrace_51679
  have hstable : (prefixWord ++ tailWord_51679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51679).length < 2 ^ (prefixWord ++ tailWord_51679).sum := by decide
  have hdescent : baseEnd_51679 < baseStart_51679 := by decide
  rcases family_descends (prefixWord ++ tailWord_51679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51690 : List Nat := [3, 1, 3, 1, 3, 1, 3, 5]
def baseStart_51690 : Nat := 118140960795 + 51690 * 2 ^ 59
def prefixEnd_51690 : Nat := 4983230072969 + 3 ^ 40 * 51690 * 2
def baseEnd_51690 : Nat := 7864241490669035951789

theorem tailTrace_51690 : CollatzResearch.WordTrace tailWord_51690 prefixEnd_51690 7864241490669035951789 := by
  unfold tailWord_51690
  simp only [CollatzResearch.WordTrace]
  refine ⟨471322295685858198570131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1256859455162288529520349 471322295685858198570131)
  ·
    refine ⟨706983443528787297855197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 471322295685858198570131 706983443528787297855197)
    ·
      refine ⟨265118791323295236695699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 706983443528787297855197 265118791323295236695699)
      ·
        refine ⟨397678186984942855043549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265118791323295236695699 397678186984942855043549)
        ·
          refine ⟨149129320119353570641331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397678186984942855043549 149129320119353570641331)
          ·
            refine ⟨223693980179030355961997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149129320119353570641331 223693980179030355961997)
            ·
              refine ⟨83885242567136383485749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223693980179030355961997 83885242567136383485749)
              ·
                refine ⟨7864241490669035951789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83885242567136383485749 7864241490669035951789)
                ·
                  rfl

theorem cell20_51690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_51690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51690 prefixEnd_51690 := by exact prefixLift 51690
  have htrace : WordTrace (prefixWord ++ tailWord_51690) baseStart_51690 baseEnd_51690 := by
    simpa [prefixWord, tailWord_51690, baseEnd_51690] using wordTrace_append hprefix tailTrace_51690
  have hstable : (prefixWord ++ tailWord_51690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51690).length < 2 ^ (prefixWord ++ tailWord_51690).sum := by decide
  have hdescent : baseEnd_51690 < baseStart_51690 := by decide
  rcases family_descends (prefixWord ++ tailWord_51690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51697 : List Nat := [1, 2, 2, 2, 3, 1, 1, 5, 3]
def baseStart_51697 : Nat := 118140960795 + 51697 * 2 ^ 59
def prefixEnd_51697 : Nat := 4983230072969 + 3 ^ 40 * 51697 * 2
def baseEnd_51697 : Nat := 23595919462746194622005

theorem tailTrace_51697 : CollatzResearch.WordTrace tailWord_51697 prefixEnd_51697 23595919462746194622005 := by
  unfold tailWord_51697
  simp only [CollatzResearch.WordTrace]
  refine ⟨1885544493718072989785345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1257029662478715326523563 1885544493718072989785345)
  ·
    refine ⟨1414158370288554742339009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1885544493718072989785345 1414158370288554742339009)
    ·
      refine ⟨1060618777716416056754257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1414158370288554742339009 1060618777716416056754257)
      ·
        refine ⟨795464083287312042565693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1060618777716416056754257 795464083287312042565693)
        ·
          refine ⟨298299031232742015962135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 795464083287312042565693 298299031232742015962135)
          ·
            refine ⟨447448546849113023943203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298299031232742015962135 447448546849113023943203)
            ·
              refine ⟨671172820273669535914805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447448546849113023943203 671172820273669535914805)
              ·
                refine ⟨62922451900656518992013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 671172820273669535914805 62922451900656518992013)
                ·
                  refine ⟨23595919462746194622005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62922451900656518992013 23595919462746194622005)
                  ·
                    rfl

theorem cell20_51697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_51697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51697 prefixEnd_51697 := by exact prefixLift 51697
  have htrace : WordTrace (prefixWord ++ tailWord_51697) baseStart_51697 baseEnd_51697 := by
    simpa [prefixWord, tailWord_51697, baseEnd_51697] using wordTrace_append hprefix tailTrace_51697
  have hstable : (prefixWord ++ tailWord_51697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51697).length < 2 ^ (prefixWord ++ tailWord_51697).sum := by decide
  have hdescent : baseEnd_51697 < baseStart_51697 := by decide
  rcases family_descends (prefixWord ++ tailWord_51697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51704 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_51704 : Nat := 118140960795 + 51704 * 2 ^ 59
def prefixEnd_51704 : Nat := 4983230072969 + 3 ^ 40 * 51704 * 2
def baseEnd_51704 : Nat := 23599114453485281388643

theorem tailTrace_51704 : CollatzResearch.WordTrace tailWord_51704 prefixEnd_51704 23599114453485281388643 := by
  unfold tailWord_51704
  simp only [CollatzResearch.WordTrace]
  refine ⟨942899902346356592645083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1257199869795142123526777 942899902346356592645083)
  ·
    refine ⟨1414349853519534888967625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 942899902346356592645083 1414349853519534888967625)
    ·
      refine ⟨1060762390139651166725719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1414349853519534888967625 1060762390139651166725719)
      ·
        refine ⟨1591143585209476750088579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1060762390139651166725719 1591143585209476750088579)
        ·
          refine ⟨2386715377814215125132869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591143585209476750088579 2386715377814215125132869)
          ·
            refine ⟨447509133340165335962413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2386715377814215125132869 447509133340165335962413)
            ·
              refine ⟨167815925002562000985905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 447509133340165335962413 167815925002562000985905)
              ·
                refine ⟨125861943751921500739429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167815925002562000985905 125861943751921500739429)
                ·
                  refine ⟨23599114453485281388643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125861943751921500739429 23599114453485281388643)
                  ·
                    rfl

theorem cell20_51704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_51704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51704 prefixEnd_51704 := by exact prefixLift 51704
  have htrace : WordTrace (prefixWord ++ tailWord_51704) baseStart_51704 baseEnd_51704 := by
    simpa [prefixWord, tailWord_51704, baseEnd_51704] using wordTrace_append hprefix tailTrace_51704
  have hstable : (prefixWord ++ tailWord_51704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51704).length < 2 ^ (prefixWord ++ tailWord_51704).sum := by decide
  have hdescent : baseEnd_51704 < baseStart_51704 := by decide
  rcases family_descends (prefixWord ++ tailWord_51704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51748 : List Nat := [2, 3, 1, 5, 1, 1, 3, 1, 3]
def baseStart_51748 : Nat := 118140960795 + 51748 * 2 ^ 59
def prefixEnd_51748 : Nat := 4983230072969 + 3 ^ 40 * 51748 * 2
def baseEnd_51748 : Nat := 23619197252416683921797

theorem tailTrace_51748 : CollatzResearch.WordTrace tailWord_51748 prefixEnd_51748 23619197252416683921797 := by
  unfold tailWord_51748
  simp only [CollatzResearch.WordTrace]
  refine ⟨943702308266654349945949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1258269744355539133261265 943702308266654349945949)
  ·
    refine ⟨353888365599995381229731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 943702308266654349945949 353888365599995381229731)
    ·
      refine ⟨530832548399993071844597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353888365599995381229731 530832548399993071844597)
      ·
        refine ⟨49765551412499350485431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 530832548399993071844597 49765551412499350485431)
        ·
          refine ⟨74648327118749025728147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49765551412499350485431 74648327118749025728147)
          ·
            refine ⟨111972490678123538592221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74648327118749025728147 111972490678123538592221)
            ·
              refine ⟨41989684004296326972083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111972490678123538592221 41989684004296326972083)
              ·
                refine ⟨62984526006444490458125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41989684004296326972083 62984526006444490458125)
                ·
                  refine ⟨23619197252416683921797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62984526006444490458125 23619197252416683921797)
                  ·
                    rfl

theorem cell20_51748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_51748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51748 prefixEnd_51748 := by exact prefixLift 51748
  have htrace : WordTrace (prefixWord ++ tailWord_51748) baseStart_51748 baseEnd_51748 := by
    simpa [prefixWord, tailWord_51748, baseEnd_51748] using wordTrace_append hprefix tailTrace_51748
  have hstable : (prefixWord ++ tailWord_51748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51748).length < 2 ^ (prefixWord ++ tailWord_51748).sum := by decide
  have hdescent : baseEnd_51748 < baseStart_51748 := by decide
  rcases family_descends (prefixWord ++ tailWord_51748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51773 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 5]
def baseStart_51773 : Nat := 118140960795 + 51773 * 2 ^ 59
def prefixEnd_51773 : Nat := 4983230072969 + 3 ^ 40 * 51773 * 2
def baseEnd_51773 : Nat := 23630607933627708088361

theorem tailTrace_51773 : CollatzResearch.WordTrace tailWord_51773 prefixEnd_51773 23630607933627708088361 := by
  unfold tailWord_51773
  simp only [CollatzResearch.WordTrace]
  refine ⟨1888316441442737969551973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1258877627628491979701315 1888316441442737969551973)
  ·
    refine ⟨354059332770513369290995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1888316441442737969551973 354059332770513369290995)
    ·
      refine ⟨531088999155770053936493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354059332770513369290995 531088999155770053936493)
      ·
        refine ⟨199158374683413770226185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 531088999155770053936493 199158374683413770226185)
        ·
          refine ⟨149368781012560327669639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199158374683413770226185 149368781012560327669639)
          ·
            refine ⟨224053171518840491504459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149368781012560327669639 224053171518840491504459)
            ·
              refine ⟨336079757278260737256689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224053171518840491504459 336079757278260737256689)
              ·
                refine ⟨252059817958695552942517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336079757278260737256689 252059817958695552942517)
                ·
                  refine ⟨23630607933627708088361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252059817958695552942517 23630607933627708088361)
                  ·
                    rfl

theorem cell20_51773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_51773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51773 prefixEnd_51773 := by exact prefixLift 51773
  have htrace : WordTrace (prefixWord ++ tailWord_51773) baseStart_51773 baseEnd_51773 := by
    simpa [prefixWord, tailWord_51773, baseEnd_51773] using wordTrace_append hprefix tailTrace_51773
  have hstable : (prefixWord ++ tailWord_51773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51773).length < 2 ^ (prefixWord ++ tailWord_51773).sum := by decide
  have hdescent : baseEnd_51773 < baseStart_51773 := by decide
  rcases family_descends (prefixWord ++ tailWord_51773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51797 : List Nat := [1, 3, 2, 2, 1, 1, 2, 6, 2]
def baseStart_51797 : Nat := 118140960795 + 51797 * 2 ^ 59
def prefixEnd_51797 : Nat := 4983230072969 + 3 ^ 40 * 51797 * 2
def baseEnd_51797 : Nat := 23641562187590291288263

theorem tailTrace_51797 : CollatzResearch.WordTrace tailWord_51797 prefixEnd_51797 23641562187590291288263 := by
  unfold tailWord_51797
  simp only [CollatzResearch.WordTrace]
  refine ⟨1889191793355790068425645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1259461195570526712283763 1889191793355790068425645)
  ·
    refine ⟨708446922508421275659617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1889191793355790068425645 708446922508421275659617)
    ·
      refine ⟨531335191881315956744713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 708446922508421275659617 531335191881315956744713)
      ·
        refine ⟨398501393910986967558535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531335191881315956744713 398501393910986967558535)
        ·
          refine ⟨597752090866480451337803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398501393910986967558535 597752090866480451337803)
          ·
            refine ⟨896628136299720677006705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597752090866480451337803 896628136299720677006705)
            ·
              refine ⟨672471102224790507755029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896628136299720677006705 672471102224790507755029)
              ·
                refine ⟨31522082916787055051017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 672471102224790507755029 31522082916787055051017)
                ·
                  refine ⟨23641562187590291288263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31522082916787055051017 23641562187590291288263)
                  ·
                    rfl

theorem cell20_51797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_51797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51797 prefixEnd_51797 := by exact prefixLift 51797
  have htrace : WordTrace (prefixWord ++ tailWord_51797) baseStart_51797 baseEnd_51797 := by
    simpa [prefixWord, tailWord_51797, baseEnd_51797] using wordTrace_append hprefix tailTrace_51797
  have hstable : (prefixWord ++ tailWord_51797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51797).length < 2 ^ (prefixWord ++ tailWord_51797).sum := by decide
  have hdescent : baseEnd_51797 < baseStart_51797 := by decide
  rcases family_descends (prefixWord ++ tailWord_51797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51811 : List Nat := [1, 1, 1, 5, 1, 2, 3, 3, 3]
def baseStart_51811 : Nat := 118140960795 + 51811 * 2 ^ 59
def prefixEnd_51811 : Nat := 4983230072969 + 3 ^ 40 * 51811 * 2
def baseEnd_51811 : Nat := 23647952169068464821539

theorem tailTrace_51811 : CollatzResearch.WordTrace tailWord_51811 prefixEnd_51811 23647952169068464821539 := by
  unfold tailWord_51811
  simp only [CollatzResearch.WordTrace]
  refine ⟨1889702415305070459435287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1259801610203380306290191 1889702415305070459435287)
  ·
    refine ⟨2834553622957605689152931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1889702415305070459435287 2834553622957605689152931)
    ·
      refine ⟨4251830434436408533729397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2834553622957605689152931 4251830434436408533729397)
      ·
        refine ⟨398609103228413300037131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4251830434436408533729397 398609103228413300037131)
        ·
          refine ⟨597913654842619950055697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398609103228413300037131 597913654842619950055697)
          ·
            refine ⟨448435241131964962541773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597913654842619950055697 448435241131964962541773)
            ·
              refine ⟨168163215424486860953165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 448435241131964962541773 168163215424486860953165)
              ·
                refine ⟨63061205784182572857437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168163215424486860953165 63061205784182572857437)
                ·
                  refine ⟨23647952169068464821539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63061205784182572857437 23647952169068464821539)
                  ·
                    rfl

theorem cell20_51811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 3].length) (baseStart_51811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51811 prefixEnd_51811 := by exact prefixLift 51811
  have htrace : WordTrace (prefixWord ++ tailWord_51811) baseStart_51811 baseEnd_51811 := by
    simpa [prefixWord, tailWord_51811, baseEnd_51811] using wordTrace_append hprefix tailTrace_51811
  have hstable : (prefixWord ++ tailWord_51811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51811).length < 2 ^ (prefixWord ++ tailWord_51811).sum := by decide
  have hdescent : baseEnd_51811 < baseStart_51811 := by decide
  rcases family_descends (prefixWord ++ tailWord_51811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51818 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_51818 : Nat := 118140960795 + 51818 * 2 ^ 59
def prefixEnd_51818 : Nat := 4983230072969 + 3 ^ 40 * 51818 * 2
def baseEnd_51818 : Nat := 23651147159807551588177

theorem tailTrace_51818 : CollatzResearch.WordTrace tailWord_51818 prefixEnd_51818 23651147159807551588177 := by
  unfold tailWord_51818
  simp only [CollatzResearch.WordTrace]
  refine ⟨472489431569927663735027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1259971817519807103293405 472489431569927663735027)
  ·
    refine ⟨708734147354891495602541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 472489431569927663735027 708734147354891495602541)
    ·
      refine ⟨265775305258084310850953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 708734147354891495602541 265775305258084310850953)
      ·
        refine ⟨199331478943563233138215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265775305258084310850953 199331478943563233138215)
        ·
          refine ⟨298997218415344849707323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199331478943563233138215 298997218415344849707323)
          ·
            refine ⟨448495827623017274560985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298997218415344849707323 448495827623017274560985)
            ·
              refine ⟨336371870717262955920739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448495827623017274560985 336371870717262955920739)
              ·
                refine ⟨504557806075894433881109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336371870717262955920739 504557806075894433881109)
                ·
                  refine ⟨23651147159807551588177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 504557806075894433881109 23651147159807551588177)
                  ·
                    rfl

theorem cell20_51818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_51818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51818 prefixEnd_51818 := by exact prefixLift 51818
  have htrace : WordTrace (prefixWord ++ tailWord_51818) baseStart_51818 baseEnd_51818 := by
    simpa [prefixWord, tailWord_51818, baseEnd_51818] using wordTrace_append hprefix tailTrace_51818
  have hstable : (prefixWord ++ tailWord_51818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51818).length < 2 ^ (prefixWord ++ tailWord_51818).sum := by decide
  have hdescent : baseEnd_51818 < baseStart_51818 := by decide
  rcases family_descends (prefixWord ++ tailWord_51818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51839 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 8]
def baseStart_51839 : Nat := 118140960795 + 51839 * 2 ^ 59
def prefixEnd_51839 : Nat := 4983230072969 + 3 ^ 40 * 51839 * 2
def baseEnd_51839 : Nat := 23660732132024811888091

theorem tailTrace_51839 : CollatzResearch.WordTrace tailWord_51839 prefixEnd_51839 23660732132024811888091 := by
  unfold tailWord_51839
  simp only [CollatzResearch.WordTrace]
  refine ⟨1890723659203631241454571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1260482439469087494303047 1890723659203631241454571)
  ·
    refine ⟨2836085488805446862181857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1890723659203631241454571 2836085488805446862181857)
    ·
      refine ⟨2127064116604085146636393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2836085488805446862181857 2127064116604085146636393)
      ·
        refine ⟨1595298087453063859977295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2127064116604085146636393 1595298087453063859977295)
        ·
          refine ⟨2392947131179595789965943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1595298087453063859977295 2392947131179595789965943)
          ·
            refine ⟨3589420696769393684948915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392947131179595789965943 3589420696769393684948915)
            ·
              refine ⟨5384131045154090527423373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3589420696769393684948915 5384131045154090527423373)
              ·
                refine ⟨2019049141932783947783765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5384131045154090527423373 2019049141932783947783765)
                ·
                  refine ⟨23660732132024811888091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2019049141932783947783765 23660732132024811888091)
                  ·
                    rfl

theorem cell20_51839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_51839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51839 prefixEnd_51839 := by exact prefixLift 51839
  have htrace : WordTrace (prefixWord ++ tailWord_51839) baseStart_51839 baseEnd_51839 := by
    simpa [prefixWord, tailWord_51839, baseEnd_51839] using wordTrace_append hprefix tailTrace_51839
  have hstable : (prefixWord ++ tailWord_51839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51839).length < 2 ^ (prefixWord ++ tailWord_51839).sum := by decide
  have hdescent : baseEnd_51839 < baseStart_51839 := by decide
  rcases family_descends (prefixWord ++ tailWord_51839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51873 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 4]
def baseStart_51873 : Nat := 118140960795 + 51873 * 2 ^ 59
def prefixEnd_51873 : Nat := 4983230072969 + 3 ^ 40 * 51873 * 2
def baseEnd_51873 : Nat := 23676250658471804754619

theorem tailTrace_51873 : CollatzResearch.WordTrace tailWord_51873 prefixEnd_51873 23676250658471804754619 := by
  unfold tailWord_51873
  simp only [CollatzResearch.WordTrace]
  refine ⟨1891963741080455048192273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1261309160720303365461515 1891963741080455048192273)
  ·
    refine ⟨1418972805810341286144205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1891963741080455048192273 1418972805810341286144205)
    ·
      refine ⟨532114802178877982304077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1418972805810341286144205 532114802178877982304077)
      ·
        refine ⟨199543050817079243364029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 532114802178877982304077 199543050817079243364029)
        ·
          refine ⟨74828644056404716261511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199543050817079243364029 74828644056404716261511)
          ·
            refine ⟨112242966084607074392267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74828644056404716261511 112242966084607074392267)
            ·
              refine ⟨168364449126910611588401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112242966084607074392267 168364449126910611588401)
              ·
                refine ⟨126273336845182958691301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168364449126910611588401 126273336845182958691301)
                ·
                  refine ⟨23676250658471804754619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126273336845182958691301 23676250658471804754619)
                  ·
                    rfl

theorem cell20_51873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_51873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51873 prefixEnd_51873 := by exact prefixLift 51873
  have htrace : WordTrace (prefixWord ++ tailWord_51873) baseStart_51873 baseEnd_51873 := by
    simpa [prefixWord, tailWord_51873, baseEnd_51873] using wordTrace_append hprefix tailTrace_51873
  have hstable : (prefixWord ++ tailWord_51873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51873).length < 2 ^ (prefixWord ++ tailWord_51873).sum := by decide
  have hdescent : baseEnd_51873 < baseStart_51873 := by decide
  rcases family_descends (prefixWord ++ tailWord_51873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51901 : List Nat := [1, 4, 1, 2, 1, 4, 7]
def baseStart_51901 : Nat := 118140960795 + 51901 * 2 ^ 59
def prefixEnd_51901 : Nat := 4983230072969 + 3 ^ 40 * 51901 * 2
def baseEnd_51901 : Nat := 2632114513492016869019

theorem tailTrace_51901 : CollatzResearch.WordTrace tailWord_51901 prefixEnd_51901 2632114513492016869019 := by
  unfold tailWord_51901
  simp only [CollatzResearch.WordTrace]
  refine ⟨1892984984979015830211557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1261989989986010553474371 1892984984979015830211557)
  ·
    refine ⟨354934684683565468164667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1892984984979015830211557 354934684683565468164667)
    ·
      refine ⟨532402027025348202247001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354934684683565468164667 532402027025348202247001)
      ·
        refine ⟨399301520269011151685251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532402027025348202247001 399301520269011151685251)
        ·
          refine ⟨598952280403516727527877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399301520269011151685251 598952280403516727527877)
          ·
            refine ⟨112303552575659386411477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 598952280403516727527877 112303552575659386411477)
            ·
              refine ⟨2632114513492016869019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 112303552575659386411477 2632114513492016869019)
              ·
                rfl

theorem cell20_51901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 7].length) (baseStart_51901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51901 prefixEnd_51901 := by exact prefixLift 51901
  have htrace : WordTrace (prefixWord ++ tailWord_51901) baseStart_51901 baseEnd_51901 := by
    simpa [prefixWord, tailWord_51901, baseEnd_51901] using wordTrace_append hprefix tailTrace_51901
  have hstable : (prefixWord ++ tailWord_51901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51901).length < 2 ^ (prefixWord ++ tailWord_51901).sum := by decide
  have hdescent : baseEnd_51901 < baseStart_51901 := by decide
  rcases family_descends (prefixWord ++ tailWord_51901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51904 : List Nat := [2, 1, 1, 2, 4, 4, 1, 2, 3]
def baseStart_51904 : Nat := 118140960795 + 51904 * 2 ^ 59
def prefixEnd_51904 : Nat := 4983230072969 + 3 ^ 40 * 51904 * 2
def baseEnd_51904 : Nat := 23690399903173474721159

theorem tailTrace_51904 : CollatzResearch.WordTrace tailWord_51904 prefixEnd_51904 23690399903173474721159 := by
  unfold tailWord_51904
  simp only [CollatzResearch.WordTrace]
  refine ⟨946547201984073671285383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1262062935978764895047177 946547201984073671285383)
  ·
    refine ⟨1419820802976110506928075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 946547201984073671285383 1419820802976110506928075)
    ·
      refine ⟨2129731204464165760392113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1419820802976110506928075 2129731204464165760392113)
      ·
        refine ⟨1597298403348124320294085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2129731204464165760392113 1597298403348124320294085)
        ·
          refine ⟨299493450627773310055141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1597298403348124320294085 299493450627773310055141)
          ·
            refine ⟨56155021992707495635339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299493450627773310055141 56155021992707495635339)
            ·
              refine ⟨84232532989061243453009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56155021992707495635339 84232532989061243453009)
              ·
                refine ⟨63174399741795932589757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84232532989061243453009 63174399741795932589757)
                ·
                  refine ⟨23690399903173474721159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63174399741795932589757 23690399903173474721159)
                  ·
                    rfl

theorem cell20_51904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_51904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51904 prefixEnd_51904 := by exact prefixLift 51904
  have htrace : WordTrace (prefixWord ++ tailWord_51904) baseStart_51904 baseEnd_51904 := by
    simpa [prefixWord, tailWord_51904, baseEnd_51904] using wordTrace_append hprefix tailTrace_51904
  have hstable : (prefixWord ++ tailWord_51904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51904).length < 2 ^ (prefixWord ++ tailWord_51904).sum := by decide
  have hdescent : baseEnd_51904 < baseStart_51904 := by decide
  rcases family_descends (prefixWord ++ tailWord_51904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_51966 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_51966 : Nat := 118140960795 + 51966 * 2 ^ 59
def prefixEnd_51966 : Nat := 4983230072969 + 3 ^ 40 * 51966 * 2
def baseEnd_51966 : Nat := 23718698392576814654239

theorem tailTrace_51966 : CollatzResearch.WordTrace tailWord_51966 prefixEnd_51966 23718698392576814654239 := by
  unfold tailWord_51966
  simp only [CollatzResearch.WordTrace]
  refine ⟨236919466217941491415969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1263570486495687954218501 236919466217941491415969)
  ·
    refine ⟨177689599663456118561977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236919466217941491415969 177689599663456118561977)
    ·
      refine ⟨133267199747592088921483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177689599663456118561977 133267199747592088921483)
      ·
        refine ⟨199900799621388133382225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133267199747592088921483 199900799621388133382225)
        ·
          refine ⟨149925599716041100036669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199900799621388133382225 149925599716041100036669)
          ·
            refine ⟨56222099893515412513751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149925599716041100036669 56222099893515412513751)
            ·
              refine ⟨84333149840273118770627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56222099893515412513751 84333149840273118770627)
              ·
                refine ⟨126499724760409678155941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84333149840273118770627 126499724760409678155941)
                ·
                  refine ⟨23718698392576814654239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126499724760409678155941 23718698392576814654239)
                  ·
                    rfl

theorem cell20_51966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_51966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_51966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_51966 prefixEnd_51966 := by exact prefixLift 51966
  have htrace : WordTrace (prefixWord ++ tailWord_51966) baseStart_51966 baseEnd_51966 := by
    simpa [prefixWord, tailWord_51966, baseEnd_51966] using wordTrace_append hprefix tailTrace_51966
  have hstable : (prefixWord ++ tailWord_51966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_51966).length < 2 ^ (prefixWord ++ tailWord_51966).sum := by decide
  have hdescent : baseEnd_51966 < baseStart_51966 := by decide
  rcases family_descends (prefixWord ++ tailWord_51966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52021 : List Nat := [1, 3, 3, 1, 3, 3, 2, 2, 2]
def baseStart_52021 : Nat := 118140960795 + 52021 * 2 ^ 59
def prefixEnd_52021 : Nat := 4983230072969 + 3 ^ 40 * 52021 * 2
def baseEnd_52021 : Nat := 23743801891241067820681

theorem tailTrace_52021 : CollatzResearch.WordTrace tailWord_52021 prefixEnd_52021 23743801891241067820681 := by
  unfold tailWord_52021
  simp only [CollatzResearch.WordTrace]
  refine ⟨1897361744544276324579917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1264907829696184216386611 1897361744544276324579917)
  ·
    refine ⟨711510654204103621717469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1897361744544276324579917 711510654204103621717469)
    ·
      refine ⟨266816495326538858144051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 711510654204103621717469 266816495326538858144051)
      ·
        refine ⟨400224742989808287216077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266816495326538858144051 400224742989808287216077)
        ·
          refine ⟨150084278621178107706029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400224742989808287216077 150084278621178107706029)
          ·
            refine ⟨56281604482941790389761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150084278621178107706029 56281604482941790389761)
            ·
              refine ⟨42211203362206342792321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56281604482941790389761 42211203362206342792321)
              ·
                refine ⟨31658402521654757094241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42211203362206342792321 31658402521654757094241)
                ·
                  refine ⟨23743801891241067820681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31658402521654757094241 23743801891241067820681)
                  ·
                    rfl

theorem cell20_52021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_52021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52021 prefixEnd_52021 := by exact prefixLift 52021
  have htrace : WordTrace (prefixWord ++ tailWord_52021) baseStart_52021 baseEnd_52021 := by
    simpa [prefixWord, tailWord_52021, baseEnd_52021] using wordTrace_append hprefix tailTrace_52021
  have hstable : (prefixWord ++ tailWord_52021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52021).length < 2 ^ (prefixWord ++ tailWord_52021).sum := by decide
  have hdescent : baseEnd_52021 < baseStart_52021 := by decide
  rcases family_descends (prefixWord ++ tailWord_52021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52063 : List Nat := [1, 1, 2, 3, 1, 3, 4, 3, 2]
def baseStart_52063 : Nat := 118140960795 + 52063 * 2 ^ 59
def prefixEnd_52063 : Nat := 4983230072969 + 3 ^ 40 * 52063 * 2
def baseEnd_52063 : Nat := 23762971835675588420509

theorem tailTrace_52063 : CollatzResearch.WordTrace tailWord_52063 prefixEnd_52063 23762971835675588420509 := by
  unfold tailWord_52063
  simp only [CollatzResearch.WordTrace]
  refine ⟨1898893610392117497608843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1265929073594744998405895 1898893610392117497608843)
  ·
    refine ⟨2848340415588176246413265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1898893610392117497608843 2848340415588176246413265)
    ·
      refine ⟨2136255311691132184809949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2848340415588176246413265 2136255311691132184809949)
      ·
        refine ⟨801095741884174569303731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2136255311691132184809949 801095741884174569303731)
        ·
          refine ⟨1201643612826261853955597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801095741884174569303731 1201643612826261853955597)
          ·
            refine ⟨450616354809848195233349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1201643612826261853955597 450616354809848195233349)
            ·
              refine ⟨84490566526846536606253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 450616354809848195233349 84490566526846536606253)
              ·
                refine ⟨31683962447567451227345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84490566526846536606253 31683962447567451227345)
                ·
                  refine ⟨23762971835675588420509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31683962447567451227345 23762971835675588420509)
                  ·
                    rfl

theorem cell20_52063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 2].length) (baseStart_52063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52063 prefixEnd_52063 := by exact prefixLift 52063
  have htrace : WordTrace (prefixWord ++ tailWord_52063) baseStart_52063 baseEnd_52063 := by
    simpa [prefixWord, tailWord_52063, baseEnd_52063] using wordTrace_append hprefix tailTrace_52063
  have hstable : (prefixWord ++ tailWord_52063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52063).length < 2 ^ (prefixWord ++ tailWord_52063).sum := by decide
  have hdescent : baseEnd_52063 < baseStart_52063 := by decide
  rcases family_descends (prefixWord ++ tailWord_52063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52114 : List Nat := [3, 2, 3, 2, 3, 1, 1, 3, 2]
def baseStart_52114 : Nat := 118140960795 + 52114 * 2 ^ 59
def prefixEnd_52114 : Nat := 4983230072969 + 3 ^ 40 * 52114 * 2
def baseEnd_52114 : Nat := 23786249625346077720301

theorem tailTrace_52114 : CollatzResearch.WordTrace tailWord_52114 prefixEnd_52114 23786249625346077720301 := by
  unfold tailWord_52114
  simp only [CollatzResearch.WordTrace]
  refine ⟨475188433301838301928849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1267169155471568805143597 475188433301838301928849)
  ·
    refine ⟨356391324976378726446637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 475188433301838301928849 356391324976378726446637)
    ·
      refine ⟨133646746866142022417489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356391324976378726446637 133646746866142022417489)
      ·
        refine ⟨100235060149606516813117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133646746866142022417489 100235060149606516813117)
        ·
          refine ⟨37588147556102443804919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100235060149606516813117 37588147556102443804919)
          ·
            refine ⟨56382221334153665707379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37588147556102443804919 56382221334153665707379)
            ·
              refine ⟨84573332001230498561069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56382221334153665707379 84573332001230498561069)
              ·
                refine ⟨31714999500461436960401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84573332001230498561069 31714999500461436960401)
                ·
                  refine ⟨23786249625346077720301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31714999500461436960401 23786249625346077720301)
                  ·
                    rfl

theorem cell20_52114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_52114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52114 prefixEnd_52114 := by exact prefixLift 52114
  have htrace : WordTrace (prefixWord ++ tailWord_52114) baseStart_52114 baseEnd_52114 := by
    simpa [prefixWord, tailWord_52114, baseEnd_52114] using wordTrace_append hprefix tailTrace_52114
  have hstable : (prefixWord ++ tailWord_52114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52114).length < 2 ^ (prefixWord ++ tailWord_52114).sum := by decide
  have hdescent : baseEnd_52114 < baseStart_52114 := by decide
  rcases family_descends (prefixWord ++ tailWord_52114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52129 : List Nat := [1, 2, 3, 4, 1, 1, 8]
def baseStart_52129 : Nat := 118140960795 + 52129 * 2 ^ 59
def prefixEnd_52129 : Nat := 4983230072969 + 3 ^ 40 * 52129 * 2
def baseEnd_52129 : Nat := 2643677337119188024471

theorem tailTrace_52129 : CollatzResearch.WordTrace tailWord_52129 prefixEnd_52129 2643677337119188024471 := by
  unfold tailWord_52129
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901300828153010769511441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1267533885435340513007627 1901300828153010769511441)
  ·
    refine ⟨1425975621114758077133581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1901300828153010769511441 1425975621114758077133581)
    ·
      refine ⟨534740857918034278925093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1425975621114758077133581 534740857918034278925093)
      ·
        refine ⟨100263910859631427298455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 534740857918034278925093 100263910859631427298455)
        ·
          refine ⟨150395866289447140947683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100263910859631427298455 150395866289447140947683)
          ·
            refine ⟨225593799434170711421525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150395866289447140947683 225593799434170711421525)
            ·
              refine ⟨2643677337119188024471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 225593799434170711421525 2643677337119188024471)
              ·
                rfl

theorem cell20_52129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 8].length) (baseStart_52129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52129 prefixEnd_52129 := by exact prefixLift 52129
  have htrace : WordTrace (prefixWord ++ tailWord_52129) baseStart_52129 baseEnd_52129 := by
    simpa [prefixWord, tailWord_52129, baseEnd_52129] using wordTrace_append hprefix tailTrace_52129
  have hstable : (prefixWord ++ tailWord_52129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52129).length < 2 ^ (prefixWord ++ tailWord_52129).sum := by decide
  have hdescent : baseEnd_52129 < baseStart_52129 := by decide
  rcases family_descends (prefixWord ++ tailWord_52129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52135 : List Nat := [1, 1, 6, 1, 3, 1, 3, 2, 2]
def baseStart_52135 : Nat := 118140960795 + 52135 * 2 ^ 59
def prefixEnd_52135 : Nat := 4983230072969 + 3 ^ 40 * 52135 * 2
def baseEnd_52135 : Nat := 23795834597563338020215

theorem tailTrace_52135 : CollatzResearch.WordTrace tailWord_52135 prefixEnd_52135 23795834597563338020215 := by
  unfold tailWord_52135
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901519666131273794229859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1267679777420849196153239 1901519666131273794229859)
  ·
    refine ⟨2852279499196910691344789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1901519666131273794229859 2852279499196910691344789)
    ·
      refine ⟨133700601524855188656787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2852279499196910691344789 133700601524855188656787)
      ·
        refine ⟨200550902287282782985181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133700601524855188656787 200550902287282782985181)
        ·
          refine ⟨75206588357731043619443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200550902287282782985181 75206588357731043619443)
          ·
            refine ⟨112809882536596565429165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75206588357731043619443 112809882536596565429165)
            ·
              refine ⟨42303705951223712035937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112809882536596565429165 42303705951223712035937)
              ·
                refine ⟨31727779463417784026953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42303705951223712035937 31727779463417784026953)
                ·
                  refine ⟨23795834597563338020215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31727779463417784026953 23795834597563338020215)
                  ·
                    rfl

theorem cell20_52135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 2].length) (baseStart_52135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52135 prefixEnd_52135 := by exact prefixLift 52135
  have htrace : WordTrace (prefixWord ++ tailWord_52135) baseStart_52135 baseEnd_52135 := by
    simpa [prefixWord, tailWord_52135, baseEnd_52135] using wordTrace_append hprefix tailTrace_52135
  have hstable : (prefixWord ++ tailWord_52135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52135).length < 2 ^ (prefixWord ++ tailWord_52135).sum := by decide
  have hdescent : baseEnd_52135 < baseStart_52135 := by decide
  rcases family_descends (prefixWord ++ tailWord_52135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52143 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 4]
def baseStart_52143 : Nat := 118140960795 + 52143 * 2 ^ 59
def prefixEnd_52143 : Nat := 4983230072969 + 3 ^ 40 * 52143 * 2
def baseEnd_52143 : Nat := 23799486015550865753515

theorem tailTrace_52143 : CollatzResearch.WordTrace tailWord_52143 prefixEnd_52143 23799486015550865753515 := by
  unfold tailWord_52143
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901811450102291160521083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1267874300068194107014055 1901811450102291160521083)
  ·
    refine ⟨2852717175153436740781625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1901811450102291160521083 2852717175153436740781625)
    ·
      refine ⟨2139537881365077555586219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2852717175153436740781625 2139537881365077555586219)
      ·
        refine ⟨3209306822047616333379329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139537881365077555586219 3209306822047616333379329)
        ·
          refine ⟨2406980116535712250034497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3209306822047616333379329 2406980116535712250034497)
          ·
            refine ⟨1805235087401784187525873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2406980116535712250034497 1805235087401784187525873)
            ·
              refine ⟨1353926315551338140644405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1805235087401784187525873 1353926315551338140644405)
              ·
                refine ⟨126930592082937950685413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1353926315551338140644405 126930592082937950685413)
                ·
                  refine ⟨23799486015550865753515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126930592082937950685413 23799486015550865753515)
                  ·
                    rfl

theorem cell20_52143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_52143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52143 prefixEnd_52143 := by exact prefixLift 52143
  have htrace : WordTrace (prefixWord ++ tailWord_52143) baseStart_52143 baseEnd_52143 := by
    simpa [prefixWord, tailWord_52143, baseEnd_52143] using wordTrace_append hprefix tailTrace_52143
  have hstable : (prefixWord ++ tailWord_52143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52143).length < 2 ^ (prefixWord ++ tailWord_52143).sum := by decide
  have hdescent : baseEnd_52143 < baseStart_52143 := by decide
  rcases family_descends (prefixWord ++ tailWord_52143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52153 : List Nat := [1, 2, 1, 4, 2, 3, 1, 3, 3]
def baseStart_52153 : Nat := 118140960795 + 52153 * 2 ^ 59
def prefixEnd_52153 : Nat := 4983230072969 + 3 ^ 40 * 52153 * 2
def baseEnd_52153 : Nat := 23804050288035275420141

theorem tailTrace_52153 : CollatzResearch.WordTrace tailWord_52153 prefixEnd_52153 23804050288035275420141 := by
  unfold tailWord_52153
  simp only [CollatzResearch.WordTrace]
  refine ⟨1902176180066062868385113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1268117453377375245590075 1902176180066062868385113)
  ·
    refine ⟨1426632135049547151288835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1902176180066062868385113 1426632135049547151288835)
    ·
      refine ⟨2139948202574320726933253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426632135049547151288835 2139948202574320726933253)
      ·
        refine ⟨401240287982685136299985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2139948202574320726933253 401240287982685136299985)
        ·
          refine ⟨300930215987013852224989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401240287982685136299985 300930215987013852224989)
          ·
            refine ⟨112848830995130194584371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300930215987013852224989 112848830995130194584371)
            ·
              refine ⟨169273246492695291876557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112848830995130194584371 169273246492695291876557)
              ·
                refine ⟨63477467434760734453709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169273246492695291876557 63477467434760734453709)
                ·
                  refine ⟨23804050288035275420141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63477467434760734453709 23804050288035275420141)
                  ·
                    rfl

theorem cell20_52153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_52153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52153 prefixEnd_52153 := by exact prefixLift 52153
  have htrace : WordTrace (prefixWord ++ tailWord_52153) baseStart_52153 baseEnd_52153 := by
    simpa [prefixWord, tailWord_52153, baseEnd_52153] using wordTrace_append hprefix tailTrace_52153
  have hstable : (prefixWord ++ tailWord_52153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52153).length < 2 ^ (prefixWord ++ tailWord_52153).sum := by decide
  have hdescent : baseEnd_52153 < baseStart_52153 := by decide
  rcases family_descends (prefixWord ++ tailWord_52153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52250 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_52250 : Nat := 118140960795 + 52250 * 2 ^ 59
def prefixEnd_52250 : Nat := 4983230072969 + 3 ^ 40 * 52250 * 2
def baseEnd_52250 : Nat := 23848323731134049186411

theorem tailTrace_52250 : CollatzResearch.WordTrace tailWord_52250 prefixEnd_52250 23848323731134049186411 := by
  unfold tailWord_52250
  simp only [CollatzResearch.WordTrace]
  refine ⟨476428515178662108666551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1270476040476432289777469 476428515178662108666551)
  ·
    refine ⟨714642772767993162999827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 476428515178662108666551 714642772767993162999827)
    ·
      refine ⟨1071964159151989744499741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 714642772767993162999827 1071964159151989744499741)
      ·
        refine ⟨401986559681996154187403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1071964159151989744499741 401986559681996154187403)
        ·
          refine ⟨602979839522994231281105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401986559681996154187403 602979839522994231281105)
          ·
            refine ⟨452234879642245673460829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602979839522994231281105 452234879642245673460829)
            ·
              refine ⟨169588079865842127547811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 452234879642245673460829 169588079865842127547811)
              ·
                refine ⟨254382119798763191321717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169588079865842127547811 254382119798763191321717)
                ·
                  refine ⟨23848323731134049186411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 254382119798763191321717 23848323731134049186411)
                  ·
                    rfl

theorem cell20_52250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_52250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52250 prefixEnd_52250 := by exact prefixLift 52250
  have htrace : WordTrace (prefixWord ++ tailWord_52250) baseStart_52250 baseEnd_52250 := by
    simpa [prefixWord, tailWord_52250, baseEnd_52250] using wordTrace_append hprefix tailTrace_52250
  have hstable : (prefixWord ++ tailWord_52250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52250).length < 2 ^ (prefixWord ++ tailWord_52250).sum := by decide
  have hdescent : baseEnd_52250 < baseStart_52250 := by decide
  rcases family_descends (prefixWord ++ tailWord_52250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52253 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 4]
def baseStart_52253 : Nat := 118140960795 + 52253 * 2 ^ 59
def prefixEnd_52253 : Nat := 4983230072969 + 3 ^ 40 * 52253 * 2
def baseEnd_52253 : Nat := 23849693012879372086399

theorem tailTrace_52253 : CollatzResearch.WordTrace tailWord_52253 prefixEnd_52253 23849693012879372086399 := by
  unfold tailWord_52253
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905823479703779947025413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1270548986469186631350275 1905823479703779947025413)
  ·
    refine ⟨357341902444458740067265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1905823479703779947025413 357341902444458740067265)
    ·
      refine ⟨268006426833344055050449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 357341902444458740067265 268006426833344055050449)
      ·
        refine ⟨201004820125008041287837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268006426833344055050449 201004820125008041287837)
        ·
          refine ⟨75376807546878015482939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201004820125008041287837 75376807546878015482939)
          ·
            refine ⟨113065211320317023224409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75376807546878015482939 113065211320317023224409)
            ·
              refine ⟨84798908490237767418307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113065211320317023224409 84798908490237767418307)
              ·
                refine ⟨127198362735356651127461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84798908490237767418307 127198362735356651127461)
                ·
                  refine ⟨23849693012879372086399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127198362735356651127461 23849693012879372086399)
                  ·
                    rfl

theorem cell20_52253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_52253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52253 prefixEnd_52253 := by exact prefixLift 52253
  have htrace : WordTrace (prefixWord ++ tailWord_52253) baseStart_52253 baseEnd_52253 := by
    simpa [prefixWord, tailWord_52253, baseEnd_52253] using wordTrace_append hprefix tailTrace_52253
  have hstable : (prefixWord ++ tailWord_52253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52253).length < 2 ^ (prefixWord ++ tailWord_52253).sum := by decide
  have hdescent : baseEnd_52253 < baseStart_52253 := by decide
  rcases family_descends (prefixWord ++ tailWord_52253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52263 : List Nat := [1, 1, 7, 1, 1, 2, 3, 1, 3]
def baseStart_52263 : Nat := 118140960795 + 52263 * 2 ^ 59
def prefixEnd_52263 : Nat := 4983230072969 + 3 ^ 40 * 52263 * 2
def baseEnd_52263 : Nat := 23854257285363781753025

theorem tailTrace_52263 : CollatzResearch.WordTrace tailWord_52263 prefixEnd_52263 23854257285363781753025 := by
  unfold tailWord_52263
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906188209667551654889443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1270792139778367769926295 1906188209667551654889443)
  ·
    refine ⟨2859282314501327482334165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1906188209667551654889443 2859282314501327482334165)
    ·
      refine ⟨67014429246124862867207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2859282314501327482334165 67014429246124862867207)
      ·
        refine ⟨100521643869187294300811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67014429246124862867207 100521643869187294300811)
        ·
          refine ⟨150782465803780941451217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100521643869187294300811 150782465803780941451217)
          ·
            refine ⟨113086849352835706088413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150782465803780941451217 113086849352835706088413)
            ·
              refine ⟨42407568507313389783155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113086849352835706088413 42407568507313389783155)
              ·
                refine ⟨63611352760970084674733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42407568507313389783155 63611352760970084674733)
                ·
                  refine ⟨23854257285363781753025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63611352760970084674733 23854257285363781753025)
                  ·
                    rfl

theorem cell20_52263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 3].length) (baseStart_52263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52263 prefixEnd_52263 := by exact prefixLift 52263
  have htrace : WordTrace (prefixWord ++ tailWord_52263) baseStart_52263 baseEnd_52263 := by
    simpa [prefixWord, tailWord_52263, baseEnd_52263] using wordTrace_append hprefix tailTrace_52263
  have hstable : (prefixWord ++ tailWord_52263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52263).length < 2 ^ (prefixWord ++ tailWord_52263).sum := by decide
  have hdescent : baseEnd_52263 < baseStart_52263 := by decide
  rcases family_descends (prefixWord ++ tailWord_52263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52267 : List Nat := [1, 1, 1, 1, 2, 1, 9, 1, 3]
def baseStart_52267 : Nat := 118140960795 + 52267 * 2 ^ 59
def prefixEnd_52267 : Nat := 4983230072969 + 3 ^ 40 * 52267 * 2
def baseEnd_52267 : Nat := 23856082994357545619675

theorem tailTrace_52267 : CollatzResearch.WordTrace tailWord_52267 prefixEnd_52267 23856082994357545619675 := by
  unfold tailWord_52267
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906334101653060338035055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1270889401102040225356703 1906334101653060338035055)
  ·
    refine ⟨2859501152479590507052583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1906334101653060338035055 2859501152479590507052583)
    ·
      refine ⟨4289251728719385760578875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2859501152479590507052583 4289251728719385760578875)
      ·
        refine ⟨6433877593079078640868313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4289251728719385760578875 6433877593079078640868313)
        ·
          refine ⟨4825408194809308980651235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6433877593079078640868313 4825408194809308980651235)
          ·
            refine ⟨7238112292213963470976853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4825408194809308980651235 7238112292213963470976853)
            ·
              refine ⟨42410814212191192212755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7238112292213963470976853 42410814212191192212755)
              ·
                refine ⟨63616221318286788319133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42410814212191192212755 63616221318286788319133)
                ·
                  refine ⟨23856082994357545619675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63616221318286788319133 23856082994357545619675)
                  ·
                    rfl

theorem cell20_52267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 3].length) (baseStart_52267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52267 prefixEnd_52267 := by exact prefixLift 52267
  have htrace : WordTrace (prefixWord ++ tailWord_52267) baseStart_52267 baseEnd_52267 := by
    simpa [prefixWord, tailWord_52267, baseEnd_52267] using wordTrace_append hprefix tailTrace_52267
  have hstable : (prefixWord ++ tailWord_52267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52267).length < 2 ^ (prefixWord ++ tailWord_52267).sum := by decide
  have hdescent : baseEnd_52267 < baseStart_52267 := by decide
  rcases family_descends (prefixWord ++ tailWord_52267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52281 : List Nat := [1, 2, 1, 5, 2, 2, 1, 6]
def baseStart_52281 : Nat := 118140960795 + 52281 * 2 ^ 59
def prefixEnd_52281 : Nat := 4983230072969 + 3 ^ 40 * 52281 * 2
def baseEnd_52281 : Nat := 7954157658611906384317

theorem tailTrace_52281 : CollatzResearch.WordTrace tailWord_52281 prefixEnd_52281 7954157658611906384317 := by
  unfold tailWord_52281
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906844723602340729044697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1271229815734893819363131 1906844723602340729044697)
  ·
    refine ⟨1430133542701755546783523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1906844723602340729044697 1430133542701755546783523)
    ·
      refine ⟨2145200314052633320175285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1430133542701755546783523 2145200314052633320175285)
      ·
        refine ⟨201112529442434373766433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2145200314052633320175285 201112529442434373766433)
        ·
          refine ⟨150834397081825780324825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201112529442434373766433 150834397081825780324825)
          ·
            refine ⟨113125797811369335243619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150834397081825780324825 113125797811369335243619)
            ·
              refine ⟨169688696717054002865429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113125797811369335243619 169688696717054002865429)
              ·
                refine ⟨7954157658611906384317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 169688696717054002865429 7954157658611906384317)
                ·
                  rfl

theorem cell20_52281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 6].length) (baseStart_52281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52281 prefixEnd_52281 := by exact prefixLift 52281
  have htrace : WordTrace (prefixWord ++ tailWord_52281) baseStart_52281 baseEnd_52281 := by
    simpa [prefixWord, tailWord_52281, baseEnd_52281] using wordTrace_append hprefix tailTrace_52281
  have hstable : (prefixWord ++ tailWord_52281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52281).length < 2 ^ (prefixWord ++ tailWord_52281).sum := by decide
  have hdescent : baseEnd_52281 < baseStart_52281 := by decide
  rcases family_descends (prefixWord ++ tailWord_52281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52318 : List Nat := [4, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_52318 : Nat := 118140960795 + 52318 * 2 ^ 59
def prefixEnd_52318 : Nat := 4983230072969 + 3 ^ 40 * 52318 * 2
def baseEnd_52318 : Nat := 23879360784028034919467

theorem tailTrace_52318 : CollatzResearch.WordTrace tailWord_52318 prefixEnd_52318 23879360784028034919467 := by
  unfold tailWord_52318
  simp only [CollatzResearch.WordTrace]
  refine ⟨238524278058537006017701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1272129482978864032094405 238524278058537006017701)
  ·
    refine ⟨44723302135975688628319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 238524278058537006017701 44723302135975688628319)
    ·
      refine ⟨67084953203963532942479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44723302135975688628319 67084953203963532942479)
      ·
        refine ⟨100627429805945299413719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67084953203963532942479 100627429805945299413719)
        ·
          refine ⟨150941144708917949120579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100627429805945299413719 150941144708917949120579)
          ·
            refine ⟨226411717063376923680869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150941144708917949120579 226411717063376923680869)
            ·
              refine ⟨42452196949383173190163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226411717063376923680869 42452196949383173190163)
              ·
                refine ⟨63678295424074759785245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42452196949383173190163 63678295424074759785245)
                ·
                  refine ⟨23879360784028034919467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63678295424074759785245 23879360784028034919467)
                  ·
                    rfl

theorem cell20_52318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_52318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52318 prefixEnd_52318 := by exact prefixLift 52318
  have htrace : WordTrace (prefixWord ++ tailWord_52318) baseStart_52318 baseEnd_52318 := by
    simpa [prefixWord, tailWord_52318, baseEnd_52318] using wordTrace_append hprefix tailTrace_52318
  have hstable : (prefixWord ++ tailWord_52318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52318).length < 2 ^ (prefixWord ++ tailWord_52318).sum := by decide
  have hdescent : baseEnd_52318 < baseStart_52318 := by decide
  rcases family_descends (prefixWord ++ tailWord_52318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52322 : List Nat := [3, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_52322 : Nat := 118140960795 + 52322 * 2 ^ 59
def prefixEnd_52322 : Nat := 4983230072969 + 3 ^ 40 * 52322 * 2
def baseEnd_52322 : Nat := 23881186493021798786117

theorem tailTrace_52322 : CollatzResearch.WordTrace tailWord_52322 prefixEnd_52322 23881186493021798786117 := by
  unfold tailWord_52322
  simp only [CollatzResearch.WordTrace]
  refine ⟨477085029113451182821805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1272226744302536487524813 477085029113451182821805)
  ·
    refine ⟨178906885917544193558177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 477085029113451182821805 178906885917544193558177)
    ·
      refine ⟨134180164438158145168633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178906885917544193558177 134180164438158145168633)
      ·
        refine ⟨100635123328618608876475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134180164438158145168633 100635123328618608876475)
        ·
          refine ⟨150952684992927913314713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100635123328618608876475 150952684992927913314713)
          ·
            refine ⟨113214513744695934986035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150952684992927913314713 113214513744695934986035)
            ·
              refine ⟨169821770617043902479053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113214513744695934986035 169821770617043902479053)
              ·
                refine ⟨63683163981391463429645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169821770617043902479053 63683163981391463429645)
                ·
                  refine ⟨23881186493021798786117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63683163981391463429645 23881186493021798786117)
                  ·
                    rfl

theorem cell20_52322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_52322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52322 prefixEnd_52322 := by exact prefixLift 52322
  have htrace : WordTrace (prefixWord ++ tailWord_52322) baseStart_52322 baseEnd_52322 := by
    simpa [prefixWord, tailWord_52322, baseEnd_52322] using wordTrace_append hprefix tailTrace_52322
  have hstable : (prefixWord ++ tailWord_52322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52322).length < 2 ^ (prefixWord ++ tailWord_52322).sum := by decide
  have hdescent : baseEnd_52322 < baseStart_52322 := by decide
  rcases family_descends (prefixWord ++ tailWord_52322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52347 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 7]
def baseStart_52347 : Nat := 118140960795 + 52347 * 2 ^ 59
def prefixEnd_52347 : Nat := 4983230072969 + 3 ^ 40 * 52347 * 2
def baseEnd_52347 : Nat := 23892597174232822952681

theorem tailTrace_52347 : CollatzResearch.WordTrace tailWord_52347 prefixEnd_52347 23892597174232822952681 := by
  unfold tailWord_52347
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909251941363234000947295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1272834627575489333964863 1909251941363234000947295)
  ·
    refine ⟨2863877912044851001420943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1909251941363234000947295 2863877912044851001420943)
    ·
      refine ⟨4295816868067276502131415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2863877912044851001420943 4295816868067276502131415)
      ·
        refine ⟨6443725302100914753197123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4295816868067276502131415 6443725302100914753197123)
        ·
          refine ⟨9665587953151372129795685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6443725302100914753197123 9665587953151372129795685)
          ·
            refine ⟨1812297741215882274336691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9665587953151372129795685 1812297741215882274336691)
            ·
              refine ⟨2718446611823823411505037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812297741215882274336691 2718446611823823411505037)
              ·
                refine ⟨1019417479433933779314389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2718446611823823411505037 1019417479433933779314389)
                ·
                  refine ⟨23892597174232822952681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1019417479433933779314389 23892597174232822952681)
                  ·
                    rfl

theorem cell20_52347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_52347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52347 prefixEnd_52347 := by exact prefixLift 52347
  have htrace : WordTrace (prefixWord ++ tailWord_52347) baseStart_52347 baseEnd_52347 := by
    simpa [prefixWord, tailWord_52347, baseEnd_52347] using wordTrace_append hprefix tailTrace_52347
  have hstable : (prefixWord ++ tailWord_52347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52347).length < 2 ^ (prefixWord ++ tailWord_52347).sum := by decide
  have hdescent : baseEnd_52347 < baseStart_52347 := by decide
  rcases family_descends (prefixWord ++ tailWord_52347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52357 : List Nat := [1, 3, 1, 1, 7, 7]
def baseStart_52357 : Nat := 118140960795 + 52357 * 2 ^ 59
def prefixEnd_52357 : Nat := 4983230072969 + 3 ^ 40 * 52357 * 2
def baseEnd_52357 : Nat := 885080053582119726641

theorem tailTrace_52357 : CollatzResearch.WordTrace tailWord_52357 prefixEnd_52357 885080053582119726641 := by
  unfold tailWord_52357
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909616671327005708811325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1273077780884670472540883 1909616671327005708811325)
  ·
    refine ⟨716106251747627140804247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1909616671327005708811325 716106251747627140804247)
    ·
      refine ⟨1074159377621440711206371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 716106251747627140804247 1074159377621440711206371)
      ·
        refine ⟨1611239066432161066809557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074159377621440711206371 1611239066432161066809557)
        ·
          refine ⟨37763415619503775003349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1611239066432161066809557 37763415619503775003349)
          ·
            refine ⟨885080053582119726641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 37763415619503775003349 885080053582119726641)
            ·
              rfl

theorem cell20_52357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 7].length) (baseStart_52357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52357 prefixEnd_52357 := by exact prefixLift 52357
  have htrace : WordTrace (prefixWord ++ tailWord_52357) baseStart_52357 baseEnd_52357 := by
    simpa [prefixWord, tailWord_52357, baseEnd_52357] using wordTrace_append hprefix tailTrace_52357
  have hstable : (prefixWord ++ tailWord_52357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52357).length < 2 ^ (prefixWord ++ tailWord_52357).sum := by decide
  have hdescent : baseEnd_52357 < baseStart_52357 := by decide
  rcases family_descends (prefixWord ++ tailWord_52357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52360 : List Nat := [2, 1, 3, 4, 2, 1, 2, 2, 3]
def baseStart_52360 : Nat := 118140960795 + 52360 * 2 ^ 59
def prefixEnd_52360 : Nat := 4983230072969 + 3 ^ 40 * 52360 * 2
def baseEnd_52360 : Nat := 23898530728462555519295

theorem tailTrace_52360 : CollatzResearch.WordTrace tailWord_52360 prefixEnd_52360 23898530728462555519295 := by
  unfold tailWord_52360
  simp only [CollatzResearch.WordTrace]
  refine ⟨954863045158068610585267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1273150726877424814113689 954863045158068610585267)
  ·
    refine ⟨1432294567737102915877901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 954863045158068610585267 1432294567737102915877901)
    ·
      refine ⟨537110462901413593454213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1432294567737102915877901 537110462901413593454213)
      ·
        refine ⟨100708211794015048772665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 537110462901413593454213 100708211794015048772665)
        ·
          refine ⟨75531158845511286579499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100708211794015048772665 75531158845511286579499)
          ·
            refine ⟨113296738268266929869249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75531158845511286579499 113296738268266929869249)
            ·
              refine ⟨84972553701200197401937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113296738268266929869249 84972553701200197401937)
              ·
                refine ⟨63729415275900148051453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84972553701200197401937 63729415275900148051453)
                ·
                  refine ⟨23898530728462555519295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63729415275900148051453 23898530728462555519295)
                  ·
                    rfl

theorem cell20_52360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_52360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52360 prefixEnd_52360 := by exact prefixLift 52360
  have htrace : WordTrace (prefixWord ++ tailWord_52360) baseStart_52360 baseEnd_52360 := by
    simpa [prefixWord, tailWord_52360, baseEnd_52360] using wordTrace_append hprefix tailTrace_52360
  have hstable : (prefixWord ++ tailWord_52360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52360).length < 2 ^ (prefixWord ++ tailWord_52360).sum := by decide
  have hdescent : baseEnd_52360 < baseStart_52360 := by decide
  rcases family_descends (prefixWord ++ tailWord_52360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52388 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 4]
def baseStart_52388 : Nat := 118140960795 + 52388 * 2 ^ 59
def prefixEnd_52388 : Nat := 4983230072969 + 3 ^ 40 * 52388 * 2
def baseEnd_52388 : Nat := 23911310691418902585847

theorem tailTrace_52388 : CollatzResearch.WordTrace tailWord_52388 prefixEnd_52388 23911310691418902585847 := by
  unfold tailWord_52388
  simp only [CollatzResearch.WordTrace]
  refine ⟨955373667107349001594909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1273831556143132002126545 955373667107349001594909)
  ·
    refine ⟨358265125165255875598091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 955373667107349001594909 358265125165255875598091)
    ·
      refine ⟨537397687747883813397137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358265125165255875598091 537397687747883813397137)
      ·
        refine ⟨403048265810912860047853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537397687747883813397137 403048265810912860047853)
        ·
          refine ⟨151143099679092322517945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 403048265810912860047853 151143099679092322517945)
          ·
            refine ⟨113357324759319241888459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151143099679092322517945 113357324759319241888459)
            ·
              refine ⟨170035987138978862832689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113357324759319241888459 170035987138978862832689)
              ·
                refine ⟨127526990354234147124517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170035987138978862832689 127526990354234147124517)
                ·
                  refine ⟨23911310691418902585847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127526990354234147124517 23911310691418902585847)
                  ·
                    rfl

theorem cell20_52388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_52388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52388 prefixEnd_52388 := by exact prefixLift 52388
  have htrace : WordTrace (prefixWord ++ tailWord_52388) baseStart_52388 baseEnd_52388 := by
    simpa [prefixWord, tailWord_52388, baseEnd_52388] using wordTrace_append hprefix tailTrace_52388
  have hstable : (prefixWord ++ tailWord_52388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52388).length < 2 ^ (prefixWord ++ tailWord_52388).sum := by decide
  have hdescent : baseEnd_52388 < baseStart_52388 := by decide
  rcases family_descends (prefixWord ++ tailWord_52388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52426 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_52426 : Nat := 118140960795 + 52426 * 2 ^ 59
def prefixEnd_52426 : Nat := 4983230072969 + 3 ^ 40 * 52426 * 2
def baseEnd_52426 : Nat := 23928654926859659319025

theorem tailTrace_52426 : CollatzResearch.WordTrace tailWord_52426 prefixEnd_52426 23928654926859659319025 := by
  unfold tailWord_52426
  simp only [CollatzResearch.WordTrace]
  refine ⟨478033327019257623268283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1274755538718020328715421 478033327019257623268283)
  ·
    refine ⟨717049990528886434902425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 478033327019257623268283 717049990528886434902425)
    ·
      refine ⟨537787492896664826176819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 717049990528886434902425 537787492896664826176819)
      ·
        refine ⟨806681239344997239265229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537787492896664826176819 806681239344997239265229)
        ·
          refine ⟨302505464754373964724461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 806681239344997239265229 302505464754373964724461)
          ·
            refine ⟨113439549282890236771673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302505464754373964724461 113439549282890236771673)
            ·
              refine ⟨85079661962167677578755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113439549282890236771673 85079661962167677578755)
              ·
                refine ⟨127619492943251516368133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85079661962167677578755 127619492943251516368133)
                ·
                  refine ⟨23928654926859659319025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127619492943251516368133 23928654926859659319025)
                  ·
                    rfl

theorem cell20_52426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_52426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52426 prefixEnd_52426 := by exact prefixLift 52426
  have htrace : WordTrace (prefixWord ++ tailWord_52426) baseStart_52426 baseEnd_52426 := by
    simpa [prefixWord, tailWord_52426, baseEnd_52426] using wordTrace_append hprefix tailTrace_52426
  have hstable : (prefixWord ++ tailWord_52426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52426).length < 2 ^ (prefixWord ++ tailWord_52426).sum := by decide
  have hdescent : baseEnd_52426 < baseStart_52426 := by decide
  rcases family_descends (prefixWord ++ tailWord_52426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52447 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 4]
def baseStart_52447 : Nat := 118140960795 + 52447 * 2 ^ 59
def prefixEnd_52447 : Nat := 4983230072969 + 3 ^ 40 * 52447 * 2
def baseEnd_52447 : Nat := 23938239899076919618939

theorem tailTrace_52447 : CollatzResearch.WordTrace tailWord_52447 prefixEnd_52447 23938239899076919618939 := by
  unfold tailWord_52447
  simp only [CollatzResearch.WordTrace]
  refine ⟨1912899241000951079587595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1275266160667300719725063 1912899241000951079587595)
  ·
    refine ⟨2869348861501426619381393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1912899241000951079587595 2869348861501426619381393)
    ·
      refine ⟨2152011646126069964536045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2869348861501426619381393 2152011646126069964536045)
      ·
        refine ⟨807004367297276236701017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2152011646126069964536045 807004367297276236701017)
        ·
          refine ⟨605253275472957177525763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 807004367297276236701017 605253275472957177525763)
          ·
            refine ⟨907879913209435766288645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605253275472957177525763 907879913209435766288645)
            ·
              refine ⟨170227483726769206179121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 907879913209435766288645 170227483726769206179121)
              ·
                refine ⟨127670612795076904634341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170227483726769206179121 127670612795076904634341)
                ·
                  refine ⟨23938239899076919618939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127670612795076904634341 23938239899076919618939)
                  ·
                    rfl

theorem cell20_52447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_52447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52447 prefixEnd_52447 := by exact prefixLift 52447
  have htrace : WordTrace (prefixWord ++ tailWord_52447) baseStart_52447 baseEnd_52447 := by
    simpa [prefixWord, tailWord_52447, baseEnd_52447] using wordTrace_append hprefix tailTrace_52447
  have hstable : (prefixWord ++ tailWord_52447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52447).length < 2 ^ (prefixWord ++ tailWord_52447).sum := by decide
  have hdescent : baseEnd_52447 < baseStart_52447 := by decide
  rcases family_descends (prefixWord ++ tailWord_52447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52492 : List Nat := [2, 2, 1, 2, 2, 3, 1, 7]
def baseStart_52492 : Nat := 118140960795 + 52492 * 2 ^ 59
def prefixEnd_52492 : Nat := 4983230072969 + 3 ^ 40 * 52492 * 2
def baseEnd_52492 : Nat := 7986259708418921039585

theorem tailTrace_52492 : CollatzResearch.WordTrace tailWord_52492 prefixEnd_52492 7986259708418921039585 := by
  unfold tailWord_52492
  simp only [CollatzResearch.WordTrace]
  refine ⟨957270262918961882487865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1276360350558615843317153 957270262918961882487865)
  ·
    refine ⟨717952697189221411865899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 957270262918961882487865 717952697189221411865899)
    ·
      refine ⟨1076929045783832117798849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 717952697189221411865899 1076929045783832117798849)
      ·
        refine ⟨807696784337874088349137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1076929045783832117798849 807696784337874088349137)
        ·
          refine ⟨605772588253405566261853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 807696784337874088349137 605772588253405566261853)
          ·
            refine ⟨227164720595027087348195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 605772588253405566261853 227164720595027087348195)
            ·
              refine ⟨340747080892540631022293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227164720595027087348195 340747080892540631022293)
              ·
                refine ⟨7986259708418921039585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 340747080892540631022293 7986259708418921039585)
                ·
                  rfl

theorem cell20_52492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_52492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52492 prefixEnd_52492 := by exact prefixLift 52492
  have htrace : WordTrace (prefixWord ++ tailWord_52492) baseStart_52492 baseEnd_52492 := by
    simpa [prefixWord, tailWord_52492, baseEnd_52492] using wordTrace_append hprefix tailTrace_52492
  have hstable : (prefixWord ++ tailWord_52492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52492).length < 2 ^ (prefixWord ++ tailWord_52492).sum := by decide
  have hdescent : baseEnd_52492 < baseStart_52492 := by decide
  rcases family_descends (prefixWord ++ tailWord_52492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52509 : List Nat := [1, 4, 2, 3, 1, 1, 2, 6]
def baseStart_52509 : Nat := 118140960795 + 52509 * 2 ^ 59
def prefixEnd_52509 : Nat := 4983230072969 + 3 ^ 40 * 52509 * 2
def baseEnd_52509 : Nat := 7988846129493419850673

theorem tailTrace_52509 : CollatzResearch.WordTrace tailWord_52509 prefixEnd_52509 7988846129493419850673 := by
  unfold tailWord_52509
  simp only [CollatzResearch.WordTrace]
  refine ⟨1915160566776335668344581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1276773711184223778896387 1915160566776335668344581)
  ·
    refine ⟨359092606270562937814609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1915160566776335668344581 359092606270562937814609)
    ·
      refine ⟨269319454702922203360957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359092606270562937814609 269319454702922203360957)
      ·
        refine ⟨100994795513595826260359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269319454702922203360957 100994795513595826260359)
        ·
          refine ⟨151492193270393739390539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100994795513595826260359 151492193270393739390539)
          ·
            refine ⟨227238289905590609085809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151492193270393739390539 227238289905590609085809)
            ·
              refine ⟨170428717429192956814357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227238289905590609085809 170428717429192956814357)
              ·
                refine ⟨7988846129493419850673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170428717429192956814357 7988846129493419850673)
                ·
                  rfl

theorem cell20_52509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 6].length) (baseStart_52509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52509 prefixEnd_52509 := by exact prefixLift 52509
  have htrace : WordTrace (prefixWord ++ tailWord_52509) baseStart_52509 baseEnd_52509 := by
    simpa [prefixWord, tailWord_52509, baseEnd_52509] using wordTrace_append hprefix tailTrace_52509
  have hstable : (prefixWord ++ tailWord_52509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52509).length < 2 ^ (prefixWord ++ tailWord_52509).sum := by decide
  have hdescent : baseEnd_52509 < baseStart_52509 := by decide
  rcases family_descends (prefixWord ++ tailWord_52509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52530 : List Nat := [3, 2, 1, 1, 4, 9]
def baseStart_52530 : Nat := 118140960795 + 52530 * 2 ^ 59
def prefixEnd_52530 : Nat := 4983230072969 + 3 ^ 40 * 52530 * 2
def baseEnd_52530 : Nat := 888004568914722957479

theorem tailTrace_52530 : CollatzResearch.WordTrace tailWord_52530 prefixEnd_52530 888004568914722957479 := by
  unfold tailWord_52530
  simp only [CollatzResearch.WordTrace]
  refine ⟨478981624925064063714761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1277284333133504169906029 478981624925064063714761)
  ·
    refine ⟨359236218693798047786071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 478981624925064063714761 359236218693798047786071)
    ·
      refine ⟨538854328040697071679107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359236218693798047786071 538854328040697071679107)
      ·
        refine ⟨808281492061045607518661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538854328040697071679107 808281492061045607518661)
        ·
          refine ⟨151552779761446051409749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 808281492061045607518661 151552779761446051409749)
          ·
            refine ⟨888004568914722957479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 151552779761446051409749 888004568914722957479)
            ·
              rfl

theorem cell20_52530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 9].length) (baseStart_52530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52530 prefixEnd_52530 := by exact prefixLift 52530
  have htrace : WordTrace (prefixWord ++ tailWord_52530) baseStart_52530 baseEnd_52530 := by
    simpa [prefixWord, tailWord_52530, baseEnd_52530] using wordTrace_append hprefix tailTrace_52530
  have hstable : (prefixWord ++ tailWord_52530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52530).length < 2 ^ (prefixWord ++ tailWord_52530).sum := by decide
  have hdescent : baseEnd_52530 < baseStart_52530 := by decide
  rcases family_descends (prefixWord ++ tailWord_52530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52533 : List Nat := [1, 3, 3, 1, 2, 3, 2, 2, 3]
def baseStart_52533 : Nat := 118140960795 + 52533 * 2 ^ 59
def prefixEnd_52533 : Nat := 4983230072969 + 3 ^ 40 * 52533 * 2
def baseEnd_52533 : Nat := 23977492642442842751921

theorem tailTrace_52533 : CollatzResearch.WordTrace tailWord_52533 prefixEnd_52533 23977492642442842751921 := by
  unfold tailWord_52533
  simp only [CollatzResearch.WordTrace]
  refine ⟨1916035918689387767218253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1277357279126258511478835 1916035918689387767218253)
  ·
    refine ⟨718513469508520412706845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1916035918689387767218253 718513469508520412706845)
    ·
      refine ⟨269442551065695154765067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 718513469508520412706845 269442551065695154765067)
      ·
        refine ⟨404163826598542732147601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269442551065695154765067 404163826598542732147601)
        ·
          refine ⟨303122869948907049110701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404163826598542732147601 303122869948907049110701)
          ·
            refine ⟨113671076230840143416513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303122869948907049110701 113671076230840143416513)
            ·
              refine ⟨85253307173130107562385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113671076230840143416513 85253307173130107562385)
              ·
                refine ⟨63939980379847580671789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85253307173130107562385 63939980379847580671789)
                ·
                  refine ⟨23977492642442842751921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63939980379847580671789 23977492642442842751921)
                  ·
                    rfl

theorem cell20_52533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_52533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52533 prefixEnd_52533 := by exact prefixLift 52533
  have htrace : WordTrace (prefixWord ++ tailWord_52533) baseStart_52533 baseEnd_52533 := by
    simpa [prefixWord, tailWord_52533, baseEnd_52533] using wordTrace_append hprefix tailTrace_52533
  have hstable : (prefixWord ++ tailWord_52533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52533).length < 2 ^ (prefixWord ++ tailWord_52533).sum := by decide
  have hdescent : baseEnd_52533 < baseStart_52533 := by decide
  rcases family_descends (prefixWord ++ tailWord_52533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52561 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 4]
def baseStart_52561 : Nat := 118140960795 + 52561 * 2 ^ 59
def prefixEnd_52561 : Nat := 4983230072969 + 3 ^ 40 * 52561 * 2
def baseEnd_52561 : Nat := 23990272605399189818473

theorem tailTrace_52561 : CollatzResearch.WordTrace tailWord_52561 prefixEnd_52561 23990272605399189818473 := by
  unfold tailWord_52561
  simp only [CollatzResearch.WordTrace]
  refine ⟨1917057162587948549237537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1278038108391965699491691 1917057162587948549237537)
  ·
    refine ⟨1437792871940961411928153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1917057162587948549237537 1437792871940961411928153)
    ·
      refine ⟨1078344653955721058946115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1437792871940961411928153 1078344653955721058946115)
      ·
        refine ⟨1617516980933581588419173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078344653955721058946115 1617516980933581588419173)
        ·
          refine ⟨303284433925046547828595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1617516980933581588419173 303284433925046547828595)
          ·
            refine ⟨454926650887569821742893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303284433925046547828595 454926650887569821742893)
            ·
              refine ⟨170597494082838683153585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 454926650887569821742893 170597494082838683153585)
              ·
                refine ⟨127948120562129012365189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170597494082838683153585 127948120562129012365189)
                ·
                  refine ⟨23990272605399189818473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127948120562129012365189 23990272605399189818473)
                  ·
                    rfl

theorem cell20_52561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_52561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52561 prefixEnd_52561 := by exact prefixLift 52561
  have htrace : WordTrace (prefixWord ++ tailWord_52561) baseStart_52561 baseEnd_52561 := by
    simpa [prefixWord, tailWord_52561, baseEnd_52561] using wordTrace_append hprefix tailTrace_52561
  have hstable : (prefixWord ++ tailWord_52561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52561).length < 2 ^ (prefixWord ++ tailWord_52561).sum := by decide
  have hdescent : baseEnd_52561 < baseStart_52561 := by decide
  rcases family_descends (prefixWord ++ tailWord_52561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52575 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 5]
def baseStart_52575 : Nat := 118140960795 + 52575 * 2 ^ 59
def prefixEnd_52575 : Nat := 4983230072969 + 3 ^ 40 * 52575 * 2
def baseEnd_52575 : Nat := 23996662586877363351749

theorem tailTrace_52575 : CollatzResearch.WordTrace tailWord_52575 prefixEnd_52575 23996662586877363351749 := by
  unfold tailWord_52575
  simp only [CollatzResearch.WordTrace]
  refine ⟨1917567784537228940247179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1278378523024819293498119 1917567784537228940247179)
  ·
    refine ⟨2876351676805843410370769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1917567784537228940247179 2876351676805843410370769)
    ·
      refine ⟨2157263757604382557778077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2876351676805843410370769 2157263757604382557778077)
      ·
        refine ⟨808973909101643459166779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2157263757604382557778077 808973909101643459166779)
        ·
          refine ⟨1213460863652465188750169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808973909101643459166779 1213460863652465188750169)
          ·
            refine ⟨910095647739348891562627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1213460863652465188750169 910095647739348891562627)
            ·
              refine ⟨1365143471609023337343941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910095647739348891562627 1365143471609023337343941)
              ·
                refine ⟨255964400926691875751989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1365143471609023337343941 255964400926691875751989)
                ·
                  refine ⟨23996662586877363351749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255964400926691875751989 23996662586877363351749)
                  ·
                    rfl

theorem cell20_52575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_52575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52575 prefixEnd_52575 := by exact prefixLift 52575
  have htrace : WordTrace (prefixWord ++ tailWord_52575) baseStart_52575 baseEnd_52575 := by
    simpa [prefixWord, tailWord_52575, baseEnd_52575] using wordTrace_append hprefix tailTrace_52575
  have hstable : (prefixWord ++ tailWord_52575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52575).length < 2 ^ (prefixWord ++ tailWord_52575).sum := by decide
  have hdescent : baseEnd_52575 < baseStart_52575 := by decide
  rcases family_descends (prefixWord ++ tailWord_52575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52599 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 4]
def baseStart_52599 : Nat := 118140960795 + 52599 * 2 ^ 59
def prefixEnd_52599 : Nat := 4983230072969 + 3 ^ 40 * 52599 * 2
def baseEnd_52599 : Nat := 24007616840839946551651

theorem tailTrace_52599 : CollatzResearch.WordTrace tailWord_52599 prefixEnd_52599 24007616840839946551651 := by
  unfold tailWord_52599
  simp only [CollatzResearch.WordTrace]
  refine ⟨1918443136450281039120851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1278962090966854026080567 1918443136450281039120851)
  ·
    refine ⟨2877664704675421558681277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1918443136450281039120851 2877664704675421558681277)
    ·
      refine ⟨1079124264253283084505479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2877664704675421558681277 1079124264253283084505479)
      ·
        refine ⟨1618686396379924626758219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1079124264253283084505479 1618686396379924626758219)
        ·
          refine ⟨2428029594569886940137329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618686396379924626758219 2428029594569886940137329)
          ·
            refine ⟨1821022195927415205102997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2428029594569886940137329 1821022195927415205102997)
            ·
              refine ⟨85360415434097587739203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1821022195927415205102997 85360415434097587739203)
              ·
                refine ⟨128040623151146381608805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85360415434097587739203 128040623151146381608805)
                ·
                  refine ⟨24007616840839946551651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128040623151146381608805 24007616840839946551651)
                  ·
                    rfl

theorem cell20_52599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_52599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52599 prefixEnd_52599 := by exact prefixLift 52599
  have htrace : WordTrace (prefixWord ++ tailWord_52599) baseStart_52599 baseEnd_52599 := by
    simpa [prefixWord, tailWord_52599, baseEnd_52599] using wordTrace_append hprefix tailTrace_52599
  have hstable : (prefixWord ++ tailWord_52599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52599).length < 2 ^ (prefixWord ++ tailWord_52599).sum := by decide
  have hdescent : baseEnd_52599 < baseStart_52599 := by decide
  rcases family_descends (prefixWord ++ tailWord_52599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52633 : List Nat := [1, 2, 1, 2, 1, 7, 1, 3, 2]
def baseStart_52633 : Nat := 118140960795 + 52633 * 2 ^ 59
def prefixEnd_52633 : Nat := 4983230072969 + 3 ^ 40 * 52633 * 2
def baseEnd_52633 : Nat := 24023135367286939418179

theorem tailTrace_52633 : CollatzResearch.WordTrace tailWord_52633 prefixEnd_52633 24023135367286939418179 := by
  unfold tailWord_52633
  simp only [CollatzResearch.WordTrace]
  refine ⟨1919683218327104845858553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1279788812218069897239035 1919683218327104845858553)
  ·
    refine ⟨1439762413745328634393915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1919683218327104845858553 1439762413745328634393915)
    ·
      refine ⟨2159643620617992951590873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1439762413745328634393915 2159643620617992951590873)
      ·
        refine ⟨1619732715463494713693155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2159643620617992951590873 1619732715463494713693155)
        ·
          refine ⟨2429599073195242070539733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1619732715463494713693155 2429599073195242070539733)
          ·
            refine ⟨56943728278013486028275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 2429599073195242070539733 56943728278013486028275)
            ·
              refine ⟨85415592417020229042413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56943728278013486028275 85415592417020229042413)
              ·
                refine ⟨32030847156382585890905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85415592417020229042413 32030847156382585890905)
                ·
                  refine ⟨24023135367286939418179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32030847156382585890905 24023135367286939418179)
                  ·
                    rfl

theorem cell20_52633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 2].length) (baseStart_52633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52633 prefixEnd_52633 := by exact prefixLift 52633
  have htrace : WordTrace (prefixWord ++ tailWord_52633) baseStart_52633 baseEnd_52633 := by
    simpa [prefixWord, tailWord_52633, baseEnd_52633] using wordTrace_append hprefix tailTrace_52633
  have hstable : (prefixWord ++ tailWord_52633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52633).length < 2 ^ (prefixWord ++ tailWord_52633).sum := by decide
  have hdescent : baseEnd_52633 < baseStart_52633 := by decide
  rcases family_descends (prefixWord ++ tailWord_52633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52661 : List Nat := [1, 3, 3, 2, 2, 2, 2, 5]
def baseStart_52661 : Nat := 118140960795 + 52661 * 2 ^ 59
def prefixEnd_52661 : Nat := 4983230072969 + 3 ^ 40 * 52661 * 2
def baseEnd_52661 : Nat := 8011971776747762161577

theorem tailTrace_52661 : CollatzResearch.WordTrace tailWord_52661 prefixEnd_52661 8011971776747762161577 := by
  unfold tailWord_52661
  simp only [CollatzResearch.WordTrace]
  refine ⟨1920704462225665627877837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1280469641483777085251891 1920704462225665627877837)
  ·
    refine ⟨720264173334624610454189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1920704462225665627877837 720264173334624610454189)
    ·
      refine ⟨270099065000484228920321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 720264173334624610454189 270099065000484228920321)
      ·
        refine ⟨202574298750363171690241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270099065000484228920321 202574298750363171690241)
        ·
          refine ⟨151930724062772378767681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202574298750363171690241 151930724062772378767681)
          ·
            refine ⟨113948043047079284075761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151930724062772378767681 113948043047079284075761)
            ·
              refine ⟨85461032285309463056821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113948043047079284075761 85461032285309463056821)
              ·
                refine ⟨8011971776747762161577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85461032285309463056821 8011971776747762161577)
                ·
                  rfl

theorem cell20_52661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 5].length) (baseStart_52661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52661 prefixEnd_52661 := by exact prefixLift 52661
  have htrace : WordTrace (prefixWord ++ tailWord_52661) baseStart_52661 baseEnd_52661 := by
    simpa [prefixWord, tailWord_52661, baseEnd_52661] using wordTrace_append hprefix tailTrace_52661
  have hstable : (prefixWord ++ tailWord_52661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52661).length < 2 ^ (prefixWord ++ tailWord_52661).sum := by decide
  have hdescent : baseEnd_52661 < baseStart_52661 := by decide
  rcases family_descends (prefixWord ++ tailWord_52661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52682 : List Nat := [3, 1, 2, 1, 2, 3, 2, 6]
def baseStart_52682 : Nat := 118140960795 + 52682 * 2 ^ 59
def prefixEnd_52682 : Nat := 4983230072969 + 3 ^ 40 * 52682 * 2
def baseEnd_52682 : Nat := 8015166767486848928215

theorem tailTrace_52682 : CollatzResearch.WordTrace tailWord_52682 prefixEnd_52682 8015166767486848928215 := by
  unfold tailWord_52682
  simp only [CollatzResearch.WordTrace]
  refine ⟨480367598787396553598075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1280980263433057476261533 480367598787396553598075)
  ·
    refine ⟨720551398181094830397113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 480367598787396553598075 720551398181094830397113)
    ·
      refine ⟨540413548635821122797835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 720551398181094830397113 540413548635821122797835)
      ·
        refine ⟨810620322953731684196753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540413548635821122797835 810620322953731684196753)
        ·
          refine ⟨607965242215298763147565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 810620322953731684196753 607965242215298763147565)
          ·
            refine ⟨227986965830737036180337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 607965242215298763147565 227986965830737036180337)
            ·
              refine ⟨170990224373052777135253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227986965830737036180337 170990224373052777135253)
              ·
                refine ⟨8015166767486848928215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170990224373052777135253 8015166767486848928215)
                ·
                  rfl

theorem cell20_52682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_52682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52682 prefixEnd_52682 := by exact prefixLift 52682
  have htrace : WordTrace (prefixWord ++ tailWord_52682) baseStart_52682 baseEnd_52682 := by
    simpa [prefixWord, tailWord_52682, baseEnd_52682] using wordTrace_append hprefix tailTrace_52682
  have hstable : (prefixWord ++ tailWord_52682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52682).length < 2 ^ (prefixWord ++ tailWord_52682).sum := by decide
  have hdescent : baseEnd_52682 < baseStart_52682 := by decide
  rcases family_descends (prefixWord ++ tailWord_52682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52709 : List Nat := [1, 3, 1, 5, 1, 2, 1, 4, 2]
def baseStart_52709 : Nat := 118140960795 + 52709 * 2 ^ 59
def prefixEnd_52709 : Nat := 4983230072969 + 3 ^ 40 * 52709 * 2
def baseEnd_52709 : Nat := 24057823838168452884535

theorem tailTrace_52709 : CollatzResearch.WordTrace tailWord_52709 prefixEnd_52709 24057823838168452884535 := by
  unfold tailWord_52709
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922455166051769825625181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1281636777367846550416787 1922455166051769825625181)
  ·
    refine ⟨720920687269413684609443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1922455166051769825625181 720920687269413684609443)
    ·
      refine ⟨1081381030904120526914165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 720920687269413684609443 1081381030904120526914165)
      ·
        refine ⟨101379471647261299398203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1081381030904120526914165 101379471647261299398203)
        ·
          refine ⟨152069207470891949097305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101379471647261299398203 152069207470891949097305)
          ·
            refine ⟨114051905603168961822979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152069207470891949097305 114051905603168961822979)
            ·
              refine ⟨171077858404753442734469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114051905603168961822979 171077858404753442734469)
              ·
                refine ⟨32077098450891270512713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171077858404753442734469 32077098450891270512713)
                ·
                  refine ⟨24057823838168452884535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32077098450891270512713 24057823838168452884535)
                  ·
                    rfl

theorem cell20_52709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_52709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52709 prefixEnd_52709 := by exact prefixLift 52709
  have htrace : WordTrace (prefixWord ++ tailWord_52709) baseStart_52709 baseEnd_52709 := by
    simpa [prefixWord, tailWord_52709, baseEnd_52709] using wordTrace_append hprefix tailTrace_52709
  have hstable : (prefixWord ++ tailWord_52709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52709).length < 2 ^ (prefixWord ++ tailWord_52709).sum := by decide
  have hdescent : baseEnd_52709 < baseStart_52709 := by decide
  rcases family_descends (prefixWord ++ tailWord_52709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52720 : List Nat := [2, 1, 1, 1, 3, 4, 3, 5]
def baseStart_52720 : Nat := 118140960795 + 52720 * 2 ^ 59
def prefixEnd_52720 : Nat := 4983230072969 + 3 ^ 40 * 52720 * 2
def baseEnd_52720 : Nat := 8020948179300434505941

theorem tailTrace_52720 : CollatzResearch.WordTrace tailWord_52720 prefixEnd_52720 8020948179300434505941 := by
  unfold tailWord_52720
  simp only [CollatzResearch.WordTrace]
  refine ⟨961428184505959352137807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1281904246007945802850409 961428184505959352137807)
  ·
    refine ⟨1442142276758939028206711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 961428184505959352137807 1442142276758939028206711)
    ·
      refine ⟨2163213415138408542310067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1442142276758939028206711 2163213415138408542310067)
      ·
        refine ⟨3244820122707612813465101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2163213415138408542310067 3244820122707612813465101)
        ·
          refine ⟨1216807546015354805049413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3244820122707612813465101 1216807546015354805049413)
          ·
            refine ⟨228151414877879025946765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1216807546015354805049413 228151414877879025946765)
            ·
              refine ⟨85556780579204634730037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228151414877879025946765 85556780579204634730037)
              ·
                refine ⟨8020948179300434505941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85556780579204634730037 8020948179300434505941)
                ·
                  rfl

theorem cell20_52720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_52720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52720 prefixEnd_52720 := by exact prefixLift 52720
  have htrace : WordTrace (prefixWord ++ tailWord_52720) baseStart_52720 baseEnd_52720 := by
    simpa [prefixWord, tailWord_52720, baseEnd_52720] using wordTrace_append hprefix tailTrace_52720
  have hstable : (prefixWord ++ tailWord_52720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52720).length < 2 ^ (prefixWord ++ tailWord_52720).sum := by decide
  have hdescent : baseEnd_52720 < baseStart_52720 := by decide
  rcases family_descends (prefixWord ++ tailWord_52720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52747 : List Nat := [1, 1, 1, 1, 8, 1, 2, 3, 2]
def baseStart_52747 : Nat := 118140960795 + 52747 * 2 ^ 59
def prefixEnd_52747 : Nat := 4983230072969 + 3 ^ 40 * 52747 * 2
def baseEnd_52747 : Nat := 24075168073609209617713

theorem tailTrace_52747 : CollatzResearch.WordTrace tailWord_52747 prefixEnd_52747 24075168073609209617713 := by
  unfold tailWord_52747
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923841139914102315508495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1282560759942734877005663 1923841139914102315508495)
  ·
    refine ⟨2885761709871153473262743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1923841139914102315508495 2885761709871153473262743)
    ·
      refine ⟨4328642564806730209894115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2885761709871153473262743 4328642564806730209894115)
      ·
        refine ⟨6492963847210095314841173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4328642564806730209894115 6492963847210095314841173)
        ·
          refine ⟨76089420084493304470795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 6492963847210095314841173 76089420084493304470795)
          ·
            refine ⟨114134130126739956706193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76089420084493304470795 114134130126739956706193)
            ·
              refine ⟨85600597595054967529645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114134130126739956706193 85600597595054967529645)
              ·
                refine ⟨32100224098145612823617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85600597595054967529645 32100224098145612823617)
                ·
                  refine ⟨24075168073609209617713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32100224098145612823617 24075168073609209617713)
                  ·
                    rfl

theorem cell20_52747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 2].length) (baseStart_52747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52747 prefixEnd_52747 := by exact prefixLift 52747
  have htrace : WordTrace (prefixWord ++ tailWord_52747) baseStart_52747 baseEnd_52747 := by
    simpa [prefixWord, tailWord_52747, baseEnd_52747] using wordTrace_append hprefix tailTrace_52747
  have hstable : (prefixWord ++ tailWord_52747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52747).length < 2 ^ (prefixWord ++ tailWord_52747).sum := by decide
  have hdescent : baseEnd_52747 < baseStart_52747 := by decide
  rcases family_descends (prefixWord ++ tailWord_52747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52768 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 4]
def baseStart_52768 : Nat := 118140960795 + 52768 * 2 ^ 59
def prefixEnd_52768 : Nat := 4983230072969 + 3 ^ 40 * 52768 * 2
def baseEnd_52768 : Nat := 24084753045826469917627

theorem tailTrace_52768 : CollatzResearch.WordTrace tailWord_52768 prefixEnd_52768 24084753045826469917627 := by
  unfold tailWord_52768
  simp only [CollatzResearch.WordTrace]
  refine ⟨962303536419011451011479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1283071381892015268015305 962303536419011451011479)
  ·
    refine ⟨1443455304628517176517219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962303536419011451011479 1443455304628517176517219)
    ·
      refine ⟨2165182956942775764775829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1443455304628517176517219 2165182956942775764775829)
      ·
        refine ⟨101492951106692613973867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2165182956942775764775829 101492951106692613973867)
        ·
          refine ⟨152239426660038920960801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101492951106692613973867 152239426660038920960801)
          ·
            refine ⟨114179569995029190720601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152239426660038920960801 114179569995029190720601)
            ·
              refine ⟨85634677496271893040451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114179569995029190720601 85634677496271893040451)
              ·
                refine ⟨128452016244407839560677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85634677496271893040451 128452016244407839560677)
                ·
                  refine ⟨24084753045826469917627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128452016244407839560677 24084753045826469917627)
                  ·
                    rfl

theorem cell20_52768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_52768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52768 prefixEnd_52768 := by exact prefixLift 52768
  have htrace : WordTrace (prefixWord ++ tailWord_52768) baseStart_52768 baseEnd_52768 := by
    simpa [prefixWord, tailWord_52768, baseEnd_52768] using wordTrace_append hprefix tailTrace_52768
  have hstable : (prefixWord ++ tailWord_52768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52768).length < 2 ^ (prefixWord ++ tailWord_52768).sum := by decide
  have hdescent : baseEnd_52768 < baseStart_52768 := by decide
  rcases family_descends (prefixWord ++ tailWord_52768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52789 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 4]
def baseStart_52789 : Nat := 118140960795 + 52789 * 2 ^ 59
def prefixEnd_52789 : Nat := 4983230072969 + 3 ^ 40 * 52789 * 2
def baseEnd_52789 : Nat := 24094338018043730217541

theorem tailTrace_52789 : CollatzResearch.WordTrace tailWord_52789 prefixEnd_52789 24094338018043730217541 := by
  unfold tailWord_52789
  simp only [CollatzResearch.WordTrace]
  refine ⟨1925373005761943488537421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1283582003841295659024947 1925373005761943488537421)
  ·
    refine ⟨722014877160728808201533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1925373005761943488537421 722014877160728808201533)
    ·
      refine ⟨270755578935273303075575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 722014877160728808201533 270755578935273303075575)
      ·
        refine ⟨406133368402909954613363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270755578935273303075575 406133368402909954613363)
        ·
          refine ⟨609200052604364931920045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406133368402909954613363 609200052604364931920045)
          ·
            refine ⟨228450019726636849470017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 609200052604364931920045 228450019726636849470017)
            ·
              refine ⟨171337514794977637102513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228450019726636849470017 171337514794977637102513)
              ·
                refine ⟨128503136096233227826885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171337514794977637102513 128503136096233227826885)
                ·
                  refine ⟨24094338018043730217541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128503136096233227826885 24094338018043730217541)
                  ·
                    rfl

theorem cell20_52789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_52789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52789 prefixEnd_52789 := by exact prefixLift 52789
  have htrace : WordTrace (prefixWord ++ tailWord_52789) baseStart_52789 baseEnd_52789 := by
    simpa [prefixWord, tailWord_52789, baseEnd_52789] using wordTrace_append hprefix tailTrace_52789
  have hstable : (prefixWord ++ tailWord_52789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52789).length < 2 ^ (prefixWord ++ tailWord_52789).sum := by decide
  have hdescent : baseEnd_52789 < baseStart_52789 := by decide
  rcases family_descends (prefixWord ++ tailWord_52789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52820 : List Nat := [2, 4, 1, 1, 1, 2, 2, 4, 3]
def baseStart_52820 : Nat := 118140960795 + 52820 * 2 ^ 59
def prefixEnd_52820 : Nat := 4983230072969 + 3 ^ 40 * 52820 * 2
def baseEnd_52820 : Nat := 24108487262745400184081

theorem tailTrace_52820 : CollatzResearch.WordTrace tailWord_52820 prefixEnd_52820 24108487262745400184081 := by
  unfold tailWord_52820
  simp only [CollatzResearch.WordTrace]
  refine ⟨963251834324817891457957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1284335779099757188610609 963251834324817891457957)
  ·
    refine ⟨180609718935903354648367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 963251834324817891457957 180609718935903354648367)
    ·
      refine ⟨270914578403855031972551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180609718935903354648367 270914578403855031972551)
      ·
        refine ⟨406371867605782547958827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270914578403855031972551 406371867605782547958827)
        ·
          refine ⟨609557801408673821938241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406371867605782547958827 609557801408673821938241)
          ·
            refine ⟨457168351056505366453681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609557801408673821938241 457168351056505366453681)
            ·
              refine ⟨342876263292379024840261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457168351056505366453681 342876263292379024840261)
              ·
                refine ⟨64289299367321067157549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 342876263292379024840261 64289299367321067157549)
                ·
                  refine ⟨24108487262745400184081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64289299367321067157549 24108487262745400184081)
                  ·
                    rfl

theorem cell20_52820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_52820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52820 prefixEnd_52820 := by exact prefixLift 52820
  have htrace : WordTrace (prefixWord ++ tailWord_52820) baseStart_52820 baseEnd_52820 := by
    simpa [prefixWord, tailWord_52820, baseEnd_52820] using wordTrace_append hprefix tailTrace_52820
  have hstable : (prefixWord ++ tailWord_52820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52820).length < 2 ^ (prefixWord ++ tailWord_52820).sum := by decide
  have hdescent : baseEnd_52820 < baseStart_52820 := by decide
  rcases family_descends (prefixWord ++ tailWord_52820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52823 : List Nat := [1, 1, 3, 2, 2, 4, 3, 2, 2]
def baseStart_52823 : Nat := 118140960795 + 52823 * 2 ^ 59
def prefixEnd_52823 : Nat := 4983230072969 + 3 ^ 40 * 52823 * 2
def baseEnd_52823 : Nat := 24109856544490723084069

theorem tailTrace_52823 : CollatzResearch.WordTrace tailWord_52823 prefixEnd_52823 24109856544490723084069 := by
  unfold tailWord_52823
  simp only [CollatzResearch.WordTrace]
  refine ⟨1926613087638767295275123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1284408725092511530183415 1926613087638767295275123)
  ·
    refine ⟨2889919631458150942912685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1926613087638767295275123 2889919631458150942912685)
    ·
      refine ⟨1083719861796806603592257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2889919631458150942912685 1083719861796806603592257)
      ·
        refine ⟨812789896347604952694193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1083719861796806603592257 812789896347604952694193)
        ·
          refine ⟨609592422260703714520645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812789896347604952694193 609592422260703714520645)
          ·
            refine ⟨114298579173881946472621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 609592422260703714520645 114298579173881946472621)
            ·
              refine ⟨42861967190205729927233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114298579173881946472621 42861967190205729927233)
              ·
                refine ⟨32146475392654297445425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42861967190205729927233 32146475392654297445425)
                ·
                  refine ⟨24109856544490723084069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32146475392654297445425 24109856544490723084069)
                  ·
                    rfl

theorem cell20_52823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 2].length) (baseStart_52823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52823 prefixEnd_52823 := by exact prefixLift 52823
  have htrace : WordTrace (prefixWord ++ tailWord_52823) baseStart_52823 baseEnd_52823 := by
    simpa [prefixWord, tailWord_52823, baseEnd_52823] using wordTrace_append hprefix tailTrace_52823
  have hstable : (prefixWord ++ tailWord_52823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52823).length < 2 ^ (prefixWord ++ tailWord_52823).sum := by decide
  have hdescent : baseEnd_52823 < baseStart_52823 := by decide
  rcases family_descends (prefixWord ++ tailWord_52823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52837 : List Nat := [1, 3, 1, 3, 3, 1, 4, 1, 3]
def baseStart_52837 : Nat := 118140960795 + 52837 * 2 ^ 59
def prefixEnd_52837 : Nat := 4983230072969 + 3 ^ 40 * 52837 * 2
def baseEnd_52837 : Nat := 24116246525968896617345

theorem tailTrace_52837 : CollatzResearch.WordTrace tailWord_52837 prefixEnd_52837 24116246525968896617345 := by
  unfold tailWord_52837
  simp only [CollatzResearch.WordTrace]
  refine ⟨1927123709588047686284765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1284749139725365124189843 1927123709588047686284765)
  ·
    refine ⟨722671391095517882356787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1927123709588047686284765 722671391095517882356787)
    ·
      refine ⟨1084007086643276823535181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 722671391095517882356787 1084007086643276823535181)
      ·
        refine ⟨406502657491228808825693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1084007086643276823535181 406502657491228808825693)
        ·
          refine ⟨152438496559210803309635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 406502657491228808825693 152438496559210803309635)
          ·
            refine ⟨228657744838816204964453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152438496559210803309635 228657744838816204964453)
            ·
              refine ⟨42873327157278038430835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228657744838816204964453 42873327157278038430835)
              ·
                refine ⟨64309990735917057646253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42873327157278038430835 64309990735917057646253)
                ·
                  refine ⟨24116246525968896617345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64309990735917057646253 24116246525968896617345)
                  ·
                    rfl

theorem cell20_52837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_52837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52837 prefixEnd_52837 := by exact prefixLift 52837
  have htrace : WordTrace (prefixWord ++ tailWord_52837) baseStart_52837 baseEnd_52837 := by
    simpa [prefixWord, tailWord_52837, baseEnd_52837] using wordTrace_append hprefix tailTrace_52837
  have hstable : (prefixWord ++ tailWord_52837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52837).length < 2 ^ (prefixWord ++ tailWord_52837).sum := by decide
  have hdescent : baseEnd_52837 < baseStart_52837 := by decide
  rcases family_descends (prefixWord ++ tailWord_52837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52872 : List Nat := [2, 1, 3, 5, 9]
def baseStart_52872 : Nat := 118140960795 + 52872 * 2 ^ 59
def prefixEnd_52872 : Nat := 4983230072969 + 3 ^ 40 * 52872 * 2
def baseEnd_52872 : Nat := 297928660242769511735

theorem tailTrace_52872 : CollatzResearch.WordTrace tailWord_52872 prefixEnd_52872 297928660242769511735 := by
  unfold tailWord_52872
  simp only [CollatzResearch.WordTrace]
  refine ⟨964200132230624331904435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1285600176307499109205913 964200132230624331904435)
  ·
    refine ⟨1446300198345936497856653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 964200132230624331904435 1446300198345936497856653)
    ·
      refine ⟨542362574379726186696245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1446300198345936497856653 542362574379726186696245)
      ·
        refine ⟨50846491348099330002773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 542362574379726186696245 50846491348099330002773)
        ·
          refine ⟨297928660242769511735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 50846491348099330002773 297928660242769511735)
          ·
            rfl

theorem cell20_52872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 9].length) (baseStart_52872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52872 prefixEnd_52872 := by exact prefixLift 52872
  have htrace : WordTrace (prefixWord ++ tailWord_52872) baseStart_52872 baseEnd_52872 := by
    simpa [prefixWord, tailWord_52872, baseEnd_52872] using wordTrace_append hprefix tailTrace_52872
  have hstable : (prefixWord ++ tailWord_52872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52872).length < 2 ^ (prefixWord ++ tailWord_52872).sum := by decide
  have hdescent : baseEnd_52872 < baseStart_52872 := by decide
  rcases family_descends (prefixWord ++ tailWord_52872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52878 : List Nat := [4, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_52878 : Nat := 118140960795 + 52878 * 2 ^ 59
def prefixEnd_52878 : Nat := 4983230072969 + 3 ^ 40 * 52878 * 2
def baseEnd_52878 : Nat := 24134960043154976250511

theorem tailTrace_52878 : CollatzResearch.WordTrace tailWord_52878 prefixEnd_52878 24134960043154976250511 := by
  unfold tailWord_52878
  simp only [CollatzResearch.WordTrace]
  refine ⟨241077387804938961065911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1285746068293007792351525 241077387804938961065911)
  ·
    refine ⟨361616081707408441598867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241077387804938961065911 361616081707408441598867)
    ·
      refine ⟨542424122561112662398301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361616081707408441598867 542424122561112662398301)
      ·
        refine ⟨203409045960417248399363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 542424122561112662398301 203409045960417248399363)
        ·
          refine ⟨305113568940625872599045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203409045960417248399363 305113568940625872599045)
          ·
            refine ⟨57208794176367351112321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 305113568940625872599045 57208794176367351112321)
            ·
              refine ⟨42906595632275513334241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57208794176367351112321 42906595632275513334241)
              ·
                refine ⟨32179946724206635000681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42906595632275513334241 32179946724206635000681)
                ·
                  refine ⟨24134960043154976250511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32179946724206635000681 24134960043154976250511)
                  ·
                    rfl

theorem cell20_52878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_52878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52878 prefixEnd_52878 := by exact prefixLift 52878
  have htrace : WordTrace (prefixWord ++ tailWord_52878) baseStart_52878 baseEnd_52878 := by
    simpa [prefixWord, tailWord_52878, baseEnd_52878] using wordTrace_append hprefix tailTrace_52878
  have hstable : (prefixWord ++ tailWord_52878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52878).length < 2 ^ (prefixWord ++ tailWord_52878).sum := by decide
  have hdescent : baseEnd_52878 < baseStart_52878 := by decide
  rcases family_descends (prefixWord ++ tailWord_52878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52896 : List Nat := [2, 1, 1, 4, 3, 1, 2, 3, 3]
def baseStart_52896 : Nat := 118140960795 + 52896 * 2 ^ 59
def prefixEnd_52896 : Nat := 4983230072969 + 3 ^ 40 * 52896 * 2
def baseEnd_52896 : Nat := 24143175733626913650437

theorem tailTrace_52896 : CollatzResearch.WordTrace tailWord_52896 prefixEnd_52896 24143175733626913650437 := by
  unfold tailWord_52896
  simp only [CollatzResearch.WordTrace]
  refine ⟨964637808187150381341271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1286183744249533841788361 964637808187150381341271)
  ·
    refine ⟨1446956712280725572011907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 964637808187150381341271 1446956712280725572011907)
    ·
      refine ⟨2170435068421088358017861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1446956712280725572011907 2170435068421088358017861)
      ·
        refine ⟨406956575328954067128349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2170435068421088358017861 406956575328954067128349)
        ·
          refine ⟨152608715748357775173131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 406956575328954067128349 152608715748357775173131)
          ·
            refine ⟨228913073622536662759697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152608715748357775173131 228913073622536662759697)
            ·
              refine ⟨171684805216902497069773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228913073622536662759697 171684805216902497069773)
              ·
                refine ⟨64381801956338436401165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171684805216902497069773 64381801956338436401165)
                ·
                  refine ⟨24143175733626913650437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64381801956338436401165 24143175733626913650437)
                  ·
                    rfl

theorem cell20_52896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_52896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52896 prefixEnd_52896 := by exact prefixLift 52896
  have htrace : WordTrace (prefixWord ++ tailWord_52896) baseStart_52896 baseEnd_52896 := by
    simpa [prefixWord, tailWord_52896, baseEnd_52896] using wordTrace_append hprefix tailTrace_52896
  have hstable : (prefixWord ++ tailWord_52896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52896).length < 2 ^ (prefixWord ++ tailWord_52896).sum := by decide
  have hdescent : baseEnd_52896 < baseStart_52896 := by decide
  rcases family_descends (prefixWord ++ tailWord_52896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52993 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 5]
def baseStart_52993 : Nat := 118140960795 + 52993 * 2 ^ 59
def prefixEnd_52993 : Nat := 4983230072969 + 3 ^ 40 * 52993 * 2
def baseEnd_52993 : Nat := 24187449176725687416707

theorem tailTrace_52993 : CollatzResearch.WordTrace tailWord_52993 prefixEnd_52993 24187449176725687416707 := by
  unfold tailWord_52993
  simp only [CollatzResearch.WordTrace]
  refine ⟨1932813497022886328963633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1288542331348590885975755 1932813497022886328963633)
  ·
    refine ⟨1449610122767164746722725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1932813497022886328963633 1449610122767164746722725)
    ·
      refine ⟨271801898018843390010511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1449610122767164746722725 271801898018843390010511)
      ·
        refine ⟨407702847028265085015767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271801898018843390010511 407702847028265085015767)
        ·
          refine ⟨611554270542397627523651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407702847028265085015767 611554270542397627523651)
          ·
            refine ⟨917331405813596441285477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611554270542397627523651 917331405813596441285477)
            ·
              refine ⟨171999638590049332741027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 917331405813596441285477 171999638590049332741027)
              ·
                refine ⟨257999457885073999111541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171999638590049332741027 257999457885073999111541)
                ·
                  refine ⟨24187449176725687416707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 257999457885073999111541 24187449176725687416707)
                  ·
                    rfl

theorem cell20_52993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_52993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52993 prefixEnd_52993 := by exact prefixLift 52993
  have htrace : WordTrace (prefixWord ++ tailWord_52993) baseStart_52993 baseEnd_52993 := by
    simpa [prefixWord, tailWord_52993, baseEnd_52993] using wordTrace_append hprefix tailTrace_52993
  have hstable : (prefixWord ++ tailWord_52993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52993).length < 2 ^ (prefixWord ++ tailWord_52993).sum := by decide
  have hdescent : baseEnd_52993 < baseStart_52993 := by decide
  rcases family_descends (prefixWord ++ tailWord_52993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52996 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 4]
def baseStart_52996 : Nat := 118140960795 + 52996 * 2 ^ 59
def prefixEnd_52996 : Nat := 4983230072969 + 3 ^ 40 * 52996 * 2
def baseEnd_52996 : Nat := 24188818458471010316695

theorem tailTrace_52996 : CollatzResearch.WordTrace tailWord_52996 prefixEnd_52996 24188818458471010316695 := by
  unfold tailWord_52996
  simp only [CollatzResearch.WordTrace]
  refine ⟨966461458006008920661421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1288615277341345227548561 966461458006008920661421)
  ·
    refine ⟨362423046752253345248033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 966461458006008920661421 362423046752253345248033)
    ·
      refine ⟨271817285064190008936025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362423046752253345248033 271817285064190008936025)
      ·
        refine ⟨203862963798142506702019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271817285064190008936025 203862963798142506702019)
        ·
          refine ⟨305794445697213760053029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203862963798142506702019 305794445697213760053029)
          ·
            refine ⟨57336458568227580009943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 305794445697213760053029 57336458568227580009943)
            ·
              refine ⟨86004687852341370014915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57336458568227580009943 86004687852341370014915)
              ·
                refine ⟨129007031778512055022373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86004687852341370014915 129007031778512055022373)
                ·
                  refine ⟨24188818458471010316695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129007031778512055022373 24188818458471010316695)
                  ·
                    rfl

theorem cell20_52996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_52996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52996 prefixEnd_52996 := by exact prefixLift 52996
  have htrace : WordTrace (prefixWord ++ tailWord_52996) baseStart_52996 baseEnd_52996 := by
    simpa [prefixWord, tailWord_52996, baseEnd_52996] using wordTrace_append hprefix tailTrace_52996
  have hstable : (prefixWord ++ tailWord_52996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52996).length < 2 ^ (prefixWord ++ tailWord_52996).sum := by decide
  have hdescent : baseEnd_52996 < baseStart_52996 := by decide
  rcases family_descends (prefixWord ++ tailWord_52996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_52998 : List Nat := [6, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_52998 : Nat := 118140960795 + 52998 * 2 ^ 59
def prefixEnd_52998 : Nat := 4983230072969 + 3 ^ 40 * 52998 * 2
def baseEnd_52998 : Nat := 24189731312967892250021

theorem tailTrace_52998 : CollatzResearch.WordTrace tailWord_52998 prefixEnd_52998 24189731312967892250021 := by
  unfold tailWord_52998
  simp only [CollatzResearch.WordTrace]
  refine ⟨60406120687649130715489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1288663908003181455263765 60406120687649130715489)
  ·
    refine ⟨45304590515736848036617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60406120687649130715489 45304590515736848036617)
    ·
      refine ⟨33978442886802636027463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45304590515736848036617 33978442886802636027463)
      ·
        refine ⟨50967664330203954041195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33978442886802636027463 50967664330203954041195)
        ·
          refine ⟨76451496495305931061793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50967664330203954041195 76451496495305931061793)
          ·
            refine ⟨57338622371479448296345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76451496495305931061793 57338622371479448296345)
            ·
              refine ⟨43003966778609586222259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57338622371479448296345 43003966778609586222259)
              ·
                refine ⟨64505950167914379333389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43003966778609586222259 64505950167914379333389)
                ·
                  refine ⟨24189731312967892250021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64505950167914379333389 24189731312967892250021)
                  ·
                    rfl

theorem cell20_52998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_52998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_52998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_52998 prefixEnd_52998 := by exact prefixLift 52998
  have htrace : WordTrace (prefixWord ++ tailWord_52998) baseStart_52998 baseEnd_52998 := by
    simpa [prefixWord, tailWord_52998, baseEnd_52998] using wordTrace_append hprefix tailTrace_52998
  have hstable : (prefixWord ++ tailWord_52998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_52998).length < 2 ^ (prefixWord ++ tailWord_52998).sum := by decide
  have hdescent : baseEnd_52998 < baseStart_52998 := by decide
  rcases family_descends (prefixWord ++ tailWord_52998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53045 : List Nat := [1, 3, 3, 1, 12]
def baseStart_53045 : Nat := 118140960795 + 53045 * 2 ^ 59
def prefixEnd_53045 : Nat := 4983230072969 + 3 ^ 40 * 53045 * 2
def baseEnd_53045 : Nat := 298903498686970588681

theorem tailTrace_53045 : CollatzResearch.WordTrace tailWord_53045 prefixEnd_53045 298903498686970588681 := by
  unfold tailWord_53045
  simp only [CollatzResearch.WordTrace]
  refine ⟨1934710092834499209856589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1289806728556332806571059 1934710092834499209856589)
  ·
    refine ⟨725516284812937203696221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1934710092834499209856589 725516284812937203696221)
    ·
      refine ⟨272068606804851451386083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 725516284812937203696221 272068606804851451386083)
      ·
        refine ⟨408102910207277177079125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272068606804851451386083 408102910207277177079125)
        ·
          refine ⟨298903498686970588681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 408102910207277177079125 298903498686970588681)
          ·
            rfl

theorem cell20_53045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 12].length) (baseStart_53045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53045 prefixEnd_53045 := by exact prefixLift 53045
  have htrace : WordTrace (prefixWord ++ tailWord_53045) baseStart_53045 baseEnd_53045 := by
    simpa [prefixWord, tailWord_53045, baseEnd_53045] using wordTrace_append hprefix tailTrace_53045
  have hstable : (prefixWord ++ tailWord_53045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53045).length < 2 ^ (prefixWord ++ tailWord_53045).sum := by decide
  have hdescent : baseEnd_53045 < baseStart_53045 := by decide
  rcases family_descends (prefixWord ++ tailWord_53045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53048 : List Nat := [2, 1, 2, 1, 3, 4, 2, 2, 3]
def baseStart_53048 : Nat := 118140960795 + 53048 * 2 ^ 59
def prefixEnd_53048 : Nat := 4983230072969 + 3 ^ 40 * 53048 * 2
def baseEnd_53048 : Nat := 24212552675389940583149

theorem tailTrace_53048 : CollatzResearch.WordTrace tailWord_53048 prefixEnd_53048 24212552675389940583149 := by
  unfold tailWord_53048
  simp only [CollatzResearch.WordTrace]
  refine ⟨967409755911815361107899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1289879674549087148143865 967409755911815361107899)
  ·
    refine ⟨1451114633867723041661849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 967409755911815361107899 1451114633867723041661849)
    ·
      refine ⟨1088335975400792281246387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1451114633867723041661849 1088335975400792281246387)
      ·
        refine ⟨1632503963101188421869581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1088335975400792281246387 1632503963101188421869581)
        ·
          refine ⟨612188986162945658201093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1632503963101188421869581 612188986162945658201093)
          ·
            refine ⟨114785434905552310912705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 612188986162945658201093 114785434905552310912705)
            ·
              refine ⟨86089076179164233184529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114785434905552310912705 86089076179164233184529)
              ·
                refine ⟨64566807134373174888397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86089076179164233184529 64566807134373174888397)
                ·
                  refine ⟨24212552675389940583149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64566807134373174888397 24212552675389940583149)
                  ·
                    rfl

theorem cell20_53048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_53048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53048 prefixEnd_53048 := by exact prefixLift 53048
  have htrace : WordTrace (prefixWord ++ tailWord_53048) baseStart_53048 baseEnd_53048 := by
    simpa [prefixWord, tailWord_53048, baseEnd_53048] using wordTrace_append hprefix tailTrace_53048
  have hstable : (prefixWord ++ tailWord_53048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53048).length < 2 ^ (prefixWord ++ tailWord_53048).sum := by decide
  have hdescent : baseEnd_53048 < baseStart_53048 := by decide
  rcases family_descends (prefixWord ++ tailWord_53048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53079 : List Nat := [1, 1, 3, 2, 5, 1, 3, 4]
def baseStart_53079 : Nat := 118140960795 + 53079 * 2 ^ 59
def prefixEnd_53079 : Nat := 4983230072969 + 3 ^ 40 * 53079 * 2
def baseEnd_53079 : Nat := 8075567306697203516563

theorem tailTrace_53079 : CollatzResearch.WordTrace tailWord_53079 prefixEnd_53079 8075567306697203516563 := by
  unfold tailWord_53079
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935950174711323016594291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1290633449807548677729527 1935950174711323016594291)
  ·
    refine ⟨2903925262066984524891437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1935950174711323016594291 2903925262066984524891437)
    ·
      refine ⟨1088971973275119196834289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2903925262066984524891437 1088971973275119196834289)
      ·
        refine ⟨816728979956339397625717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1088971973275119196834289 816728979956339397625717)
        ·
          refine ⟨76568341870906818527411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 816728979956339397625717 76568341870906818527411)
          ·
            refine ⟨114852512806360227791117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76568341870906818527411 114852512806360227791117)
            ·
              refine ⟨43069692302385085421669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114852512806360227791117 43069692302385085421669)
              ·
                refine ⟨8075567306697203516563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43069692302385085421669 8075567306697203516563)
                ·
                  rfl

theorem cell20_53079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 4].length) (baseStart_53079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53079 prefixEnd_53079 := by exact prefixLift 53079
  have htrace : WordTrace (prefixWord ++ tailWord_53079) baseStart_53079 baseEnd_53079 := by
    simpa [prefixWord, tailWord_53079, baseEnd_53079] using wordTrace_append hprefix tailTrace_53079
  have hstable : (prefixWord ++ tailWord_53079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53079).length < 2 ^ (prefixWord ++ tailWord_53079).sum := by decide
  have hdescent : baseEnd_53079 < baseStart_53079 := by decide
  rcases family_descends (prefixWord ++ tailWord_53079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53114 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_53114 : Nat := 118140960795 + 53114 * 2 ^ 59
def prefixEnd_53114 : Nat := 4983230072969 + 3 ^ 40 * 53114 * 2
def baseEnd_53114 : Nat := 24242676873787044382879

theorem tailTrace_53114 : CollatzResearch.WordTrace tailWord_53114 prefixEnd_53114 24242676873787044382879 := by
  unfold tailWord_53114
  simp only [CollatzResearch.WordTrace]
  refine ⟨484306682396130998529599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1291484486389682662745597 484306682396130998529599)
  ·
    refine ⟨726460023594196497794399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 484306682396130998529599 726460023594196497794399)
    ·
      refine ⟨1089690035391294746691599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726460023594196497794399 1089690035391294746691599)
      ·
        refine ⟨1634535053086942120037399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1089690035391294746691599 1634535053086942120037399)
        ·
          refine ⟨2451802579630413180056099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1634535053086942120037399 2451802579630413180056099)
          ·
            refine ⟨3677703869445619770084149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2451802579630413180056099 3677703869445619770084149)
            ·
              refine ⟨344784737760526853445389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3677703869445619770084149 344784737760526853445389)
              ·
                refine ⟨129294276660197570042021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344784737760526853445389 129294276660197570042021)
                ·
                  refine ⟨24242676873787044382879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129294276660197570042021 24242676873787044382879)
                  ·
                    rfl

theorem cell20_53114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_53114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53114 prefixEnd_53114 := by exact prefixLift 53114
  have htrace : WordTrace (prefixWord ++ tailWord_53114) baseStart_53114 baseEnd_53114 := by
    simpa [prefixWord, tailWord_53114, baseEnd_53114] using wordTrace_append hprefix tailTrace_53114
  have hstable : (prefixWord ++ tailWord_53114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53114).length < 2 ^ (prefixWord ++ tailWord_53114).sum := by decide
  have hdescent : baseEnd_53114 < baseStart_53114 := by decide
  rcases family_descends (prefixWord ++ tailWord_53114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53144 : List Nat := [2, 1, 2, 6, 1, 2, 1, 3, 2]
def baseStart_53144 : Nat := 118140960795 + 53144 * 2 ^ 59
def prefixEnd_53144 : Nat := 4983230072969 + 3 ^ 40 * 53144 * 2
def baseEnd_53144 : Nat := 24256369691240273382757

theorem tailTrace_53144 : CollatzResearch.WordTrace tailWord_53144 prefixEnd_53144 24256369691240273382757 := by
  unfold tailWord_53144
  simp only [CollatzResearch.WordTrace]
  refine ⟨969160459737919558855243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1292213946317226078473657 969160459737919558855243)
  ·
    refine ⟨1453740689606879338282865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 969160459737919558855243 1453740689606879338282865)
    ·
      refine ⟨1090305517205159503712149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1453740689606879338282865 1090305517205159503712149)
      ·
        refine ⟨51108071118991851736507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1090305517205159503712149 51108071118991851736507)
        ·
          refine ⟨76662106678487777604761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51108071118991851736507 76662106678487777604761)
          ·
            refine ⟨57496580008865833203571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76662106678487777604761 57496580008865833203571)
            ·
              refine ⟨86244870013298749805357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57496580008865833203571 86244870013298749805357)
              ·
                refine ⟨32341826254987031177009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86244870013298749805357 32341826254987031177009)
                ·
                  refine ⟨24256369691240273382757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32341826254987031177009 24256369691240273382757)
                  ·
                    rfl

theorem cell20_53144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 2].length) (baseStart_53144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53144 prefixEnd_53144 := by exact prefixLift 53144
  have htrace : WordTrace (prefixWord ++ tailWord_53144) baseStart_53144 baseEnd_53144 := by
    simpa [prefixWord, tailWord_53144, baseEnd_53144] using wordTrace_append hprefix tailTrace_53144
  have hstable : (prefixWord ++ tailWord_53144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53144).length < 2 ^ (prefixWord ++ tailWord_53144).sum := by decide
  have hdescent : baseEnd_53144 < baseStart_53144 := by decide
  rcases family_descends (prefixWord ++ tailWord_53144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53169 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 4]
def baseStart_53169 : Nat := 118140960795 + 53169 * 2 ^ 59
def prefixEnd_53169 : Nat := 4983230072969 + 3 ^ 40 * 53169 * 2
def baseEnd_53169 : Nat := 24267780372451297549321

theorem tailTrace_53169 : CollatzResearch.WordTrace tailWord_53169 prefixEnd_53169 24267780372451297549321 := by
  unfold tailWord_53169
  simp only [CollatzResearch.WordTrace]
  refine ⟨1939232744385268387370561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1292821829590178924913707 1939232744385268387370561)
  ·
    refine ⟨1454424558288951290527921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1939232744385268387370561 1454424558288951290527921)
    ·
      refine ⟨1090818418716713467895941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1454424558288951290527921 1090818418716713467895941)
      ·
        refine ⟨204528453509383775230489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1090818418716713467895941 204528453509383775230489)
        ·
          refine ⟨153396340132037831422867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204528453509383775230489 153396340132037831422867)
          ·
            refine ⟨230094510198056747134301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153396340132037831422867 230094510198056747134301)
            ·
              refine ⟨86285441324271280175363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230094510198056747134301 86285441324271280175363)
              ·
                refine ⟨129428161986406920263045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86285441324271280175363 129428161986406920263045)
                ·
                  refine ⟨24267780372451297549321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129428161986406920263045 24267780372451297549321)
                  ·
                    rfl

theorem cell20_53169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_53169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53169 prefixEnd_53169 := by exact prefixLift 53169
  have htrace : WordTrace (prefixWord ++ tailWord_53169) baseStart_53169 baseEnd_53169 := by
    simpa [prefixWord, tailWord_53169, baseEnd_53169] using wordTrace_append hprefix tailTrace_53169
  have hstable : (prefixWord ++ tailWord_53169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53169).length < 2 ^ (prefixWord ++ tailWord_53169).sum := by decide
  have hdescent : baseEnd_53169 < baseStart_53169 := by decide
  rcases family_descends (prefixWord ++ tailWord_53169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53172 : List Nat := [2, 5, 2, 1, 2, 1, 2, 5]
def baseStart_53172 : Nat := 118140960795 + 53172 * 2 ^ 59
def prefixEnd_53172 : Nat := 4983230072969 + 3 ^ 40 * 53172 * 2
def baseEnd_53172 : Nat := 8089716551398873483103

theorem tailTrace_53172 : CollatzResearch.WordTrace tailWord_53172 prefixEnd_53172 8089716551398873483103 := by
  unfold tailWord_53172
  simp only [CollatzResearch.WordTrace]
  refine ⟨969671081687199949864885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1292894775582933266486513 969671081687199949864885)
  ·
    refine ⟨90906663908174995299833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 969671081687199949864885 90906663908174995299833)
    ·
      refine ⟨68179997931131246474875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90906663908174995299833 68179997931131246474875)
      ·
        refine ⟨102269996896696869712313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68179997931131246474875 102269996896696869712313)
        ·
          refine ⟨76702497672522652284235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102269996896696869712313 76702497672522652284235)
          ·
            refine ⟨115053746508783978426353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76702497672522652284235 115053746508783978426353)
            ·
              refine ⟨86290309881587983819765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115053746508783978426353 86290309881587983819765)
              ·
                refine ⟨8089716551398873483103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86290309881587983819765 8089716551398873483103)
                ·
                  rfl

theorem cell20_53172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_53172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53172 prefixEnd_53172 := by exact prefixLift 53172
  have htrace : WordTrace (prefixWord ++ tailWord_53172) baseStart_53172 baseEnd_53172 := by
    simpa [prefixWord, tailWord_53172, baseEnd_53172] using wordTrace_append hprefix tailTrace_53172
  have hstable : (prefixWord ++ tailWord_53172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53172).length < 2 ^ (prefixWord ++ tailWord_53172).sum := by decide
  have hdescent : baseEnd_53172 < baseStart_53172 := by decide
  rcases family_descends (prefixWord ++ tailWord_53172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53183 : List Nat := [1, 1, 2, 2, 2, 1, 5, 3, 3]
def baseStart_53183 : Nat := 118140960795 + 53183 * 2 ^ 59
def prefixEnd_53183 : Nat := 4983230072969 + 3 ^ 40 * 53183 * 2
def baseEnd_53183 : Nat := 24274170353929471082597

theorem tailTrace_53183 : CollatzResearch.WordTrace tailWord_53183 prefixEnd_53183 24274170353929471082597 := by
  unfold tailWord_53183
  simp only [CollatzResearch.WordTrace]
  refine ⟨1939743366334548778380203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1293162244223032518920135 1939743366334548778380203)
  ·
    refine ⟨2909615049501823167570305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1939743366334548778380203 2909615049501823167570305)
    ·
      refine ⟨2182211287126367375677729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2909615049501823167570305 2182211287126367375677729)
      ·
        refine ⟨1636658465344775531758297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2182211287126367375677729 1636658465344775531758297)
        ·
          refine ⟨1227493849008581648818723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1636658465344775531758297 1227493849008581648818723)
          ·
            refine ⟨1841240773512872473228085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227493849008581648818723 1841240773512872473228085)
            ·
              refine ⟨172616322516831794365133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1841240773512872473228085 172616322516831794365133)
              ·
                refine ⟨64731120943811922886925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172616322516831794365133 64731120943811922886925)
                ·
                  refine ⟨24274170353929471082597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64731120943811922886925 24274170353929471082597)
                  ·
                    rfl

theorem cell20_53183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 3].length) (baseStart_53183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53183 prefixEnd_53183 := by exact prefixLift 53183
  have htrace : WordTrace (prefixWord ++ tailWord_53183) baseStart_53183 baseEnd_53183 := by
    simpa [prefixWord, tailWord_53183, baseEnd_53183] using wordTrace_append hprefix tailTrace_53183
  have hstable : (prefixWord ++ tailWord_53183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53183).length < 2 ^ (prefixWord ++ tailWord_53183).sum := by decide
  have hdescent : baseEnd_53183 < baseStart_53183 := by decide
  rcases family_descends (prefixWord ++ tailWord_53183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53207 : List Nat := [1, 1, 3, 2, 1, 1, 4, 5, 2]
def baseStart_53207 : Nat := 118140960795 + 53207 * 2 ^ 59
def prefixEnd_53207 : Nat := 4983230072969 + 3 ^ 40 * 53207 * 2
def baseEnd_53207 : Nat := 24285124607892054282499

theorem tailTrace_53207 : CollatzResearch.WordTrace tailWord_53207 prefixEnd_53207 24285124607892054282499 := by
  unfold tailWord_53207
  simp only [CollatzResearch.WordTrace]
  refine ⟨1940618718247600877253875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1293745812165067251502583 1940618718247600877253875)
  ·
    refine ⟨2910928077371401315880813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1940618718247600877253875 2910928077371401315880813)
    ·
      refine ⟨1091598029014275493455305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2910928077371401315880813 1091598029014275493455305)
      ·
        refine ⟨818698521760706620091479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1091598029014275493455305 818698521760706620091479)
        ·
          refine ⟨1228047782641059930137219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818698521760706620091479 1228047782641059930137219)
          ·
            refine ⟨1842071673961589895205829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228047782641059930137219 1842071673961589895205829)
            ·
              refine ⟨345388438867798105351093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1842071673961589895205829 345388438867798105351093)
              ·
                refine ⟨32380166143856072376665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 345388438867798105351093 32380166143856072376665)
                ·
                  refine ⟨24285124607892054282499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32380166143856072376665 24285124607892054282499)
                  ·
                    rfl

theorem cell20_53207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 2].length) (baseStart_53207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53207 prefixEnd_53207 := by exact prefixLift 53207
  have htrace : WordTrace (prefixWord ++ tailWord_53207) baseStart_53207 baseEnd_53207 := by
    simpa [prefixWord, tailWord_53207, baseEnd_53207] using wordTrace_append hprefix tailTrace_53207
  have hstable : (prefixWord ++ tailWord_53207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53207).length < 2 ^ (prefixWord ++ tailWord_53207).sum := by decide
  have hdescent : baseEnd_53207 < baseStart_53207 := by decide
  rcases family_descends (prefixWord ++ tailWord_53207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53242 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_53242 : Nat := 118140960795 + 53242 * 2 ^ 59
def prefixEnd_53242 : Nat := 4983230072969 + 3 ^ 40 * 53242 * 2
def baseEnd_53242 : Nat := 24301099561587488115689

theorem tailTrace_53242 : CollatzResearch.WordTrace tailWord_53242 prefixEnd_53242 24301099561587488115689 := by
  unfold tailWord_53242
  simp only [CollatzResearch.WordTrace]
  refine ⟨485473818280200463694495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1294596848747201236518653 485473818280200463694495)
  ·
    refine ⟨728210727420300695541743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 485473818280200463694495 728210727420300695541743)
    ·
      refine ⟨1092316091130451043312615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 728210727420300695541743 1092316091130451043312615)
      ·
        refine ⟨1638474136695676564968923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092316091130451043312615 1638474136695676564968923)
        ·
          refine ⟨2457711205043514847453385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638474136695676564968923 2457711205043514847453385)
          ·
            refine ⟨1843283403782636135590039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2457711205043514847453385 1843283403782636135590039)
            ·
              refine ⟨2764925105673954203385059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1843283403782636135590039 2764925105673954203385059)
              ·
                refine ⟨4147387658510931305077589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2764925105673954203385059 4147387658510931305077589)
                ·
                  refine ⟨24301099561587488115689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4147387658510931305077589 24301099561587488115689)
                  ·
                    rfl

theorem cell20_53242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_53242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53242 prefixEnd_53242 := by exact prefixLift 53242
  have htrace : WordTrace (prefixWord ++ tailWord_53242) baseStart_53242 baseEnd_53242 := by
    simpa [prefixWord, tailWord_53242, baseEnd_53242] using wordTrace_append hprefix tailTrace_53242
  have hstable : (prefixWord ++ tailWord_53242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53242).length < 2 ^ (prefixWord ++ tailWord_53242).sum := by decide
  have hdescent : baseEnd_53242 < baseStart_53242 := by decide
  rcases family_descends (prefixWord ++ tailWord_53242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53254 : List Nat := [6, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_53254 : Nat := 118140960795 + 53254 * 2 ^ 59
def prefixEnd_53254 : Nat := 4983230072969 + 3 ^ 40 * 53254 * 2
def baseEnd_53254 : Nat := 24306576688568779715641

theorem tailTrace_53254 : CollatzResearch.WordTrace tailWord_53254 prefixEnd_53254 24306576688568779715641 := by
  unfold tailWord_53254
  simp only [CollatzResearch.WordTrace]
  refine ⟨60697904658666497006713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1294888632718218602809877 60697904658666497006713)
  ·
    refine ⟨45523428493999872755035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60697904658666497006713 45523428493999872755035)
    ·
      refine ⟨68285142740999809132553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45523428493999872755035 68285142740999809132553)
      ·
        refine ⟨51213857055749856849415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68285142740999809132553 51213857055749856849415)
        ·
          refine ⟨76820785583624785274123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51213857055749856849415 76820785583624785274123)
          ·
            refine ⟨115231178375437177911185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76820785583624785274123 115231178375437177911185)
            ·
              refine ⟨86423383781577883433389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115231178375437177911185 86423383781577883433389)
              ·
                refine ⟨32408768918091706287521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86423383781577883433389 32408768918091706287521)
                ·
                  refine ⟨24306576688568779715641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32408768918091706287521 24306576688568779715641)
                  ·
                    rfl

theorem cell20_53254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_53254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53254 prefixEnd_53254 := by exact prefixLift 53254
  have htrace : WordTrace (prefixWord ++ tailWord_53254) baseStart_53254 baseEnd_53254 := by
    simpa [prefixWord, tailWord_53254, baseEnd_53254] using wordTrace_append hprefix tailTrace_53254
  have hstable : (prefixWord ++ tailWord_53254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53254).length < 2 ^ (prefixWord ++ tailWord_53254).sum := by decide
  have hdescent : baseEnd_53254 < baseStart_53254 := by decide
  rcases family_descends (prefixWord ++ tailWord_53254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53262 : List Nat := [4, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_53262 : Nat := 118140960795 + 53262 * 2 ^ 59
def prefixEnd_53262 : Nat := 4983230072969 + 3 ^ 40 * 53262 * 2
def baseEnd_53262 : Nat := 24310228106556307448941

theorem tailTrace_53262 : CollatzResearch.WordTrace tailWord_53262 prefixEnd_53262 24310228106556307448941 := by
  unfold tailWord_53262
  simp only [CollatzResearch.WordTrace]
  refine ⟨242828091631043158813255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1295083155365563513670693 242828091631043158813255)
  ·
    refine ⟨364242137446564738219883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242828091631043158813255 364242137446564738219883)
    ·
      refine ⟨546363206169847107329825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364242137446564738219883 546363206169847107329825)
      ·
        refine ⟨409772404627385330497369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546363206169847107329825 409772404627385330497369)
        ·
          refine ⟨307329303470538997873027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409772404627385330497369 307329303470538997873027)
          ·
            refine ⟨460993955205808496809541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307329303470538997873027 460993955205808496809541)
            ·
              refine ⟨86436366601089093151789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 460993955205808496809541 86436366601089093151789)
              ·
                refine ⟨32413637475408409931921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86436366601089093151789 32413637475408409931921)
                ·
                  refine ⟨24310228106556307448941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32413637475408409931921 24310228106556307448941)
                  ·
                    rfl

theorem cell20_53262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_53262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53262 prefixEnd_53262 := by exact prefixLift 53262
  have htrace : WordTrace (prefixWord ++ tailWord_53262) baseStart_53262 baseEnd_53262 := by
    simpa [prefixWord, tailWord_53262, baseEnd_53262] using wordTrace_append hprefix tailTrace_53262
  have hstable : (prefixWord ++ tailWord_53262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53262).length < 2 ^ (prefixWord ++ tailWord_53262).sum := by decide
  have hdescent : baseEnd_53262 < baseStart_53262 := by decide
  rcases family_descends (prefixWord ++ tailWord_53262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53276 : List Nat := [2, 2, 3, 1, 3, 1, 3, 2, 3]
def baseStart_53276 : Nat := 118140960795 + 53276 * 2 ^ 59
def prefixEnd_53276 : Nat := 4983230072969 + 3 ^ 40 * 53276 * 2
def baseEnd_53276 : Nat := 24316618088034480982217

theorem tailTrace_53276 : CollatzResearch.WordTrace tailWord_53276 prefixEnd_53276 24316618088034480982217 := by
  unfold tailWord_53276
  simp only [CollatzResearch.WordTrace]
  refine ⟨971567677498812830757841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1295423569998417107677121 971567677498812830757841)
  ·
    refine ⟨728675758124109623068381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 971567677498812830757841 728675758124109623068381)
    ·
      refine ⟨273253409296541108650643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 728675758124109623068381 273253409296541108650643)
      ·
        refine ⟨409880113944811662975965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273253409296541108650643 409880113944811662975965)
        ·
          refine ⟨153705042729304373615987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409880113944811662975965 153705042729304373615987)
          ·
            refine ⟨230557564093956560423981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153705042729304373615987 230557564093956560423981)
            ·
              refine ⟨86459086535233710158993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230557564093956560423981 86459086535233710158993)
              ·
                refine ⟨64844314901425282619245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86459086535233710158993 64844314901425282619245)
                ·
                  refine ⟨24316618088034480982217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64844314901425282619245 24316618088034480982217)
                  ·
                    rfl

theorem cell20_53276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_53276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53276 prefixEnd_53276 := by exact prefixLift 53276
  have htrace : WordTrace (prefixWord ++ tailWord_53276) baseStart_53276 baseEnd_53276 := by
    simpa [prefixWord, tailWord_53276, baseEnd_53276] using wordTrace_append hprefix tailTrace_53276
  have hstable : (prefixWord ++ tailWord_53276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53276).length < 2 ^ (prefixWord ++ tailWord_53276).sum := by decide
  have hdescent : baseEnd_53276 < baseStart_53276 := by decide
  rcases family_descends (prefixWord ++ tailWord_53276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53283 : List Nat := [1, 1, 1, 4, 3, 1, 1, 6, 2]
def baseStart_53283 : Nat := 118140960795 + 53283 * 2 ^ 59
def prefixEnd_53283 : Nat := 4983230072969 + 3 ^ 40 * 53283 * 2
def baseEnd_53283 : Nat := 24319813078773567748855

theorem tailTrace_53283 : CollatzResearch.WordTrace tailWord_53283 prefixEnd_53283 24319813078773567748855 := by
  unfold tailWord_53283
  simp only [CollatzResearch.WordTrace]
  refine ⟨1943390665972265857020503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1295593777314843904680335 1943390665972265857020503)
  ·
    refine ⟨2915085998958398785530755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1943390665972265857020503 2915085998958398785530755)
    ·
      refine ⟨4372628998437598178296133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2915085998958398785530755 4372628998437598178296133)
      ·
        refine ⟨819867937207049658430525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4372628998437598178296133 819867937207049658430525)
        ·
          refine ⟨307450476452643621911447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 819867937207049658430525 307450476452643621911447)
          ·
            refine ⟨461175714678965432867171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307450476452643621911447 461175714678965432867171)
            ·
              refine ⟨691763572018448149300757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461175714678965432867171 691763572018448149300757)
              ·
                refine ⟨32426417438364756998473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 691763572018448149300757 32426417438364756998473)
                ·
                  refine ⟨24319813078773567748855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32426417438364756998473 24319813078773567748855)
                  ·
                    rfl

theorem cell20_53283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 2].length) (baseStart_53283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53283 prefixEnd_53283 := by exact prefixLift 53283
  have htrace : WordTrace (prefixWord ++ tailWord_53283) baseStart_53283 baseEnd_53283 := by
    simpa [prefixWord, tailWord_53283, baseEnd_53283] using wordTrace_append hprefix tailTrace_53283
  have hstable : (prefixWord ++ tailWord_53283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53283).length < 2 ^ (prefixWord ++ tailWord_53283).sum := by decide
  have hdescent : baseEnd_53283 < baseStart_53283 := by decide
  rcases family_descends (prefixWord ++ tailWord_53283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53338 : List Nat := [3, 1, 1, 2, 1, 1, 7, 2, 2]
def baseStart_53338 : Nat := 118140960795 + 53338 * 2 ^ 59
def prefixEnd_53338 : Nat := 4983230072969 + 3 ^ 40 * 53338 * 2
def baseEnd_53338 : Nat := 24344916577437820915297

theorem tailTrace_53338 : CollatzResearch.WordTrace tailWord_53338 prefixEnd_53338 24344916577437820915297 := by
  unfold tailWord_53338
  simp only [CollatzResearch.WordTrace]
  refine ⟨486349170193252562568167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1296931120515340166848445 486349170193252562568167)
  ·
    refine ⟨729523755289878843852251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 486349170193252562568167 729523755289878843852251)
    ·
      refine ⟨1094285632934818265778377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 729523755289878843852251 1094285632934818265778377)
      ·
        refine ⟨820714224701113699333783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1094285632934818265778377 820714224701113699333783)
        ·
          refine ⟨1231071337051670549000675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820714224701113699333783 1231071337051670549000675)
          ·
            refine ⟨1846607005577505823501013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231071337051670549000675 1846607005577505823501013)
            ·
              refine ⟨43279851693222792738305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1846607005577505823501013 43279851693222792738305)
              ·
                refine ⟨32459888769917094553729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43279851693222792738305 32459888769917094553729)
                ·
                  refine ⟨24344916577437820915297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32459888769917094553729 24344916577437820915297)
                  ·
                    rfl

theorem cell20_53338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_53338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53338 prefixEnd_53338 := by exact prefixLift 53338
  have htrace : WordTrace (prefixWord ++ tailWord_53338) baseStart_53338 baseEnd_53338 := by
    simpa [prefixWord, tailWord_53338, baseEnd_53338] using wordTrace_append hprefix tailTrace_53338
  have hstable : (prefixWord ++ tailWord_53338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53338).length < 2 ^ (prefixWord ++ tailWord_53338).sum := by decide
  have hdescent : baseEnd_53338 < baseStart_53338 := by decide
  rcases family_descends (prefixWord ++ tailWord_53338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53349 : List Nat := [1, 3, 1, 3, 2, 2, 1, 7]
def baseStart_53349 : Nat := 118140960795 + 53349 * 2 ^ 59
def prefixEnd_53349 : Nat := 4983230072969 + 3 ^ 40 * 53349 * 2
def baseEnd_53349 : Nat := 8116645759056890516195

theorem tailTrace_53349 : CollatzResearch.WordTrace tailWord_53349 prefixEnd_53349 8116645759056890516195 := by
  unfold tailWord_53349
  simp only [CollatzResearch.WordTrace]
  refine ⟨1945797883733159128923101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1297198589155439419282067 1945797883733159128923101)
  ·
    refine ⟨729674206399934673346163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1945797883733159128923101 729674206399934673346163)
    ·
      refine ⟨1094511309599902010019245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 729674206399934673346163 1094511309599902010019245)
      ·
        refine ⟨410441741099963253757217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1094511309599902010019245 410441741099963253757217)
        ·
          refine ⟨307831305824972440317913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410441741099963253757217 307831305824972440317913)
          ·
            refine ⟨230873479368729330238435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307831305824972440317913 230873479368729330238435)
            ·
              refine ⟨346310219053093995357653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230873479368729330238435 346310219053093995357653)
              ·
                refine ⟨8116645759056890516195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 346310219053093995357653 8116645759056890516195)
                ·
                  rfl

theorem cell20_53349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 7].length) (baseStart_53349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53349 prefixEnd_53349 := by exact prefixLift 53349
  have htrace : WordTrace (prefixWord ++ tailWord_53349) baseStart_53349 baseEnd_53349 := by
    simpa [prefixWord, tailWord_53349, baseEnd_53349] using wordTrace_append hprefix tailTrace_53349
  have hstable : (prefixWord ++ tailWord_53349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53349).length < 2 ^ (prefixWord ++ tailWord_53349).sum := by decide
  have hdescent : baseEnd_53349 < baseStart_53349 := by decide
  rcases family_descends (prefixWord ++ tailWord_53349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53366 : List Nat := [5, 1, 1, 2, 1, 2, 2, 6]
def baseStart_53366 : Nat := 118140960795 + 53366 * 2 ^ 59
def prefixEnd_53366 : Nat := 4983230072969 + 3 ^ 40 * 53366 * 2
def baseEnd_53366 : Nat := 8119232180131389327283

theorem tailTrace_53366 : CollatzResearch.WordTrace tailWord_53366 prefixEnd_53366 8119232180131389327283 := by
  unfold tailWord_53366
  simp only [CollatzResearch.WordTrace]
  refine ⟨121651120291973189518247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1297611949781047354861301 121651120291973189518247)
  ·
    refine ⟨182476680437959784277371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121651120291973189518247 182476680437959784277371)
    ·
      refine ⟨273715020656939676416057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182476680437959784277371 273715020656939676416057)
      ·
        refine ⟨205286265492704757312043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273715020656939676416057 205286265492704757312043)
        ·
          refine ⟨307929398239057135968065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205286265492704757312043 307929398239057135968065)
          ·
            refine ⟨230947048679292851976049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307929398239057135968065 230947048679292851976049)
            ·
              refine ⟨173210286509469638982037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230947048679292851976049 173210286509469638982037)
              ·
                refine ⟨8119232180131389327283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173210286509469638982037 8119232180131389327283)
                ·
                  rfl

theorem cell20_53366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_53366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53366 prefixEnd_53366 := by exact prefixLift 53366
  have htrace : WordTrace (prefixWord ++ tailWord_53366) baseStart_53366 baseEnd_53366 := by
    simpa [prefixWord, tailWord_53366, baseEnd_53366] using wordTrace_append hprefix tailTrace_53366
  have hstable : (prefixWord ++ tailWord_53366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53366).length < 2 ^ (prefixWord ++ tailWord_53366).sum := by decide
  have hdescent : baseEnd_53366 < baseStart_53366 := by decide
  rcases family_descends (prefixWord ++ tailWord_53366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53397 : List Nat := [1, 3, 2, 1, 1, 1, 5, 4, 2]
def baseStart_53397 : Nat := 118140960795 + 53397 * 2 ^ 59
def prefixEnd_53397 : Nat := 4983230072969 + 3 ^ 40 * 53397 * 2
def baseEnd_53397 : Nat := 24371845785095837948389

theorem tailTrace_53397 : CollatzResearch.WordTrace tailWord_53397 prefixEnd_53397 24371845785095837948389 := by
  unfold tailWord_53397
  simp only [CollatzResearch.WordTrace]
  refine ⟨1947548587559263326670445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1298365725039508884446963 1947548587559263326670445)
  ·
    refine ⟨730330720334723747501417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1947548587559263326670445 730330720334723747501417)
    ·
      refine ⟨547748040251042810626063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 730330720334723747501417 547748040251042810626063)
      ·
        refine ⟨821622060376564215939095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547748040251042810626063 821622060376564215939095)
        ·
          refine ⟨1232433090564846323908643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821622060376564215939095 1232433090564846323908643)
          ·
            refine ⟨1848649635847269485862965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232433090564846323908643 1848649635847269485862965)
            ·
              refine ⟨173310903360681514299653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1848649635847269485862965 173310903360681514299653)
              ·
                refine ⟨32495794380127783931185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173310903360681514299653 32495794380127783931185)
                ·
                  refine ⟨24371845785095837948389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32495794380127783931185 24371845785095837948389)
                  ·
                    rfl

theorem cell20_53397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_53397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53397 prefixEnd_53397 := by exact prefixLift 53397
  have htrace : WordTrace (prefixWord ++ tailWord_53397) baseStart_53397 baseEnd_53397 := by
    simpa [prefixWord, tailWord_53397, baseEnd_53397] using wordTrace_append hprefix tailTrace_53397
  have hstable : (prefixWord ++ tailWord_53397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53397).length < 2 ^ (prefixWord ++ tailWord_53397).sum := by decide
  have hdescent : baseEnd_53397 < baseStart_53397 := by decide
  rcases family_descends (prefixWord ++ tailWord_53397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53401 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 8]
def baseStart_53401 : Nat := 118140960795 + 53401 * 2 ^ 59
def prefixEnd_53401 : Nat := 4983230072969 + 3 ^ 40 * 53401 * 2
def baseEnd_53401 : Nat := 24373671494089601815039

theorem tailTrace_53401 : CollatzResearch.WordTrace tailWord_53401 prefixEnd_53401 24373671494089601815039 := by
  unfold tailWord_53401
  simp only [CollatzResearch.WordTrace]
  refine ⟨1947694479544772009816057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1298462986363181339877371 1947694479544772009816057)
  ·
    refine ⟨1460770859658579007362043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1947694479544772009816057 1460770859658579007362043)
    ·
      refine ⟨2191156289487868511043065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1460770859658579007362043 2191156289487868511043065)
      ·
        refine ⟨1643367217115901383282299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2191156289487868511043065 1643367217115901383282299)
        ·
          refine ⟨2465050825673852074923449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643367217115901383282299 2465050825673852074923449)
          ·
            refine ⟨1848788119255389056192587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2465050825673852074923449 1848788119255389056192587)
            ·
              refine ⟨2773182178883083584288881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848788119255389056192587 2773182178883083584288881)
              ·
                refine ⟨2079886634162312688216661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2773182178883083584288881 2079886634162312688216661)
                ·
                  refine ⟨24373671494089601815039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2079886634162312688216661 24373671494089601815039)
                  ·
                    rfl

theorem cell20_53401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_53401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53401 prefixEnd_53401 := by exact prefixLift 53401
  have htrace : WordTrace (prefixWord ++ tailWord_53401) baseStart_53401 baseEnd_53401 := by
    simpa [prefixWord, tailWord_53401, baseEnd_53401] using wordTrace_append hprefix tailTrace_53401
  have hstable : (prefixWord ++ tailWord_53401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53401).length < 2 ^ (prefixWord ++ tailWord_53401).sum := by decide
  have hdescent : baseEnd_53401 < baseStart_53401 := by decide
  rcases family_descends (prefixWord ++ tailWord_53401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53421 : List Nat := [1, 5, 2, 1, 2, 2, 3, 4]
def baseStart_53421 : Nat := 118140960795 + 53421 * 2 ^ 59
def prefixEnd_53421 : Nat := 4983230072969 + 3 ^ 40 * 53421 * 2
def baseEnd_53421 : Nat := 8127600013019473716097

theorem tailTrace_53421 : CollatzResearch.WordTrace tailWord_53421 prefixEnd_53421 8127600013019473716097 := by
  unfold tailWord_53421
  simp only [CollatzResearch.WordTrace]
  refine ⟨1948423939472315425544117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1298949292981543617029411 1948423939472315425544117)
  ·
    refine ⟨182664744325529571144761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1948423939472315425544117 182664744325529571144761)
    ·
      refine ⟨136998558244147178358571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182664744325529571144761 136998558244147178358571)
      ·
        refine ⟨205497837366220767537857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136998558244147178358571 205497837366220767537857)
        ·
          refine ⟨154123378024665575653393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205497837366220767537857 154123378024665575653393)
          ·
            refine ⟨115592533518499181740045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154123378024665575653393 115592533518499181740045)
            ·
              refine ⟨43347200069437193152517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115592533518499181740045 43347200069437193152517)
              ·
                refine ⟨8127600013019473716097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43347200069437193152517 8127600013019473716097)
                ·
                  rfl

theorem cell20_53421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 4].length) (baseStart_53421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53421 prefixEnd_53421 := by exact prefixLift 53421
  have htrace : WordTrace (prefixWord ++ tailWord_53421) baseStart_53421 baseEnd_53421 := by
    simpa [prefixWord, tailWord_53421, baseEnd_53421] using wordTrace_append hprefix tailTrace_53421
  have hstable : (prefixWord ++ tailWord_53421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53421).length < 2 ^ (prefixWord ++ tailWord_53421).sum := by decide
  have hdescent : baseEnd_53421 < baseStart_53421 := by decide
  rcases family_descends (prefixWord ++ tailWord_53421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53432 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_53432 : Nat := 118140960795 + 53432 * 2 ^ 59
def prefixEnd_53432 : Nat := 4983230072969 + 3 ^ 40 * 53432 * 2
def baseEnd_53432 : Nat := 24387820738791271781579

theorem tailTrace_53432 : CollatzResearch.WordTrace tailWord_53432 prefixEnd_53432 24387820738791271781579 := by
  unfold tailWord_53432
  simp only [CollatzResearch.WordTrace]
  refine ⟨974412571216232152097275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1299216761621642869463033 974412571216232152097275)
  ·
    refine ⟨1461618856824348228145913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 974412571216232152097275 1461618856824348228145913)
    ·
      refine ⟨1096214142618261171109435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1461618856824348228145913 1096214142618261171109435)
      ·
        refine ⟨1644321213927391756664153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096214142618261171109435 1644321213927391756664153)
        ·
          refine ⟨1233240910445543817498115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1644321213927391756664153 1233240910445543817498115)
          ·
            refine ⟨1849861365668315726247173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233240910445543817498115 1849861365668315726247173)
            ·
              refine ⟨346849006062809198671345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1849861365668315726247173 346849006062809198671345)
              ·
                refine ⟨260136754547106899003509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346849006062809198671345 260136754547106899003509)
                ·
                  refine ⟨24387820738791271781579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 260136754547106899003509 24387820738791271781579)
                  ·
                    rfl

theorem cell20_53432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_53432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53432 prefixEnd_53432 := by exact prefixLift 53432
  have htrace : WordTrace (prefixWord ++ tailWord_53432) baseStart_53432 baseEnd_53432 := by
    simpa [prefixWord, tailWord_53432, baseEnd_53432] using wordTrace_append hprefix tailTrace_53432
  have hstable : (prefixWord ++ tailWord_53432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53432).length < 2 ^ (prefixWord ++ tailWord_53432).sum := by decide
  have hdescent : baseEnd_53432 < baseStart_53432 := by decide
  rcases family_descends (prefixWord ++ tailWord_53432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53435 : List Nat := [1, 1, 1, 1, 1, 2, 8, 3, 2]
def baseStart_53435 : Nat := 118140960795 + 53435 * 2 ^ 59
def prefixEnd_53435 : Nat := 4983230072969 + 3 ^ 40 * 53435 * 2
def baseEnd_53435 : Nat := 24389190020536594681567

theorem tailTrace_53435 : CollatzResearch.WordTrace tailWord_53435 prefixEnd_53435 24389190020536594681567 := by
  unfold tailWord_53435
  simp only [CollatzResearch.WordTrace]
  refine ⟨1948934561421595816553759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1299289707614397211035839 1948934561421595816553759)
  ·
    refine ⟨2923401842132393724830639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1948934561421595816553759 2923401842132393724830639)
    ·
      refine ⟨4385102763198590587245959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2923401842132393724830639 4385102763198590587245959)
      ·
        refine ⟨6577654144797885880868939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4385102763198590587245959 6577654144797885880868939)
        ·
          refine ⟨9866481217196828821303409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6577654144797885880868939 9866481217196828821303409)
          ·
            refine ⟨7399860912897621615977557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9866481217196828821303409 7399860912897621615977557)
            ·
              refine ⟨86717120073019003312237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 7399860912897621615977557 86717120073019003312237)
              ·
                refine ⟨32518920027382126242089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86717120073019003312237 32518920027382126242089)
                ·
                  refine ⟨24389190020536594681567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32518920027382126242089 24389190020536594681567)
                  ·
                    rfl

theorem cell20_53435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 2].length) (baseStart_53435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53435 prefixEnd_53435 := by exact prefixLift 53435
  have htrace : WordTrace (prefixWord ++ tailWord_53435) baseStart_53435 baseEnd_53435 := by
    simpa [prefixWord, tailWord_53435, baseEnd_53435] using wordTrace_append hprefix tailTrace_53435
  have hstable : (prefixWord ++ tailWord_53435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53435).length < 2 ^ (prefixWord ++ tailWord_53435).sum := by decide
  have hdescent : baseEnd_53435 < baseStart_53435 := by decide
  rcases family_descends (prefixWord ++ tailWord_53435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53439 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 8]
def baseStart_53439 : Nat := 118140960795 + 53439 * 2 ^ 59
def prefixEnd_53439 : Nat := 4983230072969 + 3 ^ 40 * 53439 * 2
def baseEnd_53439 : Nat := 24391015729530358548217

theorem tailTrace_53439 : CollatzResearch.WordTrace tailWord_53439 prefixEnd_53439 24391015729530358548217 := by
  unfold tailWord_53439
  simp only [CollatzResearch.WordTrace]
  refine ⟨1949080453407104499699371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1299386968938069666466247 1949080453407104499699371)
  ·
    refine ⟨2923620680110656749549057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1949080453407104499699371 2923620680110656749549057)
    ·
      refine ⟨2192715510082992562161793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2923620680110656749549057 2192715510082992562161793)
      ·
        refine ⟨1644536632562244421621345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2192715510082992562161793 1644536632562244421621345)
        ·
          refine ⟨1233402474421683316216009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1644536632562244421621345 1233402474421683316216009)
          ·
            refine ⟨925051855816262487162007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1233402474421683316216009 925051855816262487162007)
            ·
              refine ⟨1387577783724393730743011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925051855816262487162007 1387577783724393730743011)
              ·
                refine ⟨2081366675586590596114517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387577783724393730743011 2081366675586590596114517)
                ·
                  refine ⟨24391015729530358548217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2081366675586590596114517 24391015729530358548217)
                  ·
                    rfl

theorem cell20_53439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_53439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53439 prefixEnd_53439 := by exact prefixLift 53439
  have htrace : WordTrace (prefixWord ++ tailWord_53439) baseStart_53439 baseEnd_53439 := by
    simpa [prefixWord, tailWord_53439, baseEnd_53439] using wordTrace_append hprefix tailTrace_53439
  have hstable : (prefixWord ++ tailWord_53439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53439).length < 2 ^ (prefixWord ++ tailWord_53439).sum := by decide
  have hdescent : baseEnd_53439 < baseStart_53439 := by decide
  rcases family_descends (prefixWord ++ tailWord_53439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53452 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 4]
def baseStart_53452 : Nat := 118140960795 + 53452 * 2 ^ 59
def prefixEnd_53452 : Nat := 4983230072969 + 3 ^ 40 * 53452 * 2
def baseEnd_53452 : Nat := 24396949283760091114831

theorem tailTrace_53452 : CollatzResearch.WordTrace tailWord_53452 prefixEnd_53452 24396949283760091114831 := by
  unfold tailWord_53452
  simp only [CollatzResearch.WordTrace]
  refine ⟨974777301180003859961305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1299703068240005146615073 974777301180003859961305)
  ·
    refine ⟨731082975885002894970979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 974777301180003859961305 731082975885002894970979)
    ·
      refine ⟨1096624463827504342456469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 731082975885002894970979 1096624463827504342456469)
      ·
        refine ⟨51404271741914266052647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1096624463827504342456469 51404271741914266052647)
        ·
          refine ⟨77106407612871399078971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51404271741914266052647 77106407612871399078971)
          ·
            refine ⟨115659611419307098618457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77106407612871399078971 115659611419307098618457)
            ·
              refine ⟨86744708564480323963843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115659611419307098618457 86744708564480323963843)
              ·
                refine ⟨130117062846720485945765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86744708564480323963843 130117062846720485945765)
                ·
                  refine ⟨24396949283760091114831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130117062846720485945765 24396949283760091114831)
                  ·
                    rfl

theorem cell20_53452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_53452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53452 prefixEnd_53452 := by exact prefixLift 53452
  have htrace : WordTrace (prefixWord ++ tailWord_53452) baseStart_53452 baseEnd_53452 := by
    simpa [prefixWord, tailWord_53452, baseEnd_53452] using wordTrace_append hprefix tailTrace_53452
  have hstable : (prefixWord ++ tailWord_53452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53452).length < 2 ^ (prefixWord ++ tailWord_53452).sum := by decide
  have hdescent : baseEnd_53452 < baseStart_53452 := by decide
  rcases family_descends (prefixWord ++ tailWord_53452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53462 : List Nat := [5, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_53462 : Nat := 118140960795 + 53462 * 2 ^ 59
def prefixEnd_53462 : Nat := 4983230072969 + 3 ^ 40 * 53462 * 2
def baseEnd_53462 : Nat := 24401513556244500781457

theorem tailTrace_53462 : CollatzResearch.WordTrace tailWord_53462 prefixEnd_53462 24401513556244500781457 := by
  unfold tailWord_53462
  simp only [CollatzResearch.WordTrace]
  refine ⟨121869958270236214236665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1299946221549186285191093 121869958270236214236665)
  ·
    refine ⟨91402468702677160677499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121869958270236214236665 91402468702677160677499)
    ·
      refine ⟨137103703054015741016249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91402468702677160677499 137103703054015741016249)
      ·
        refine ⟨102827777290511805762187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137103703054015741016249 102827777290511805762187)
        ·
          refine ⟨154241665935767708643281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102827777290511805762187 154241665935767708643281)
          ·
            refine ⟨115681249451825781482461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154241665935767708643281 115681249451825781482461)
            ·
              refine ⟨43380468544434668055923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115681249451825781482461 43380468544434668055923)
              ·
                refine ⟨65070702816652002083885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43380468544434668055923 65070702816652002083885)
                ·
                  refine ⟨24401513556244500781457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65070702816652002083885 24401513556244500781457)
                  ·
                    rfl

theorem cell20_53462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_53462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53462 prefixEnd_53462 := by exact prefixLift 53462
  have htrace : WordTrace (prefixWord ++ tailWord_53462) baseStart_53462 baseEnd_53462 := by
    simpa [prefixWord, tailWord_53462, baseEnd_53462] using wordTrace_append hprefix tailTrace_53462
  have hstable : (prefixWord ++ tailWord_53462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53462).length < 2 ^ (prefixWord ++ tailWord_53462).sum := by decide
  have hdescent : baseEnd_53462 < baseStart_53462 := by decide
  rcases family_descends (prefixWord ++ tailWord_53462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53480 : List Nat := [2, 1, 4, 1, 2, 2, 4, 4]
def baseStart_53480 : Nat := 118140960795 + 53480 * 2 ^ 59
def prefixEnd_53480 : Nat := 4983230072969 + 3 ^ 40 * 53480 * 2
def baseEnd_53480 : Nat := 8136576415572146060461

theorem tailTrace_53480 : CollatzResearch.WordTrace tailWord_53480 prefixEnd_53480 8136576415572146060461 := by
  unfold tailWord_53480
  simp only [CollatzResearch.WordTrace]
  refine ⟨975287923129284250970947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1300383897505712334627929 975287923129284250970947)
  ·
    refine ⟨1462931884693926376456421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 975287923129284250970947 1462931884693926376456421)
    ·
      refine ⟨274299728380111195585579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1462931884693926376456421 274299728380111195585579)
      ·
        refine ⟨411449592570166793378369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274299728380111195585579 411449592570166793378369)
        ·
          refine ⟨308587194427625095033777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411449592570166793378369 308587194427625095033777)
          ·
            refine ⟨231440395820718821275333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308587194427625095033777 231440395820718821275333)
            ·
              refine ⟨43395074216384778989125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231440395820718821275333 43395074216384778989125)
              ·
                refine ⟨8136576415572146060461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43395074216384778989125 8136576415572146060461)
                ·
                  rfl

theorem cell20_53480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_53480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53480 prefixEnd_53480 := by exact prefixLift 53480
  have htrace : WordTrace (prefixWord ++ tailWord_53480) baseStart_53480 baseEnd_53480 := by
    simpa [prefixWord, tailWord_53480, baseEnd_53480] using wordTrace_append hprefix tailTrace_53480
  have hstable : (prefixWord ++ tailWord_53480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53480).length < 2 ^ (prefixWord ++ tailWord_53480).sum := by decide
  have hdescent : baseEnd_53480 < baseStart_53480 := by decide
  rcases family_descends (prefixWord ++ tailWord_53480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53490 : List Nat := [3, 2, 1, 3, 2, 1, 3, 3, 2]
def baseStart_53490 : Nat := 118140960795 + 53490 * 2 ^ 59
def prefixEnd_53490 : Nat := 4983230072969 + 3 ^ 40 * 53490 * 2
def baseEnd_53490 : Nat := 24414293519200847848009

theorem tailTrace_53490 : CollatzResearch.WordTrace tailWord_53490 prefixEnd_53490 24414293519200847848009 := by
  unfold tailWord_53490
  simp only [CollatzResearch.WordTrace]
  refine ⟨487735144055585052451481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1300627050814893473203949 487735144055585052451481)
  ·
    refine ⟨365801358041688789338611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 487735144055585052451481 365801358041688789338611)
    ·
      refine ⟨548702037062533184007917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365801358041688789338611 548702037062533184007917)
      ·
        refine ⟨205763263898449944002969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548702037062533184007917 205763263898449944002969)
        ·
          refine ⟨154322447923837458002227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205763263898449944002969 154322447923837458002227)
          ·
            refine ⟨231483671885756187003341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154322447923837458002227 231483671885756187003341)
            ·
              refine ⟨86806376957158570126253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231483671885756187003341 86806376957158570126253)
              ·
                refine ⟨32552391358934463797345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86806376957158570126253 32552391358934463797345)
                ·
                  refine ⟨24414293519200847848009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32552391358934463797345 24414293519200847848009)
                  ·
                    rfl

theorem cell20_53490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_53490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53490 prefixEnd_53490 := by exact prefixLift 53490
  have htrace : WordTrace (prefixWord ++ tailWord_53490) baseStart_53490 baseEnd_53490 := by
    simpa [prefixWord, tailWord_53490, baseEnd_53490] using wordTrace_append hprefix tailTrace_53490
  have hstable : (prefixWord ++ tailWord_53490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53490).length < 2 ^ (prefixWord ++ tailWord_53490).sum := by decide
  have hdescent : baseEnd_53490 < baseStart_53490 := by decide
  rcases family_descends (prefixWord ++ tailWord_53490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53494 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_53494 : Nat := 118140960795 + 53494 * 2 ^ 59
def prefixEnd_53494 : Nat := 4983230072969 + 3 ^ 40 * 53494 * 2
def baseEnd_53494 : Nat := 24416119228194611714659

theorem tailTrace_53494 : CollatzResearch.WordTrace tailWord_53494 prefixEnd_53494 24416119228194611714659 := by
  unfold tailWord_53494
  simp only [CollatzResearch.WordTrace]
  refine ⟨121942904262990555809471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1300724312138565928634357 121942904262990555809471)
  ·
    refine ⟨182914356394485833714207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121942904262990555809471 182914356394485833714207)
    ·
      refine ⟨274371534591728750571311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182914356394485833714207 274371534591728750571311)
      ·
        refine ⟨411557301887593125856967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274371534591728750571311 411557301887593125856967)
        ·
          refine ⟨617335952831389688785451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411557301887593125856967 617335952831389688785451)
          ·
            refine ⟨926003929247084533178177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617335952831389688785451 926003929247084533178177)
            ·
              refine ⟨694502946935313399883633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926003929247084533178177 694502946935313399883633)
              ·
                refine ⟨520877210201485049912725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694502946935313399883633 520877210201485049912725)
                ·
                  refine ⟨24416119228194611714659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 520877210201485049912725 24416119228194611714659)
                  ·
                    rfl

theorem cell20_53494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_53494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53494 prefixEnd_53494 := by exact prefixLift 53494
  have htrace : WordTrace (prefixWord ++ tailWord_53494) baseStart_53494 baseEnd_53494 := by
    simpa [prefixWord, tailWord_53494, baseEnd_53494] using wordTrace_append hprefix tailTrace_53494
  have hstable : (prefixWord ++ tailWord_53494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53494).length < 2 ^ (prefixWord ++ tailWord_53494).sum := by decide
  have hdescent : baseEnd_53494 < baseStart_53494 := by decide
  rcases family_descends (prefixWord ++ tailWord_53494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53566 : List Nat := [4, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_53566 : Nat := 118140960795 + 53566 * 2 ^ 59
def prefixEnd_53566 : Nat := 4983230072969 + 3 ^ 40 * 53566 * 2
def baseEnd_53566 : Nat := 24448981990082361314365

theorem tailTrace_53566 : CollatzResearch.WordTrace tailWord_53566 prefixEnd_53566 24448981990082361314365 := by
  unfold tailWord_53566
  simp only [CollatzResearch.WordTrace]
  refine ⟨244214065493375648696569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1302475015964670126381701 244214065493375648696569)
  ·
    refine ⟨183160549120031736522427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244214065493375648696569 183160549120031736522427)
    ·
      refine ⟨274740823680047604783641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183160549120031736522427 274740823680047604783641)
      ·
        refine ⟨206055617760035703587731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274740823680047604783641 206055617760035703587731)
        ·
          refine ⟨309083426640053555381597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206055617760035703587731 309083426640053555381597)
          ·
            refine ⟨115906284990020083268099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309083426640053555381597 115906284990020083268099)
            ·
              refine ⟨173859427485030124902149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115906284990020083268099 173859427485030124902149)
              ·
                refine ⟨32598642653443148419153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173859427485030124902149 32598642653443148419153)
                ·
                  refine ⟨24448981990082361314365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32598642653443148419153 24448981990082361314365)
                  ·
                    rfl

theorem cell20_53566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_53566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53566 prefixEnd_53566 := by exact prefixLift 53566
  have htrace : WordTrace (prefixWord ++ tailWord_53566) baseStart_53566 baseEnd_53566 := by
    simpa [prefixWord, tailWord_53566, baseEnd_53566] using wordTrace_append hprefix tailTrace_53566
  have hstable : (prefixWord ++ tailWord_53566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53566).length < 2 ^ (prefixWord ++ tailWord_53566).sum := by decide
  have hdescent : baseEnd_53566 < baseStart_53566 := by decide
  rcases family_descends (prefixWord ++ tailWord_53566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53618 : List Nat := [3, 2, 1, 2, 1, 5, 1, 2, 3]
def baseStart_53618 : Nat := 118140960795 + 53618 * 2 ^ 59
def prefixEnd_53618 : Nat := 4983230072969 + 3 ^ 40 * 53618 * 2
def baseEnd_53618 : Nat := 24472716207001291580819

theorem tailTrace_53618 : CollatzResearch.WordTrace tailWord_53618 prefixEnd_53618 24472716207001291580819 := by
  unfold tailWord_53618
  simp only [CollatzResearch.WordTrace]
  refine ⟨488902279939654517616377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1303739413172412046977005 488902279939654517616377)
  ·
    refine ⟨366676709954740888212283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 488902279939654517616377 366676709954740888212283)
    ·
      refine ⟨550015064932111332318425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366676709954740888212283 550015064932111332318425)
      ·
        refine ⟨412511298699083499238819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550015064932111332318425 412511298699083499238819)
        ·
          refine ⟨618766948048625248858229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412511298699083499238819 618766948048625248858229)
          ·
            refine ⟨58009401379558617080459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 618766948048625248858229 58009401379558617080459)
            ·
              refine ⟨87014102069337925620689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58009401379558617080459 87014102069337925620689)
              ·
                refine ⟨65260576552003444215517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87014102069337925620689 65260576552003444215517)
                ·
                  refine ⟨24472716207001291580819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65260576552003444215517 24472716207001291580819)
                  ·
                    rfl

theorem cell20_53618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_53618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53618 prefixEnd_53618 := by exact prefixLift 53618
  have htrace : WordTrace (prefixWord ++ tailWord_53618) baseStart_53618 baseEnd_53618 := by
    simpa [prefixWord, tailWord_53618, baseEnd_53618] using wordTrace_append hprefix tailTrace_53618
  have hstable : (prefixWord ++ tailWord_53618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53618).length < 2 ^ (prefixWord ++ tailWord_53618).sum := by decide
  have hdescent : baseEnd_53618 < baseStart_53618 := by decide
  rcases family_descends (prefixWord ++ tailWord_53618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53694 : List Nat := [4, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_53694 : Nat := 118140960795 + 53694 * 2 ^ 59
def prefixEnd_53694 : Nat := 4983230072969 + 3 ^ 40 * 53694 * 2
def baseEnd_53694 : Nat := 24507404677882805047175

theorem tailTrace_53694 : CollatzResearch.WordTrace tailWord_53694 prefixEnd_53694 24507404677882805047175 := by
  unfold tailWord_53694
  simp only [CollatzResearch.WordTrace]
  refine ⟨244797633435410381279017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1305587378322188700154757 244797633435410381279017)
  ·
    refine ⟨183598225076557785959263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244797633435410381279017 183598225076557785959263)
    ·
      refine ⟨275397337614836678938895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183598225076557785959263 275397337614836678938895)
      ·
        refine ⟨413096006422255018408343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275397337614836678938895 413096006422255018408343)
        ·
          refine ⟨619644009633382527612515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413096006422255018408343 619644009633382527612515)
          ·
            refine ⟨929466014450073791418773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619644009633382527612515 929466014450073791418773)
            ·
              refine ⟨43568719427347208972755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 929466014450073791418773 43568719427347208972755)
              ·
                refine ⟨65353079141020813459133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43568719427347208972755 65353079141020813459133)
                ·
                  refine ⟨24507404677882805047175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65353079141020813459133 24507404677882805047175)
                  ·
                    rfl

theorem cell20_53694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_53694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53694 prefixEnd_53694 := by exact prefixLift 53694
  have htrace : WordTrace (prefixWord ++ tailWord_53694) baseStart_53694 baseEnd_53694 := by
    simpa [prefixWord, tailWord_53694, baseEnd_53694] using wordTrace_append hprefix tailTrace_53694
  have hstable : (prefixWord ++ tailWord_53694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53694).length < 2 ^ (prefixWord ++ tailWord_53694).sum := by decide
  have hdescent : baseEnd_53694 < baseStart_53694 := by decide
  rcases family_descends (prefixWord ++ tailWord_53694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53705 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 4]
def baseStart_53705 : Nat := 118140960795 + 53705 * 2 ^ 59
def prefixEnd_53705 : Nat := 4983230072969 + 3 ^ 40 * 53705 * 2
def baseEnd_53705 : Nat := 24512425377615655680463

theorem tailTrace_53705 : CollatzResearch.WordTrace tailWord_53705 prefixEnd_53705 24512425377615655680463 := by
  unfold tailWord_53705
  simp only [CollatzResearch.WordTrace]
  refine ⟨1958782270443431928882569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1305854846962287952588379 1958782270443431928882569)
  ·
    refine ⟨1469086702832573946661927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1958782270443431928882569 1469086702832573946661927)
    ·
      refine ⟨2203630054248860919992891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1469086702832573946661927 2203630054248860919992891)
      ·
        refine ⟨3305445081373291379989337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2203630054248860919992891 3305445081373291379989337)
        ·
          refine ⟨2479083811029968534992003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3305445081373291379989337 2479083811029968534992003)
          ·
            refine ⟨3718625716544952802488005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2479083811029968534992003 3718625716544952802488005)
            ·
              refine ⟨697242321852178650466501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3718625716544952802488005 697242321852178650466501)
              ·
                refine ⟨130732935347283496962469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 697242321852178650466501 130732935347283496962469)
                ·
                  refine ⟨24512425377615655680463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130732935347283496962469 24512425377615655680463)
                  ·
                    rfl

theorem cell20_53705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_53705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53705 prefixEnd_53705 := by exact prefixLift 53705
  have htrace : WordTrace (prefixWord ++ tailWord_53705) baseStart_53705 baseEnd_53705 := by
    simpa [prefixWord, tailWord_53705, baseEnd_53705] using wordTrace_append hprefix tailTrace_53705
  have hstable : (prefixWord ++ tailWord_53705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53705).length < 2 ^ (prefixWord ++ tailWord_53705).sum := by decide
  have hdescent : baseEnd_53705 < baseStart_53705 := by decide
  rcases family_descends (prefixWord ++ tailWord_53705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53718 : List Nat := [5, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_53718 : Nat := 118140960795 + 53718 * 2 ^ 59
def prefixEnd_53718 : Nat := 4983230072969 + 3 ^ 40 * 53718 * 2
def baseEnd_53718 : Nat := 24518358931845388247077

theorem tailTrace_53718 : CollatzResearch.WordTrace tailWord_53718 prefixEnd_53718 24518358931845388247077 := by
  unfold tailWord_53718
  simp only [CollatzResearch.WordTrace]
  refine ⟨122453526212270946819113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1306170946264223432737205 122453526212270946819113)
  ·
    refine ⟨91840144659203210114335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122453526212270946819113 91840144659203210114335)
    ·
      refine ⟨137760216988804815171503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91840144659203210114335 137760216988804815171503)
      ·
        refine ⟨206640325483207222757255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137760216988804815171503 206640325483207222757255)
        ·
          refine ⟨309960488224810834135883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206640325483207222757255 309960488224810834135883)
          ·
            refine ⟨464940732337216251203825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309960488224810834135883 464940732337216251203825)
            ·
              refine ⟨348705549252912188402869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 464940732337216251203825 348705549252912188402869)
              ·
                refine ⟨32691145242460517662769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 348705549252912188402869 32691145242460517662769)
                ·
                  refine ⟨24518358931845388247077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32691145242460517662769 24518358931845388247077)
                  ·
                    rfl

theorem cell20_53718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_53718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53718 prefixEnd_53718 := by exact prefixLift 53718
  have htrace : WordTrace (prefixWord ++ tailWord_53718) baseStart_53718 baseEnd_53718 := by
    simpa [prefixWord, tailWord_53718, baseEnd_53718] using wordTrace_append hprefix tailTrace_53718
  have hstable : (prefixWord ++ tailWord_53718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53718).length < 2 ^ (prefixWord ++ tailWord_53718).sum := by decide
  have hdescent : baseEnd_53718 < baseStart_53718 := by decide
  rcases family_descends (prefixWord ++ tailWord_53718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53743 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 4]
def baseStart_53743 : Nat := 118140960795 + 53743 * 2 ^ 59
def prefixEnd_53743 : Nat := 4983230072969 + 3 ^ 40 * 53743 * 2
def baseEnd_53743 : Nat := 24529769613056412413641

theorem tailTrace_53743 : CollatzResearch.WordTrace tailWord_53743 prefixEnd_53743 24529769613056412413641 := by
  unfold tailWord_53743
  simp only [CollatzResearch.WordTrace]
  refine ⟨1960168244305764418765883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1306778829537176279177255 1960168244305764418765883)
  ·
    refine ⟨2940252366458646628148825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1960168244305764418765883 2940252366458646628148825)
    ·
      refine ⟨2205189274843984971111619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2940252366458646628148825 2205189274843984971111619)
      ·
        refine ⟨3307783912265977456667429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2205189274843984971111619 3307783912265977456667429)
        ·
          refine ⟨620209483549870773125143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3307783912265977456667429 620209483549870773125143)
          ·
            refine ⟨930314225324806159687715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620209483549870773125143 930314225324806159687715)
            ·
              refine ⟨1395471337987209239531573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930314225324806159687715 1395471337987209239531573)
              ·
                refine ⟨130825437936300866206085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1395471337987209239531573 130825437936300866206085)
                ·
                  refine ⟨24529769613056412413641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130825437936300866206085 24529769613056412413641)
                  ·
                    rfl

theorem cell20_53743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_53743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53743 prefixEnd_53743 := by exact prefixLift 53743
  have htrace : WordTrace (prefixWord ++ tailWord_53743) baseStart_53743 baseEnd_53743 := by
    simpa [prefixWord, tailWord_53743, baseEnd_53743] using wordTrace_append hprefix tailTrace_53743
  have hstable : (prefixWord ++ tailWord_53743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53743).length < 2 ^ (prefixWord ++ tailWord_53743).sum := by decide
  have hdescent : baseEnd_53743 < baseStart_53743 := by decide
  rcases family_descends (prefixWord ++ tailWord_53743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53773 : List Nat := [1, 7, 1, 1, 1, 1, 1, 5, 2]
def baseStart_53773 : Nat := 118140960795 + 53773 * 2 ^ 59
def prefixEnd_53773 : Nat := 4983230072969 + 3 ^ 40 * 53773 * 2
def baseEnd_53773 : Nat := 24543462430509641413519

theorem tailTrace_53773 : CollatzResearch.WordTrace tailWord_53773 prefixEnd_53773 24543462430509641413519 := by
  unfold tailWord_53773
  simp only [CollatzResearch.WordTrace]
  refine ⟨1961262434197079542357973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1307508289464719694905315 1961262434197079542357973)
  ·
    refine ⟨45967088301494051774015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 1961262434197079542357973 45967088301494051774015)
    ·
      refine ⟨68950632452241077661023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45967088301494051774015 68950632452241077661023)
      ·
        refine ⟨103425948678361616491535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68950632452241077661023 103425948678361616491535)
        ·
          refine ⟨155138923017542424737303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103425948678361616491535 155138923017542424737303)
          ·
            refine ⟨232708384526313637105955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155138923017542424737303 232708384526313637105955)
            ·
              refine ⟨349062576789470455658933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232708384526313637105955 349062576789470455658933)
              ·
                refine ⟨32724616574012855218025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 349062576789470455658933 32724616574012855218025)
                ·
                  refine ⟨24543462430509641413519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32724616574012855218025 24543462430509641413519)
                  ·
                    rfl

theorem cell20_53773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_53773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53773 prefixEnd_53773 := by exact prefixLift 53773
  have htrace : WordTrace (prefixWord ++ tailWord_53773) baseStart_53773 baseEnd_53773 := by
    simpa [prefixWord, tailWord_53773, baseEnd_53773] using wordTrace_append hprefix tailTrace_53773
  have hstable : (prefixWord ++ tailWord_53773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53773).length < 2 ^ (prefixWord ++ tailWord_53773).sum := by decide
  have hdescent : baseEnd_53773 < baseStart_53773 := by decide
  rcases family_descends (prefixWord ++ tailWord_53773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53781 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 6]
def baseStart_53781 : Nat := 118140960795 + 53781 * 2 ^ 59
def prefixEnd_53781 : Nat := 4983230072969 + 3 ^ 40 * 53781 * 2
def baseEnd_53781 : Nat := 24547113848497169146819

theorem tailTrace_53781 : CollatzResearch.WordTrace tailWord_53781 prefixEnd_53781 24547113848497169146819 := by
  unfold tailWord_53781
  simp only [CollatzResearch.WordTrace]
  refine ⟨1961554218168096908649197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1307702812112064605766131 1961554218168096908649197)
  ·
    refine ⟨735582831813036340743449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1961554218168096908649197 735582831813036340743449)
    ·
      refine ⟨551687123859777255557587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 735582831813036340743449 551687123859777255557587)
      ·
        refine ⟨827530685789665883336381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551687123859777255557587 827530685789665883336381)
        ·
          refine ⟨310324007171124706251143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 827530685789665883336381 310324007171124706251143)
          ·
            refine ⟨465486010756687059376715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310324007171124706251143 465486010756687059376715)
            ·
              refine ⟨698229016135030589065073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465486010756687059376715 698229016135030589065073)
              ·
                refine ⟨523671762101272941798805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698229016135030589065073 523671762101272941798805)
                ·
                  refine ⟨24547113848497169146819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 523671762101272941798805 24547113848497169146819)
                  ·
                    rfl

theorem cell20_53781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_53781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53781 prefixEnd_53781 := by exact prefixLift 53781
  have htrace : WordTrace (prefixWord ++ tailWord_53781) baseStart_53781 baseEnd_53781 := by
    simpa [prefixWord, tailWord_53781, baseEnd_53781] using wordTrace_append hprefix tailTrace_53781
  have hstable : (prefixWord ++ tailWord_53781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53781).length < 2 ^ (prefixWord ++ tailWord_53781).sum := by decide
  have hdescent : baseEnd_53781 < baseStart_53781 := by decide
  rcases family_descends (prefixWord ++ tailWord_53781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53908 : List Nat := [2, 4, 2, 2, 1, 2, 1, 4, 2]
def baseStart_53908 : Nat := 118140960795 + 53908 * 2 ^ 59
def prefixEnd_53908 : Nat := 4983230072969 + 3 ^ 40 * 53908 * 2
def baseEnd_53908 : Nat := 24605080109049171912967

theorem tailTrace_53908 : CollatzResearch.WordTrace tailWord_53908 prefixEnd_53908 24605080109049171912967 := by
  unfold tailWord_53908
  simp only [CollatzResearch.WordTrace]
  refine ⟨983093144353998799261189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1310790859138665065681585 983093144353998799261189)
  ·
    refine ⟨184329964566374774861473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 983093144353998799261189 184329964566374774861473)
    ·
      refine ⟨138247473424781081146105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184329964566374774861473 138247473424781081146105)
      ·
        refine ⟨103685605068585810859579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138247473424781081146105 103685605068585810859579)
        ·
          refine ⟨155528407602878716289369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103685605068585810859579 155528407602878716289369)
          ·
            refine ⟨116646305702159037217027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155528407602878716289369 116646305702159037217027)
            ·
              refine ⟨174969458553238555825541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116646305702159037217027 174969458553238555825541)
              ·
                refine ⟨32806773478732229217289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174969458553238555825541 32806773478732229217289)
                ·
                  refine ⟨24605080109049171912967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32806773478732229217289 24605080109049171912967)
                  ·
                    rfl

theorem cell20_53908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_53908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53908 prefixEnd_53908 := by exact prefixLift 53908
  have htrace : WordTrace (prefixWord ++ tailWord_53908) baseStart_53908 baseEnd_53908 := by
    simpa [prefixWord, tailWord_53908, baseEnd_53908] using wordTrace_append hprefix tailTrace_53908
  have hstable : (prefixWord ++ tailWord_53908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53908).length < 2 ^ (prefixWord ++ tailWord_53908).sum := by decide
  have hdescent : baseEnd_53908 < baseStart_53908 := by decide
  rcases family_descends (prefixWord ++ tailWord_53908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_53978 : List Nat := [3, 1, 1, 2, 2, 2, 2, 7]
def baseStart_53978 : Nat := 118140960795 + 53978 * 2 ^ 59
def prefixEnd_53978 : Nat := 4983230072969 + 3 ^ 40 * 53978 * 2
def baseEnd_53978 : Nat := 8212343338813346526449

theorem tailTrace_53978 : CollatzResearch.WordTrace tailWord_53978 prefixEnd_53978 8212343338813346526449 := by
  unfold tailWord_53978
  simp only [CollatzResearch.WordTrace]
  refine ⟨492184849613599888392647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1312492932302933035713725 492184849613599888392647)
  ·
    refine ⟨738277274420399832588971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 492184849613599888392647 738277274420399832588971)
    ·
      refine ⟨1107415911630599748883457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738277274420399832588971 1107415911630599748883457)
      ·
        refine ⟨830561933722949811662593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1107415911630599748883457 830561933722949811662593)
        ·
          refine ⟨622921450292212358746945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 830561933722949811662593 622921450292212358746945)
          ·
            refine ⟨467191087719159269060209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622921450292212358746945 467191087719159269060209)
            ·
              refine ⟨350393315789369451795157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467191087719159269060209 350393315789369451795157)
              ·
                refine ⟨8212343338813346526449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 350393315789369451795157 8212343338813346526449)
                ·
                  rfl

theorem cell20_53978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_53978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_53978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_53978 prefixEnd_53978 := by exact prefixLift 53978
  have htrace : WordTrace (prefixWord ++ tailWord_53978) baseStart_53978 baseEnd_53978 := by
    simpa [prefixWord, tailWord_53978, baseEnd_53978] using wordTrace_append hprefix tailTrace_53978
  have hstable : (prefixWord ++ tailWord_53978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_53978).length < 2 ^ (prefixWord ++ tailWord_53978).sum := by decide
  have hdescent : baseEnd_53978 < baseStart_53978 := by decide
  rcases family_descends (prefixWord ++ tailWord_53978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54002 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_54002 : Nat := 118140960795 + 54002 * 2 ^ 59
def prefixEnd_54002 : Nat := 4983230072969 + 3 ^ 40 * 54002 * 2
def baseEnd_54002 : Nat := 24647984270402622779249

theorem tailTrace_54002 : CollatzResearch.WordTrace tailWord_54002 prefixEnd_54002 24647984270402622779249 := by
  unfold tailWord_54002
  simp only [CollatzResearch.WordTrace]
  refine ⟨492403687591862913111065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1313076500244967768296173 492403687591862913111065)
  ·
    refine ⟨369302765693897184833299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 492403687591862913111065 369302765693897184833299)
    ·
      refine ⟨553954148540845777249949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369302765693897184833299 553954148540845777249949)
      ·
        refine ⟨207732805702817166468731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 553954148540845777249949 207732805702817166468731)
        ·
          refine ⟨311599208554225749703097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207732805702817166468731 311599208554225749703097)
          ·
            refine ⟨233699406415669312277323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311599208554225749703097 233699406415669312277323)
            ·
              refine ⟨350549109623503968415985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233699406415669312277323 350549109623503968415985)
              ·
                refine ⟨262911832217627976311989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350549109623503968415985 262911832217627976311989)
                ·
                  refine ⟨24647984270402622779249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 262911832217627976311989 24647984270402622779249)
                  ·
                    rfl

theorem cell20_54002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_54002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54002 prefixEnd_54002 := by exact prefixLift 54002
  have htrace : WordTrace (prefixWord ++ tailWord_54002) baseStart_54002 baseEnd_54002 := by
    simpa [prefixWord, tailWord_54002, baseEnd_54002] using wordTrace_append hprefix tailTrace_54002
  have hstable : (prefixWord ++ tailWord_54002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54002).length < 2 ^ (prefixWord ++ tailWord_54002).sum := by decide
  have hdescent : baseEnd_54002 < baseStart_54002 := by decide
  rcases family_descends (prefixWord ++ tailWord_54002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54077 : List Nat := [1, 4, 1, 4, 2, 2, 2, 2, 2]
def baseStart_54077 : Nat := 118140960795 + 54077 * 2 ^ 59
def prefixEnd_54077 : Nat := 4983230072969 + 3 ^ 40 * 54077 * 2
def baseEnd_54077 : Nat := 24682216314035695278943

theorem tailTrace_54077 : CollatzResearch.WordTrace tailWord_54077 prefixEnd_54077 24682216314035695278943 := by
  unfold tailWord_54077
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972350225095739461424485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1314900150063826307616323 1972350225095739461424485)
  ·
    refine ⟨369815667205451149017091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1972350225095739461424485 369815667205451149017091)
    ·
      refine ⟨554723500808176723525637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369815667205451149017091 554723500808176723525637)
      ·
        refine ⟨104010656401533135661057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 554723500808176723525637 104010656401533135661057)
        ·
          refine ⟨78007992301149851745793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104010656401533135661057 78007992301149851745793)
          ·
            refine ⟨58505994225862388809345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78007992301149851745793 58505994225862388809345)
            ·
              refine ⟨43879495669396791607009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58505994225862388809345 43879495669396791607009)
              ·
                refine ⟨32909621752047593705257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43879495669396791607009 32909621752047593705257)
                ·
                  refine ⟨24682216314035695278943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32909621752047593705257 24682216314035695278943)
                  ·
                    rfl

theorem cell20_54077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_54077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54077 prefixEnd_54077 := by exact prefixLift 54077
  have htrace : WordTrace (prefixWord ++ tailWord_54077) baseStart_54077 baseEnd_54077 := by
    simpa [prefixWord, tailWord_54077, baseEnd_54077] using wordTrace_append hprefix tailTrace_54077
  have hstable : (prefixWord ++ tailWord_54077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54077).length < 2 ^ (prefixWord ++ tailWord_54077).sum := by decide
  have hdescent : baseEnd_54077 < baseStart_54077 := by decide
  rcases family_descends (prefixWord ++ tailWord_54077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54084 : List Nat := [2, 3, 4, 2, 2, 1, 1, 5]
def baseStart_54084 : Nat := 118140960795 + 54084 * 2 ^ 59
def prefixEnd_54084 : Nat := 4983230072969 + 3 ^ 40 * 54084 * 2
def baseEnd_54084 : Nat := 8228470434924927348527

theorem tailTrace_54084 : CollatzResearch.WordTrace tailWord_54084 prefixEnd_54084 8228470434924927348527 := by
  unfold tailWord_54084
  simp only [CollatzResearch.WordTrace]
  refine ⟨986302768035189828464653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1315070357380253104619537 986302768035189828464653)
  ·
    refine ⟨369863538013196185674245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 986302768035189828464653 369863538013196185674245)
    ·
      refine ⟨69349413377474284813921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 369863538013196185674245 69349413377474284813921)
      ·
        refine ⟨52012060033105713610441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69349413377474284813921 52012060033105713610441)
        ·
          refine ⟨39009045024829285207831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52012060033105713610441 39009045024829285207831)
          ·
            refine ⟨58513567537243927811747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39009045024829285207831 58513567537243927811747)
            ·
              refine ⟨87770351305865891717621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58513567537243927811747 87770351305865891717621)
              ·
                refine ⟨8228470434924927348527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87770351305865891717621 8228470434924927348527)
                ·
                  rfl

theorem cell20_54084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_54084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54084 prefixEnd_54084 := by exact prefixLift 54084
  have htrace : WordTrace (prefixWord ++ tailWord_54084) baseStart_54084 baseEnd_54084 := by
    simpa [prefixWord, tailWord_54084, baseEnd_54084] using wordTrace_append hprefix tailTrace_54084
  have hstable : (prefixWord ++ tailWord_54084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54084).length < 2 ^ (prefixWord ++ tailWord_54084).sum := by decide
  have hdescent : baseEnd_54084 < baseStart_54084 := by decide
  rcases family_descends (prefixWord ++ tailWord_54084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54119 : List Nat := [1, 1, 5, 1, 2, 3, 2, 3, 2]
def baseStart_54119 : Nat := 118140960795 + 54119 * 2 ^ 59
def prefixEnd_54119 : Nat := 4983230072969 + 3 ^ 40 * 54119 * 2
def baseEnd_54119 : Nat := 24701386258470215878771

theorem tailTrace_54119 : CollatzResearch.WordTrace tailWord_54119 prefixEnd_54119 24701386258470215878771 := by
  unfold tailWord_54119
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973882090943580634453411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1315921393962387089635607 1973882090943580634453411)
  ·
    refine ⟨2960823136415370951680117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1973882090943580634453411 2960823136415370951680117)
    ·
      refine ⟨277577169038941026720011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2960823136415370951680117 277577169038941026720011)
      ·
        refine ⟨416365753558411540080017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277577169038941026720011 416365753558411540080017)
        ·
          refine ⟨312274315168808655060013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416365753558411540080017 312274315168808655060013)
          ·
            refine ⟨117102868188303245647505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312274315168808655060013 117102868188303245647505)
            ·
              refine ⟨87827151141227434235629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117102868188303245647505 87827151141227434235629)
              ·
                refine ⟨32935181677960287838361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87827151141227434235629 32935181677960287838361)
                ·
                  refine ⟨24701386258470215878771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32935181677960287838361 24701386258470215878771)
                  ·
                    rfl

theorem cell20_54119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 2].length) (baseStart_54119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54119 prefixEnd_54119 := by exact prefixLift 54119
  have htrace : WordTrace (prefixWord ++ tailWord_54119) baseStart_54119 baseEnd_54119 := by
    simpa [prefixWord, tailWord_54119, baseEnd_54119] using wordTrace_append hprefix tailTrace_54119
  have hstable : (prefixWord ++ tailWord_54119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54119).length < 2 ^ (prefixWord ++ tailWord_54119).sum := by decide
  have hdescent : baseEnd_54119 < baseStart_54119 := by decide
  rcases family_descends (prefixWord ++ tailWord_54119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54133 : List Nat := [1, 3, 4, 1, 1, 2, 3, 2, 3]
def baseStart_54133 : Nat := 118140960795 + 54133 * 2 ^ 59
def prefixEnd_54133 : Nat := 4983230072969 + 3 ^ 40 * 54133 * 2
def baseEnd_54133 : Nat := 24707776239948389412047

theorem tailTrace_54133 : CollatzResearch.WordTrace tailWord_54133 prefixEnd_54133 24707776239948389412047 := by
  unfold tailWord_54133
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974392712892861025463053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1316261808595240683642035 1974392712892861025463053)
  ·
    refine ⟨740397267334822884548645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1974392712892861025463053 740397267334822884548645)
    ·
      refine ⟨138824487625279290852871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 740397267334822884548645 138824487625279290852871)
      ·
        refine ⟨208236731437918936279307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138824487625279290852871 208236731437918936279307)
        ·
          refine ⟨312355097156878404418961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208236731437918936279307 312355097156878404418961)
          ·
            refine ⟨234266322867658803314221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312355097156878404418961 234266322867658803314221)
            ·
              refine ⟨87849871075372051242833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234266322867658803314221 87849871075372051242833)
              ·
                refine ⟨65887403306529038432125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87849871075372051242833 65887403306529038432125)
                ·
                  refine ⟨24707776239948389412047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65887403306529038432125 24707776239948389412047)
                  ·
                    rfl

theorem cell20_54133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_54133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54133 prefixEnd_54133 := by exact prefixLift 54133
  have htrace : WordTrace (prefixWord ++ tailWord_54133) baseStart_54133 baseEnd_54133 := by
    simpa [prefixWord, tailWord_54133, baseEnd_54133] using wordTrace_append hprefix tailTrace_54133
  have hstable : (prefixWord ++ tailWord_54133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54133).length < 2 ^ (prefixWord ++ tailWord_54133).sum := by decide
  have hdescent : baseEnd_54133 < baseStart_54133 := by decide
  rcases family_descends (prefixWord ++ tailWord_54133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54146 : List Nat := [3, 4, 2, 2, 1, 1, 3, 1, 3]
def baseStart_54146 : Nat := 118140960795 + 54146 * 2 ^ 59
def prefixEnd_54146 : Nat := 4983230072969 + 3 ^ 40 * 54146 * 2
def baseEnd_54146 : Nat := 24713709794178121978661

theorem tailTrace_54146 : CollatzResearch.WordTrace tailWord_54146 prefixEnd_54146 24713709794178121978661 := by
  unfold tailWord_54146
  simp only [CollatzResearch.WordTrace]
  refine ⟨493716715461441061421573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1316577907897176163790861 493716715461441061421573)
  ·
    refine ⟨92571884149020199016545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 493716715461441061421573 92571884149020199016545)
    ·
      refine ⟨69428913111765149262409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92571884149020199016545 69428913111765149262409)
      ·
        refine ⟨52071684833823861946807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69428913111765149262409 52071684833823861946807)
        ·
          refine ⟨78107527250735792920211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52071684833823861946807 78107527250735792920211)
          ·
            refine ⟨117161290876103689380317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78107527250735792920211 117161290876103689380317)
            ·
              refine ⟨43935484078538883517619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117161290876103689380317 43935484078538883517619)
              ·
                refine ⟨65903226117808325276429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43935484078538883517619 65903226117808325276429)
                ·
                  refine ⟨24713709794178121978661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65903226117808325276429 24713709794178121978661)
                  ·
                    rfl

theorem cell20_54146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_54146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54146 prefixEnd_54146 := by exact prefixLift 54146
  have htrace : WordTrace (prefixWord ++ tailWord_54146) baseStart_54146 baseEnd_54146 := by
    simpa [prefixWord, tailWord_54146, baseEnd_54146] using wordTrace_append hprefix tailTrace_54146
  have hstable : (prefixWord ++ tailWord_54146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54146).length < 2 ^ (prefixWord ++ tailWord_54146).sum := by decide
  have hdescent : baseEnd_54146 < baseStart_54146 := by decide
  rcases family_descends (prefixWord ++ tailWord_54146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54198 : List Nat := [5, 1, 4, 1, 1, 1, 2, 5]
def baseStart_54198 : Nat := 118140960795 + 54198 * 2 ^ 59
def prefixEnd_54198 : Nat := 4983230072969 + 3 ^ 40 * 54198 * 2
def baseEnd_54198 : Nat := 8245814670365684081705

theorem tailTrace_54198 : CollatzResearch.WordTrace tailWord_54198 prefixEnd_54198 8245814670365684081705 := by
  unfold tailWord_54198
  simp only [CollatzResearch.WordTrace]
  refine ⟨123547716103586070411203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1317842305104918084386165 123547716103586070411203)
  ·
    refine ⟨185321574155379105616805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123547716103586070411203 185321574155379105616805)
    ·
      refine ⟨34747795154133582303151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185321574155379105616805 34747795154133582303151)
      ·
        refine ⟨52121692731200373454727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34747795154133582303151 52121692731200373454727)
        ·
          refine ⟨78182539096800560182091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52121692731200373454727 78182539096800560182091)
          ·
            refine ⟨117273808645200840273137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78182539096800560182091 117273808645200840273137)
            ·
              refine ⟨87955356483900630204853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117273808645200840273137 87955356483900630204853)
              ·
                refine ⟨8245814670365684081705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87955356483900630204853 8245814670365684081705)
                ·
                  rfl

theorem cell20_54198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_54198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54198 prefixEnd_54198 := by exact prefixLift 54198
  have htrace : WordTrace (prefixWord ++ tailWord_54198) baseStart_54198 baseEnd_54198 := by
    simpa [prefixWord, tailWord_54198, baseEnd_54198] using wordTrace_append hprefix tailTrace_54198
  have hstable : (prefixWord ++ tailWord_54198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54198).length < 2 ^ (prefixWord ++ tailWord_54198).sum := by decide
  have hdescent : baseEnd_54198 < baseStart_54198 := by decide
  rcases family_descends (prefixWord ++ tailWord_54198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54199 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 4]
def baseStart_54199 : Nat := 118140960795 + 54199 * 2 ^ 59
def prefixEnd_54199 : Nat := 4983230072969 + 3 ^ 40 * 54199 * 2
def baseEnd_54199 : Nat := 24737900438345493211777

theorem tailTrace_54199 : CollatzResearch.WordTrace tailWord_54199 prefixEnd_54199 24737900438345493211777 := by
  unfold tailWord_54199
  simp only [CollatzResearch.WordTrace]
  refine ⟨1976799930653754297365651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1317866620435836198243767 1976799930653754297365651)
  ·
    refine ⟨2965199895980631446048477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1976799930653754297365651 2965199895980631446048477)
    ·
      refine ⟨1111949960992736792268179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2965199895980631446048477 1111949960992736792268179)
      ·
        refine ⟨1667924941489105188402269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1111949960992736792268179 1667924941489105188402269)
        ·
          refine ⟨625471853058414445650851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1667924941489105188402269 625471853058414445650851)
          ·
            refine ⟨938207779587621668476277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625471853058414445650851 938207779587621668476277)
            ·
              refine ⟨87956979336339531419651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 938207779587621668476277 87956979336339531419651)
              ·
                refine ⟨131935469004509297129477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87956979336339531419651 131935469004509297129477)
                ·
                  refine ⟨24737900438345493211777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131935469004509297129477 24737900438345493211777)
                  ·
                    rfl

theorem cell20_54199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_54199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54199 prefixEnd_54199 := by exact prefixLift 54199
  have htrace : WordTrace (prefixWord ++ tailWord_54199) baseStart_54199 baseEnd_54199 := by
    simpa [prefixWord, tailWord_54199, baseEnd_54199] using wordTrace_append hprefix tailTrace_54199
  have hstable : (prefixWord ++ tailWord_54199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54199).length < 2 ^ (prefixWord ++ tailWord_54199).sum := by decide
  have hdescent : baseEnd_54199 < baseStart_54199 := by decide
  rcases family_descends (prefixWord ++ tailWord_54199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54205 : List Nat := [1, 4, 1, 2, 5, 1, 2, 1, 3]
def baseStart_54205 : Nat := 118140960795 + 54205 * 2 ^ 59
def prefixEnd_54205 : Nat := 4983230072969 + 3 ^ 40 * 54205 * 2
def baseEnd_54205 : Nat := 24740639001836139011753

theorem tailTrace_54205 : CollatzResearch.WordTrace tailWord_54205 prefixEnd_54205 24740639001836139011753 := by
  unfold tailWord_54205
  simp only [CollatzResearch.WordTrace]
  refine ⟨1977018768632017322084069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1318012512421344881389379 1977018768632017322084069)
  ·
    refine ⟨370691019118503247890763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1977018768632017322084069 370691019118503247890763)
    ·
      refine ⟨556036528677754871836145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370691019118503247890763 556036528677754871836145)
      ·
        refine ⟨417027396508316153877109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556036528677754871836145 417027396508316153877109)
        ·
          refine ⟨39096318422654639425979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 417027396508316153877109 39096318422654639425979)
          ·
            refine ⟨58644477633981959138969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39096318422654639425979 58644477633981959138969)
            ·
              refine ⟨43983358225486469354227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58644477633981959138969 43983358225486469354227)
              ·
                refine ⟨65975037338229704031341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43983358225486469354227 65975037338229704031341)
                ·
                  refine ⟨24740639001836139011753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65975037338229704031341 24740639001836139011753)
                  ·
                    rfl

theorem cell20_54205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_54205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54205 prefixEnd_54205 := by exact prefixLift 54205
  have htrace : WordTrace (prefixWord ++ tailWord_54205) baseStart_54205 baseEnd_54205 := by
    simpa [prefixWord, tailWord_54205, baseEnd_54205] using wordTrace_append hprefix tailTrace_54205
  have hstable : (prefixWord ++ tailWord_54205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54205).length < 2 ^ (prefixWord ++ tailWord_54205).sum := by decide
  have hdescent : baseEnd_54205 < baseStart_54205 := by decide
  rcases family_descends (prefixWord ++ tailWord_54205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54247 : List Nat := [1, 1, 5, 2, 2, 2, 2, 2, 3]
def baseStart_54247 : Nat := 118140960795 + 54247 * 2 ^ 59
def prefixEnd_54247 : Nat := 4983230072969 + 3 ^ 40 * 54247 * 2
def baseEnd_54247 : Nat := 24759808946270659611581

theorem tailTrace_54247 : CollatzResearch.WordTrace tailWord_54247 prefixEnd_54247 24759808946270659611581 := by
  unfold tailWord_54247
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978550634479858495112995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1319033756319905663408663 1978550634479858495112995)
  ·
    refine ⟨2967825951719787742669493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1978550634479858495112995 2967825951719787742669493)
    ·
      refine ⟨278233682973730100875265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2967825951719787742669493 278233682973730100875265)
      ·
        refine ⟨208675262230297575656449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278233682973730100875265 208675262230297575656449)
        ·
          refine ⟨156506446672723181742337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208675262230297575656449 156506446672723181742337)
          ·
            refine ⟨117379835004542386306753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156506446672723181742337 117379835004542386306753)
            ·
              refine ⟨88034876253406789730065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117379835004542386306753 88034876253406789730065)
              ·
                refine ⟨66026157190055092297549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88034876253406789730065 66026157190055092297549)
                ·
                  refine ⟨24759808946270659611581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66026157190055092297549 24759808946270659611581)
                  ·
                    rfl

theorem cell20_54247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 3].length) (baseStart_54247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54247 prefixEnd_54247 := by exact prefixLift 54247
  have htrace : WordTrace (prefixWord ++ tailWord_54247) baseStart_54247 baseEnd_54247 := by
    simpa [prefixWord, tailWord_54247, baseEnd_54247] using wordTrace_append hprefix tailTrace_54247
  have hstable : (prefixWord ++ tailWord_54247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54247).length < 2 ^ (prefixWord ++ tailWord_54247).sum := by decide
  have hdescent : baseEnd_54247 < baseStart_54247 := by decide
  rcases family_descends (prefixWord ++ tailWord_54247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54250 : List Nat := [3, 1, 3, 1, 2, 4, 2, 2, 2]
def baseStart_54250 : Nat := 118140960795 + 54250 * 2 ^ 59
def prefixEnd_54250 : Nat := 4983230072969 + 3 ^ 40 * 54250 * 2
def baseEnd_54250 : Nat := 24761178228015982511569

theorem tailTrace_54250 : CollatzResearch.WordTrace tailWord_54250 prefixEnd_54250 24761178228015982511569 := by
  unfold tailWord_54250
  simp only [CollatzResearch.WordTrace]
  refine ⟨494665013367247501868051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1319106702312660004981469 494665013367247501868051)
  ·
    refine ⟨741997520050871252802077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 494665013367247501868051 741997520050871252802077)
    ·
      refine ⟨278249070019076719800779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 741997520050871252802077 278249070019076719800779)
      ·
        refine ⟨417373605028615079701169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278249070019076719800779 417373605028615079701169)
        ·
          refine ⟨313030203771461309775877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417373605028615079701169 313030203771461309775877)
          ·
            refine ⟨58693163207148995582977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313030203771461309775877 58693163207148995582977)
            ·
              refine ⟨44019872405361746687233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58693163207148995582977 44019872405361746687233)
              ·
                refine ⟨33014904304021310015425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44019872405361746687233 33014904304021310015425)
                ·
                  refine ⟨24761178228015982511569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33014904304021310015425 24761178228015982511569)
                  ·
                    rfl

theorem cell20_54250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_54250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54250 prefixEnd_54250 := by exact prefixLift 54250
  have htrace : WordTrace (prefixWord ++ tailWord_54250) baseStart_54250 baseEnd_54250 := by
    simpa [prefixWord, tailWord_54250, baseEnd_54250] using wordTrace_append hprefix tailTrace_54250
  have hstable : (prefixWord ++ tailWord_54250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54250).length < 2 ^ (prefixWord ++ tailWord_54250).sum := by decide
  have hdescent : baseEnd_54250 < baseStart_54250 := by decide
  rcases family_descends (prefixWord ++ tailWord_54250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54268 : List Nat := [2, 2, 2, 1, 2, 3, 2, 3, 3]
def baseStart_54268 : Nat := 118140960795 + 54268 * 2 ^ 59
def prefixEnd_54268 : Nat := 4983230072969 + 3 ^ 40 * 54268 * 2
def baseEnd_54268 : Nat := 24769393918487919911495

theorem tailTrace_54268 : CollatzResearch.WordTrace tailWord_54268 prefixEnd_54268 24769393918487919911495 := by
  unfold tailWord_54268
  simp only [CollatzResearch.WordTrace]
  refine ⟨989658283701889540813729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1319544378269186054418305 989658283701889540813729)
  ·
    refine ⟨742243712776417155610297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 989658283701889540813729 742243712776417155610297)
    ·
      refine ⟨556682784582312866707723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 742243712776417155610297 556682784582312866707723)
      ·
        refine ⟨835024176873469300061585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556682784582312866707723 835024176873469300061585)
        ·
          refine ⟨626268132655101975046189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835024176873469300061585 626268132655101975046189)
          ·
            refine ⟨234850549745663240642321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 626268132655101975046189 234850549745663240642321)
            ·
              refine ⟨176137912309247430481741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234850549745663240642321 176137912309247430481741)
              ·
                refine ⟨66051717115967786430653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176137912309247430481741 66051717115967786430653)
                ·
                  refine ⟨24769393918487919911495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66051717115967786430653 24769393918487919911495)
                  ·
                    rfl

theorem cell20_54268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_54268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54268 prefixEnd_54268 := by exact prefixLift 54268
  have htrace : WordTrace (prefixWord ++ tailWord_54268) baseStart_54268 baseEnd_54268 := by
    simpa [prefixWord, tailWord_54268, baseEnd_54268] using wordTrace_append hprefix tailTrace_54268
  have hstable : (prefixWord ++ tailWord_54268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54268).length < 2 ^ (prefixWord ++ tailWord_54268).sum := by decide
  have hdescent : baseEnd_54268 < baseStart_54268 := by decide
  rcases family_descends (prefixWord ++ tailWord_54268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54306 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_54306 : Nat := 118140960795 + 54306 * 2 ^ 59
def prefixEnd_54306 : Nat := 4983230072969 + 3 ^ 40 * 54306 * 2
def baseEnd_54306 : Nat := 24786738153928676644673

theorem tailTrace_54306 : CollatzResearch.WordTrace tailWord_54306 prefixEnd_54306 24786738153928676644673 := by
  unfold tailWord_54306
  simp only [CollatzResearch.WordTrace]
  refine ⟨495175635316527892877693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1320468360844074381007181 495175635316527892877693)
  ·
    refine ⟨185690863243697959829135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 495175635316527892877693 185690863243697959829135)
    ·
      refine ⟨278536294865546939743703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185690863243697959829135 278536294865546939743703)
      ·
        refine ⟨417804442298320409615555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278536294865546939743703 417804442298320409615555)
        ·
          refine ⟨626706663447480614423333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417804442298320409615555 626706663447480614423333)
          ·
            refine ⟨117507499396402615204375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 626706663447480614423333 117507499396402615204375)
            ·
              refine ⟨176261249094603922806563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117507499396402615204375 176261249094603922806563)
              ·
                refine ⟨264391873641905884209845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176261249094603922806563 264391873641905884209845)
                ·
                  refine ⟨24786738153928676644673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264391873641905884209845 24786738153928676644673)
                  ·
                    rfl

theorem cell20_54306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_54306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54306 prefixEnd_54306 := by exact prefixLift 54306
  have htrace : WordTrace (prefixWord ++ tailWord_54306) baseStart_54306 baseEnd_54306 := by
    simpa [prefixWord, tailWord_54306, baseEnd_54306] using wordTrace_append hprefix tailTrace_54306
  have hstable : (prefixWord ++ tailWord_54306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54306).length < 2 ^ (prefixWord ++ tailWord_54306).sum := by decide
  have hdescent : baseEnd_54306 < baseStart_54306 := by decide
  rcases family_descends (prefixWord ++ tailWord_54306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54337 : List Nat := [1, 2, 5, 1, 3, 1, 1, 6]
def baseStart_54337 : Nat := 118140960795 + 54337 * 2 ^ 59
def prefixEnd_54337 : Nat := 4983230072969 + 3 ^ 40 * 54337 * 2
def baseEnd_54337 : Nat := 8266962466210115537071

theorem tailTrace_54337 : CollatzResearch.WordTrace tailWord_54337 prefixEnd_54337 8266962466210115537071 := by
  unfold tailWord_54337
  simp only [CollatzResearch.WordTrace]
  refine ⟨1981833204153803865889265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1321222136102535910592843 1981833204153803865889265)
  ·
    refine ⟨1486374903115352899416949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1981833204153803865889265 1486374903115352899416949)
    ·
      refine ⟨139347647167064334320339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1486374903115352899416949 139347647167064334320339)
      ·
        refine ⟨209021470750596501480509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139347647167064334320339 209021470750596501480509)
        ·
          refine ⟨78383051531473688055191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209021470750596501480509 78383051531473688055191)
          ·
            refine ⟨117574577297210532082787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78383051531473688055191 117574577297210532082787)
            ·
              refine ⟨176361865945815798124181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117574577297210532082787 176361865945815798124181)
              ·
                refine ⟨8266962466210115537071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 176361865945815798124181 8266962466210115537071)
                ·
                  rfl

theorem cell20_54337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 6].length) (baseStart_54337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54337 prefixEnd_54337 := by exact prefixLift 54337
  have htrace : WordTrace (prefixWord ++ tailWord_54337) baseStart_54337 baseEnd_54337 := by
    simpa [prefixWord, tailWord_54337, baseEnd_54337] using wordTrace_append hprefix tailTrace_54337
  have hstable : (prefixWord ++ tailWord_54337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54337).length < 2 ^ (prefixWord ++ tailWord_54337).sum := by decide
  have hdescent : baseEnd_54337 < baseStart_54337 := by decide
  rcases family_descends (prefixWord ++ tailWord_54337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54378 : List Nat := [3, 1, 3, 2, 2, 3, 2, 1, 3]
def baseStart_54378 : Nat := 118140960795 + 54378 * 2 ^ 59
def prefixEnd_54378 : Nat := 4983230072969 + 3 ^ 40 * 54378 * 2
def baseEnd_54378 : Nat := 24819600915816426244379

theorem tailTrace_54378 : CollatzResearch.WordTrace tailWord_54378 prefixEnd_54378 24819600915816426244379 := by
  unfold tailWord_54378
  simp only [CollatzResearch.WordTrace]
  refine ⟨495832149251316967032947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1322219064670178578754525 495832149251316967032947)
  ·
    refine ⟨743748223876975450549421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 495832149251316967032947 743748223876975450549421)
    ·
      refine ⟨278905583953865793956033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 743748223876975450549421 278905583953865793956033)
      ·
        refine ⟨209179187965399345467025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278905583953865793956033 209179187965399345467025)
        ·
          refine ⟨156884390974049509100269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209179187965399345467025 156884390974049509100269)
          ·
            refine ⟨58831646615268565912601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156884390974049509100269 58831646615268565912601)
            ·
              refine ⟨44123734961451424434451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58831646615268565912601 44123734961451424434451)
              ·
                refine ⟨66185602442177136651677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44123734961451424434451 66185602442177136651677)
                ·
                  refine ⟨24819600915816426244379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66185602442177136651677 24819600915816426244379)
                  ·
                    rfl

theorem cell20_54378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_54378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54378 prefixEnd_54378 := by exact prefixLift 54378
  have htrace : WordTrace (prefixWord ++ tailWord_54378) baseStart_54378 baseEnd_54378 := by
    simpa [prefixWord, tailWord_54378, baseEnd_54378] using wordTrace_append hprefix tailTrace_54378
  have hstable : (prefixWord ++ tailWord_54378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54378).length < 2 ^ (prefixWord ++ tailWord_54378).sum := by decide
  have hdescent : baseEnd_54378 < baseStart_54378 := by decide
  rcases family_descends (prefixWord ++ tailWord_54378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54423 : List Nat := [1, 1, 3, 3, 3, 1, 4, 2, 2]
def baseStart_54423 : Nat := 118140960795 + 54423 * 2 ^ 59
def prefixEnd_54423 : Nat := 4983230072969 + 3 ^ 40 * 54423 * 2
def baseEnd_54423 : Nat := 24840140141996269744195

theorem tailTrace_54423 : CollatzResearch.WordTrace tailWord_54423 prefixEnd_54423 24840140141996269744195 := by
  unfold tailWord_54423
  simp only [CollatzResearch.WordTrace]
  refine ⟨1984969881842240553519923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1323313254561493702346615 1984969881842240553519923)
  ·
    refine ⟨2977454822763360830279885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1984969881842240553519923 2977454822763360830279885)
    ·
      refine ⟨1116545558536260311354957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2977454822763360830279885 1116545558536260311354957)
      ·
        refine ⟨418704584451097616758109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1116545558536260311354957 418704584451097616758109)
        ·
          refine ⟨157014219169161606284291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418704584451097616758109 157014219169161606284291)
          ·
            refine ⟨235521328753742409426437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157014219169161606284291 235521328753742409426437)
            ·
              refine ⟨44160249141326701767457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235521328753742409426437 44160249141326701767457)
              ·
                refine ⟨33120186855995026325593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44160249141326701767457 33120186855995026325593)
                ·
                  refine ⟨24840140141996269744195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33120186855995026325593 24840140141996269744195)
                  ·
                    rfl

theorem cell20_54423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 2].length) (baseStart_54423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54423 prefixEnd_54423 := by exact prefixLift 54423
  have htrace : WordTrace (prefixWord ++ tailWord_54423) baseStart_54423 baseEnd_54423 := by
    simpa [prefixWord, tailWord_54423, baseEnd_54423] using wordTrace_append hprefix tailTrace_54423
  have hstable : (prefixWord ++ tailWord_54423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54423).length < 2 ^ (prefixWord ++ tailWord_54423).sum := by decide
  have hdescent : baseEnd_54423 < baseStart_54423 := by decide
  rcases family_descends (prefixWord ++ tailWord_54423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54430 : List Nat := [4, 3, 1, 1, 2, 3, 1, 5]
def baseStart_54430 : Nat := 118140960795 + 54430 * 2 ^ 59
def prefixEnd_54430 : Nat := 4983230072969 + 3 ^ 40 * 54430 * 2
def baseEnd_54430 : Nat := 8281111710911785503611

theorem tailTrace_54430 : CollatzResearch.WordTrace tailWord_54430 prefixEnd_54430 8281111710911785503611 := by
  unfold tailWord_54430
  simp only [CollatzResearch.WordTrace]
  refine ⟨248153149102110093628093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1323483461877920499349829 248153149102110093628093)
  ·
    refine ⟨93057430913291285110535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248153149102110093628093 93057430913291285110535)
    ·
      refine ⟨139586146369936927665803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93057430913291285110535 139586146369936927665803)
      ·
        refine ⟨209379219554905391498705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139586146369936927665803 209379219554905391498705)
        ·
          refine ⟨157034414666179043624029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209379219554905391498705 157034414666179043624029)
          ·
            refine ⟨58887905499817141359011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157034414666179043624029 58887905499817141359011)
            ·
              refine ⟨88331858249725712038517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58887905499817141359011 88331858249725712038517)
              ·
                refine ⟨8281111710911785503611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88331858249725712038517 8281111710911785503611)
                ·
                  rfl

theorem cell20_54430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_54430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54430 prefixEnd_54430 := by exact prefixLift 54430
  have htrace : WordTrace (prefixWord ++ tailWord_54430) baseStart_54430 baseEnd_54430 := by
    simpa [prefixWord, tailWord_54430, baseEnd_54430] using wordTrace_append hprefix tailTrace_54430
  have hstable : (prefixWord ++ tailWord_54430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54430).length < 2 ^ (prefixWord ++ tailWord_54430).sum := by decide
  have hdescent : baseEnd_54430 < baseStart_54430 := by decide
  rcases family_descends (prefixWord ++ tailWord_54430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54448 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_54448 : Nat := 118140960795 + 54448 * 2 ^ 59
def prefixEnd_54448 : Nat := 4983230072969 + 3 ^ 40 * 54448 * 2
def baseEnd_54448 : Nat := 24851550823207293910759

theorem tailTrace_54448 : CollatzResearch.WordTrace tailWord_54448 prefixEnd_54448 24851550823207293910759 := by
  unfold tailWord_54448
  simp only [CollatzResearch.WordTrace]
  refine ⟨992940853375834911589999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1323921137834446548786665 992940853375834911589999)
  ·
    refine ⟨1489411280063752367384999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 992940853375834911589999 1489411280063752367384999)
    ·
      refine ⟨2234116920095628551077499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1489411280063752367384999 2234116920095628551077499)
      ·
        refine ⟨3351175380143442826616249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2234116920095628551077499 3351175380143442826616249)
        ·
          refine ⟨2513381535107582119962187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3351175380143442826616249 2513381535107582119962187)
          ·
            refine ⟨3770072302661373179943281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2513381535107582119962187 3770072302661373179943281)
            ·
              refine ⟨2827554226996029884957461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3770072302661373179943281 2827554226996029884957461)
              ·
                refine ⟨132541604390438900857381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2827554226996029884957461 132541604390438900857381)
                ·
                  refine ⟨24851550823207293910759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132541604390438900857381 24851550823207293910759)
                  ·
                    rfl

theorem cell20_54448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_54448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54448 prefixEnd_54448 := by exact prefixLift 54448
  have htrace : WordTrace (prefixWord ++ tailWord_54448) baseStart_54448 baseEnd_54448 := by
    simpa [prefixWord, tailWord_54448, baseEnd_54448] using wordTrace_append hprefix tailTrace_54448
  have hstable : (prefixWord ++ tailWord_54448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54448).length < 2 ^ (prefixWord ++ tailWord_54448).sum := by decide
  have hdescent : baseEnd_54448 < baseStart_54448 := by decide
  rcases family_descends (prefixWord ++ tailWord_54448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54479 : List Nat := [1, 1, 2, 1, 1, 3, 2, 6, 3]
def baseStart_54479 : Nat := 118140960795 + 54479 * 2 ^ 59
def prefixEnd_54479 : Nat := 4983230072969 + 3 ^ 40 * 54479 * 2
def baseEnd_54479 : Nat := 24865700067908963877299

theorem tailTrace_54479 : CollatzResearch.WordTrace tailWord_54479 prefixEnd_54479 24865700067908963877299 := by
  unfold tailWord_54479
  simp only [CollatzResearch.WordTrace]
  refine ⟨1987012369639362117558491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1324674913092908078372327 1987012369639362117558491)
  ·
    refine ⟨2980518554459043176337737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1987012369639362117558491 2980518554459043176337737)
    ·
      refine ⟨2235388915844282382253303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2980518554459043176337737 2235388915844282382253303)
      ·
        refine ⟨3353083373766423573379955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2235388915844282382253303 3353083373766423573379955)
        ·
          refine ⟨5029625060649635360069933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353083373766423573379955 5029625060649635360069933)
          ·
            refine ⟨1886109397743613260026225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5029625060649635360069933 1886109397743613260026225)
            ·
              refine ⟨1414582048307709945019669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1886109397743613260026225 1414582048307709945019669)
              ·
                refine ⟨66308533514423903672797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1414582048307709945019669 66308533514423903672797)
                ·
                  refine ⟨24865700067908963877299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66308533514423903672797 24865700067908963877299)
                  ·
                    rfl

theorem cell20_54479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 3].length) (baseStart_54479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54479 prefixEnd_54479 := by exact prefixLift 54479
  have htrace : WordTrace (prefixWord ++ tailWord_54479) baseStart_54479 baseEnd_54479 := by
    simpa [prefixWord, tailWord_54479, baseEnd_54479] using wordTrace_append hprefix tailTrace_54479
  have hstable : (prefixWord ++ tailWord_54479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54479).length < 2 ^ (prefixWord ++ tailWord_54479).sum := by decide
  have hdescent : baseEnd_54479 < baseStart_54479 := by decide
  rcases family_descends (prefixWord ++ tailWord_54479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54482 : List Nat := [3, 2, 2, 2, 1, 1, 1, 6, 2]
def baseStart_54482 : Nat := 118140960795 + 54482 * 2 ^ 59
def prefixEnd_54482 : Nat := 4983230072969 + 3 ^ 40 * 54482 * 2
def baseEnd_54482 : Nat := 24867069349654286777287

theorem tailTrace_54482 : CollatzResearch.WordTrace tailWord_54482 prefixEnd_54482 24867069349654286777287 := by
  unfold tailWord_54482
  simp only [CollatzResearch.WordTrace]
  refine ⟨496780447157123407479425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1324747859085662419945133 496780447157123407479425)
  ·
    refine ⟨372585335367842555609569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 496780447157123407479425 372585335367842555609569)
    ·
      refine ⟨279439001525881916707177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372585335367842555609569 279439001525881916707177)
      ·
        refine ⟨209579251144411437530383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279439001525881916707177 209579251144411437530383)
        ·
          refine ⟨314368876716617156295575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209579251144411437530383 314368876716617156295575)
          ·
            refine ⟨471553315074925734443363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314368876716617156295575 471553315074925734443363)
            ·
              refine ⟨707329972612388601665045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471553315074925734443363 707329972612388601665045)
              ·
                refine ⟨33156092466205715703049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 707329972612388601665045 33156092466205715703049)
                ·
                  refine ⟨24867069349654286777287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33156092466205715703049 24867069349654286777287)
                  ·
                    rfl

theorem cell20_54482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_54482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54482 prefixEnd_54482 := by exact prefixLift 54482
  have htrace : WordTrace (prefixWord ++ tailWord_54482) baseStart_54482 baseEnd_54482 := by
    simpa [prefixWord, tailWord_54482, baseEnd_54482] using wordTrace_append hprefix tailTrace_54482
  have hstable : (prefixWord ++ tailWord_54482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54482).length < 2 ^ (prefixWord ++ tailWord_54482).sum := by decide
  have hdescent : baseEnd_54482 < baseStart_54482 := by decide
  rcases family_descends (prefixWord ++ tailWord_54482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54531 : List Nat := [1, 1, 1, 3, 2, 4, 8]
def baseStart_54531 : Nat := 118140960795 + 54531 * 2 ^ 59
def prefixEnd_54531 : Nat := 4983230072969 + 3 ^ 40 * 54531 * 2
def baseEnd_54531 : Nat := 2765492698314210460417

theorem tailTrace_54531 : CollatzResearch.WordTrace tailWord_54531 prefixEnd_54531 2765492698314210460417 := by
  unfold tailWord_54531
  simp only [CollatzResearch.WordTrace]
  refine ⟨1988908965450974998451447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1325939310300649998967631 1988908965450974998451447)
  ·
    refine ⟨2983363448176462497677171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1988908965450974998451447 2983363448176462497677171)
    ·
      refine ⟨4475045172264693746515757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2983363448176462497677171 4475045172264693746515757)
      ·
        refine ⟨1678141939599260154943409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4475045172264693746515757 1678141939599260154943409)
        ·
          refine ⟨1258606454699445116207557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1678141939599260154943409 1258606454699445116207557)
          ·
            refine ⟨235988710256145959288917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1258606454699445116207557 235988710256145959288917)
            ·
              refine ⟨2765492698314210460417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 235988710256145959288917 2765492698314210460417)
              ·
                rfl

theorem cell20_54531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 8].length) (baseStart_54531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54531 prefixEnd_54531 := by exact prefixLift 54531
  have htrace : WordTrace (prefixWord ++ tailWord_54531) baseStart_54531 baseEnd_54531 := by
    simpa [prefixWord, tailWord_54531, baseEnd_54531] using wordTrace_append hprefix tailTrace_54531
  have hstable : (prefixWord ++ tailWord_54531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54531).length < 2 ^ (prefixWord ++ tailWord_54531).sum := by decide
  have hdescent : baseEnd_54531 < baseStart_54531 := by decide
  rcases family_descends (prefixWord ++ tailWord_54531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54582 : List Nat := [5, 1, 2, 3, 2, 7]
def baseStart_54582 : Nat := 118140960795 + 54582 * 2 ^ 59
def prefixEnd_54582 : Nat := 4983230072969 + 3 ^ 40 * 54582 * 2
def baseEnd_54582 : Nat := 922693039796236423835

theorem tailTrace_54582 : CollatzResearch.WordTrace tailWord_54582 prefixEnd_54582 922693039796236423835 := by
  unfold tailWord_54582
  simp only [CollatzResearch.WordTrace]
  refine ⟨124423068016638169284875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1327179392177473805705333 124423068016638169284875)
  ·
    refine ⟨186634602024957253927313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124423068016638169284875 186634602024957253927313)
    ·
      refine ⟨139975951518717940445485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186634602024957253927313 139975951518717940445485)
      ·
        refine ⟨52490981819519227667057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139975951518717940445485 52490981819519227667057)
        ·
          refine ⟨39368236364639420750293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52490981819519227667057 39368236364639420750293)
          ·
            refine ⟨922693039796236423835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 39368236364639420750293 922693039796236423835)
            ·
              rfl

theorem cell20_54582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 7].length) (baseStart_54582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54582 prefixEnd_54582 := by exact prefixLift 54582
  have htrace : WordTrace (prefixWord ++ tailWord_54582) baseStart_54582 baseEnd_54582 := by
    simpa [prefixWord, tailWord_54582, baseEnd_54582] using wordTrace_append hprefix tailTrace_54582
  have hstable : (prefixWord ++ tailWord_54582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54582).length < 2 ^ (prefixWord ++ tailWord_54582).sum := by decide
  have hdescent : baseEnd_54582 < baseStart_54582 := by decide
  rcases family_descends (prefixWord ++ tailWord_54582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54600 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_54600 : Nat := 118140960795 + 54600 * 2 ^ 59
def prefixEnd_54600 : Nat := 4983230072969 + 3 ^ 40 * 54600 * 2
def baseEnd_54600 : Nat := 24920927764970320843471

theorem tailTrace_54600 : CollatzResearch.WordTrace tailWord_54600 prefixEnd_54600 24920927764970320843471 := by
  unfold tailWord_54600
  simp only [CollatzResearch.WordTrace]
  refine ⟨995712801100499891356627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1327617068133999855142169 995712801100499891356627)
  ·
    refine ⟨1493569201650749837034941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 995712801100499891356627 1493569201650749837034941)
    ·
      refine ⟨560088450619031188888103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1493569201650749837034941 560088450619031188888103)
      ·
        refine ⟨840132675928546783332155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560088450619031188888103 840132675928546783332155)
        ·
          refine ⟨1260199013892820174998233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840132675928546783332155 1260199013892820174998233)
          ·
            refine ⟨945149260419615131248675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1260199013892820174998233 945149260419615131248675)
            ·
              refine ⟨1417723890629422696873013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945149260419615131248675 1417723890629422696873013)
              ·
                refine ⟨132911614746508377831845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1417723890629422696873013 132911614746508377831845)
                ·
                  refine ⟨24920927764970320843471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132911614746508377831845 24920927764970320843471)
                  ·
                    rfl

theorem cell20_54600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_54600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54600 prefixEnd_54600 := by exact prefixLift 54600
  have htrace : WordTrace (prefixWord ++ tailWord_54600) baseStart_54600 baseEnd_54600 := by
    simpa [prefixWord, tailWord_54600, baseEnd_54600] using wordTrace_append hprefix tailTrace_54600
  have hstable : (prefixWord ++ tailWord_54600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54600).length < 2 ^ (prefixWord ++ tailWord_54600).sum := by decide
  have hdescent : baseEnd_54600 < baseStart_54600 := by decide
  rcases family_descends (prefixWord ++ tailWord_54600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54665 : List Nat := [1, 2, 1, 1, 7, 1, 3, 1, 3]
def baseStart_54665 : Nat := 118140960795 + 54665 * 2 ^ 59
def prefixEnd_54665 : Nat := 4983230072969 + 3 ^ 40 * 54665 * 2
def baseEnd_54665 : Nat := 24950595536118983676539

theorem tailTrace_54665 : CollatzResearch.WordTrace tailWord_54665 prefixEnd_54665 24950595536118983676539 := by
  unfold tailWord_54665
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993796346965515883829449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1329197564643677255886299 1993796346965515883829449)
  ·
    refine ⟨1495347260224136912872087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1993796346965515883829449 1495347260224136912872087)
    ·
      refine ⟨2243020890336205369308131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1495347260224136912872087 2243020890336205369308131)
      ·
        refine ⟨3364531335504308053962197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243020890336205369308131 3364531335504308053962197)
        ·
          refine ⟨78856203175882220014739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3364531335504308053962197 78856203175882220014739)
          ·
            refine ⟨118284304763823330022109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78856203175882220014739 118284304763823330022109)
            ·
              refine ⟨44356614286433748758291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118284304763823330022109 44356614286433748758291)
              ·
                refine ⟨66534921429650623137437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44356614286433748758291 66534921429650623137437)
                ·
                  refine ⟨24950595536118983676539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66534921429650623137437 24950595536118983676539)
                  ·
                    rfl

theorem cell20_54665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_54665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54665 prefixEnd_54665 := by exact prefixLift 54665
  have htrace : WordTrace (prefixWord ++ tailWord_54665) baseStart_54665 baseEnd_54665 := by
    simpa [prefixWord, tailWord_54665, baseEnd_54665] using wordTrace_append hprefix tailTrace_54665
  have hstable : (prefixWord ++ tailWord_54665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54665).length < 2 ^ (prefixWord ++ tailWord_54665).sum := by decide
  have hdescent : baseEnd_54665 < baseStart_54665 := by decide
  rcases family_descends (prefixWord ++ tailWord_54665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54693 : List Nat := [1, 3, 1, 2, 1, 1, 2, 7, 2]
def baseStart_54693 : Nat := 118140960795 + 54693 * 2 ^ 59
def prefixEnd_54693 : Nat := 4983230072969 + 3 ^ 40 * 54693 * 2
def baseEnd_54693 : Nat := 24963375499075330743091

theorem tailTrace_54693 : CollatzResearch.WordTrace tailWord_54693 prefixEnd_54693 24963375499075330743091 := by
  unfold tailWord_54693
  simp only [CollatzResearch.WordTrace]
  refine ⟨1994817590864076665848733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1329878393909384443899155 1994817590864076665848733)
  ·
    refine ⟨748056596574028749693275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1994817590864076665848733 748056596574028749693275)
    ·
      refine ⟨1122084894861043124539913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 748056596574028749693275 1122084894861043124539913)
      ·
        refine ⟨841563671145782343404935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1122084894861043124539913 841563671145782343404935)
        ·
          refine ⟨1262345506718673515107403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841563671145782343404935 1262345506718673515107403)
          ·
            refine ⟨1893518260078010272661105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262345506718673515107403 1893518260078010272661105)
            ·
              refine ⟨1420138695058507704495829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1893518260078010272661105 1420138695058507704495829)
              ·
                refine ⟨33284500665433774324121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1420138695058507704495829 33284500665433774324121)
                ·
                  refine ⟨24963375499075330743091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33284500665433774324121 24963375499075330743091)
                  ·
                    rfl

theorem cell20_54693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_54693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54693 prefixEnd_54693 := by exact prefixLift 54693
  have htrace : WordTrace (prefixWord ++ tailWord_54693) baseStart_54693 baseEnd_54693 := by
    simpa [prefixWord, tailWord_54693, baseEnd_54693] using wordTrace_append hprefix tailTrace_54693
  have hstable : (prefixWord ++ tailWord_54693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54693).length < 2 ^ (prefixWord ++ tailWord_54693).sum := by decide
  have hdescent : baseEnd_54693 < baseStart_54693 := by decide
  rcases family_descends (prefixWord ++ tailWord_54693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54696 : List Nat := [2, 1, 6, 1, 3, 1, 6]
def baseStart_54696 : Nat := 118140960795 + 54696 * 2 ^ 59
def prefixEnd_54696 : Nat := 4983230072969 + 3 ^ 40 * 54696 * 2
def baseEnd_54696 : Nat := 2773860531202294849231

theorem tailTrace_54696 : CollatzResearch.WordTrace tailWord_54696 prefixEnd_54696 2773860531202294849231 := by
  unfold tailWord_54696
  simp only [CollatzResearch.WordTrace]
  refine ⟨997463504926604089103971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1329951339902138785471961 997463504926604089103971)
  ·
    refine ⟨1496195257389906133655957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 997463504926604089103971 1496195257389906133655957)
    ·
      refine ⟨70134152690151850015123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1496195257389906133655957 70134152690151850015123)
      ·
        refine ⟨105201229035227775022685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70134152690151850015123 105201229035227775022685)
        ·
          refine ⟨39450460888210415633507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105201229035227775022685 39450460888210415633507)
          ·
            refine ⟨59175691332315623450261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39450460888210415633507 59175691332315623450261)
            ·
              refine ⟨2773860531202294849231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59175691332315623450261 2773860531202294849231)
              ·
                rfl

theorem cell20_54696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 6].length) (baseStart_54696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54696 prefixEnd_54696 := by exact prefixLift 54696
  have htrace : WordTrace (prefixWord ++ tailWord_54696) baseStart_54696 baseEnd_54696 := by
    simpa [prefixWord, tailWord_54696, baseEnd_54696] using wordTrace_append hprefix tailTrace_54696
  have hstable : (prefixWord ++ tailWord_54696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54696).length < 2 ^ (prefixWord ++ tailWord_54696).sum := by decide
  have hdescent : baseEnd_54696 < baseStart_54696 := by decide
  rcases family_descends (prefixWord ++ tailWord_54696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54759 : List Nat := [1, 1, 5, 2, 1, 10]
def baseStart_54759 : Nat := 118140960795 + 54759 * 2 ^ 59
def prefixEnd_54759 : Nat := 4983230072969 + 3 ^ 40 * 54759 * 2
def baseEnd_54759 : Nat := 925685173980460538623

theorem tailTrace_54759 : CollatzResearch.WordTrace tailWord_54759 prefixEnd_54759 925685173980460538623 := by
  unfold tailWord_54759
  simp only [CollatzResearch.WordTrace]
  refine ⟨1997224808624969937751331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1331483205749979958500887 1997224808624969937751331)
  ·
    refine ⟨2995837212937454906626997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1997224808624969937751331 2995837212937454906626997)
    ·
      refine ⟨280859738712886397496281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2995837212937454906626997 280859738712886397496281)
      ·
        refine ⟨210644804034664798122211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280859738712886397496281 210644804034664798122211)
        ·
          refine ⟨315967206051997197183317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210644804034664798122211 315967206051997197183317)
          ·
            refine ⟨925685173980460538623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 315967206051997197183317 925685173980460538623)
            ·
              rfl

theorem cell20_54759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 10].length) (baseStart_54759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54759 prefixEnd_54759 := by exact prefixLift 54759
  have htrace : WordTrace (prefixWord ++ tailWord_54759) baseStart_54759 baseEnd_54759 := by
    simpa [prefixWord, tailWord_54759, baseEnd_54759] using wordTrace_append hprefix tailTrace_54759
  have hstable : (prefixWord ++ tailWord_54759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54759).length < 2 ^ (prefixWord ++ tailWord_54759).sum := by decide
  have hdescent : baseEnd_54759 < baseStart_54759 := by decide
  rcases family_descends (prefixWord ++ tailWord_54759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54765 : List Nat := [1, 5, 1, 3, 2, 1, 1, 4, 2]
def baseStart_54765 : Nat := 118140960795 + 54765 * 2 ^ 59
def prefixEnd_54765 : Nat := 4983230072969 + 3 ^ 40 * 54765 * 2
def baseEnd_54765 : Nat := 24996238260963080342797

theorem tailTrace_54765 : CollatzResearch.WordTrace tailWord_54765 prefixEnd_54765 24996238260963080342797 := by
  unfold tailWord_54765
  simp only [CollatzResearch.WordTrace]
  refine ⟨1997443646603232962469749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1331629097735488641646499 1997443646603232962469749)
  ·
    refine ⟨187260341869053090231539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1997443646603232962469749 187260341869053090231539)
    ·
      refine ⟨280890512803579635347309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187260341869053090231539 280890512803579635347309)
      ·
        refine ⟨105333942301342363255241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280890512803579635347309 105333942301342363255241)
        ·
          refine ⟨79000456726006772441431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105333942301342363255241 79000456726006772441431)
          ·
            refine ⟨118500685089010158662147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79000456726006772441431 118500685089010158662147)
            ·
              refine ⟨177751027633515237993221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118500685089010158662147 177751027633515237993221)
              ·
                refine ⟨33328317681284107123729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177751027633515237993221 33328317681284107123729)
                ·
                  refine ⟨24996238260963080342797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33328317681284107123729 24996238260963080342797)
                  ·
                    rfl

theorem cell20_54765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_54765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54765 prefixEnd_54765 := by exact prefixLift 54765
  have htrace : WordTrace (prefixWord ++ tailWord_54765) baseStart_54765 baseEnd_54765 := by
    simpa [prefixWord, tailWord_54765, baseEnd_54765] using wordTrace_append hprefix tailTrace_54765
  have hstable : (prefixWord ++ tailWord_54765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54765).length < 2 ^ (prefixWord ++ tailWord_54765).sum := by decide
  have hdescent : baseEnd_54765 < baseStart_54765 := by decide
  rcases family_descends (prefixWord ++ tailWord_54765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54776 : List Nat := [2, 1, 2, 1, 1, 7, 1, 5]
def baseStart_54776 : Nat := 118140960795 + 54776 * 2 ^ 59
def prefixEnd_54776 : Nat := 4983230072969 + 3 ^ 40 * 54776 * 2
def baseEnd_54776 : Nat := 8333752986898643658695

theorem tailTrace_54776 : CollatzResearch.WordTrace tailWord_54776 prefixEnd_54776 8333752986898643658695 := by
  unfold tailWord_54776
  simp only [CollatzResearch.WordTrace]
  refine ⟨998922424781690920560091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1331896566375587894080121 998922424781690920560091)
  ·
    refine ⟨1498383637172536380840137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 998922424781690920560091 1498383637172536380840137)
    ·
      refine ⟨1123787727879402285630103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1498383637172536380840137 1123787727879402285630103)
      ·
        refine ⟨1685681591819103428445155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123787727879402285630103 1685681591819103428445155)
        ·
          refine ⟨2528522387728655142667733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685681591819103428445155 2528522387728655142667733)
          ·
            refine ⟨59262243462390354906275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 2528522387728655142667733 59262243462390354906275)
            ·
              refine ⟨88893365193585532359413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59262243462390354906275 88893365193585532359413)
              ·
                refine ⟨8333752986898643658695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88893365193585532359413 8333752986898643658695)
                ·
                  rfl

theorem cell20_54776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_54776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54776 prefixEnd_54776 := by exact prefixLift 54776
  have htrace : WordTrace (prefixWord ++ tailWord_54776) baseStart_54776 baseEnd_54776 := by
    simpa [prefixWord, tailWord_54776, baseEnd_54776] using wordTrace_append hprefix tailTrace_54776
  have hstable : (prefixWord ++ tailWord_54776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54776).length < 2 ^ (prefixWord ++ tailWord_54776).sum := by decide
  have hdescent : baseEnd_54776 < baseStart_54776 := by decide
  rcases family_descends (prefixWord ++ tailWord_54776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54786 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_54786 : Nat := 118140960795 + 54786 * 2 ^ 59
def prefixEnd_54786 : Nat := 4983230072969 + 3 ^ 40 * 54786 * 2
def baseEnd_54786 : Nat := 25005823233180340642711

theorem tailTrace_54786 : CollatzResearch.WordTrace tailWord_54786 prefixEnd_54786 25005823233180340642711 := by
  unfold tailWord_54786
  simp only [CollatzResearch.WordTrace]
  refine ⟨499552394881788387246053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1332139719684769032656141 499552394881788387246053)
  ·
    refine ⟨93666074040335322608635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 499552394881788387246053 93666074040335322608635)
    ·
      refine ⟨140499111060502983912953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93666074040335322608635 140499111060502983912953)
      ·
        refine ⟨105374333295377237934715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140499111060502983912953 105374333295377237934715)
        ·
          refine ⟨158061499943065856902073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105374333295377237934715 158061499943065856902073)
          ·
            refine ⟨118546124957299392676555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158061499943065856902073 118546124957299392676555)
            ·
              refine ⟨177819187435949089014833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118546124957299392676555 177819187435949089014833)
              ·
                refine ⟨133364390576961816761125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177819187435949089014833 133364390576961816761125)
                ·
                  refine ⟨25005823233180340642711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133364390576961816761125 25005823233180340642711)
                  ·
                    rfl

theorem cell20_54786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_54786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54786 prefixEnd_54786 := by exact prefixLift 54786
  have htrace : WordTrace (prefixWord ++ tailWord_54786) baseStart_54786 baseEnd_54786 := by
    simpa [prefixWord, tailWord_54786, baseEnd_54786] using wordTrace_append hprefix tailTrace_54786
  have hstable : (prefixWord ++ tailWord_54786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54786).length < 2 ^ (prefixWord ++ tailWord_54786).sum := by decide
  have hdescent : baseEnd_54786 < baseStart_54786 := by decide
  rcases family_descends (prefixWord ++ tailWord_54786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54824 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 4]
def baseStart_54824 : Nat := 118140960795 + 54824 * 2 ^ 59
def prefixEnd_54824 : Nat := 4983230072969 + 3 ^ 40 * 54824 * 2
def baseEnd_54824 : Nat := 25023167468621097375889

theorem tailTrace_54824 : CollatzResearch.WordTrace tailWord_54824 prefixEnd_54824 25023167468621097375889 := by
  unfold tailWord_54824
  simp only [CollatzResearch.WordTrace]
  refine ⟨999797776694743019433763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1333063702259657359245017 999797776694743019433763)
  ·
    refine ⟨1499696665042114529150645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 999797776694743019433763 1499696665042114529150645)
    ·
      refine ⟨140596562347698237107873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1499696665042114529150645 140596562347698237107873)
      ·
        refine ⟨105447421760773677830905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140596562347698237107873 105447421760773677830905)
        ·
          refine ⟨79085566320580258373179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105447421760773677830905 79085566320580258373179)
          ·
            refine ⟨118628349480870387559769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79085566320580258373179 118628349480870387559769)
            ·
              refine ⟨88971262110652790669827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118628349480870387559769 88971262110652790669827)
              ·
                refine ⟨133456893165979186004741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88971262110652790669827 133456893165979186004741)
                ·
                  refine ⟨25023167468621097375889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133456893165979186004741 25023167468621097375889)
                  ·
                    rfl

theorem cell20_54824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_54824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54824 prefixEnd_54824 := by exact prefixLift 54824
  have htrace : WordTrace (prefixWord ++ tailWord_54824) baseStart_54824 baseEnd_54824 := by
    simpa [prefixWord, tailWord_54824, baseEnd_54824] using wordTrace_append hprefix tailTrace_54824
  have hstable : (prefixWord ++ tailWord_54824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54824).length < 2 ^ (prefixWord ++ tailWord_54824).sum := by decide
  have hdescent : baseEnd_54824 < baseStart_54824 := by decide
  rcases family_descends (prefixWord ++ tailWord_54824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54883 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 4]
def baseStart_54883 : Nat := 118140960795 + 54883 * 2 ^ 59
def prefixEnd_54883 : Nat := 4983230072969 + 3 ^ 40 * 54883 * 2
def baseEnd_54883 : Nat := 25050096676279114408981

theorem tailTrace_54883 : CollatzResearch.WordTrace tailWord_54883 prefixEnd_54883 25050096676279114408981 := by
  unfold tailWord_54883
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001747460175739115265303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1334498306783826076843535 2001747460175739115265303)
  ·
    refine ⟨3002621190263608672897955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2001747460175739115265303 3002621190263608672897955)
    ·
      refine ⟨4503931785395413009346933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3002621190263608672897955 4503931785395413009346933)
      ·
        refine ⟨422243604880819969626275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4503931785395413009346933 422243604880819969626275)
        ·
          refine ⟨633365407321229954439413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422243604880819969626275 633365407321229954439413)
          ·
            refine ⟨59378006936365308228695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 633365407321229954439413 59378006936365308228695)
            ·
              refine ⟨89067010404547962343043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59378006936365308228695 89067010404547962343043)
              ·
                refine ⟨133600515606821943514565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89067010404547962343043 133600515606821943514565)
                ·
                  refine ⟨25050096676279114408981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133600515606821943514565 25050096676279114408981)
                  ·
                    rfl

theorem cell20_54883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 4].length) (baseStart_54883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54883 prefixEnd_54883 := by exact prefixLift 54883
  have htrace : WordTrace (prefixWord ++ tailWord_54883) baseStart_54883 baseEnd_54883 := by
    simpa [prefixWord, tailWord_54883, baseEnd_54883] using wordTrace_append hprefix tailTrace_54883
  have hstable : (prefixWord ++ tailWord_54883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54883).length < 2 ^ (prefixWord ++ tailWord_54883).sum := by decide
  have hdescent : baseEnd_54883 < baseStart_54883 := by decide
  rcases family_descends (prefixWord ++ tailWord_54883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54890 : List Nat := [3, 1, 3, 2, 1, 3, 2, 5]
def baseStart_54890 : Nat := 118140960795 + 54890 * 2 ^ 59
def prefixEnd_54890 : Nat := 4983230072969 + 3 ^ 40 * 54890 * 2
def baseEnd_54890 : Nat := 8351097222339400391873

theorem tailTrace_54890 : CollatzResearch.WordTrace tailWord_54890 prefixEnd_54890 8351097222339400391873 := by
  unfold tailWord_54890
  simp only [CollatzResearch.WordTrace]
  refine ⟨500500692787594827692531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1334668514100252873846749 500500692787594827692531)
  ·
    refine ⟨750751039181392241538797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 500500692787594827692531 750751039181392241538797)
    ·
      refine ⟨281531639693022090577049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 750751039181392241538797 281531639693022090577049)
      ·
        refine ⟨211148729769766567932787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281531639693022090577049 211148729769766567932787)
        ·
          refine ⟨316723094654649851899181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211148729769766567932787 316723094654649851899181)
          ·
            refine ⟨118771160495493694462193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316723094654649851899181 118771160495493694462193)
            ·
              refine ⟨89078370371620270846645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118771160495493694462193 89078370371620270846645)
              ·
                refine ⟨8351097222339400391873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89078370371620270846645 8351097222339400391873)
                ·
                  rfl

theorem cell20_54890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_54890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54890 prefixEnd_54890 := by exact prefixLift 54890
  have htrace : WordTrace (prefixWord ++ tailWord_54890) baseStart_54890 baseEnd_54890 := by
    simpa [prefixWord, tailWord_54890, baseEnd_54890] using wordTrace_append hprefix tailTrace_54890
  have hstable : (prefixWord ++ tailWord_54890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54890).length < 2 ^ (prefixWord ++ tailWord_54890).sum := by decide
  have hdescent : baseEnd_54890 < baseStart_54890 := by decide
  rcases family_descends (prefixWord ++ tailWord_54890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54935 : List Nat := [1, 1, 3, 3, 2, 2, 1, 4, 3]
def baseStart_54935 : Nat := 118140960795 + 54935 * 2 ^ 59
def prefixEnd_54935 : Nat := 4983230072969 + 3 ^ 40 * 54935 * 2
def baseEnd_54935 : Nat := 25073830893198044675435

theorem tailTrace_54935 : CollatzResearch.WordTrace tailWord_54935 prefixEnd_54935 25073830893198044675435 := by
  unfold tailWord_54935
  simp only [CollatzResearch.WordTrace]
  refine ⟨2003644055987351996158259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1335762703991567997438839 2003644055987351996158259)
  ·
    refine ⟨3005466083981027994237389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2003644055987351996158259 3005466083981027994237389)
    ·
      refine ⟨1127049781492885497839021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3005466083981027994237389 1127049781492885497839021)
      ·
        refine ⟨422643668059832061689633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1127049781492885497839021 422643668059832061689633)
        ·
          refine ⟨316982751044874046267225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422643668059832061689633 316982751044874046267225)
          ·
            refine ⟨237737063283655534700419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316982751044874046267225 237737063283655534700419)
            ·
              refine ⟨356605594925483302050629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237737063283655534700419 356605594925483302050629)
              ·
                refine ⟨66863549048528119134493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 356605594925483302050629 66863549048528119134493)
                ·
                  refine ⟨25073830893198044675435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66863549048528119134493 25073830893198044675435)
                  ·
                    rfl

theorem cell20_54935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 3].length) (baseStart_54935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54935 prefixEnd_54935 := by exact prefixLift 54935
  have htrace : WordTrace (prefixWord ++ tailWord_54935) baseStart_54935 baseEnd_54935 := by
    simpa [prefixWord, tailWord_54935, baseEnd_54935] using wordTrace_append hprefix tailTrace_54935
  have hstable : (prefixWord ++ tailWord_54935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54935).length < 2 ^ (prefixWord ++ tailWord_54935).sum := by decide
  have hdescent : baseEnd_54935 < baseStart_54935 := by decide
  rcases family_descends (prefixWord ++ tailWord_54935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54949 : List Nat := [1, 3, 1, 2, 1, 2, 5, 5]
def baseStart_54949 : Nat := 118140960795 + 54949 * 2 ^ 59
def prefixEnd_54949 : Nat := 4983230072969 + 3 ^ 40 * 54949 * 2
def baseEnd_54949 : Nat := 8360073624892072736237

theorem tailTrace_54949 : CollatzResearch.WordTrace tailWord_54949 prefixEnd_54949 8360073624892072736237 := by
  unfold tailWord_54949
  simp only [CollatzResearch.WordTrace]
  refine ⟨2004154677936632387167901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1336103118624421591445267 2004154677936632387167901)
  ·
    refine ⟨751558004226237145187963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2004154677936632387167901 751558004226237145187963)
    ·
      refine ⟨1127337006339355717781945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 751558004226237145187963 1127337006339355717781945)
      ·
        refine ⟨845502754754516788336459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1127337006339355717781945 845502754754516788336459)
        ·
          refine ⟨1268254132131775182504689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845502754754516788336459 1268254132131775182504689)
          ·
            refine ⟨951190599098831386878517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1268254132131775182504689 951190599098831386878517)
            ·
              refine ⟨89174118665515442519861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 951190599098831386878517 89174118665515442519861)
              ·
                refine ⟨8360073624892072736237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89174118665515442519861 8360073624892072736237)
                ·
                  rfl

theorem cell20_54949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 5].length) (baseStart_54949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54949 prefixEnd_54949 := by exact prefixLift 54949
  have htrace : WordTrace (prefixWord ++ tailWord_54949) baseStart_54949 baseEnd_54949 := by
    simpa [prefixWord, tailWord_54949, baseEnd_54949] using wordTrace_append hprefix tailTrace_54949
  have hstable : (prefixWord ++ tailWord_54949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54949).length < 2 ^ (prefixWord ++ tailWord_54949).sum := by decide
  have hdescent : baseEnd_54949 < baseStart_54949 := by decide
  rcases family_descends (prefixWord ++ tailWord_54949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_54980 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_54980 : Nat := 118140960795 + 54980 * 2 ^ 59
def prefixEnd_54980 : Nat := 4983230072969 + 3 ^ 40 * 54980 * 2
def baseEnd_54980 : Nat := 25094370119377888175251

theorem tailTrace_54980 : CollatzResearch.WordTrace tailWord_54980 prefixEnd_54980 25094370119377888175251 := by
  unfold tailWord_54980
  simp only [CollatzResearch.WordTrace]
  refine ⟨1002642670412162340773197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1336856893882883121030929 1002642670412162340773197)
  ·
    refine ⟨375991001404560877789949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1002642670412162340773197 375991001404560877789949)
    ·
      refine ⟨140996625526710329171231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 375991001404560877789949 140996625526710329171231)
      ·
        refine ⟨211494938290065493756847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140996625526710329171231 211494938290065493756847)
        ·
          refine ⟨317242407435098240635271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211494938290065493756847 317242407435098240635271)
          ·
            refine ⟨475863611152647360952907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317242407435098240635271 475863611152647360952907)
            ·
              refine ⟨713795416728971041429361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475863611152647360952907 713795416728971041429361)
              ·
                refine ⟨535346562546728281072021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713795416728971041429361 535346562546728281072021)
                ·
                  refine ⟨25094370119377888175251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 535346562546728281072021 25094370119377888175251)
                  ·
                    rfl

theorem cell20_54980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_54980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_54980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_54980 prefixEnd_54980 := by exact prefixLift 54980
  have htrace : WordTrace (prefixWord ++ tailWord_54980) baseStart_54980 baseEnd_54980 := by
    simpa [prefixWord, tailWord_54980, baseEnd_54980] using wordTrace_append hprefix tailTrace_54980
  have hstable : (prefixWord ++ tailWord_54980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_54980).length < 2 ^ (prefixWord ++ tailWord_54980).sum := by decide
  have hdescent : baseEnd_54980 < baseStart_54980 := by decide
  rcases family_descends (prefixWord ++ tailWord_54980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55018 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_55018 : Nat := 118140960795 + 55018 * 2 ^ 59
def prefixEnd_55018 : Nat := 4983230072969 + 3 ^ 40 * 55018 * 2
def baseEnd_55018 : Nat := 25111714354818644908429

theorem tailTrace_55018 : CollatzResearch.WordTrace tailWord_55018 prefixEnd_55018 25111714354818644908429 := by
  unfold tailWord_55018
  simp only [CollatzResearch.WordTrace]
  refine ⟨501667828671664292857427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1337780876457771447619805 501667828671664292857427)
  ·
    refine ⟨752501743007496439286141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 501667828671664292857427 752501743007496439286141)
    ·
      refine ⟨282188153627811164732303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 752501743007496439286141 282188153627811164732303)
      ·
        refine ⟨423282230441716747098455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282188153627811164732303 423282230441716747098455)
        ·
          refine ⟨634923345662575120647683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423282230441716747098455 634923345662575120647683)
          ·
            refine ⟨952385018493862680971525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634923345662575120647683 952385018493862680971525)
            ·
              refine ⟨178572190967599252682161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 952385018493862680971525 178572190967599252682161)
              ·
                refine ⟨133929143225699439511621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178572190967599252682161 133929143225699439511621)
                ·
                  refine ⟨25111714354818644908429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133929143225699439511621 25111714354818644908429)
                  ·
                    rfl

theorem cell20_55018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_55018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55018 prefixEnd_55018 := by exact prefixLift 55018
  have htrace : WordTrace (prefixWord ++ tailWord_55018) baseStart_55018 baseEnd_55018 := by
    simpa [prefixWord, tailWord_55018, baseEnd_55018] using wordTrace_append hprefix tailTrace_55018
  have hstable : (prefixWord ++ tailWord_55018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55018).length < 2 ^ (prefixWord ++ tailWord_55018).sum := by decide
  have hdescent : baseEnd_55018 < baseStart_55018 := by decide
  rcases family_descends (prefixWord ++ tailWord_55018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55021 : List Nat := [1, 5, 1, 2, 1, 4, 2, 4]
def baseStart_55021 : Nat := 118140960795 + 55021 * 2 ^ 59
def prefixEnd_55021 : Nat := 4983230072969 + 3 ^ 40 * 55021 * 2
def baseEnd_55021 : Nat := 8371027878854655936139

theorem tailTrace_55021 : CollatzResearch.WordTrace tailWord_55021 prefixEnd_55021 8371027878854655936139 := by
  unfold tailWord_55021
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006780733675788683788917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1337853822450525789192611 2006780733675788683788917)
  ·
    refine ⟨188135693782105189105211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2006780733675788683788917 188135693782105189105211)
    ·
      refine ⟨282203540673157783657817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188135693782105189105211 282203540673157783657817)
      ·
        refine ⟨211652655504868337743363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282203540673157783657817 211652655504868337743363)
        ·
          refine ⟨317478983257302506615045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211652655504868337743363 317478983257302506615045)
          ·
            refine ⟨59527309360744219990321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 317478983257302506615045 59527309360744219990321)
            ·
              refine ⟨44645482020558164992741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59527309360744219990321 44645482020558164992741)
              ·
                refine ⟨8371027878854655936139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44645482020558164992741 8371027878854655936139)
                ·
                  rfl

theorem cell20_55021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 4].length) (baseStart_55021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55021 prefixEnd_55021 := by exact prefixLift 55021
  have htrace : WordTrace (prefixWord ++ tailWord_55021) baseStart_55021 baseEnd_55021 := by
    simpa [prefixWord, tailWord_55021, baseEnd_55021] using wordTrace_append hprefix tailTrace_55021
  have hstable : (prefixWord ++ tailWord_55021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55021).length < 2 ^ (prefixWord ++ tailWord_55021).sum := by decide
  have hdescent : baseEnd_55021 < baseStart_55021 := by decide
  rcases family_descends (prefixWord ++ tailWord_55021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55025 : List Nat := [1, 2, 2, 2, 2, 4, 1, 6]
def baseStart_55025 : Nat := 118140960795 + 55025 * 2 ^ 59
def prefixEnd_55025 : Nat := 4983230072969 + 3 ^ 40 * 55025 * 2
def baseEnd_55025 : Nat := 8371636448519243891689

theorem tailTrace_55025 : CollatzResearch.WordTrace tailWord_55025 prefixEnd_55025 8371636448519243891689 := by
  unfold tailWord_55025
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006926625661297366934529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1337951083774198244623019 2006926625661297366934529)
  ·
    refine ⟨1505194969245973025200897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2006926625661297366934529 1505194969245973025200897)
    ·
      refine ⟨1128896226934479768900673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1505194969245973025200897 1128896226934479768900673)
      ·
        refine ⟨846672170200859826675505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1128896226934479768900673 846672170200859826675505)
        ·
          refine ⟨635004127650644870006629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 846672170200859826675505 635004127650644870006629)
          ·
            refine ⟨119063273934495913126243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 635004127650644870006629 119063273934495913126243)
            ·
              refine ⟨178594910901743869689365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119063273934495913126243 178594910901743869689365)
              ·
                refine ⟨8371636448519243891689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178594910901743869689365 8371636448519243891689)
                ·
                  rfl

theorem cell20_55025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 6].length) (baseStart_55025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55025 prefixEnd_55025 := by exact prefixLift 55025
  have htrace : WordTrace (prefixWord ++ tailWord_55025) baseStart_55025 baseEnd_55025 := by
    simpa [prefixWord, tailWord_55025, baseEnd_55025] using wordTrace_append hprefix tailTrace_55025
  have hstable : (prefixWord ++ tailWord_55025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55025).length < 2 ^ (prefixWord ++ tailWord_55025).sum := by decide
  have hdescent : baseEnd_55025 < baseStart_55025 := by decide
  rcases family_descends (prefixWord ++ tailWord_55025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55039 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 6]
def baseStart_55039 : Nat := 118140960795 + 55039 * 2 ^ 59
def prefixEnd_55039 : Nat := 4983230072969 + 3 ^ 40 * 55039 * 2
def baseEnd_55039 : Nat := 25121299327035905208343

theorem tailTrace_55039 : CollatzResearch.WordTrace tailWord_55039 prefixEnd_55039 25121299327035905208343 := by
  unfold tailWord_55039
  simp only [CollatzResearch.WordTrace]
  refine ⟨2007437247610577757944171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1338291498407051838629447 2007437247610577757944171)
  ·
    refine ⟨3011155871415866636916257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2007437247610577757944171 3011155871415866636916257)
    ·
      refine ⟨2258366903561899977687193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3011155871415866636916257 2258366903561899977687193)
      ·
        refine ⟨1693775177671424983265395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2258366903561899977687193 1693775177671424983265395)
        ·
          refine ⟨2540662766507137474898093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1693775177671424983265395 2540662766507137474898093)
          ·
            refine ⟨952748537440176553086785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2540662766507137474898093 952748537440176553086785)
            ·
              refine ⟨714561403080132414815089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 952748537440176553086785 714561403080132414815089)
              ·
                refine ⟨535921052310099311111317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714561403080132414815089 535921052310099311111317)
                ·
                  refine ⟨25121299327035905208343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 535921052310099311111317 25121299327035905208343)
                  ·
                    rfl

theorem cell20_55039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_55039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55039 prefixEnd_55039 := by exact prefixLift 55039
  have htrace : WordTrace (prefixWord ++ tailWord_55039) baseStart_55039 baseEnd_55039 := by
    simpa [prefixWord, tailWord_55039, baseEnd_55039] using wordTrace_append hprefix tailTrace_55039
  have hstable : (prefixWord ++ tailWord_55039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55039).length < 2 ^ (prefixWord ++ tailWord_55039).sum := by decide
  have hdescent : baseEnd_55039 < baseStart_55039 := by decide
  rcases family_descends (prefixWord ++ tailWord_55039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55063 : List Nat := [1, 1, 3, 4, 2, 1, 1, 7]
def baseStart_55063 : Nat := 118140960795 + 55063 * 2 ^ 59
def prefixEnd_55063 : Nat := 4983230072969 + 3 ^ 40 * 55063 * 2
def baseEnd_55063 : Nat := 8377417860332829469415

theorem tailTrace_55063 : CollatzResearch.WordTrace tailWord_55063 prefixEnd_55063 8377417860332829469415 := by
  unfold tailWord_55063
  simp only [CollatzResearch.WordTrace]
  refine ⟨2008312599523629856817843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1338875066349086571211895 2008312599523629856817843)
  ·
    refine ⟨3012468899285444785226765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2008312599523629856817843 3012468899285444785226765)
    ·
      refine ⟨1129675837232041794460037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3012468899285444785226765 1129675837232041794460037)
      ·
        refine ⟨211814219481007836461257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1129675837232041794460037 211814219481007836461257)
        ·
          refine ⟨158860664610755877345943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211814219481007836461257 158860664610755877345943)
          ·
            refine ⟨238290996916133816018915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158860664610755877345943 238290996916133816018915)
            ·
              refine ⟨357436495374200724028373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238290996916133816018915 357436495374200724028373)
              ·
                refine ⟨8377417860332829469415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 357436495374200724028373 8377417860332829469415)
                ·
                  rfl

theorem cell20_55063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 7].length) (baseStart_55063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55063 prefixEnd_55063 := by exact prefixLift 55063
  have htrace : WordTrace (prefixWord ++ tailWord_55063) baseStart_55063 baseEnd_55063 := by
    simpa [prefixWord, tailWord_55063, baseEnd_55063] using wordTrace_append hprefix tailTrace_55063
  have hstable : (prefixWord ++ tailWord_55063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55063).length < 2 ^ (prefixWord ++ tailWord_55063).sum := by decide
  have hdescent : baseEnd_55063 < baseStart_55063 := by decide
  rcases family_descends (prefixWord ++ tailWord_55063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55066 : List Nat := [3, 1, 1, 3, 2, 2, 4, 1, 3]
def baseStart_55066 : Nat := 118140960795 + 55066 * 2 ^ 59
def prefixEnd_55066 : Nat := 4983230072969 + 3 ^ 40 * 55066 * 2
def baseEnd_55066 : Nat := 25133622862743811308233

theorem tailTrace_55066 : CollatzResearch.WordTrace tailWord_55066 prefixEnd_55066 25133622862743811308233 := by
  unfold tailWord_55066
  simp only [CollatzResearch.WordTrace]
  refine ⟨502105504628190342294263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1338948012341840912784701 502105504628190342294263)
  ·
    refine ⟨753158256942285513441395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 502105504628190342294263 753158256942285513441395)
    ·
      refine ⟨1129737385413428270162093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 753158256942285513441395 1129737385413428270162093)
      ·
        refine ⟨423651519530035601310785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1129737385413428270162093 423651519530035601310785)
        ·
          refine ⟨317738639647526700983089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423651519530035601310785 317738639647526700983089)
          ·
            refine ⟨238303979735645025737317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317738639647526700983089 238303979735645025737317)
            ·
              refine ⟨44681996200433442325747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238303979735645025737317 44681996200433442325747)
              ·
                refine ⟨67022994300650163488621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44681996200433442325747 67022994300650163488621)
                ·
                  refine ⟨25133622862743811308233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67022994300650163488621 25133622862743811308233)
                  ·
                    rfl

theorem cell20_55066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_55066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55066 prefixEnd_55066 := by exact prefixLift 55066
  have htrace : WordTrace (prefixWord ++ tailWord_55066) baseStart_55066 baseEnd_55066 := by
    simpa [prefixWord, tailWord_55066, baseEnd_55066] using wordTrace_append hprefix tailTrace_55066
  have hstable : (prefixWord ++ tailWord_55066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55066).length < 2 ^ (prefixWord ++ tailWord_55066).sum := by decide
  have hdescent : baseEnd_55066 < baseStart_55066 := by decide
  rcases family_descends (prefixWord ++ tailWord_55066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55101 : List Nat := [1, 4, 1, 4, 1, 9]
def baseStart_55101 : Nat := 118140960795 + 55101 * 2 ^ 59
def prefixEnd_55101 : Nat := 4983230072969 + 3 ^ 40 * 55101 * 2
def baseEnd_55101 : Nat := 931466585794046116349

theorem tailTrace_55101 : CollatzResearch.WordTrace tailWord_55101 prefixEnd_55101 931466585794046116349 := by
  unfold tailWord_55101
  simp only [CollatzResearch.WordTrace]
  refine ⟨2009698573385962346701157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1339799048923974897800771 2009698573385962346701157)
  ·
    refine ⟨376818482509867940006467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2009698573385962346701157 376818482509867940006467)
    ·
      refine ⟨565227723764801910009701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376818482509867940006467 565227723764801910009701)
      ·
        refine ⟨105980198205900358126819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 565227723764801910009701 105980198205900358126819)
        ·
          refine ⟨158970297308850537190229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105980198205900358126819 158970297308850537190229)
          ·
            refine ⟨931466585794046116349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 158970297308850537190229 931466585794046116349)
            ·
              rfl

theorem cell20_55101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 9].length) (baseStart_55101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55101 prefixEnd_55101 := by exact prefixLift 55101
  have htrace : WordTrace (prefixWord ++ tailWord_55101) baseStart_55101 baseEnd_55101 := by
    simpa [prefixWord, tailWord_55101, baseEnd_55101] using wordTrace_append hprefix tailTrace_55101
  have hstable : (prefixWord ++ tailWord_55101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55101).length < 2 ^ (prefixWord ++ tailWord_55101).sum := by decide
  have hdescent : baseEnd_55101 < baseStart_55101 := by decide
  rcases family_descends (prefixWord ++ tailWord_55101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55125 : List Nat := [1, 3, 2, 2, 2, 2, 2, 3, 3]
def baseStart_55125 : Nat := 118140960795 + 55125 * 2 ^ 59
def prefixEnd_55125 : Nat := 4983230072969 + 3 ^ 40 * 55125 * 2
def baseEnd_55125 : Nat := 25160552070401828341325

theorem tailTrace_55125 : CollatzResearch.WordTrace tailWord_55125 prefixEnd_55125 25160552070401828341325 := by
  unfold tailWord_55125
  simp only [CollatzResearch.WordTrace]
  refine ⟨2010573925299014445574829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1340382616866009630383219 2010573925299014445574829)
  ·
    refine ⟨753965221987130417090561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2010573925299014445574829 753965221987130417090561)
    ·
      refine ⟨565473916490347812817921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 753965221987130417090561 565473916490347812817921)
      ·
        refine ⟨424105437367760859613441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 565473916490347812817921 424105437367760859613441)
        ·
          refine ⟨318079078025820644710081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424105437367760859613441 318079078025820644710081)
          ·
            refine ⟨238559308519365483532561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318079078025820644710081 238559308519365483532561)
            ·
              refine ⟨178919481389524112649421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238559308519365483532561 178919481389524112649421)
              ·
                refine ⟨67094805521071542243533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178919481389524112649421 67094805521071542243533)
                ·
                  refine ⟨25160552070401828341325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67094805521071542243533 25160552070401828341325)
                  ·
                    rfl

theorem cell20_55125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_55125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55125 prefixEnd_55125 := by exact prefixLift 55125
  have htrace : WordTrace (prefixWord ++ tailWord_55125) baseStart_55125 baseEnd_55125 := by
    simpa [prefixWord, tailWord_55125, baseEnd_55125] using wordTrace_append hprefix tailTrace_55125
  have hstable : (prefixWord ++ tailWord_55125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55125).length < 2 ^ (prefixWord ++ tailWord_55125).sum := by decide
  have hdescent : baseEnd_55125 < baseStart_55125 := by decide
  rcases family_descends (prefixWord ++ tailWord_55125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55149 : List Nat := [1, 5, 1, 1, 1, 1, 3, 5, 2]
def baseStart_55149 : Nat := 118140960795 + 55149 * 2 ^ 59
def prefixEnd_55149 : Nat := 4983230072969 + 3 ^ 40 * 55149 * 2
def baseEnd_55149 : Nat := 25171506324364411541227

theorem tailTrace_55149 : CollatzResearch.WordTrace tailWord_55149 prefixEnd_55149 25171506324364411541227 := by
  unfold tailWord_55149
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011449277212066544448501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1340966184808044362965667 2011449277212066544448501)
  ·
    refine ⟨188573369738631238542047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2011449277212066544448501 188573369738631238542047)
    ·
      refine ⟨282860054607946857813071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188573369738631238542047 282860054607946857813071)
      ·
        refine ⟨424290081911920286719607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282860054607946857813071 424290081911920286719607)
        ·
          refine ⟨636435122867880430079411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424290081911920286719607 636435122867880430079411)
          ·
            refine ⟨954652684301820645119117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636435122867880430079411 954652684301820645119117)
            ·
              refine ⟨357994756613182741919669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 954652684301820645119117 357994756613182741919669)
              ·
                refine ⟨33562008432485882054969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 357994756613182741919669 33562008432485882054969)
                ·
                  refine ⟨25171506324364411541227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33562008432485882054969 25171506324364411541227)
                  ·
                    rfl

theorem cell20_55149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_55149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55149 prefixEnd_55149 := by exact prefixLift 55149
  have htrace : WordTrace (prefixWord ++ tailWord_55149) baseStart_55149 baseEnd_55149 := by
    simpa [prefixWord, tailWord_55149, baseEnd_55149] using wordTrace_append hprefix tailTrace_55149
  have hstable : (prefixWord ++ tailWord_55149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55149).length < 2 ^ (prefixWord ++ tailWord_55149).sum := by decide
  have hdescent : baseEnd_55149 < baseStart_55149 := by decide
  rcases family_descends (prefixWord ++ tailWord_55149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
