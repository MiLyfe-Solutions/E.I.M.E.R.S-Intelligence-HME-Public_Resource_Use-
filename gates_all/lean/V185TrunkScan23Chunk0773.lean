import V185TrunkScan23Chunk0772

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4571558 : List Nat := [23]
def baseStart_4571558 : Nat := 118140960795 + 4571558 * 2 ^ 59
def prefixEnd_4571558 : Nat := 4983230072969 + 3 ^ 40 * 4571558 * 2
def baseEnd_4571558 : Nat := 39753536789902115057

theorem tailTrace_4571558 : CollatzResearch.WordTrace tailWord_4571558 prefixEnd_4571558 39753536789902115057 := by
  unfold tailWord_4571558
  simp only [CollatzResearch.WordTrace]
  refine ⟨39753536789902115057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 23 111158945581355733861356885 39753536789902115057)
  ·
    rfl

theorem cell23_4571558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 23].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 23].length) (baseStart_4571558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571558 prefixEnd_4571558 := by exact prefixLift 4571558
  have htrace : WordTrace (prefixWord ++ tailWord_4571558) baseStart_4571558 baseEnd_4571558 := by
    simpa [prefixWord, tailWord_4571558, baseEnd_4571558] using wordTrace_append hprefix tailTrace_4571558
  have hstable : (prefixWord ++ tailWord_4571558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571558).length < 2 ^ (prefixWord ++ tailWord_4571558).sum := by decide
  have hdescent : baseEnd_4571558 < baseStart_4571558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571575 : List Nat := [1, 1, 3, 1, 3, 3, 3, 8]
def baseStart_4571575 : Nat := 118140960795 + 4571575 * 2 ^ 59
def prefixEnd_4571575 : Nat := 4983230072969 + 3 ^ 40 * 4571575 * 2
def baseEnd_4571575 : Nat := 86941308262150237981045

theorem tailTrace_4571575 : CollatzResearch.WordTrace tailWord_4571575 prefixEnd_4571575 86941308262150237981045 := by
  unfold tailWord_4571575
  simp only [CollatzResearch.WordTrace]
  refine ⟨166739038412972012695404179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111159358941981341796936119 166739038412972012695404179)
  ·
    refine ⟨250108557619458019043106269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166739038412972012695404179 250108557619458019043106269)
    ·
      refine ⟨93790709107296757141164851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250108557619458019043106269 93790709107296757141164851)
      ·
        refine ⟨140686063660945135711747277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93790709107296757141164851 140686063660945135711747277)
        ·
          refine ⟨52757273872854425891905229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140686063660945135711747277 52757273872854425891905229)
          ·
            refine ⟨19783977702320409709464461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52757273872854425891905229 19783977702320409709464461)
            ·
              refine ⟨7418991638370153641049173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19783977702320409709464461 7418991638370153641049173)
              ·
                refine ⟨86941308262150237981045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7418991638370153641049173 86941308262150237981045)
                ·
                  rfl

theorem cell23_4571575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 8].length) (baseStart_4571575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571575 prefixEnd_4571575 := by exact prefixLift 4571575
  have htrace : WordTrace (prefixWord ++ tailWord_4571575) baseStart_4571575 baseEnd_4571575 := by
    simpa [prefixWord, tailWord_4571575, baseEnd_4571575] using wordTrace_append hprefix tailTrace_4571575
  have hstable : (prefixWord ++ tailWord_4571575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571575).length < 2 ^ (prefixWord ++ tailWord_4571575).sum := by decide
  have hdescent : baseEnd_4571575 < baseStart_4571575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571582 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_4571582 : Nat := 118140960795 + 4571582 * 2 ^ 59
def prefixEnd_4571582 : Nat := 4983230072969 + 3 ^ 40 * 4571582 * 2
def baseEnd_4571582 : Nat := 2347418917442637898100683

theorem tailTrace_4571582 : CollatzResearch.WordTrace tailWord_4571582 prefixEnd_4571582 2347418917442637898100683 := by
  unfold tailWord_4571582
  simp only [CollatzResearch.WordTrace]
  refine ⟨20842411715493331611363625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111159529149297768593939333 20842411715493331611363625)
  ·
    refine ⟨15631808786619998708522719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20842411715493331611363625 15631808786619998708522719)
    ·
      refine ⟨23447713179929998062784079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15631808786619998708522719 23447713179929998062784079)
      ·
        refine ⟨35171569769894997094176119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23447713179929998062784079 35171569769894997094176119)
        ·
          refine ⟨52757354654842495641264179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35171569769894997094176119 52757354654842495641264179)
          ·
            refine ⟨79136031982263743461896269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52757354654842495641264179 79136031982263743461896269)
            ·
              refine ⟨29676011993348903798211101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79136031982263743461896269 29676011993348903798211101)
              ·
                refine ⟨11128504497505838924329163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29676011993348903798211101 11128504497505838924329163)
                ·
                  refine ⟨16692756746258758386493745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11128504497505838924329163 16692756746258758386493745)
                  ·
                    refine ⟨12519567559694068789870309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16692756746258758386493745 12519567559694068789870309)
                    ·
                      refine ⟨2347418917442637898100683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12519567559694068789870309 2347418917442637898100683)
                      ·
                        rfl

theorem cell23_4571582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_4571582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571582 prefixEnd_4571582 := by exact prefixLift 4571582
  have htrace : WordTrace (prefixWord ++ tailWord_4571582) baseStart_4571582 baseEnd_4571582 := by
    simpa [prefixWord, tailWord_4571582, baseEnd_4571582] using wordTrace_append hprefix tailTrace_4571582
  have hstable : (prefixWord ++ tailWord_4571582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571582).length < 2 ^ (prefixWord ++ tailWord_4571582).sum := by decide
  have hdescent : baseEnd_4571582 < baseStart_4571582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571592 : List Nat := [2, 1, 3, 1, 3, 3, 3, 7]
def baseStart_4571592 : Nat := 118140960795 + 4571592 * 2 ^ 59
def prefixEnd_4571592 : Nat := 4983230072969 + 3 ^ 40 * 4571592 * 2
def baseEnd_4571592 : Nat := 86941631564784550332431

theorem tailTrace_4571592 : CollatzResearch.WordTrace tailWord_4571592 prefixEnd_4571592 86941631564784550332431 := by
  unfold tailWord_4571592
  simp only [CollatzResearch.WordTrace]
  refine ⟨83369829226955212299386515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111159772302606949732515353 83369829226955212299386515)
  ·
    refine ⟨125054743840432818449079773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83369829226955212299386515 125054743840432818449079773)
    ·
      refine ⟨46895528940162306918404915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125054743840432818449079773 46895528940162306918404915)
      ·
        refine ⟨70343293410243460377607373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46895528940162306918404915 70343293410243460377607373)
        ·
          refine ⟨26378735028841297641602765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70343293410243460377607373 26378735028841297641602765)
          ·
            refine ⟨9892025635815486615601037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26378735028841297641602765 9892025635815486615601037)
            ·
              refine ⟨3709509613430807480850389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9892025635815486615601037 3709509613430807480850389)
              ·
                refine ⟨86941631564784550332431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3709509613430807480850389 86941631564784550332431)
                ·
                  rfl

theorem cell23_4571592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 7].length) (baseStart_4571592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571592 prefixEnd_4571592 := by exact prefixLift 4571592
  have htrace : WordTrace (prefixWord ++ tailWord_4571592) baseStart_4571592 baseEnd_4571592 := by
    simpa [prefixWord, tailWord_4571592, baseEnd_4571592] using wordTrace_append hprefix tailTrace_4571592
  have hstable : (prefixWord ++ tailWord_4571592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571592).length < 2 ^ (prefixWord ++ tailWord_4571592).sum := by decide
  have hdescent : baseEnd_4571592 < baseStart_4571592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571606 : List Nat := [5, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_4571606 : Nat := 118140960795 + 4571606 * 2 ^ 59
def prefixEnd_4571606 : Nat := 4983230072969 + 3 ^ 40 * 4571606 * 2
def baseEnd_4571606 : Nat := 2347431240978345804200573

theorem tailTrace_4571606 : CollatzResearch.WordTrace tailWord_4571606 prefixEnd_4571606 2347431240978345804200573 := by
  unfold tailWord_4571606
  simp only [CollatzResearch.WordTrace]
  refine ⟨10421260567241231561861417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111160112717239803326521781 10421260567241231561861417)
  ·
    refine ⟨7815945425430923671396063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10421260567241231561861417 7815945425430923671396063)
    ·
      refine ⟨11723918138146385507094095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7815945425430923671396063 11723918138146385507094095)
      ·
        refine ⟨17585877207219578260641143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11723918138146385507094095 17585877207219578260641143)
        ·
          refine ⟨26378815810829367390961715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17585877207219578260641143 26378815810829367390961715)
          ·
            refine ⟨39568223716244051086442573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26378815810829367390961715 39568223716244051086442573)
            ·
              refine ⟨14838083893591519157415965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39568223716244051086442573 14838083893591519157415965)
              ·
                refine ⟨5564281460096819684030987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14838083893591519157415965 5564281460096819684030987)
                ·
                  refine ⟨8346422190145229526046481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5564281460096819684030987 8346422190145229526046481)
                  ·
                    refine ⟨6259816642608922144534861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8346422190145229526046481 6259816642608922144534861)
                    ·
                      refine ⟨2347431240978345804200573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6259816642608922144534861 2347431240978345804200573)
                      ·
                        rfl

theorem cell23_4571606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_4571606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571606 prefixEnd_4571606 := by exact prefixLift 4571606
  have htrace : WordTrace (prefixWord ++ tailWord_4571606) baseStart_4571606 baseEnd_4571606 := by
    simpa [prefixWord, tailWord_4571606, baseEnd_4571606] using wordTrace_append hprefix tailTrace_4571606
  have hstable : (prefixWord ++ tailWord_4571606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571606).length < 2 ^ (prefixWord ++ tailWord_4571606).sum := by decide
  have hdescent : baseEnd_4571606 < baseStart_4571606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571625 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 2, 3, 4]
def baseStart_4571625 : Nat := 118140960795 + 4571625 * 2 ^ 59
def prefixEnd_4571625 : Nat := 4983230072969 + 3 ^ 40 * 4571625 * 2
def baseEnd_4571625 : Nat := 2347440997110781229862985

theorem tailTrace_4571625 : CollatzResearch.WordTrace tailWord_4571625 prefixEnd_4571625 2347440997110781229862985 := by
  unfold tailWord_4571625
  simp only [CollatzResearch.WordTrace]
  refine ⟨166740862062790871234724329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111160574708527247489816219 166740862062790871234724329)
  ·
    refine ⟨125055646547093153426043247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166740862062790871234724329 125055646547093153426043247)
    ·
      refine ⟨187583469820639730139064871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125055646547093153426043247 187583469820639730139064871)
      ·
        refine ⟨281375204730959595208597307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187583469820639730139064871 281375204730959595208597307)
        ·
          refine ⟨422062807096439392812895961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281375204730959595208597307 422062807096439392812895961)
          ·
            refine ⟨316547105322329544609671971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422062807096439392812895961 316547105322329544609671971)
            ·
              refine ⟨474820657983494316914507957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316547105322329544609671971 474820657983494316914507957)
              ·
                refine ⟨44514436685952592210735121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 474820657983494316914507957 44514436685952592210735121)
                ·
                  refine ⟨33385827514464444158051341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44514436685952592210735121 33385827514464444158051341)
                  ·
                    refine ⟨12519685317924166559269253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33385827514464444158051341 12519685317924166559269253)
                    ·
                      refine ⟨2347440997110781229862985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12519685317924166559269253 2347440997110781229862985)
                      ·
                        rfl

theorem cell23_4571625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_4571625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571625 prefixEnd_4571625 := by exact prefixLift 4571625
  have htrace : WordTrace (prefixWord ++ tailWord_4571625) baseStart_4571625 baseEnd_4571625 := by
    simpa [prefixWord, tailWord_4571625, baseEnd_4571625] using wordTrace_append hprefix tailTrace_4571625
  have hstable : (prefixWord ++ tailWord_4571625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571625).length < 2 ^ (prefixWord ++ tailWord_4571625).sum := by decide
  have hdescent : baseEnd_4571625 < baseStart_4571625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571635 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 2, 6]
def baseStart_4571635 : Nat := 118140960795 + 4571635 * 2 ^ 59
def prefixEnd_4571635 : Nat := 4983230072969 + 3 ^ 40 * 4571635 * 2
def baseEnd_4571635 : Nat := 782482043972442063579313

theorem tailTrace_4571635 : CollatzResearch.WordTrace tailWord_4571635 prefixEnd_4571635 782482043972442063579313 := by
  unfold tailWord_4571635
  simp only [CollatzResearch.WordTrace]
  refine ⟨166741226792754642942588359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111160817861836428628392239 166741226792754642942588359)
  ·
    refine ⟨250111840189131964413882539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166741226792754642942588359 250111840189131964413882539)
    ·
      refine ⟨375167760283697946620823809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250111840189131964413882539 375167760283697946620823809)
      ·
        refine ⟨281375820212773459965617857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375167760283697946620823809 281375820212773459965617857)
        ·
          refine ⟨211031865159580094974213393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281375820212773459965617857 211031865159580094974213393)
          ·
            refine ⟨158273898869685071230660045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211031865159580094974213393 158273898869685071230660045)
            ·
              refine ⟨59352712076131901711497517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158273898869685071230660045 59352712076131901711497517)
              ·
                refine ⟨22257267028549463141811569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59352712076131901711497517 22257267028549463141811569)
                ·
                  refine ⟨16692950271412097356358677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22257267028549463141811569 16692950271412097356358677)
                  ·
                    refine ⟨782482043972442063579313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16692950271412097356358677 782482043972442063579313)
                    ·
                      rfl

theorem cell23_4571635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 6].length) (baseStart_4571635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571635 prefixEnd_4571635 := by exact prefixLift 4571635
  have htrace : WordTrace (prefixWord ++ tailWord_4571635) baseStart_4571635 baseEnd_4571635 := by
    simpa [prefixWord, tailWord_4571635, baseEnd_4571635] using wordTrace_append hprefix tailTrace_4571635
  have hstable : (prefixWord ++ tailWord_4571635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571635).length < 2 ^ (prefixWord ++ tailWord_4571635).sum := by decide
  have hdescent : baseEnd_4571635 < baseStart_4571635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571654 : List Nat := [6, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_4571654 : Nat := 118140960795 + 4571654 * 2 ^ 59
def prefixEnd_4571654 : Nat := 4983230072969 + 3 ^ 40 * 4571654 * 2
def baseEnd_4571654 : Nat := 2347455888049761616400353

theorem tailTrace_4571654 : CollatzResearch.WordTrace tailWord_4571654 prefixEnd_4571654 2347455888049761616400353 := by
  unfold tailWord_4571654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5210684993115181537110313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 111161279853123872791686677 5210684993115181537110313)
  ·
    refine ⟨3908013744836386152832735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5210684993115181537110313 3908013744836386152832735)
    ·
      refine ⟨5862020617254579229249103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3908013744836386152832735 5862020617254579229249103)
      ·
        refine ⟨8793030925881868843873655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5862020617254579229249103 8793030925881868843873655)
        ·
          refine ⟨13189546388822803265810483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8793030925881868843873655 13189546388822803265810483)
          ·
            refine ⟨19784319583234204898715725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13189546388822803265810483 19784319583234204898715725)
            ·
              refine ⟨7419119843712826837018397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19784319583234204898715725 7419119843712826837018397)
              ·
                refine ⟨2782169941392310063881899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7419119843712826837018397 2782169941392310063881899)
                ·
                  refine ⟨4173254912088465095822849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2782169941392310063881899 4173254912088465095822849)
                  ·
                    refine ⟨3129941184066348821867137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4173254912088465095822849 3129941184066348821867137)
                    ·
                      refine ⟨2347455888049761616400353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3129941184066348821867137 2347455888049761616400353)
                      ·
                        rfl

theorem cell23_4571654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_4571654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571654 prefixEnd_4571654 := by exact prefixLift 4571654
  have htrace : WordTrace (prefixWord ++ tailWord_4571654) baseStart_4571654 baseEnd_4571654 := by
    simpa [prefixWord, tailWord_4571654, baseEnd_4571654] using wordTrace_append hprefix tailTrace_4571654
  have hstable : (prefixWord ++ tailWord_4571654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571654).length < 2 ^ (prefixWord ++ tailWord_4571654).sum := by decide
  have hdescent : baseEnd_4571654 < baseStart_4571654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571662 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_4571662 : Nat := 118140960795 + 4571662 * 2 ^ 59
def prefixEnd_4571662 : Nat := 4983230072969 + 3 ^ 40 * 4571662 * 2
def baseEnd_4571662 : Nat := 2347459995894997585100315

theorem tailTrace_4571662 : CollatzResearch.WordTrace tailWord_4571662 prefixEnd_4571662 2347459995894997585100315 := by
  unfold tailWord_4571662
  simp only [CollatzResearch.WordTrace]
  refine ⟨20842776445457103319227655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111161474375771217702547493 20842776445457103319227655)
  ·
    refine ⟨31264164668185654978841483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20842776445457103319227655 31264164668185654978841483)
    ·
      refine ⟨46896247002278482468262225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31264164668185654978841483 46896247002278482468262225)
      ·
        refine ⟨35172185251708861851196669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46896247002278482468262225 35172185251708861851196669)
        ·
          refine ⟨13189569469390823194198751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35172185251708861851196669 13189569469390823194198751)
          ·
            refine ⟨19784354204086234791298127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13189569469390823194198751 19784354204086234791298127)
            ·
              refine ⟨29676531306129352186947191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19784354204086234791298127 29676531306129352186947191)
              ·
                refine ⟨44514796959194028280420787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29676531306129352186947191 44514796959194028280420787)
                ·
                  refine ⟨66772195438791042420631181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44514796959194028280420787 66772195438791042420631181)
                  ·
                    refine ⟨25039573289546640907736693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66772195438791042420631181 25039573289546640907736693)
                    ·
                      refine ⟨2347459995894997585100315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25039573289546640907736693 2347459995894997585100315)
                      ·
                        rfl

theorem cell23_4571662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_4571662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571662 prefixEnd_4571662 := by exact prefixLift 4571662
  have htrace : WordTrace (prefixWord ++ tailWord_4571662) baseStart_4571662 baseEnd_4571662 := by
    simpa [prefixWord, tailWord_4571662, baseEnd_4571662] using wordTrace_append hprefix tailTrace_4571662
  have hstable : (prefixWord ++ tailWord_4571662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571662).length < 2 ^ (prefixWord ++ tailWord_4571662).sum := by decide
  have hdescent : baseEnd_4571662 < baseStart_4571662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571676 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 4, 2, 2]
def baseStart_4571676 : Nat := 118140960795 + 4571676 * 2 ^ 59
def prefixEnd_4571676 : Nat := 4983230072969 + 3 ^ 40 * 4571676 * 2
def baseEnd_4571676 : Nat := 2347467184624160530325251

theorem tailTrace_4571676 : CollatzResearch.WordTrace tailWord_4571676 prefixEnd_4571676 2347467184624160530325251 := by
  unfold tailWord_4571676
  simp only [CollatzResearch.WordTrace]
  refine ⟨83371361092803053472415441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111161814790404071296553921 83371361092803053472415441)
  ·
    refine ⟨62528520819602290104311581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83371361092803053472415441 62528520819602290104311581)
    ·
      refine ⟨23448195307350858789116843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62528520819602290104311581 23448195307350858789116843)
      ·
        refine ⟨35172292961026288183675265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23448195307350858789116843 35172292961026288183675265)
        ·
          refine ⟨26379219720769716137756449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35172292961026288183675265 26379219720769716137756449)
          ·
            refine ⟨19784414790577287103317337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26379219720769716137756449 19784414790577287103317337)
            ·
              refine ⟨14838311092932965327488003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19784414790577287103317337 14838311092932965327488003)
              ·
                refine ⟨22257466639399447991232005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14838311092932965327488003 22257466639399447991232005)
                ·
                  refine ⟨4173274994887396498356001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22257466639399447991232005 4173274994887396498356001)
                  ·
                    refine ⟨3129956246165547373767001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4173274994887396498356001 3129956246165547373767001)
                    ·
                      refine ⟨2347467184624160530325251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3129956246165547373767001 2347467184624160530325251)
                      ·
                        rfl

theorem cell23_4571676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_4571676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571676 prefixEnd_4571676 := by exact prefixLift 4571676
  have htrace : WordTrace (prefixWord ++ tailWord_4571676) baseStart_4571676 baseEnd_4571676 := by
    simpa [prefixWord, tailWord_4571676, baseEnd_4571676] using wordTrace_append hprefix tailTrace_4571676
  have hstable : (prefixWord ++ tailWord_4571676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571676).length < 2 ^ (prefixWord ++ tailWord_4571676).sum := by decide
  have hdescent : baseEnd_4571676 < baseStart_4571676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571687 : List Nat := [1, 1, 7, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_4571687 : Nat := 118140960795 + 4571687 * 2 ^ 59
def prefixEnd_4571687 : Nat := 4983230072969 + 3 ^ 40 * 4571687 * 2
def baseEnd_4571687 : Nat := 2347472832911359987287701

theorem tailTrace_4571687 : CollatzResearch.WordTrace tailWord_4571687 prefixEnd_4571687 2347472832911359987287701 := by
  unfold tailWord_4571687
  simp only [CollatzResearch.WordTrace]
  refine ⟨166743123388566255823481315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111162082259044170548987543 166743123388566255823481315)
  ·
    refine ⟨250114685082849383735221973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166743123388566255823481315 250114685082849383735221973)
    ·
      refine ⟨5862062931629282431294265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 250114685082849383735221973 5862062931629282431294265)
      ·
        refine ⟨4396547198721961823470699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5862062931629282431294265 4396547198721961823470699)
        ·
          refine ⟨6594820798082942735206049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4396547198721961823470699 6594820798082942735206049)
          ·
            refine ⟨4946115598562207051404537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6594820798082942735206049 4946115598562207051404537)
            ·
              refine ⟨3709586698921655288553403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4946115598562207051404537 3709586698921655288553403)
              ·
                refine ⟨5564380048382482932830105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3709586698921655288553403 5564380048382482932830105)
                ·
                  refine ⟨4173285036286862199622579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5564380048382482932830105 4173285036286862199622579)
                  ·
                    refine ⟨6259927554430293299433869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4173285036286862199622579 6259927554430293299433869)
                    ·
                      refine ⟨2347472832911359987287701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6259927554430293299433869 2347472832911359987287701)
                      ·
                        rfl

theorem cell23_4571687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_4571687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571687 prefixEnd_4571687 := by exact prefixLift 4571687
  have htrace : WordTrace (prefixWord ++ tailWord_4571687) baseStart_4571687 baseEnd_4571687 := by
    simpa [prefixWord, tailWord_4571687, baseEnd_4571687] using wordTrace_append hprefix tailTrace_4571687
  have hstable : (prefixWord ++ tailWord_4571687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571687).length < 2 ^ (prefixWord ++ tailWord_4571687).sum := by decide
  have hdescent : baseEnd_4571687 < baseStart_4571687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571692 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 3]
def baseStart_4571692 : Nat := 118140960795 + 4571692 * 2 ^ 59
def prefixEnd_4571692 : Nat := 4983230072969 + 3 ^ 40 * 4571692 * 2
def baseEnd_4571692 : Nat := 2347475400314632467725177

theorem tailTrace_4571692 : CollatzResearch.WordTrace tailWord_4571692 prefixEnd_4571692 2347475400314632467725177 := by
  unfold tailWord_4571692
  simp only [CollatzResearch.WordTrace]
  refine ⟨83371652876774070838706665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111162203835698761118275553 83371652876774070838706665)
  ·
    refine ⟨62528739657580553129029999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83371652876774070838706665 62528739657580553129029999)
    ·
      refine ⟨93793109486370829693544999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62528739657580553129029999 93793109486370829693544999)
      ·
        refine ⟨140689664229556244540317499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93793109486370829693544999 140689664229556244540317499)
        ·
          refine ⟨211034496344334366810476249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140689664229556244540317499 211034496344334366810476249)
          ·
            refine ⟨158275872258250775107857187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211034496344334366810476249 158275872258250775107857187)
            ·
              refine ⟨237413808387376162661785781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158275872258250775107857187 237413808387376162661785781)
              ·
                refine ⟨22257544536316515249542417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 237413808387376162661785781 22257544536316515249542417)
                ·
                  refine ⟨16693158402237386437156813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22257544536316515249542417 16693158402237386437156813)
                  ·
                    refine ⟨6259934400839019913933805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16693158402237386437156813 6259934400839019913933805)
                    ·
                      refine ⟨2347475400314632467725177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6259934400839019913933805 2347475400314632467725177)
                      ·
                        rfl

theorem cell23_4571692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_4571692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571692 prefixEnd_4571692 := by exact prefixLift 4571692
  have htrace : WordTrace (prefixWord ++ tailWord_4571692) baseStart_4571692 baseEnd_4571692 := by
    simpa [prefixWord, tailWord_4571692, baseEnd_4571692] using wordTrace_append hprefix tailTrace_4571692
  have hstable : (prefixWord ++ tailWord_4571692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571692).length < 2 ^ (prefixWord ++ tailWord_4571692).sum := by decide
  have hdescent : baseEnd_4571692 < baseStart_4571692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571712 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 2, 5]
def baseStart_4571712 : Nat := 118140960795 + 4571712 * 2 ^ 59
def prefixEnd_4571712 : Nat := 4983230072969 + 3 ^ 40 * 4571712 * 2
def baseEnd_4571712 : Nat := 782495223309240796491695

theorem tailTrace_4571712 : CollatzResearch.WordTrace tailWord_4571712 prefixEnd_4571712 782495223309240796491695 := by
  unfold tailWord_4571712
  simp only [CollatzResearch.WordTrace]
  refine ⟨83372017606737842546570695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111162690142317123395427593 83372017606737842546570695)
  ·
    refine ⟨125058026410106763819856043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83372017606737842546570695 125058026410106763819856043)
    ·
      refine ⟨187587039615160145729784065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125058026410106763819856043 187587039615160145729784065)
      ·
        refine ⟨140690279711370109297338049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187587039615160145729784065 140690279711370109297338049)
        ·
          refine ⟨105517709783527581973003537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140690279711370109297338049 105517709783527581973003537)
          ·
            refine ⟨79138282337645686479752653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105517709783527581973003537 79138282337645686479752653)
            ·
              refine ⟨29676855876617132429907245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79138282337645686479752653 29676855876617132429907245)
              ·
                refine ⟨11128820953731424661215217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29676855876617132429907245 11128820953731424661215217)
                ·
                  refine ⟨8346615715298568495911413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11128820953731424661215217 8346615715298568495911413)
                  ·
                    refine ⟨782495223309240796491695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8346615715298568495911413 782495223309240796491695)
                    ·
                      rfl

theorem cell23_4571712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 2, 5].length) (baseStart_4571712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571712 prefixEnd_4571712 := by exact prefixLift 4571712
  have htrace : WordTrace (prefixWord ++ tailWord_4571712) baseStart_4571712 baseEnd_4571712 := by
    simpa [prefixWord, tailWord_4571712, baseEnd_4571712] using wordTrace_append hprefix tailTrace_4571712
  have hstable : (prefixWord ++ tailWord_4571712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571712).length < 2 ^ (prefixWord ++ tailWord_4571712).sum := by decide
  have hdescent : baseEnd_4571712 < baseStart_4571712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571722 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_4571722 : Nat := 118140960795 + 4571722 * 2 ^ 59
def prefixEnd_4571722 : Nat := 4983230072969 + 3 ^ 40 * 4571722 * 2
def baseEnd_4571722 : Nat := 2347490804734267350350039

theorem tailTrace_4571722 : CollatzResearch.WordTrace tailWord_4571722 prefixEnd_4571722 2347490804734267350350039 := by
  unfold tailWord_4571722
  simp only [CollatzResearch.WordTrace]
  refine ⟨41686099985859864200251355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111162933295626304534003613 41686099985859864200251355)
  ·
    refine ⟨62529149978789796300377033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41686099985859864200251355 62529149978789796300377033)
    ·
      refine ⟨46896862484092347225282775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62529149978789796300377033 46896862484092347225282775)
      ·
        refine ⟨70345293726138520837924163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46896862484092347225282775 70345293726138520837924163)
        ·
          refine ⟨105517940589207781256886245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70345293726138520837924163 105517940589207781256886245)
          ·
            refine ⟨19784613860476458985666171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105517940589207781256886245 19784613860476458985666171)
            ·
              refine ⟨29676920790714688478499257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19784613860476458985666171 29676920790714688478499257)
              ·
                refine ⟨22257690593036016358874443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29676920790714688478499257 22257690593036016358874443)
                ·
                  refine ⟨33386535889554024538311665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22257690593036016358874443 33386535889554024538311665)
                  ·
                    refine ⟨25039901917165518403733749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33386535889554024538311665 25039901917165518403733749)
                    ·
                      refine ⟨2347490804734267350350039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25039901917165518403733749 2347490804734267350350039)
                      ·
                        rfl

theorem cell23_4571722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_4571722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571722 prefixEnd_4571722 := by exact prefixLift 4571722
  have htrace : WordTrace (prefixWord ++ tailWord_4571722) baseStart_4571722 baseEnd_4571722 := by
    simpa [prefixWord, tailWord_4571722, baseEnd_4571722] using wordTrace_append hprefix tailTrace_4571722
  have hstable : (prefixWord ++ tailWord_4571722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571722).length < 2 ^ (prefixWord ++ tailWord_4571722).sum := by decide
  have hdescent : baseEnd_4571722 < baseStart_4571722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571766 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_4571766 : Nat := 118140960795 + 4571766 * 2 ^ 59
def prefixEnd_4571766 : Nat := 4983230072969 + 3 ^ 40 * 4571766 * 2
def baseEnd_4571766 : Nat := 2347513397883065178199837

theorem tailTrace_4571766 : CollatzResearch.WordTrace tailWord_4571766 prefixEnd_4571766 2347513397883065178199837 := by
  unfold tailWord_4571766
  simp only [CollatzResearch.WordTrace]
  refine ⟨10421625297205003269725447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111164003170186701543738101 10421625297205003269725447)
  ·
    refine ⟨15632437945807504904588171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10421625297205003269725447 15632437945807504904588171)
    ·
      refine ⟨23448656918711257356882257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15632437945807504904588171 23448656918711257356882257)
      ·
        refine ⟨17586492689033443017661693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23448656918711257356882257 17586492689033443017661693)
        ·
          refine ⟨6594934758387541131623135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17586492689033443017661693 6594934758387541131623135)
          ·
            refine ⟨9892402137581311697434703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6594934758387541131623135 9892402137581311697434703)
            ·
              refine ⟨14838603206371967546152055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9892402137581311697434703 14838603206371967546152055)
              ·
                refine ⟨22257904809557951319228083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14838603206371967546152055 22257904809557951319228083)
                ·
                  refine ⟨33386857214336926978842125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22257904809557951319228083 33386857214336926978842125)
                  ·
                    refine ⟨12520071455376347617065797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33386857214336926978842125 12520071455376347617065797)
                    ·
                      refine ⟨2347513397883065178199837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12520071455376347617065797 2347513397883065178199837)
                      ·
                        rfl

theorem cell23_4571766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_4571766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571766 prefixEnd_4571766 := by exact prefixLift 4571766
  have htrace : WordTrace (prefixWord ++ tailWord_4571766) baseStart_4571766 baseEnd_4571766 := by
    simpa [prefixWord, tailWord_4571766, baseEnd_4571766] using wordTrace_append hprefix tailTrace_4571766
  have hstable : (prefixWord ++ tailWord_4571766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571766).length < 2 ^ (prefixWord ++ tailWord_4571766).sum := by decide
  have hdescent : baseEnd_4571766 < baseStart_4571766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571769 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 1, 4, 3]
def baseStart_4571769 : Nat := 118140960795 + 4571769 * 2 ^ 59
def prefixEnd_4571769 : Nat := 4983230072969 + 3 ^ 40 * 4571769 * 2
def baseEnd_4571769 : Nat := 2347514938325028666462323

theorem tailTrace_4571769 : CollatzResearch.WordTrace tailWord_4571769 prefixEnd_4571769 2347514938325028666462323 := by
  unfold tailWord_4571769
  simp only [CollatzResearch.WordTrace]
  refine ⟨166746114174269183827966361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111164076116179455885310907 166746114174269183827966361)
  ·
    refine ⟨125059585630701887870974771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166746114174269183827966361 125059585630701887870974771)
    ·
      refine ⟨187589378446052831806462157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125059585630701887870974771 187589378446052831806462157)
      ·
        refine ⟨70346016917269811927423309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187589378446052831806462157 70346016917269811927423309)
        ·
          refine ⟨26379756343976179472783741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70346016917269811927423309 26379756343976179472783741)
          ·
            refine ⟨9892408628991067302293903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26379756343976179472783741 9892408628991067302293903)
            ·
              refine ⟨14838612943486600953440855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9892408628991067302293903 14838612943486600953440855)
              ·
                refine ⟨22257919415229901430161283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14838612943486600953440855 22257919415229901430161283)
                ·
                  refine ⟨33386879122844852145241925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22257919415229901430161283 33386879122844852145241925)
                  ·
                    refine ⟨6260039835533409777232861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33386879122844852145241925 6260039835533409777232861)
                    ·
                      refine ⟨2347514938325028666462323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6260039835533409777232861 2347514938325028666462323)
                      ·
                        rfl

theorem cell23_4571769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_4571769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571769 prefixEnd_4571769 := by exact prefixLift 4571769
  have htrace : WordTrace (prefixWord ++ tailWord_4571769) baseStart_4571769 baseEnd_4571769 := by
    simpa [prefixWord, tailWord_4571769, baseEnd_4571769] using wordTrace_append hprefix tailTrace_4571769
  have hstable : (prefixWord ++ tailWord_4571769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571769).length < 2 ^ (prefixWord ++ tailWord_4571769).sum := by decide
  have hdescent : baseEnd_4571769 < baseStart_4571769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571776 : List Nat := [2, 1, 1, 2, 1, 5, 1, 5, 1, 4]
def baseStart_4571776 : Nat := 118140960795 + 4571776 * 2 ^ 59
def prefixEnd_4571776 : Nat := 4983230072969 + 3 ^ 40 * 4571776 * 2
def baseEnd_4571776 : Nat := 782506177563203379691597

theorem tailTrace_4571776 : CollatzResearch.WordTrace tailWord_4571776 prefixEnd_4571776 782506177563203379691597 := by
  unfold tailWord_4571776
  simp only [CollatzResearch.WordTrace]
  refine ⟨83373184742621912011735591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111164246323495882682314121 83373184742621912011735591)
  ·
    refine ⟨125059777113932868017603387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83373184742621912011735591 125059777113932868017603387)
    ·
      refine ⟨187589665670899302026405081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125059777113932868017603387 187589665670899302026405081)
      ·
        refine ⟨140692249253174476519803811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187589665670899302026405081 140692249253174476519803811)
        ·
          refine ⟨211038373879761714779705717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140692249253174476519803811 211038373879761714779705717)
          ·
            refine ⟨19784847551227660760597411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 211038373879761714779705717 19784847551227660760597411)
            ·
              refine ⟨29677271326841491140896117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19784847551227660760597411 29677271326841491140896117)
              ·
                refine ⟨2782244186891389794459011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29677271326841491140896117 2782244186891389794459011)
                ·
                  refine ⟨4173366280337084691688517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2782244186891389794459011 4173366280337084691688517)
                  ·
                    refine ⟨782506177563203379691597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4173366280337084691688517 782506177563203379691597)
                    ·
                      rfl

theorem cell23_4571776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 1, 4].length) (baseStart_4571776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571776 prefixEnd_4571776 := by exact prefixLift 4571776
  have htrace : WordTrace (prefixWord ++ tailWord_4571776) baseStart_4571776 baseEnd_4571776 := by
    simpa [prefixWord, tailWord_4571776, baseEnd_4571776] using wordTrace_append hprefix tailTrace_4571776
  have hstable : (prefixWord ++ tailWord_4571776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571776).length < 2 ^ (prefixWord ++ tailWord_4571776).sum := by decide
  have hdescent : baseEnd_4571776 < baseStart_4571776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571826 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2]
def baseStart_4571826 : Nat := 118140960795 + 4571826 * 2 ^ 59
def prefixEnd_4571826 : Nat := 4983230072969 + 3 ^ 40 * 4571826 * 2
def baseEnd_4571826 : Nat := 2347544206722334943449561

theorem tailTrace_4571826 : CollatzResearch.WordTrace tailWord_4571826 prefixEnd_4571826 2347544206722334943449561 := by
  unfold tailWord_4571826
  simp only [CollatzResearch.WordTrace]
  refine ⟨41687048283765670640697833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111165462090041788375194221 41687048283765670640697833)
  ·
    refine ⟨31265286212824252980523375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41687048283765670640697833 31265286212824252980523375)
    ·
      refine ⟨46897929319236379470785063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31265286212824252980523375 46897929319236379470785063)
      ·
        refine ⟨70346893978854569206177595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46897929319236379470785063 70346893978854569206177595)
        ·
          refine ⟨105520340968281853809266393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70346893978854569206177595 105520340968281853809266393)
          ·
            refine ⟨79140255726211390356949795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105520340968281853809266393 79140255726211390356949795)
            ·
              refine ⟨118710383589317085535424693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79140255726211390356949795 118710383589317085535424693)
              ·
                refine ⟨11129098461498476768946065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118710383589317085535424693 11129098461498476768946065)
                ·
                  refine ⟨8346823846123857576709549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11129098461498476768946065 8346823846123857576709549)
                  ·
                    refine ⟨3130058942296446591266081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8346823846123857576709549 3130058942296446591266081)
                    ·
                      refine ⟨2347544206722334943449561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3130058942296446591266081 2347544206722334943449561)
                      ·
                        rfl

theorem cell23_4571826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_4571826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571826 prefixEnd_4571826 := by exact prefixLift 4571826
  have htrace : WordTrace (prefixWord ++ tailWord_4571826) baseStart_4571826 baseEnd_4571826 := by
    simpa [prefixWord, tailWord_4571826, baseEnd_4571826] using wordTrace_append hprefix tailTrace_4571826
  have hstable : (prefixWord ++ tailWord_4571826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571826).length < 2 ^ (prefixWord ++ tailWord_4571826).sum := by decide
  have hdescent : baseEnd_4571826 < baseStart_4571826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571866 : List Nat := [3, 1, 1, 2, 2, 2, 3, 3, 2, 4]
def baseStart_4571866 : Nat := 118140960795 + 4571866 * 2 ^ 59
def prefixEnd_4571866 : Nat := 4983230072969 + 3 ^ 40 * 4571866 * 2
def baseEnd_4571866 : Nat := 782521581982838262316459

theorem tailTrace_4571866 : CollatzResearch.WordTrace tailWord_4571866 prefixEnd_4571866 782521581982838262316459 := by
  unfold tailWord_4571866
  simp only [CollatzResearch.WordTrace]
  refine ⟨41687413013729442348561863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111166434703278512929498301 41687413013729442348561863)
  ·
    refine ⟨62531119520594163522842795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41687413013729442348561863 62531119520594163522842795)
    ·
      refine ⟨93796679280891245284264193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62531119520594163522842795 93796679280891245284264193)
      ·
        refine ⟨70347509460668433963198145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93796679280891245284264193 70347509460668433963198145)
        ·
          refine ⟨52760632095501325472398609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70347509460668433963198145 52760632095501325472398609)
          ·
            refine ⟨39570474071625994104298957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52760632095501325472398609 39570474071625994104298957)
            ·
              refine ⟨14838927776859747789112109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39570474071625994104298957 14838927776859747789112109)
              ·
                refine ⟨5564597916322405420917041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14838927776859747789112109 5564597916322405420917041)
                ·
                  refine ⟨4173448437241804065687781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5564597916322405420917041 4173448437241804065687781)
                  ·
                    refine ⟨782521581982838262316459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4173448437241804065687781 782521581982838262316459)
                    ·
                      rfl

theorem cell23_4571866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_4571866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571866 prefixEnd_4571866 := by exact prefixLift 4571866
  have htrace : WordTrace (prefixWord ++ tailWord_4571866) baseStart_4571866 baseEnd_4571866 := by
    simpa [prefixWord, tailWord_4571866, baseEnd_4571866] using wordTrace_append hprefix tailTrace_4571866
  have hstable : (prefixWord ++ tailWord_4571866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571866).length < 2 ^ (prefixWord ++ tailWord_4571866).sum := by decide
  have hdescent : baseEnd_4571866 < baseStart_4571866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571873 : List Nat := [1, 2, 3, 1, 4, 3, 1, 2, 1, 1, 4]
def baseStart_4571873 : Nat := 118140960795 + 4571873 * 2 ^ 59
def prefixEnd_4571873 : Nat := 4983230072969 + 3 ^ 40 * 4571873 * 2
def baseEnd_4571873 : Nat := 2347568340313096259561845

theorem tailTrace_4571873 : CollatzResearch.WordTrace tailWord_4571873 prefixEnd_4571873 2347568340313096259561845 := by
  unfold tailWord_4571873
  simp only [CollatzResearch.WordTrace]
  refine ⟨166749907365892409589752273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111166604910594939726501515 166749907365892409589752273)
  ·
    refine ⟨125062430524419307192314205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166749907365892409589752273 125062430524419307192314205)
    ·
      refine ⟨46898411446657240197117827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125062430524419307192314205 46898411446657240197117827)
      ·
        refine ⟨70347617169985860295676741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46898411446657240197117827 70347617169985860295676741)
        ·
          refine ⟨13190178219372348805439389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70347617169985860295676741 13190178219372348805439389)
          ·
            refine ⟨4946316832264630802039771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13190178219372348805439389 4946316832264630802039771)
            ·
              refine ⟨7419475248396946203059657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4946316832264630802039771 7419475248396946203059657)
              ·
                refine ⟨5564606436297709652294743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7419475248396946203059657 5564606436297709652294743)
                ·
                  refine ⟨8346909654446564478442115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5564606436297709652294743 8346909654446564478442115)
                  ·
                    refine ⟨12520364481669846717663173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8346909654446564478442115 12520364481669846717663173)
                    ·
                      refine ⟨2347568340313096259561845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12520364481669846717663173 2347568340313096259561845)
                      ·
                        rfl

theorem cell23_4571873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_4571873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571873 prefixEnd_4571873 := by exact prefixLift 4571873
  have htrace : WordTrace (prefixWord ++ tailWord_4571873) baseStart_4571873 baseEnd_4571873 := by
    simpa [prefixWord, tailWord_4571873, baseEnd_4571873] using wordTrace_append hprefix tailTrace_4571873
  have hstable : (prefixWord ++ tailWord_4571873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571873).length < 2 ^ (prefixWord ++ tailWord_4571873).sum := by decide
  have hdescent : baseEnd_4571873 < baseStart_4571873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571876 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_4571876 : Nat := 118140960795 + 4571876 * 2 ^ 59
def prefixEnd_4571876 : Nat := 4983230072969 + 3 ^ 40 * 4571876 * 2
def baseEnd_4571876 : Nat := 2347569880755059747824331

theorem tailTrace_4571876 : CollatzResearch.WordTrace tailWord_4571876 prefixEnd_4571876 2347569880755059747824331 := by
  unfold tailWord_4571876
  simp only [CollatzResearch.WordTrace]
  refine ⟨83375008392440770551055741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111166677856587694068074321 83375008392440770551055741)
  ·
    refine ⟨31265628147165288956645903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83375008392440770551055741 31265628147165288956645903)
    ·
      refine ⟨46898442220747933434968855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31265628147165288956645903 46898442220747933434968855)
      ·
        refine ⟨70347663331121900152453283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46898442220747933434968855 70347663331121900152453283)
        ·
          refine ⟨105521494996682850228679925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70347663331121900152453283 105521494996682850228679925)
          ·
            refine ⟨9892640155939017208938743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105521494996682850228679925 9892640155939017208938743)
            ·
              refine ⟨14838960233908525813408115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9892640155939017208938743 14838960233908525813408115)
              ·
                refine ⟨22258440350862788720112173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14838960233908525813408115 22258440350862788720112173)
                ·
                  refine ⟨8346915131573545770042065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22258440350862788720112173 8346915131573545770042065)
                  ·
                    refine ⟨6260186348680159327531549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8346915131573545770042065 6260186348680159327531549)
                    ·
                      refine ⟨2347569880755059747824331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6260186348680159327531549 2347569880755059747824331)
                      ·
                        rfl

theorem cell23_4571876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_4571876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571876 prefixEnd_4571876 := by exact prefixLift 4571876
  have htrace : WordTrace (prefixWord ++ tailWord_4571876) baseStart_4571876 baseEnd_4571876 := by
    simpa [prefixWord, tailWord_4571876, baseEnd_4571876] using wordTrace_append hprefix tailTrace_4571876
  have hstable : (prefixWord ++ tailWord_4571876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571876).length < 2 ^ (prefixWord ++ tailWord_4571876).sum := by decide
  have hdescent : baseEnd_4571876 < baseStart_4571876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571886 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_4571886 : Nat := 118140960795 + 4571886 * 2 ^ 59
def prefixEnd_4571886 : Nat := 4983230072969 + 3 ^ 40 * 4571886 * 2
def baseEnd_4571886 : Nat := 2347575015561604708699285

theorem tailTrace_4571886 : CollatzResearch.WordTrace tailWord_4571886 prefixEnd_4571886 2347575015561604708699285 := by
  unfold tailWord_4571886
  simp only [CollatzResearch.WordTrace]
  refine ⟨20843797689355664101246939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111166921009896875206650341 20843797689355664101246939)
  ·
    refine ⟨31265696534033496151870409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20843797689355664101246939 31265696534033496151870409)
    ·
      refine ⟨23449272400525122113902807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31265696534033496151870409 23449272400525122113902807)
      ·
        refine ⟨35173908600787683170854211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23449272400525122113902807 35173908600787683170854211)
        ·
          refine ⟨52760862901181524756281317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35173908600787683170854211 52760862901181524756281317)
          ·
            refine ⟨9892661793971535891802747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52760862901181524756281317 9892661793971535891802747)
            ·
              refine ⟨14838992690957303837704121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9892661793971535891802747 14838992690957303837704121)
              ·
                refine ⟨11129244518217977878278091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14838992690957303837704121 11129244518217977878278091)
                ·
                  refine ⟨16693866777326966817417137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11129244518217977878278091 16693866777326966817417137)
                  ·
                    refine ⟨12520400082995225113062853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16693866777326966817417137 12520400082995225113062853)
                    ·
                      refine ⟨2347575015561604708699285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12520400082995225113062853 2347575015561604708699285)
                      ·
                        rfl

theorem cell23_4571886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_4571886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571886 prefixEnd_4571886 := by exact prefixLift 4571886
  have htrace : WordTrace (prefixWord ++ tailWord_4571886) baseStart_4571886 baseEnd_4571886 := by
    simpa [prefixWord, tailWord_4571886, baseEnd_4571886] using wordTrace_append hprefix tailTrace_4571886
  have hstable : (prefixWord ++ tailWord_4571886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571886).length < 2 ^ (prefixWord ++ tailWord_4571886).sum := by decide
  have hdescent : baseEnd_4571886 < baseStart_4571886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571959 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_4571959 : Nat := 118140960795 + 4571959 * 2 ^ 59
def prefixEnd_4571959 : Nat := 4983230072969 + 3 ^ 40 * 4571959 * 2
def baseEnd_4571959 : Nat := 2347612499649382923086449

theorem tailTrace_4571959 : CollatzResearch.WordTrace tailWord_4571959 prefixEnd_4571959 2347612499649382923086449 := by
  unfold tailWord_4571959
  simp only [CollatzResearch.WordTrace]
  refine ⟨166753044043580846277382931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111168696029053897518255287 166753044043580846277382931)
  ·
    refine ⟨250129566065371269416074397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166753044043580846277382931 250129566065371269416074397)
    ·
      refine ⟨93798587274514226031027899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250129566065371269416074397 93798587274514226031027899)
      ·
        refine ⟨140697880911771339046541849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93798587274514226031027899 140697880911771339046541849)
        ·
          refine ⟨105523410683828504284906387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140697880911771339046541849 105523410683828504284906387)
          ·
            refine ⟨158285116025742756427359581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105523410683828504284906387 158285116025742756427359581)
            ·
              refine ⟨59356918509653533660259843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158285116025742756427359581 59356918509653533660259843)
              ·
                refine ⟨89035377764480300490389765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59356918509653533660259843 89035377764480300490389765)
                ·
                  refine ⟨16694133330840056341948081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89035377764480300490389765 16694133330840056341948081)
                  ·
                    refine ⟨12520599998130042256461061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16694133330840056341948081 12520599998130042256461061)
                    ·
                      refine ⟨2347612499649382923086449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12520599998130042256461061 2347612499649382923086449)
                      ·
                        rfl

theorem cell23_4571959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_4571959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571959 prefixEnd_4571959 := by exact prefixLift 4571959
  have htrace : WordTrace (prefixWord ++ tailWord_4571959) baseStart_4571959 baseEnd_4571959 := by
    simpa [prefixWord, tailWord_4571959, baseEnd_4571959] using wordTrace_append hprefix tailTrace_4571959
  have hstable : (prefixWord ++ tailWord_4571959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571959).length < 2 ^ (prefixWord ++ tailWord_4571959).sum := by decide
  have hdescent : baseEnd_4571959 < baseStart_4571959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571974 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_4571974 : Nat := 118140960795 + 4571974 * 2 ^ 59
def prefixEnd_4571974 : Nat := 4983230072969 + 3 ^ 40 * 4571974 * 2
def baseEnd_4571974 : Nat := 2347620201859200364398881

theorem tailTrace_4571974 : CollatzResearch.WordTrace tailWord_4571974 prefixEnd_4571974 2347620201859200364398881 := by
  unfold tailWord_4571974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5211049723078953244974343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 111169060759017669226119317 5211049723078953244974343)
  ·
    refine ⟨7816574584618429867461515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5211049723078953244974343 7816574584618429867461515)
    ·
      refine ⟨11724861876927644801192273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7816574584618429867461515 11724861876927644801192273)
      ·
        refine ⟨8793646407695733600894205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11724861876927644801192273 8793646407695733600894205)
        ·
          refine ⟨3297617402885900100335327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8793646407695733600894205 3297617402885900100335327)
          ·
            refine ⟨4946426104328850150502991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3297617402885900100335327 4946426104328850150502991)
            ·
              refine ⟨7419639156493275225754487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4946426104328850150502991 7419639156493275225754487)
              ·
                refine ⟨11129458734739912838631731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7419639156493275225754487 11129458734739912838631731)
                ·
                  refine ⟨16694188102109869257947597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11129458734739912838631731 16694188102109869257947597)
                  ·
                    refine ⟨6260320538291200971730349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16694188102109869257947597 6260320538291200971730349)
                    ·
                      refine ⟨2347620201859200364398881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6260320538291200971730349 2347620201859200364398881)
                      ·
                        rfl

theorem cell23_4571974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_4571974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571974 prefixEnd_4571974 := by exact prefixLift 4571974
  have htrace : WordTrace (prefixWord ++ tailWord_4571974) baseStart_4571974 baseEnd_4571974 := by
    simpa [prefixWord, tailWord_4571974, baseEnd_4571974] using wordTrace_append hprefix tailTrace_4571974
  have hstable : (prefixWord ++ tailWord_4571974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571974).length < 2 ^ (prefixWord ++ tailWord_4571974).sum := by decide
  have hdescent : baseEnd_4571974 < baseStart_4571974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571980 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 1, 4, 2]
def baseStart_4571980 : Nat := 118140960795 + 4571980 * 2 ^ 59
def prefixEnd_4571980 : Nat := 4983230072969 + 3 ^ 40 * 4571980 * 2
def baseEnd_4571980 : Nat := 2347623282743127340923853

theorem tailTrace_4571980 : CollatzResearch.WordTrace tailWord_4571980 prefixEnd_4571980 2347623282743127340923853 := by
  unfold tailWord_4571980
  simp only [CollatzResearch.WordTrace]
  refine ⟨83376904988252383431948697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111169206651003177909264929 83376904988252383431948697)
  ·
    refine ⟨62532678741189287573961523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83376904988252383431948697 62532678741189287573961523)
    ·
      refine ⟨93799018111783931360942285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62532678741189287573961523 93799018111783931360942285)
      ·
        refine ⟨35174631791918974260353357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93799018111783931360942285 35174631791918974260353357)
        ·
          refine ⟨13190486921969615347632509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35174631791918974260353357 13190486921969615347632509)
          ·
            refine ⟨4946432595738605755362191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13190486921969615347632509 4946432595738605755362191)
            ·
              refine ⟨7419648893607908633043287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4946432595738605755362191 7419648893607908633043287)
              ·
                refine ⟨11129473340411862949564931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7419648893607908633043287 11129473340411862949564931)
                ·
                  refine ⟨16694210010617794424347397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11129473340411862949564931 16694210010617794424347397)
                  ·
                    refine ⟨3130164376990836454565137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16694210010617794424347397 3130164376990836454565137)
                    ·
                      refine ⟨2347623282743127340923853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3130164376990836454565137 2347623282743127340923853)
                      ·
                        rfl

theorem cell23_4571980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_4571980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571980 prefixEnd_4571980 := by exact prefixLift 4571980
  have htrace : WordTrace (prefixWord ++ tailWord_4571980) baseStart_4571980 baseEnd_4571980 := by
    simpa [prefixWord, tailWord_4571980, baseEnd_4571980] using wordTrace_append hprefix tailTrace_4571980
  have hstable : (prefixWord ++ tailWord_4571980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571980).length < 2 ^ (prefixWord ++ tailWord_4571980).sum := by decide
  have hdescent : baseEnd_4571980 < baseStart_4571980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4571999 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 1, 7]
def baseStart_4571999 : Nat := 118140960795 + 4571999 * 2 ^ 59
def prefixEnd_4571999 : Nat := 4983230072969 + 3 ^ 40 * 4571999 * 2
def baseEnd_4571999 : Nat := 782544346291854255528755

theorem tailTrace_4571999 : CollatzResearch.WordTrace tailWord_4571999 prefixEnd_4571999 782544346291854255528755 := by
  unfold tailWord_4571999
  simp only [CollatzResearch.WordTrace]
  refine ⟨166754502963435933108839051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111169668642290622072559367 166754502963435933108839051)
  ·
    refine ⟨250131754445153899663258577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166754502963435933108839051 250131754445153899663258577)
    ·
      refine ⟨187598815833865424747443933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250131754445153899663258577 187598815833865424747443933)
      ·
        refine ⟨70349555937699534280291475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187598815833865424747443933 70349555937699534280291475)
        ·
          refine ⟨105524333906549301420437213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70349555937699534280291475 105524333906549301420437213)
          ·
            refine ⟨39571625214955988032663955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105524333906549301420437213 39571625214955988032663955)
            ·
              refine ⟨59357437822433982048995933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39571625214955988032663955 59357437822433982048995933)
              ·
                refine ⟨22259039183412743268373475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59357437822433982048995933 22259039183412743268373475)
                ·
                  refine ⟨33388558775119114902560213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22259039183412743268373475 33388558775119114902560213)
                  ·
                    refine ⟨782544346291854255528755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33388558775119114902560213 782544346291854255528755)
                    ·
                      rfl

theorem cell23_4571999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 7].length) (baseStart_4571999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4571999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4571999 prefixEnd_4571999 := by exact prefixLift 4571999
  have htrace : WordTrace (prefixWord ++ tailWord_4571999) baseStart_4571999 baseEnd_4571999 := by
    simpa [prefixWord, tailWord_4571999, baseEnd_4571999] using wordTrace_append hprefix tailTrace_4571999
  have hstable : (prefixWord ++ tailWord_4571999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4571999).length < 2 ^ (prefixWord ++ tailWord_4571999).sum := by decide
  have hdescent : baseEnd_4571999 < baseStart_4571999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4571999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572003 : List Nat := [1, 1, 1, 5, 3, 1, 3, 3, 5]
def baseStart_4572003 : Nat := 118140960795 + 4572003 * 2 ^ 59
def prefixEnd_4572003 : Nat := 4983230072969 + 3 ^ 40 * 4572003 * 2
def baseEnd_4572003 : Nat := 260848343644242305659583

theorem tailTrace_4572003 : CollatzResearch.WordTrace tailWord_4572003 prefixEnd_4572003 260848343644242305659583 := by
  unfold tailWord_4572003
  simp only [CollatzResearch.WordTrace]
  refine ⟨166754648855421441791984663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111169765903614294527989775 166754648855421441791984663)
  ·
    refine ⟨250131973283132162687976995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166754648855421441791984663 250131973283132162687976995)
    ·
      refine ⟨375197959924698244031965493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250131973283132162687976995 375197959924698244031965493)
      ·
        refine ⟨35174808742940460377996765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 375197959924698244031965493 35174808742940460377996765)
        ·
          refine ⟨13190553278602672641748787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35174808742940460377996765 13190553278602672641748787)
          ·
            refine ⟨19785829917904008962623181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13190553278602672641748787 19785829917904008962623181)
            ·
              refine ⟨7419686219214003360983693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19785829917904008962623181 7419686219214003360983693)
              ·
                refine ⟨2782382332205251260368885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7419686219214003360983693 2782382332205251260368885)
                ·
                  refine ⟨260848343644242305659583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2782382332205251260368885 260848343644242305659583)
                  ·
                    rfl

theorem cell23_4572003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 5].length) (baseStart_4572003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572003 prefixEnd_4572003 := by exact prefixLift 4572003
  have htrace : WordTrace (prefixWord ++ tailWord_4572003) baseStart_4572003 baseEnd_4572003 := by
    simpa [prefixWord, tailWord_4572003, baseEnd_4572003] using wordTrace_append hprefix tailTrace_4572003
  have hstable : (prefixWord ++ tailWord_4572003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572003).length < 2 ^ (prefixWord ++ tailWord_4572003).sum := by decide
  have hdescent : baseEnd_4572003 < baseStart_4572003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572036 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_4572036 : Nat := 118140960795 + 4572036 * 2 ^ 59
def prefixEnd_4572036 : Nat := 4983230072969 + 3 ^ 40 * 4572036 * 2
def baseEnd_4572036 : Nat := 2347652037659779121823595

theorem tailTrace_4572036 : CollatzResearch.WordTrace tailWord_4572036 prefixEnd_4572036 2347652037659779121823595 := by
  unfold tailWord_4572036
  simp only [CollatzResearch.WordTrace]
  refine ⟨83377926232150944213967981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111170568309534592285290641 83377926232150944213967981)
  ·
    refine ⟨31266722337056604080237993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83377926232150944213967981 31266722337056604080237993)
    ·
      refine ⟨23450041752792453060178495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31266722337056604080237993 23450041752792453060178495)
      ·
        refine ⟨35175062629188679590267743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23450041752792453060178495 35175062629188679590267743)
        ·
          refine ⟨52762593943783019385401615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35175062629188679590267743 52762593943783019385401615)
          ·
            refine ⟨79143890915674529078102423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52762593943783019385401615 79143890915674529078102423)
            ·
              refine ⟨118715836373511793617153635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79143890915674529078102423 118715836373511793617153635)
              ·
                refine ⟨178073754560267690425730453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118715836373511793617153635 178073754560267690425730453)
                ·
                  refine ⟨8347207245012547988706115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 178073754560267690425730453 8347207245012547988706115)
                  ·
                    refine ⟨12520810867518821983059173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8347207245012547988706115 12520810867518821983059173)
                    ·
                      refine ⟨2347652037659779121823595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12520810867518821983059173 2347652037659779121823595)
                      ·
                        rfl

theorem cell23_4572036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_4572036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572036 prefixEnd_4572036 := by exact prefixLift 4572036
  have htrace : WordTrace (prefixWord ++ tailWord_4572036) baseStart_4572036 baseEnd_4572036 := by
    simpa [prefixWord, tailWord_4572036, baseEnd_4572036] using wordTrace_append hprefix tailTrace_4572036
  have hstable : (prefixWord ++ tailWord_4572036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572036).length < 2 ^ (prefixWord ++ tailWord_4572036).sum := by decide
  have hdescent : baseEnd_4572036 < baseStart_4572036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572049 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_4572049 : Nat := 118140960795 + 4572049 * 2 ^ 59
def prefixEnd_4572049 : Nat := 4983230072969 + 3 ^ 40 * 4572049 * 2
def baseEnd_4572049 : Nat := 2347658712908287570961035

theorem tailTrace_4572049 : CollatzResearch.WordTrace tailWord_4572049 prefixEnd_4572049 2347658712908287570961035 := by
  unfold tailWord_4572049
  simp only [CollatzResearch.WordTrace]
  refine ⟨166756326613254791648159201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111170884408836527765439467 166756326613254791648159201)
  ·
    refine ⟨125067244959941093736119401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166756326613254791648159201 125067244959941093736119401)
    ·
      refine ⟨93800433719955820302089551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125067244959941093736119401 93800433719955820302089551)
      ·
        refine ⟨140700650579933730453134327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93800433719955820302089551 140700650579933730453134327)
        ·
          refine ⟨211050975869900595679701491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140700650579933730453134327 211050975869900595679701491)
          ·
            refine ⟨316576463804850893519552237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211050975869900595679701491 316576463804850893519552237)
            ·
              refine ⟨118716173926819085069832089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316576463804850893519552237 118716173926819085069832089)
              ·
                refine ⟨89037130445114313802374067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118716173926819085069832089 89037130445114313802374067)
                ·
                  refine ⟨133555695667671470703561101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89037130445114313802374067 133555695667671470703561101)
                  ·
                    refine ⟨50083385875376801513835413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 133555695667671470703561101 50083385875376801513835413)
                    ·
                      refine ⟨2347658712908287570961035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50083385875376801513835413 2347658712908287570961035)
                      ·
                        rfl

theorem cell23_4572049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_4572049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572049 prefixEnd_4572049 := by exact prefixLift 4572049
  have htrace : WordTrace (prefixWord ++ tailWord_4572049) baseStart_4572049 baseEnd_4572049 := by
    simpa [prefixWord, tailWord_4572049, baseEnd_4572049] using wordTrace_append hprefix tailTrace_4572049
  have hstable : (prefixWord ++ tailWord_4572049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572049).length < 2 ^ (prefixWord ++ tailWord_4572049).sum := by decide
  have hdescent : baseEnd_4572049 < baseStart_4572049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572050 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_4572050 : Nat := 118140960795 + 4572050 * 2 ^ 59
def prefixEnd_4572050 : Nat := 4983230072969 + 3 ^ 40 * 4572050 * 2
def baseEnd_4572050 : Nat := 782553075462980689016177

theorem tailTrace_4572050 : CollatzResearch.WordTrace tailWord_4572050 prefixEnd_4572050 782553075462980689016177 := by
  unfold tailWord_4572050
  simp only [CollatzResearch.WordTrace]
  refine ⟨41689090771562792204736401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111170908724167445879297069 41689090771562792204736401)
  ·
    refine ⟨31266818078672094153552301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41689090771562792204736401 31266818078672094153552301)
    ·
      refine ⟨11725056779502035307582113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31266818078672094153552301 11725056779502035307582113)
      ·
        refine ⟨8793792584626526480686585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11725056779502035307582113 8793792584626526480686585)
        ·
          refine ⟨6595344438469894860514939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8793792584626526480686585 6595344438469894860514939)
          ·
            refine ⟨9893016657704842290772409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6595344438469894860514939 9893016657704842290772409)
            ·
              refine ⟨7419762493278631718079307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9893016657704842290772409 7419762493278631718079307)
              ·
                refine ⟨11129643739917947577118961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7419762493278631718079307 11129643739917947577118961)
                ·
                  refine ⟨8347232804938460682839221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11129643739917947577118961 8347232804938460682839221)
                  ·
                    refine ⟨782553075462980689016177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8347232804938460682839221 782553075462980689016177)
                    ·
                      rfl

theorem cell23_4572050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_4572050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572050 prefixEnd_4572050 := by exact prefixLift 4572050
  have htrace : WordTrace (prefixWord ++ tailWord_4572050) baseStart_4572050 baseEnd_4572050 := by
    simpa [prefixWord, tailWord_4572050, baseEnd_4572050] using wordTrace_append hprefix tailTrace_4572050
  have hstable : (prefixWord ++ tailWord_4572050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572050).length < 2 ^ (prefixWord ++ tailWord_4572050).sum := by decide
  have hdescent : baseEnd_4572050 < baseStart_4572050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572053 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_4572053 : Nat := 118140960795 + 4572053 * 2 ^ 59
def prefixEnd_4572053 : Nat := 4983230072969 + 3 ^ 40 * 4572053 * 2
def baseEnd_4572053 : Nat := 2347660766830905555311017

theorem tailTrace_4572053 : CollatzResearch.WordTrace tailWord_4572053 prefixEnd_4572053 2347660766830905555311017 := by
  unfold tailWord_4572053
  simp only [CollatzResearch.WordTrace]
  refine ⟨166756472505240300331304813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111170981670160200220869875 166756472505240300331304813)
  ·
    refine ⟨62533677189465112624239305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166756472505240300331304813 62533677189465112624239305)
    ·
      refine ⟨46900257892098834468179479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62533677189465112624239305 46900257892098834468179479)
      ·
        refine ⟨70350386838148251702269219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46900257892098834468179479 70350386838148251702269219)
        ·
          refine ⟨105525580257222377553403829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70350386838148251702269219 105525580257222377553403829)
          ·
            refine ⟨9893023149114597895631609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105525580257222377553403829 9893023149114597895631609)
            ·
              refine ⟨7419767361835948421723707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9893023149114597895631609 7419767361835948421723707)
              ·
                refine ⟨11129651042753922632585561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7419767361835948421723707 11129651042753922632585561)
                ·
                  refine ⟨8347238282065441974439171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11129651042753922632585561 8347238282065441974439171)
                  ·
                    refine ⟨12520857423098162961658757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8347238282065441974439171 12520857423098162961658757)
                    ·
                      refine ⟨2347660766830905555311017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12520857423098162961658757 2347660766830905555311017)
                      ·
                        rfl

theorem cell23_4572053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_4572053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572053 prefixEnd_4572053 := by exact prefixLift 4572053
  have htrace : WordTrace (prefixWord ++ tailWord_4572053) baseStart_4572053 baseEnd_4572053 := by
    simpa [prefixWord, tailWord_4572053, baseEnd_4572053] using wordTrace_append hprefix tailTrace_4572053
  have hstable : (prefixWord ++ tailWord_4572053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572053).length < 2 ^ (prefixWord ++ tailWord_4572053).sum := by decide
  have hdescent : baseEnd_4572053 < baseStart_4572053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572103 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 5, 1, 3]
def baseStart_4572103 : Nat := 118140960795 + 4572103 * 2 ^ 59
def prefixEnd_4572103 : Nat := 4983230072969 + 3 ^ 40 * 4572103 * 2
def baseEnd_4572103 : Nat := 2347686440863630359685787

theorem tailTrace_4572103 : CollatzResearch.WordTrace tailWord_4572103 prefixEnd_4572103 2347686440863630359685787 := by
  unfold tailWord_4572103
  simp only [CollatzResearch.WordTrace]
  refine ⟨166758296155059158870624963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111172197436706105913749975 166758296155059158870624963)
  ·
    refine ⟨250137444232588738305937445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166758296155059158870624963 250137444232588738305937445)
    ·
      refine ⟨46900770793610388432363271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 250137444232588738305937445 46900770793610388432363271)
      ·
        refine ⟨70351156190415582648544907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46900770793610388432363271 70351156190415582648544907)
        ·
          refine ⟨105526734285623373972817361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70351156190415582648544907 105526734285623373972817361)
          ·
            refine ⟨79145050714217530479613021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105526734285623373972817361 79145050714217530479613021)
            ·
              refine ⟨29679394017831573929854883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79145050714217530479613021 29679394017831573929854883)
              ·
                refine ⟨44519091026747360894782325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29679394017831573929854883 44519091026747360894782325)
                ·
                  refine ⟨4173664783757565083885843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44519091026747360894782325 4173664783757565083885843)
                  ·
                    refine ⟨6260497175636347625828765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4173664783757565083885843 6260497175636347625828765)
                    ·
                      refine ⟨2347686440863630359685787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6260497175636347625828765 2347686440863630359685787)
                      ·
                        rfl

theorem cell23_4572103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_4572103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572103 prefixEnd_4572103 := by exact prefixLift 4572103
  have htrace : WordTrace (prefixWord ++ tailWord_4572103) baseStart_4572103 baseEnd_4572103 := by
    simpa [prefixWord, tailWord_4572103, baseEnd_4572103] using wordTrace_append hprefix tailTrace_4572103
  have hstable : (prefixWord ++ tailWord_4572103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572103).length < 2 ^ (prefixWord ++ tailWord_4572103).sum := by decide
  have hdescent : baseEnd_4572103 < baseStart_4572103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572113 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 1, 5, 2]
def baseStart_4572113 : Nat := 118140960795 + 4572113 * 2 ^ 59
def prefixEnd_4572113 : Nat := 4983230072969 + 3 ^ 40 * 4572113 * 2
def baseEnd_4572113 : Nat := 2347691575670175320560741

theorem tailTrace_4572113 : CollatzResearch.WordTrace tailWord_4572113 prefixEnd_4572113 2347691575670175320560741 := by
  unfold tailWord_4572113
  simp only [CollatzResearch.WordTrace]
  refine ⟨166758660885022930578488993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111172440590015287052325995 166758660885022930578488993)
  ·
    refine ⟨125068995663767197933866745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166758660885022930578488993 125068995663767197933866745)
    ·
      refine ⟨93801746747825398450400059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125068995663767197933866745 93801746747825398450400059)
      ·
        refine ⟨140702620121738097675600089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93801746747825398450400059 140702620121738097675600089)
        ·
          refine ⟨105526965091303573256700067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140702620121738097675600089 105526965091303573256700067)
          ·
            refine ⟨158290447636955359885050101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105526965091303573256700067 158290447636955359885050101)
            ·
              refine ⟨14839729465964564989223447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158290447636955359885050101 14839729465964564989223447)
              ·
                refine ⟨22259594198946847483835171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14839729465964564989223447 22259594198946847483835171)
                ·
                  refine ⟨33389391298420271225752757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22259594198946847483835171 33389391298420271225752757)
                  ·
                    refine ⟨3130255434226900427414321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33389391298420271225752757 3130255434226900427414321)
                    ·
                      refine ⟨2347691575670175320560741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3130255434226900427414321 2347691575670175320560741)
                      ·
                        rfl

theorem cell23_4572113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 5, 2].length) (baseStart_4572113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572113 prefixEnd_4572113 := by exact prefixLift 4572113
  have htrace : WordTrace (prefixWord ++ tailWord_4572113) baseStart_4572113 baseEnd_4572113 := by
    simpa [prefixWord, tailWord_4572113, baseEnd_4572113] using wordTrace_append hprefix tailTrace_4572113
  have hstable : (prefixWord ++ tailWord_4572113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572113).length < 2 ^ (prefixWord ++ tailWord_4572113).sum := by decide
  have hdescent : baseEnd_4572113 < baseStart_4572113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572136 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 3, 6]
def baseStart_4572136 : Nat := 118140960795 + 4572136 * 2 ^ 59
def prefixEnd_4572136 : Nat := 4983230072969 + 3 ^ 40 * 4572136 * 2
def baseEnd_4572136 : Nat := 782567795241742910191045

theorem tailTrace_4572136 : CollatzResearch.WordTrace tailWord_4572136 prefixEnd_4572136 782567795241742910191045 := by
  unfold tailWord_4572136
  simp only [CollatzResearch.WordTrace]
  refine ⟨83379749881969802753288131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111172999842626403671050841 83379749881969802753288131)
  ·
    refine ⟨125069624822954704129932197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83379749881969802753288131 125069624822954704129932197)
    ·
      refine ⟨23450554654304007024362287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125069624822954704129932197 23450554654304007024362287)
      ·
        refine ⟨35175831981456010536543431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23450554654304007024362287 35175831981456010536543431)
        ·
          refine ⟨52763747972184015804815147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35175831981456010536543431 52763747972184015804815147)
          ·
            refine ⟨79145621958276023707222721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52763747972184015804815147 79145621958276023707222721)
            ·
              refine ⟨59359216468707017780417041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79145621958276023707222721 59359216468707017780417041)
              ·
                refine ⟨44519412351530263335312781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59359216468707017780417041 44519412351530263335312781)
                ·
                  refine ⟨16694779631823848750742293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44519412351530263335312781 16694779631823848750742293)
                  ·
                    refine ⟨782567795241742910191045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16694779631823848750742293 782567795241742910191045)
                    ·
                      rfl

theorem cell23_4572136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_4572136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572136 prefixEnd_4572136 := by exact prefixLift 4572136
  have htrace : WordTrace (prefixWord ++ tailWord_4572136) baseStart_4572136 baseEnd_4572136 := by
    simpa [prefixWord, tailWord_4572136, baseEnd_4572136] using wordTrace_append hprefix tailTrace_4572136
  have hstable : (prefixWord ++ tailWord_4572136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572136).length < 2 ^ (prefixWord ++ tailWord_4572136).sum := by decide
  have hdescent : baseEnd_4572136 < baseStart_4572136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572183 : List Nat := [1, 1, 3, 5, 1, 3, 9]
def baseStart_4572183 : Nat := 118140960795 + 4572183 * 2 ^ 59
def prefixEnd_4572183 : Nat := 4983230072969 + 3 ^ 40 * 4572183 * 2
def baseEnd_4572183 : Nat := 28984290361925803045499

theorem tailTrace_4572183 : CollatzResearch.WordTrace tailWord_4572183 prefixEnd_4572183 28984290361925803045499 := by
  unfold tailWord_4572183
  simp only [CollatzResearch.WordTrace]
  refine ⟨166761213994769332533537203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111174142663179555022358135 166761213994769332533537203)
  ·
    refine ⟨250141820992153998800305805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166761213994769332533537203 250141820992153998800305805)
    ·
      refine ⟨93803182872057749550114677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250141820992153998800305805 93803182872057749550114677)
      ·
        refine ⟨8794048394255414020323251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93803182872057749550114677 8794048394255414020323251)
        ·
          refine ⟨13191072591383121030484877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8794048394255414020323251 13191072591383121030484877)
          ·
            refine ⟨4946652221768670386431829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13191072591383121030484877 4946652221768670386431829)
            ·
              refine ⟨28984290361925803045499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4946652221768670386431829 28984290361925803045499)
              ·
                rfl

theorem cell23_4572183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 9].length) (baseStart_4572183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572183 prefixEnd_4572183 := by exact prefixLift 4572183
  have htrace : WordTrace (prefixWord ++ tailWord_4572183) baseStart_4572183 baseEnd_4572183 := by
    simpa [prefixWord, tailWord_4572183, baseEnd_4572183] using wordTrace_append hprefix tailTrace_4572183
  have hstable : (prefixWord ++ tailWord_4572183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572183).length < 2 ^ (prefixWord ++ tailWord_4572183).sum := by decide
  have hdescent : baseEnd_4572183 < baseStart_4572183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572194 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_4572194 : Nat := 118140960795 + 4572194 * 2 ^ 59
def prefixEnd_4572194 : Nat := 4983230072969 + 3 ^ 40 * 4572194 * 2
def baseEnd_4572194 : Nat := 2347733167603189503647869

theorem tailTrace_4572194 : CollatzResearch.WordTrace tailWord_4572194 prefixEnd_4572194 2347733167603189503647869 := by
  unfold tailWord_4572194
  simp only [CollatzResearch.WordTrace]
  refine ⟨41690403799432370353046909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111174410131819654274791757 41690403799432370353046909)
  ·
    refine ⟨15633901424787138882392591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41690403799432370353046909 15633901424787138882392591)
    ·
      refine ⟨23450852137180708323588887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15633901424787138882392591 23450852137180708323588887)
      ·
        refine ⟨35176278205771062485383331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23450852137180708323588887 35176278205771062485383331)
        ·
          refine ⟨52764417308656593728074997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35176278205771062485383331 52764417308656593728074997)
          ·
            refine ⟨4946664122686555662007031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52764417308656593728074997 4946664122686555662007031)
            ·
              refine ⟨7419996184029833493010547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4946664122686555662007031 7419996184029833493010547)
              ·
                refine ⟨11129994276044750239515821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7419996184029833493010547 11129994276044750239515821)
                ·
                  refine ⟨4173747853516781339818433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11129994276044750239515821 4173747853516781339818433)
                  ·
                    refine ⟨3130310890137586004863825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4173747853516781339818433 3130310890137586004863825)
                    ·
                      refine ⟨2347733167603189503647869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3130310890137586004863825 2347733167603189503647869)
                      ·
                        rfl

theorem cell23_4572194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_4572194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572194 prefixEnd_4572194 := by exact prefixLift 4572194
  have htrace : WordTrace (prefixWord ++ tailWord_4572194) baseStart_4572194 baseEnd_4572194 := by
    simpa [prefixWord, tailWord_4572194, baseEnd_4572194] using wordTrace_append hprefix tailTrace_4572194
  have hstable : (prefixWord ++ tailWord_4572194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572194).length < 2 ^ (prefixWord ++ tailWord_4572194).sum := by decide
  have hdescent : baseEnd_4572194 < baseStart_4572194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572214 : List Nat := [5, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_4572214 : Nat := 118140960795 + 4572214 * 2 ^ 59
def prefixEnd_4572214 : Nat := 4983230072969 + 3 ^ 40 * 4572214 * 2
def baseEnd_4572214 : Nat := 2347743437216279425397777

theorem tailTrace_4572214 : CollatzResearch.WordTrace tailWord_4572214 prefixEnd_4572214 2347743437216279425397777 := by
  unfold tailWord_4572214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10422646541103564051744731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111174896438438016551943797 10422646541103564051744731)
  ·
    refine ⟨15633969811655346077617097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10422646541103564051744731 15633969811655346077617097)
    ·
      refine ⟨11725477358741509558212823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15633969811655346077617097 11725477358741509558212823)
      ·
        refine ⟨17588216038112264337319235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11725477358741509558212823 17588216038112264337319235)
        ·
          refine ⟨26382324057168396505978853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17588216038112264337319235 26382324057168396505978853)
          ·
            refine ⟨4946685760719074344871035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26382324057168396505978853 4946685760719074344871035)
            ·
              refine ⟨7420028641078611517306553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4946685760719074344871035 7420028641078611517306553)
              ·
                refine ⟨5565021480808958637979915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7420028641078611517306553 5565021480808958637979915)
                ·
                  refine ⟨8347532221213437956969873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5565021480808958637979915 8347532221213437956969873)
                  ·
                    refine ⟨6260649165910078467727405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8347532221213437956969873 6260649165910078467727405)
                    ·
                      refine ⟨2347743437216279425397777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6260649165910078467727405 2347743437216279425397777)
                      ·
                        rfl

theorem cell23_4572214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_4572214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572214 prefixEnd_4572214 := by exact prefixLift 4572214
  have htrace : WordTrace (prefixWord ++ tailWord_4572214) baseStart_4572214 baseEnd_4572214 := by
    simpa [prefixWord, tailWord_4572214, baseEnd_4572214] using wordTrace_append hprefix tailTrace_4572214
  have hstable : (prefixWord ++ tailWord_4572214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572214).length < 2 ^ (prefixWord ++ tailWord_4572214).sum := by decide
  have hdescent : baseEnd_4572214 < baseStart_4572214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572263 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_4572263 : Nat := 118140960795 + 4572263 * 2 ^ 59
def prefixEnd_4572263 : Nat := 4983230072969 + 3 ^ 40 * 4572263 * 2
def baseEnd_4572263 : Nat := 2347768597768349733685051

theorem tailTrace_4572263 : CollatzResearch.WordTrace tailWord_4572263 prefixEnd_4572263 2347768597768349733685051 := by
  unfold tailWord_4572263
  simp only [CollatzResearch.WordTrace]
  refine ⟨166764131834479506196449443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111176087889653004130966295 166764131834479506196449443)
  ·
    refine ⟨250146197751719259294674165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166764131834479506196449443 250146197751719259294674165)
    ·
      refine ⟨23451206039223680558875703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 250146197751719259294674165 23451206039223680558875703)
      ·
        refine ⟨35176809058835520838313555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23451206039223680558875703 35176809058835520838313555)
        ·
          refine ⟨52765213588253281257470333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35176809058835520838313555 52765213588253281257470333)
          ·
            refine ⟨19786955095594980471551375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52765213588253281257470333 19786955095594980471551375)
            ·
              refine ⟨29680432643392470707327063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19786955095594980471551375 29680432643392470707327063)
              ·
                refine ⟨44520648965088706060990595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29680432643392470707327063 44520648965088706060990595)
                ·
                  refine ⟨66780973447633059091485893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44520648965088706060990595 66780973447633059091485893)
                  ·
                    refine ⟨12521432521431198579653605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66780973447633059091485893 12521432521431198579653605)
                    ·
                      refine ⟨2347768597768349733685051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12521432521431198579653605 2347768597768349733685051)
                      ·
                        rfl

theorem cell23_4572263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_4572263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572263 prefixEnd_4572263 := by exact prefixLift 4572263
  have htrace : WordTrace (prefixWord ++ tailWord_4572263) baseStart_4572263 baseEnd_4572263 := by
    simpa [prefixWord, tailWord_4572263, baseEnd_4572263] using wordTrace_append hprefix tailTrace_4572263
  have hstable : (prefixWord ++ tailWord_4572263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572263).length < 2 ^ (prefixWord ++ tailWord_4572263).sum := by decide
  have hdescent : baseEnd_4572263 < baseStart_4572263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572318 : List Nat := [4, 3, 1, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_4572318 : Nat := 118140960795 + 4572318 * 2 ^ 59
def prefixEnd_4572318 : Nat := 4983230072969 + 3 ^ 40 * 4572318 * 2
def baseEnd_4572318 : Nat := 2347796839204347018497299

theorem tailTrace_4572318 : CollatzResearch.WordTrace tailWord_4572318 prefixEnd_4572318 2347796839204347018497299 := by
  unfold tailWord_4572318
  simp only [CollatzResearch.WordTrace]
  refine ⟨20845767231160031323712701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111177425232853500393134405 20845767231160031323712701)
  ·
    refine ⟨7817162711685011746392263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20845767231160031323712701 7817162711685011746392263)
    ·
      refine ⟨11725744067527517619588395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7817162711685011746392263 11725744067527517619588395)
      ·
        refine ⟨17588616101291276429382593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11725744067527517619588395 17588616101291276429382593)
        ·
          refine ⟨13191462075968457322036945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17588616101291276429382593 13191462075968457322036945)
          ·
            refine ⟨9893596556976342991527709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13191462075968457322036945 9893596556976342991527709)
            ·
              refine ⟨3710098708866128621822891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9893596556976342991527709 3710098708866128621822891)
              ·
                refine ⟨5565148063299192932734337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710098708866128621822891 5565148063299192932734337)
                ·
                  refine ⟨4173861047474394699550753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5565148063299192932734337 4173861047474394699550753)
                  ·
                    refine ⟨3130395785605796024663065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4173861047474394699550753 3130395785605796024663065)
                    ·
                      refine ⟨2347796839204347018497299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3130395785605796024663065 2347796839204347018497299)
                      ·
                        rfl

theorem cell23_4572318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_4572318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572318 prefixEnd_4572318 := by exact prefixLift 4572318
  have htrace : WordTrace (prefixWord ++ tailWord_4572318) baseStart_4572318 baseEnd_4572318 := by
    simpa [prefixWord, tailWord_4572318, baseEnd_4572318] using wordTrace_append hprefix tailTrace_4572318
  have hstable : (prefixWord ++ tailWord_4572318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572318).length < 2 ^ (prefixWord ++ tailWord_4572318).sum := by decide
  have hdescent : baseEnd_4572318 < baseStart_4572318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572358 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_4572358 : Nat := 118140960795 + 4572358 * 2 ^ 59
def prefixEnd_4572358 : Nat := 4983230072969 + 3 ^ 40 * 4572358 * 2
def baseEnd_4572358 : Nat := 260868597603391873555235

theorem tailTrace_4572358 : CollatzResearch.WordTrace tailWord_4572358 prefixEnd_4572358 260868597603391873555235 := by
  unfold tailWord_4572358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5211487399035479294411179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 111178397846090224947438485 5211487399035479294411179)
  ·
    refine ⟨7817231098553218941616769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5211487399035479294411179 7817231098553218941616769)
    ·
      refine ⟨5862923323914914206212577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7817231098553218941616769 5862923323914914206212577)
      ·
        refine ⟨4397192492936185654659433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5862923323914914206212577 4397192492936185654659433)
        ·
          refine ⟨3297894369702139240994575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4397192492936185654659433 3297894369702139240994575)
          ·
            refine ⟨4946841554553208861491863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3297894369702139240994575 4946841554553208861491863)
            ·
              refine ⟨7420262331829813292237795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4946841554553208861491863 7420262331829813292237795)
              ·
                refine ⟨11130393497744719938356693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7420262331829813292237795 11130393497744719938356693)
                ·
                  refine ⟨260868597603391873555235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11130393497744719938356693 260868597603391873555235)
                  ·
                    rfl

theorem cell23_4572358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_4572358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572358 prefixEnd_4572358 := by exact prefixLift 4572358
  have htrace : WordTrace (prefixWord ++ tailWord_4572358) baseStart_4572358 baseEnd_4572358 := by
    simpa [prefixWord, tailWord_4572358, baseEnd_4572358] using wordTrace_append hprefix tailTrace_4572358
  have hstable : (prefixWord ++ tailWord_4572358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572358).length < 2 ^ (prefixWord ++ tailWord_4572358).sum := by decide
  have hdescent : baseEnd_4572358 < baseStart_4572358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572360 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_4572360 : Nat := 118140960795 + 4572360 * 2 ^ 59
def prefixEnd_4572360 : Nat := 4983230072969 + 3 ^ 40 * 4572360 * 2
def baseEnd_4572360 : Nat := 2347818405391835854172105

theorem tailTrace_4572360 : CollatzResearch.WordTrace tailWord_4572360 prefixEnd_4572360 2347818405391835854172105 := by
  unfold tailWord_4572360
  simp only [CollatzResearch.WordTrace]
  refine ⟨83383834857564045881365267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111178446476752061175153689 83383834857564045881365267)
  ·
    refine ⟨125075752286346068822047901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83383834857564045881365267 125075752286346068822047901)
    ·
      refine ⟨46903407107379775808267963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125075752286346068822047901 46903407107379775808267963)
      ·
        refine ⟨70355110661069663712401945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46903407107379775808267963 70355110661069663712401945)
        ·
          refine ⟨52766332995802247784301459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70355110661069663712401945 52766332995802247784301459)
          ·
            refine ⟨79149499493703371676452189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52766332995802247784301459 79149499493703371676452189)
            ·
              refine ⟨29681062310138764378669571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79149499493703371676452189 29681062310138764378669571)
              ·
                refine ⟨44521593465208146568004357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29681062310138764378669571 44521593465208146568004357)
                ·
                  refine ⟨8347798774726527481500817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44521593465208146568004357 8347798774726527481500817)
                  ·
                    refine ⟨6260849081044895611125613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8347798774726527481500817 6260849081044895611125613)
                    ·
                      refine ⟨2347818405391835854172105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6260849081044895611125613 2347818405391835854172105)
                      ·
                        rfl

theorem cell23_4572360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_4572360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572360 prefixEnd_4572360 := by exact prefixLift 4572360
  have htrace : WordTrace (prefixWord ++ tailWord_4572360) baseStart_4572360 baseEnd_4572360 := by
    simpa [prefixWord, tailWord_4572360, baseEnd_4572360] using wordTrace_append hprefix tailTrace_4572360
  have hstable : (prefixWord ++ tailWord_4572360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572360).length < 2 ^ (prefixWord ++ tailWord_4572360).sum := by decide
  have hdescent : baseEnd_4572360 < baseStart_4572360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572383 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 6]
def baseStart_4572383 : Nat := 118140960795 + 4572383 * 2 ^ 59
def prefixEnd_4572383 : Nat := 4983230072969 + 3 ^ 40 * 4572383 * 2
def baseEnd_4572383 : Nat := 2347830215446889264184499

theorem tailTrace_4572383 : CollatzResearch.WordTrace tailWord_4572383 prefixEnd_4572383 2347830215446889264184499 := by
  unfold tailWord_4572383
  simp only [CollatzResearch.WordTrace]
  refine ⟨166768508594044766690817803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111179005729363177793878535 166768508594044766690817803)
  ·
    refine ⟨250152762891067150036226705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166768508594044766690817803 250152762891067150036226705)
    ·
      refine ⟨187614572168300362527170029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250152762891067150036226705 187614572168300362527170029)
      ·
        refine ⟨70355464563112635947688761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187614572168300362527170029 70355464563112635947688761)
        ·
          refine ⟨52766598422334476960766571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70355464563112635947688761 52766598422334476960766571)
          ·
            refine ⟨79149897633501715441149857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52766598422334476960766571 79149897633501715441149857)
            ·
              refine ⟨59362423225126286580862393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79149897633501715441149857 59362423225126286580862393)
              ·
                refine ⟨44521817418844714935646795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59362423225126286580862393 44521817418844714935646795)
                ·
                  refine ⟨66782726128267072403470193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44521817418844714935646795 66782726128267072403470193)
                  ·
                    refine ⟨50087044596200304302602645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66782726128267072403470193 50087044596200304302602645)
                    ·
                      refine ⟨2347830215446889264184499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50087044596200304302602645 2347830215446889264184499)
                      ·
                        rfl

theorem cell23_4572383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_4572383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572383 prefixEnd_4572383 := by exact prefixLift 4572383
  have htrace : WordTrace (prefixWord ++ tailWord_4572383) baseStart_4572383 baseEnd_4572383 := by
    simpa [prefixWord, tailWord_4572383, baseEnd_4572383] using wordTrace_append hprefix tailTrace_4572383
  have hstable : (prefixWord ++ tailWord_4572383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572383).length < 2 ^ (prefixWord ++ tailWord_4572383).sum := by decide
  have hdescent : baseEnd_4572383 < baseStart_4572383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572440 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 1, 6]
def baseStart_4572440 : Nat := 118140960795 + 4572440 * 2 ^ 59
def prefixEnd_4572440 : Nat := 4983230072969 + 3 ^ 40 * 4572440 * 2
def baseEnd_4572440 : Nat := 782619827948065180390579

theorem tailTrace_4572440 : CollatzResearch.WordTrace tailWord_4572440 prefixEnd_4572440 782619827948065180390579 := by
  unfold tailWord_4572440
  simp only [CollatzResearch.WordTrace]
  refine ⟨83385293777419132712821387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111180391703225510283761849 83385293777419132712821387)
  ·
    refine ⟨125077940666128699069232081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83385293777419132712821387 125077940666128699069232081)
    ·
      refine ⟨93808455499596524301924061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125077940666128699069232081 93808455499596524301924061)
      ·
        refine ⟨35178170812348696613221523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93808455499596524301924061 35178170812348696613221523)
        ·
          refine ⟨52767256218523044919832285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35178170812348696613221523 52767256218523044919832285)
          ·
            refine ⟨19787721081946141844937107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52767256218523044919832285 19787721081946141844937107)
            ·
              refine ⟨29681581622919212767405661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19787721081946141844937107 29681581622919212767405661)
              ·
                refine ⟨11130593108594704787777123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29681581622919212767405661 11130593108594704787777123)
                ·
                  refine ⟨16695889662892057181665685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11130593108594704787777123 16695889662892057181665685)
                  ·
                    refine ⟨782619827948065180390579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16695889662892057181665685 782619827948065180390579)
                    ·
                      rfl

theorem cell23_4572440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_4572440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572440 prefixEnd_4572440 := by exact prefixLift 4572440
  have htrace : WordTrace (prefixWord ++ tailWord_4572440) baseStart_4572440 baseEnd_4572440 := by
    simpa [prefixWord, tailWord_4572440, baseEnd_4572440] using wordTrace_append hprefix tailTrace_4572440
  have hstable : (prefixWord ++ tailWord_4572440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572440).length < 2 ^ (prefixWord ++ tailWord_4572440).sum := by decide
  have hdescent : baseEnd_4572440 < baseStart_4572440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572458 : List Nat := [3, 1, 4, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_4572458 : Nat := 118140960795 + 4572458 * 2 ^ 59
def prefixEnd_4572458 : Nat := 4983230072969 + 3 ^ 40 * 4572458 * 2
def baseEnd_4572458 : Nat := 2347868726495976470746655

theorem tailTrace_4572458 : CollatzResearch.WordTrace tailWord_4572458 prefixEnd_4572458 2347868726495976470746655 := by
  unfold tailWord_4572458
  simp only [CollatzResearch.WordTrace]
  refine ⟨41692811017193263624949507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111180829379182036333198685 41692811017193263624949507)
  ·
    refine ⟨62539216525789895437424261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41692811017193263624949507 62539216525789895437424261)
    ·
      refine ⟨11726103098585605394517049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62539216525789895437424261 11726103098585605394517049)
      ·
        refine ⟨8794577323939204045887787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11726103098585605394517049 8794577323939204045887787)
        ·
          refine ⟨13191865985908806068831681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8794577323939204045887787 13191865985908806068831681)
          ·
            refine ⟨9893899489431604551623761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13191865985908806068831681 9893899489431604551623761)
            ·
              refine ⟨7420424617073703413717821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9893899489431604551623761 7420424617073703413717821)
              ·
                refine ⟨2782659231402638780144183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7420424617073703413717821 2782659231402638780144183)
                ·
                  refine ⟨4173988847103958170216275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2782659231402638780144183 4173988847103958170216275)
                  ·
                    refine ⟨6260983270655937255324413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4173988847103958170216275 6260983270655937255324413)
                    ·
                      refine ⟨2347868726495976470746655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6260983270655937255324413 2347868726495976470746655)
                      ·
                        rfl

theorem cell23_4572458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_4572458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572458 prefixEnd_4572458 := by exact prefixLift 4572458
  have htrace : WordTrace (prefixWord ++ tailWord_4572458) baseStart_4572458 baseEnd_4572458 := by
    simpa [prefixWord, tailWord_4572458, baseEnd_4572458] using wordTrace_append hprefix tailTrace_4572458
  have hstable : (prefixWord ++ tailWord_4572458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572458).length < 2 ^ (prefixWord ++ tailWord_4572458).sum := by decide
  have hdescent : baseEnd_4572458 < baseStart_4572458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572461 : List Nat := [1, 5, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_4572461 : Nat := 118140960795 + 4572461 * 2 ^ 59
def prefixEnd_4572461 : Nat := 4983230072969 + 3 ^ 40 * 4572461 * 2
def baseEnd_4572461 : Nat := 782623422312646653003047

theorem tailTrace_4572461 : CollatzResearch.WordTrace tailWord_4572461 prefixEnd_4572461 782623422312646653003047 := by
  unfold tailWord_4572461
  simp only [CollatzResearch.WordTrace]
  refine ⟨166771353487762186012157237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111180902325174790674771491 166771353487762186012157237)
  ·
    refine ⟨15634814389477704938639741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166771353487762186012157237 15634814389477704938639741)
    ·
      refine ⟨5863055396054139351989903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15634814389477704938639741 5863055396054139351989903)
      ·
        refine ⟨8794583094081209027984855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5863055396054139351989903 8794583094081209027984855)
        ·
          refine ⟨13191874641121813541977283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8794583094081209027984855 13191874641121813541977283)
          ·
            refine ⟨19787811961682720312965925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13191874641121813541977283 19787811961682720312965925)
            ·
              refine ⟨3710214742815510058681111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19787811961682720312965925 3710214742815510058681111)
              ·
                refine ⟨5565322114223265088021667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710214742815510058681111 5565322114223265088021667)
                ·
                  refine ⟨8347983171334897632032501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5565322114223265088021667 8347983171334897632032501)
                  ·
                    refine ⟨782623422312646653003047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8347983171334897632032501 782623422312646653003047)
                    ·
                      rfl

theorem cell23_4572461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_4572461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572461 prefixEnd_4572461 := by exact prefixLift 4572461
  have htrace : WordTrace (prefixWord ++ tailWord_4572461) baseStart_4572461 baseEnd_4572461 := by
    simpa [prefixWord, tailWord_4572461, baseEnd_4572461] using wordTrace_append hprefix tailTrace_4572461
  have hstable : (prefixWord ++ tailWord_4572461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572461).length < 2 ^ (prefixWord ++ tailWord_4572461).sum := by decide
  have hdescent : baseEnd_4572461 < baseStart_4572461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572481 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_4572481 : Nat := 118140960795 + 4572481 * 2 ^ 59
def prefixEnd_4572481 : Nat := 4983230072969 + 3 ^ 40 * 4572481 * 2
def baseEnd_4572481 : Nat := 2347880536551029880759049

theorem tailTrace_4572481 : CollatzResearch.WordTrace tailWord_4572481 prefixEnd_4572481 2347880536551029880759049 := by
  unfold tailWord_4572481
  simp only [CollatzResearch.WordTrace]
  refine ⟨166772082947689729427885297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111181388631793152951923531 166772082947689729427885297)
  ·
    refine ⟨125079062210767297070913973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166772082947689729427885297 125079062210767297070913973)
    ·
      refine ⟨11726162082259434100398185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125079062210767297070913973 11726162082259434100398185)
      ·
        refine ⟨8794621561694575575298639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11726162082259434100398185 8794621561694575575298639)
        ·
          refine ⟨13191932342541863362947959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8794621561694575575298639 13191932342541863362947959)
          ·
            refine ⟨19787898513812795044421939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13191932342541863362947959 19787898513812795044421939)
            ·
              refine ⟨29681847770719192566632909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19787898513812795044421939 29681847770719192566632909)
              ·
                refine ⟨11130692914019697212487341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29681847770719192566632909 11130692914019697212487341)
                ·
                  refine ⟨4174009842757386454682753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11130692914019697212487341 4174009842757386454682753)
                  ·
                    refine ⟨3130507382068039841012065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4174009842757386454682753 3130507382068039841012065)
                    ·
                      refine ⟨2347880536551029880759049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3130507382068039841012065 2347880536551029880759049)
                      ·
                        rfl

theorem cell23_4572481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_4572481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572481 prefixEnd_4572481 := by exact prefixLift 4572481
  have htrace : WordTrace (prefixWord ++ tailWord_4572481) baseStart_4572481 baseEnd_4572481 := by
    simpa [prefixWord, tailWord_4572481, baseEnd_4572481] using wordTrace_append hprefix tailTrace_4572481
  have hstable : (prefixWord ++ tailWord_4572481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572481).length < 2 ^ (prefixWord ++ tailWord_4572481).sum := by decide
  have hdescent : baseEnd_4572481 < baseStart_4572481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572484 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_4572484 : Nat := 118140960795 + 4572484 * 2 ^ 59
def prefixEnd_4572484 : Nat := 4983230072969 + 3 ^ 40 * 4572484 * 2
def baseEnd_4572484 : Nat := 2347882076992993369021535

theorem tailTrace_4572484 : CollatzResearch.WordTrace tailWord_4572484 prefixEnd_4572484 2347882076992993369021535 := by
  unfold tailWord_4572484
  simp only [CollatzResearch.WordTrace]
  refine ⟨83386096183339430470122253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111181461577785907293496337 83386096183339430470122253)
  ·
    refine ⟨31269786068752286426295845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83386096183339430470122253 31269786068752286426295845)
    ·
      refine ⟨5863084887891053704930471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31269786068752286426295845 5863084887891053704930471)
      ·
        refine ⟨8794627331836580557395707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5863084887891053704930471 8794627331836580557395707)
        ·
          refine ⟨13191940997754870836093561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8794627331836580557395707 13191940997754870836093561)
          ·
            refine ⟨9893955748316153127070171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13191940997754870836093561 9893955748316153127070171)
            ·
              refine ⟨14840933622474229690605257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9893955748316153127070171 14840933622474229690605257)
              ·
                refine ⟨11130700216855672267953943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14840933622474229690605257 11130700216855672267953943)
                ·
                  refine ⟨16696050325283508401930915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11130700216855672267953943 16696050325283508401930915)
                  ·
                    refine ⟨25044075487925262602896373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16696050325283508401930915 25044075487925262602896373)
                    ·
                      refine ⟨2347882076992993369021535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25044075487925262602896373 2347882076992993369021535)
                      ·
                        rfl

theorem cell23_4572484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_4572484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572484 prefixEnd_4572484 := by exact prefixLift 4572484
  have htrace : WordTrace (prefixWord ++ tailWord_4572484) baseStart_4572484 baseEnd_4572484 := by
    simpa [prefixWord, tailWord_4572484, baseEnd_4572484] using wordTrace_append hprefix tailTrace_4572484
  have hstable : (prefixWord ++ tailWord_4572484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572484).length < 2 ^ (prefixWord ++ tailWord_4572484).sum := by decide
  have hdescent : baseEnd_4572484 < baseStart_4572484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572509 : List Nat := [1, 4, 5, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_4572509 : Nat := 118140960795 + 4572509 * 2 ^ 59
def prefixEnd_4572509 : Nat := 4983230072969 + 3 ^ 40 * 4572509 * 2
def baseEnd_4572509 : Nat := 2347894914009355771208921

theorem tailTrace_4572509 : CollatzResearch.WordTrace tailWord_4572509 prefixEnd_4572509 2347894914009355771208921 := by
  unfold tailWord_4572509
  simp only [CollatzResearch.WordTrace]
  refine ⟨166773104191588290209904581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111182069461058860139936387 166773104191588290209904581)
  ·
    refine ⟨31269957035922804414357109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166773104191588290209904581 31269957035922804414357109)
    ·
      refine ⟨2931558472117762913845979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31269957035922804414357109 2931558472117762913845979)
      ·
        refine ⟨4397337708176644370768969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2931558472117762913845979 4397337708176644370768969)
        ·
          refine ⟨3298003281132483278076727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4397337708176644370768969 3298003281132483278076727)
          ·
            refine ⟨4947004921698724917115091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3298003281132483278076727 4947004921698724917115091)
            ·
              refine ⟨7420507382548087375672637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4947004921698724917115091 7420507382548087375672637)
              ·
                refine ⟨2782690268455532765877239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7420507382548087375672637 2782690268455532765877239)
                ·
                  refine ⟨4174035402683299148815859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2782690268455532765877239 4174035402683299148815859)
                  ·
                    refine ⟨6261053104024948723223789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4174035402683299148815859 6261053104024948723223789)
                    ·
                      refine ⟨2347894914009355771208921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6261053104024948723223789 2347894914009355771208921)
                      ·
                        rfl

theorem cell23_4572509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_4572509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572509 prefixEnd_4572509 := by exact prefixLift 4572509
  have htrace : WordTrace (prefixWord ++ tailWord_4572509) baseStart_4572509 baseEnd_4572509 := by
    simpa [prefixWord, tailWord_4572509, baseEnd_4572509] using wordTrace_append hprefix tailTrace_4572509
  have hstable : (prefixWord ++ tailWord_4572509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572509).length < 2 ^ (prefixWord ++ tailWord_4572509).sum := by decide
  have hdescent : baseEnd_4572509 < baseStart_4572509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572514 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_4572514 : Nat := 118140960795 + 4572514 * 2 ^ 59
def prefixEnd_4572514 : Nat := 4983230072969 + 3 ^ 40 * 4572514 * 2
def baseEnd_4572514 : Nat := 2347897481412628251646397

theorem tailTrace_4572514 : CollatzResearch.WordTrace tailWord_4572514 prefixEnd_4572514 2347897481412628251646397 := by
  unfold tailWord_4572514
  simp only [CollatzResearch.WordTrace]
  refine ⟨41693321639142544015959149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111182191037713450709224397 41693321639142544015959149)
  ·
    refine ⟨15634995614678454005984681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41693321639142544015959149 15634995614678454005984681)
    ·
      refine ⟨11726246711008840504488511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15634995614678454005984681 11726246711008840504488511)
      ·
        refine ⟨17589370066513260756732767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11726246711008840504488511 17589370066513260756732767)
        ·
          refine ⟨26384055099769891135099151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17589370066513260756732767 26384055099769891135099151)
          ·
            refine ⟨39576082649654836702648727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26384055099769891135099151 39576082649654836702648727)
            ·
              refine ⟨59364123974482255053973091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39576082649654836702648727 59364123974482255053973091)
              ·
                refine ⟨89046185961723382580959637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59364123974482255053973091 89046185961723382580959637)
                ·
                  refine ⟨4174039966955783558482483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89046185961723382580959637 4174039966955783558482483)
                  ·
                    refine ⟨6261059950433675337723725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4174039966955783558482483 6261059950433675337723725)
                    ·
                      refine ⟨2347897481412628251646397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6261059950433675337723725 2347897481412628251646397)
                      ·
                        rfl

theorem cell23_4572514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_4572514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572514 prefixEnd_4572514 := by exact prefixLift 4572514
  have htrace : WordTrace (prefixWord ++ tailWord_4572514) baseStart_4572514 baseEnd_4572514 := by
    simpa [prefixWord, tailWord_4572514, baseEnd_4572514] using wordTrace_append hprefix tailTrace_4572514
  have hstable : (prefixWord ++ tailWord_4572514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572514).length < 2 ^ (prefixWord ++ tailWord_4572514).sum := by decide
  have hdescent : baseEnd_4572514 < baseStart_4572514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572540 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_4572540 : Nat := 118140960795 + 4572540 * 2 ^ 59
def prefixEnd_4572540 : Nat := 4983230072969 + 3 ^ 40 * 4572540 * 2
def baseEnd_4572540 : Nat := 2347910831909645149921277

theorem tailTrace_4572540 : CollatzResearch.WordTrace tailWord_4572540 prefixEnd_4572540 2347910831909645149921277 := by
  unfold tailWord_4572540
  simp only [CollatzResearch.WordTrace]
  refine ⟨83387117427237991252141537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111182823236317321669522049 83387117427237991252141537)
  ·
    refine ⟨62540338070428493439106153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83387117427237991252141537 62540338070428493439106153)
    ·
      refine ⟨46905253552821370079329615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62540338070428493439106153 46905253552821370079329615)
      ·
        refine ⟨70357880329232055118994423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46905253552821370079329615 70357880329232055118994423)
        ·
          refine ⟨105536820493848082678491635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70357880329232055118994423 105536820493848082678491635)
          ·
            refine ⟨158305230740772124017737453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105536820493848082678491635 158305230740772124017737453)
            ·
              refine ⟨59364461527789546506651545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158305230740772124017737453 59364461527789546506651545)
              ·
                refine ⟨44523346145842159879988659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59364461527789546506651545 44523346145842159879988659)
                ·
                  refine ⟨66785019218763239819982989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44523346145842159879988659 66785019218763239819982989)
                  ·
                    refine ⟨25044382207036214932493621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66785019218763239819982989 25044382207036214932493621)
                    ·
                      refine ⟨2347910831909645149921277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25044382207036214932493621 2347910831909645149921277)
                      ·
                        rfl

theorem cell23_4572540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_4572540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572540 prefixEnd_4572540 := by exact prefixLift 4572540
  have htrace : WordTrace (prefixWord ++ tailWord_4572540) baseStart_4572540 baseEnd_4572540 := by
    simpa [prefixWord, tailWord_4572540, baseEnd_4572540] using wordTrace_append hprefix tailTrace_4572540
  have hstable : (prefixWord ++ tailWord_4572540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572540).length < 2 ^ (prefixWord ++ tailWord_4572540).sum := by decide
  have hdescent : baseEnd_4572540 < baseStart_4572540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572542 : List Nat := [4, 2, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_4572542 : Nat := 118140960795 + 4572542 * 2 ^ 59
def prefixEnd_4572542 : Nat := 4983230072969 + 3 ^ 40 * 4572542 * 2
def baseEnd_4572542 : Nat := 782637286290318047365423

theorem tailTrace_4572542 : CollatzResearch.WordTrace tailWord_4572542 prefixEnd_4572542 782637286290318047365423 := by
  unfold tailWord_4572542
  simp only [CollatzResearch.WordTrace]
  refine ⟨20846788475058592105731985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111182871866979157897237253 20846788475058592105731985)
  ·
    refine ⟨15635091356293944079298989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20846788475058592105731985 15635091356293944079298989)
    ·
      refine ⟨5863159258610229029737121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15635091356293944079298989 5863159258610229029737121)
      ·
        refine ⟨4397369443957671772302841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5863159258610229029737121 4397369443957671772302841)
        ·
          refine ⟨3298027082968253829227131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4397369443957671772302841 3298027082968253829227131)
          ·
            refine ⟨4947040624452380743840697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3298027082968253829227131 4947040624452380743840697)
            ·
              refine ⟨3710280468339285557880523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4947040624452380743840697 3710280468339285557880523)
              ·
                refine ⟨5565420702508928336820785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710280468339285557880523 5565420702508928336820785)
                ·
                  refine ⟨4174065526881696252615589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5565420702508928336820785 4174065526881696252615589)
                  ·
                    refine ⟨782637286290318047365423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4174065526881696252615589 782637286290318047365423)
                    ·
                      rfl

theorem cell23_4572542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_4572542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572542 prefixEnd_4572542 := by exact prefixLift 4572542
  have htrace : WordTrace (prefixWord ++ tailWord_4572542) baseStart_4572542 baseEnd_4572542 := by
    simpa [prefixWord, tailWord_4572542, baseEnd_4572542] using wordTrace_append hprefix tailTrace_4572542
  have hstable : (prefixWord ++ tailWord_4572542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572542).length < 2 ^ (prefixWord ++ tailWord_4572542).sum := by decide
  have hdescent : baseEnd_4572542 < baseStart_4572542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572548 : List Nat := [2, 3, 2, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_4572548 : Nat := 118140960795 + 4572548 * 2 ^ 59
def prefixEnd_4572548 : Nat := 4983230072969 + 3 ^ 40 * 4572548 * 2
def baseEnd_4572548 : Nat := 2347914939754881118621241

theorem tailTrace_4572548 : CollatzResearch.WordTrace tailWord_4572548 prefixEnd_4572548 2347914939754881118621241 := by
  unfold tailWord_4572548
  simp only [CollatzResearch.WordTrace]
  refine ⟨83387263319223499935287149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111183017758964666580382865 83387263319223499935287149)
  ·
    refine ⟨31270223744708812475732681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83387263319223499935287149 31270223744708812475732681)
    ·
      refine ⟨23452667808531609356799511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31270223744708812475732681 23452667808531609356799511)
      ·
        refine ⟨35179001712797414035199267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23452667808531609356799511 35179001712797414035199267)
        ·
          refine ⟨52768502569196121052798901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35179001712797414035199267 52768502569196121052798901)
          ·
            refine ⟨4947047115862136348699897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52768502569196121052798901 4947047115862136348699897)
            ·
              refine ⟨3710285336896602261524923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4947047115862136348699897 3710285336896602261524923)
              ·
                refine ⟨5565428005344903392287385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710285336896602261524923 5565428005344903392287385)
                ·
                  refine ⟨4174071004008677544215539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5565428005344903392287385 4174071004008677544215539)
                  ·
                    refine ⟨6261106506013016316323309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4174071004008677544215539 6261106506013016316323309)
                    ·
                      refine ⟨2347914939754881118621241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6261106506013016316323309 2347914939754881118621241)
                      ·
                        rfl

theorem cell23_4572548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_4572548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572548 prefixEnd_4572548 := by exact prefixLift 4572548
  have htrace : WordTrace (prefixWord ++ tailWord_4572548) baseStart_4572548 baseEnd_4572548 := by
    simpa [prefixWord, tailWord_4572548, baseEnd_4572548] using wordTrace_append hprefix tailTrace_4572548
  have hstable : (prefixWord ++ tailWord_4572548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572548).length < 2 ^ (prefixWord ++ tailWord_4572548).sum := by decide
  have hdescent : baseEnd_4572548 < baseStart_4572548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572677 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 1, 7, 3]
def baseStart_4572677 : Nat := 118140960795 + 4572677 * 2 ^ 59
def prefixEnd_4572677 : Nat := 4983230072969 + 3 ^ 40 * 4572677 * 2
def baseEnd_4572677 : Nat := 2347981178759311113908147

theorem tailTrace_4572677 : CollatzResearch.WordTrace tailWord_4572677 prefixEnd_4572677 2347981178759311113908147 := by
  unfold tailWord_4572677
  simp only [CollatzResearch.WordTrace]
  refine ⟨166779231654979654902020285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111186154436653103268013523 166779231654979654902020285)
  ·
    refine ⟨62542211870617370588257607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166779231654979654902020285 62542211870617370588257607)
    ·
      refine ⟨93813317805926055882386411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62542211870617370588257607 93813317805926055882386411)
      ·
        refine ⟨140719976708889083823579617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93813317805926055882386411 140719976708889083823579617)
        ·
          refine ⟨105539982531666812867684713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140719976708889083823579617 105539982531666812867684713)
          ·
            refine ⟨79154986898750109650763535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105539982531666812867684713 79154986898750109650763535)
            ·
              refine ⟨118732480348125164476145303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79154986898750109650763535 118732480348125164476145303)
              ·
                refine ⟨178098720522187746714217955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118732480348125164476145303 178098720522187746714217955)
                ·
                  refine ⟨267148080783281620071326933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178098720522187746714217955 267148080783281620071326933)
                  ·
                    refine ⟨6261283143358162970421725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 267148080783281620071326933 6261283143358162970421725)
                    ·
                      refine ⟨2347981178759311113908147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6261283143358162970421725 2347981178759311113908147)
                      ·
                        rfl

theorem cell23_4572677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_4572677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572677 prefixEnd_4572677 := by exact prefixLift 4572677
  have htrace : WordTrace (prefixWord ++ tailWord_4572677) baseStart_4572677 baseEnd_4572677 := by
    simpa [prefixWord, tailWord_4572677, baseEnd_4572677] using wordTrace_append hprefix tailTrace_4572677
  have hstable : (prefixWord ++ tailWord_4572677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572677).length < 2 ^ (prefixWord ++ tailWord_4572677).sum := by decide
  have hdescent : baseEnd_4572677 < baseStart_4572677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572714 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 3, 5]
def baseStart_4572714 : Nat := 118140960795 + 4572714 * 2 ^ 59
def prefixEnd_4572714 : Nat := 4983230072969 + 3 ^ 40 * 4572714 * 2
def baseEnd_4572714 : Nat := 782666725847842489715159

theorem tailTrace_4572714 : CollatzResearch.WordTrace tailWord_4572714 prefixEnd_4572714 782666725847842489715159 := by
  unfold tailWord_4572714
  simp only [CollatzResearch.WordTrace]
  refine ⟨41695145288961402555279299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111187054103897073480744797 41695145288961402555279299)
  ·
    refine ⟨62542717933442103832918949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41695145288961402555279299 62542717933442103832918949)
    ·
      refine ⟨11726759612520394468672303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62542717933442103832918949 11726759612520394468672303)
      ·
        refine ⟨17590139418780591703008455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11726759612520394468672303 17590139418780591703008455)
        ·
          refine ⟨26385209128170887554512683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17590139418780591703008455 26385209128170887554512683)
          ·
            refine ⟨39577813692256331331769025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26385209128170887554512683 39577813692256331331769025)
            ·
              refine ⟨29683360269192248498826769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39577813692256331331769025 29683360269192248498826769)
              ·
                refine ⟨22262520201894186374120077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29683360269192248498826769 22262520201894186374120077)
                ·
                  refine ⟨8348445075710319890295029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22262520201894186374120077 8348445075710319890295029)
                  ·
                    refine ⟨782666725847842489715159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8348445075710319890295029 782666725847842489715159)
                    ·
                      rfl

theorem cell23_4572714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_4572714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572714 prefixEnd_4572714 := by exact prefixLift 4572714
  have htrace : WordTrace (prefixWord ++ tailWord_4572714) baseStart_4572714 baseEnd_4572714 := by
    simpa [prefixWord, tailWord_4572714, baseEnd_4572714] using wordTrace_append hprefix tailTrace_4572714
  have hstable : (prefixWord ++ tailWord_4572714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572714).length < 2 ^ (prefixWord ++ tailWord_4572714).sum := by decide
  have hdescent : baseEnd_4572714 < baseStart_4572714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572718 : List Nat := [4, 1, 3, 1, 2, 3, 2, 1, 6]
def baseStart_4572718 : Nat := 118140960795 + 4572718 * 2 ^ 59
def prefixEnd_4572718 : Nat := 4983230072969 + 3 ^ 40 * 4572718 * 2
def baseEnd_4572718 : Nat := 260889136829571717055051

theorem tailTrace_4572718 : CollatzResearch.WordTrace tailWord_4572718 prefixEnd_4572718 260889136829571717055051 := by
  unfold tailWord_4572718
  simp only [CollatzResearch.WordTrace]
  refine ⟨20847590880978889863032851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111187151365220745936175205 20847590880978889863032851)
  ·
    refine ⟨31271386321468334794549277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20847590880978889863032851 31271386321468334794549277)
    ·
      refine ⟨11726769870550625547955979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31271386321468334794549277 11726769870550625547955979)
      ·
        refine ⟨17590154805825938321933969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11726769870550625547955979 17590154805825938321933969)
        ·
          refine ⟨13192616104369453741450477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17590154805825938321933969 13192616104369453741450477)
          ·
            refine ⟨4947231039138545153043929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13192616104369453741450477 4947231039138545153043929)
            ·
              refine ⟨3710423279353908864782947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4947231039138545153043929 3710423279353908864782947)
              ·
                refine ⟨5565634919030863297174421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710423279353908864782947 5565634919030863297174421)
                ·
                  refine ⟨260889136829571717055051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5565634919030863297174421 260889136829571717055051)
                  ·
                    rfl

theorem cell23_4572718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_4572718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572718 prefixEnd_4572718 := by exact prefixLift 4572718
  have htrace : WordTrace (prefixWord ++ tailWord_4572718) baseStart_4572718 baseEnd_4572718 := by
    simpa [prefixWord, tailWord_4572718, baseEnd_4572718] using wordTrace_append hprefix tailTrace_4572718
  have hstable : (prefixWord ++ tailWord_4572718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572718).length < 2 ^ (prefixWord ++ tailWord_4572718).sum := by decide
  have hdescent : baseEnd_4572718 < baseStart_4572718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572777 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 6]
def baseStart_4572777 : Nat := 118140960795 + 4572777 * 2 ^ 59
def prefixEnd_4572777 : Nat := 4983230072969 + 3 ^ 40 * 4572777 * 2
def baseEnd_4572777 : Nat := 2348032526824760722657687

theorem tailTrace_4572777 : CollatzResearch.WordTrace tailWord_4572777 prefixEnd_4572777 2348032526824760722657687 := by
  unfold tailWord_4572777
  simp only [CollatzResearch.WordTrace]
  refine ⟨166782878954617371980660585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111188585969744914653773723 166782878954617371980660585)
  ·
    refine ⟨125087159215963028985495439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166782878954617371980660585 125087159215963028985495439)
    ·
      refine ⟨187630738823944543478243159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125087159215963028985495439 187630738823944543478243159)
      ·
        refine ⟨281446108235916815217364739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187630738823944543478243159 281446108235916815217364739)
        ·
          refine ⟨422169162353875222826047109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281446108235916815217364739 422169162353875222826047109)
          ·
            refine ⟨79156717941351604279883833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 422169162353875222826047109 79156717941351604279883833)
            ·
              refine ⟨59367538456013703209912875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79156717941351604279883833 59367538456013703209912875)
              ·
                refine ⟨89051307684020554814869313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59367538456013703209912875 89051307684020554814869313)
                ·
                  refine ⟨66788480763015416111151985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89051307684020554814869313 66788480763015416111151985)
                  ·
                    refine ⟨50091360572261562083363989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66788480763015416111151985 50091360572261562083363989)
                    ·
                      refine ⟨2348032526824760722657687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50091360572261562083363989 2348032526824760722657687)
                      ·
                        rfl

theorem cell23_4572777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_4572777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572777 prefixEnd_4572777 := by exact prefixLift 4572777
  have htrace : WordTrace (prefixWord ++ tailWord_4572777) baseStart_4572777 baseEnd_4572777 := by
    simpa [prefixWord, tailWord_4572777, baseEnd_4572777] using wordTrace_append hprefix tailTrace_4572777
  have hstable : (prefixWord ++ tailWord_4572777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572777).length < 2 ^ (prefixWord ++ tailWord_4572777).sum := by decide
  have hdescent : baseEnd_4572777 < baseStart_4572777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572801 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_4572801 : Nat := 118140960795 + 4572801 * 2 ^ 59
def prefixEnd_4572801 : Nat := 4983230072969 + 3 ^ 40 * 4572801 * 2
def baseEnd_4572801 : Nat := 2348044850360468628757577

theorem tailTrace_4572801 : CollatzResearch.WordTrace tailWord_4572801 prefixEnd_4572801 2348044850360468628757577 := by
  unfold tailWord_4572801
  simp only [CollatzResearch.WordTrace]
  refine ⟨166783754306530424079534257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111189169537686949386356171 166783754306530424079534257)
  ·
    refine ⟨125087815729897818059650693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166783754306530424079534257 125087815729897818059650693)
    ·
      refine ⟨23453965449355840886184505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125087815729897818059650693 23453965449355840886184505)
      ·
        refine ⟨17590474087016880664638379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23453965449355840886184505 17590474087016880664638379)
        ·
          refine ⟨26385711130525320996957569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17590474087016880664638379 26385711130525320996957569)
          ·
            refine ⟨19789283347893990747718177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26385711130525320996957569 19789283347893990747718177)
            ·
              refine ⟨14841962510920493060788633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19789283347893990747718177 14841962510920493060788633)
              ·
                refine ⟨11131471883190369795591475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14841962510920493060788633 11131471883190369795591475)
                ·
                  refine ⟨16697207824785554693387213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11131471883190369795591475 16697207824785554693387213)
                  ·
                    refine ⟨6261452934294583010020205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16697207824785554693387213 6261452934294583010020205)
                    ·
                      refine ⟨2348044850360468628757577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6261452934294583010020205 2348044850360468628757577)
                      ·
                        rfl

theorem cell23_4572801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_4572801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572801 prefixEnd_4572801 := by exact prefixLift 4572801
  have htrace : WordTrace (prefixWord ++ tailWord_4572801) baseStart_4572801 baseEnd_4572801 := by
    simpa [prefixWord, tailWord_4572801, baseEnd_4572801] using wordTrace_append hprefix tailTrace_4572801
  have hstable : (prefixWord ++ tailWord_4572801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572801).length < 2 ^ (prefixWord ++ tailWord_4572801).sum := by decide
  have hdescent : baseEnd_4572801 < baseStart_4572801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572845 : List Nat := [1, 5, 2, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_4572845 : Nat := 118140960795 + 4572845 * 2 ^ 59
def prefixEnd_4572845 : Nat := 4983230072969 + 3 ^ 40 * 4572845 * 2
def baseEnd_4572845 : Nat := 2348067443509266456607375

theorem tailTrace_4572845 : CollatzResearch.WordTrace tailWord_4572845 prefixEnd_4572845 2348067443509266456607375 := by
  unfold tailWord_4572845
  simp only [CollatzResearch.WordTrace]
  refine ⟨166785359118371019594135989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111190239412247346396090659 166785359118371019594135989)
  ·
    refine ⟨15636127417347283086950249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166785359118371019594135989 15636127417347283086950249)
    ·
      refine ⟨11727095563010462315212687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15636127417347283086950249 11727095563010462315212687)
      ·
        refine ⟨17590643344515693472819031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11727095563010462315212687 17590643344515693472819031)
        ·
          refine ⟨26385965016773540209228547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17590643344515693472819031 26385965016773540209228547)
          ·
            refine ⟨39578947525160310313842821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26385965016773540209228547 39578947525160310313842821)
            ·
              refine ⟨7421052660967558183845529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39578947525160310313842821 7421052660967558183845529)
              ·
                refine ⟨5565789495725668637884147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7421052660967558183845529 5565789495725668637884147)
                ·
                  refine ⟨8348684243588502956826221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5565789495725668637884147 8348684243588502956826221)
                  ·
                    refine ⟨3130756591345688608809833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8348684243588502956826221 3130756591345688608809833)
                    ·
                      refine ⟨2348067443509266456607375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3130756591345688608809833 2348067443509266456607375)
                      ·
                        rfl

theorem cell23_4572845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_4572845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572845 prefixEnd_4572845 := by exact prefixLift 4572845
  have htrace : WordTrace (prefixWord ++ tailWord_4572845) baseStart_4572845 baseEnd_4572845 := by
    simpa [prefixWord, tailWord_4572845, baseEnd_4572845] using wordTrace_append hprefix tailTrace_4572845
  have hstable : (prefixWord ++ tailWord_4572845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572845).length < 2 ^ (prefixWord ++ tailWord_4572845).sum := by decide
  have hdescent : baseEnd_4572845 < baseStart_4572845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572858 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2]
def baseStart_4572858 : Nat := 118140960795 + 4572858 * 2 ^ 59
def prefixEnd_4572858 : Nat := 4983230072969 + 3 ^ 40 * 4572858 * 2
def baseEnd_4572858 : Nat := 2348074118757774905744815

theorem tailTrace_4572858 : CollatzResearch.WordTrace tailWord_4572858 prefixEnd_4572858 2348074118757774905744815 := by
  unfold tailWord_4572858
  simp only [CollatzResearch.WordTrace]
  refine ⟨41696458316830980703589807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111190555511549281876239485 41696458316830980703589807)
  ·
    refine ⟨62544687475246471055384711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41696458316830980703589807 62544687475246471055384711)
    ·
      refine ⟨93817031212869706583077067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62544687475246471055384711 93817031212869706583077067)
      ·
        refine ⟨140725546819304559874615601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93817031212869706583077067 140725546819304559874615601)
        ·
          refine ⟨105544160114478419905961701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140725546819304559874615601 105544160114478419905961701)
          ·
            refine ⟨19789530021464703732367819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105544160114478419905961701 19789530021464703732367819)
            ·
              refine ⟨29684295032197055598551729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19789530021464703732367819 29684295032197055598551729)
              ·
                refine ⟨22263221274147791698913797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29684295032197055598551729 22263221274147791698913797)
                ·
                  refine ⟨4174353988902710943546337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22263221274147791698913797 4174353988902710943546337)
                  ·
                    refine ⟨3130765491677033207659753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4174353988902710943546337 3130765491677033207659753)
                    ·
                      refine ⟨2348074118757774905744815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3130765491677033207659753 2348074118757774905744815)
                      ·
                        rfl

theorem cell23_4572858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2].length) (baseStart_4572858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572858 prefixEnd_4572858 := by exact prefixLift 4572858
  have htrace : WordTrace (prefixWord ++ tailWord_4572858) baseStart_4572858 baseEnd_4572858 := by
    simpa [prefixWord, tailWord_4572858, baseEnd_4572858] using wordTrace_append hprefix tailTrace_4572858
  have hstable : (prefixWord ++ tailWord_4572858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572858).length < 2 ^ (prefixWord ++ tailWord_4572858).sum := by decide
  have hdescent : baseEnd_4572858 < baseStart_4572858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572881 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 7]
def baseStart_4572881 : Nat := 118140960795 + 4572881 * 2 ^ 59
def prefixEnd_4572881 : Nat := 4983230072969 + 3 ^ 40 * 4572881 * 2
def baseEnd_4572881 : Nat := 260898436534758701750801

theorem tailTrace_4572881 : CollatzResearch.WordTrace tailWord_4572881 prefixEnd_4572881 260898436534758701750801 := by
  unfold tailWord_4572881
  simp only [CollatzResearch.WordTrace]
  refine ⟨166786672146240597742446497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111191114764160398494964331 166786672146240597742446497)
  ·
    refine ⟨125090004109680448306834873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166786672146240597742446497 125090004109680448306834873)
    ·
      refine ⟨93817503082260336230126155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125090004109680448306834873 93817503082260336230126155)
      ·
        refine ⟨140726254623390504345189233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93817503082260336230126155 140726254623390504345189233)
        ·
          refine ⟨105544690967542878258891925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140726254623390504345189233 105544690967542878258891925)
          ·
            refine ⟨4947407389103572418385559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105544690967542878258891925 4947407389103572418385559)
            ·
              refine ⟨7421111083655358627578339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4947407389103572418385559 7421111083655358627578339)
              ·
                refine ⟨11131666625483037941367509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7421111083655358627578339 11131666625483037941367509)
                ·
                  refine ⟨260898436534758701750801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11131666625483037941367509 260898436534758701750801)
                  ·
                    rfl

theorem cell23_4572881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 7].length) (baseStart_4572881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572881 prefixEnd_4572881 := by exact prefixLift 4572881
  have htrace : WordTrace (prefixWord ++ tailWord_4572881) baseStart_4572881 baseEnd_4572881 := by
    simpa [prefixWord, tailWord_4572881, baseEnd_4572881] using wordTrace_append hprefix tailTrace_4572881
  have hstable : (prefixWord ++ tailWord_4572881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572881).length < 2 ^ (prefixWord ++ tailWord_4572881).sum := by decide
  have hdescent : baseEnd_4572881 < baseStart_4572881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572886 : List Nat := [5, 2, 1, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_4572886 : Nat := 118140960795 + 4572886 * 2 ^ 59
def prefixEnd_4572886 : Nat := 4983230072969 + 3 ^ 40 * 4572886 * 2
def baseEnd_4572886 : Nat := 2348088496216100796194687

theorem tailTrace_4572886 : CollatzResearch.WordTrace tailWord_4572886 prefixEnd_4572886 2348088496216100796194687 := by
  unfold tailWord_4572886
  simp only [CollatzResearch.WordTrace]
  refine ⟨10424178406951405224773657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111191236340814989064252341 10424178406951405224773657)
  ·
    refine ⟨7818133805213553918580243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10424178406951405224773657 7818133805213553918580243)
    ·
      refine ⟨11727200707820330877870365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7818133805213553918580243 11727200707820330877870365)
      ·
        refine ⟨4397700265432624079201387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11727200707820330877870365 4397700265432624079201387)
        ·
          refine ⟨6596550398148936118802081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4397700265432624079201387 6596550398148936118802081)
          ·
            refine ⟨4947412798611702089101561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6596550398148936118802081 4947412798611702089101561)
            ·
              refine ⟨3710559598958776566826171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4947412798611702089101561 3710559598958776566826171)
              ·
                refine ⟨5565839398438164850239257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710559598958776566826171 5565839398438164850239257)
                ·
                  refine ⟨4174379548828623637679443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5565839398438164850239257 4174379548828623637679443)
                  ·
                    refine ⟨6261569323242935456519165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4174379548828623637679443 6261569323242935456519165)
                    ·
                      refine ⟨2348088496216100796194687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6261569323242935456519165 2348088496216100796194687)
                      ·
                        rfl

theorem cell23_4572886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_4572886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572886 prefixEnd_4572886 := by exact prefixLift 4572886
  have htrace : WordTrace (prefixWord ++ tailWord_4572886) baseStart_4572886 baseEnd_4572886 := by
    simpa [prefixWord, tailWord_4572886, baseEnd_4572886] using wordTrace_append hprefix tailTrace_4572886
  have hstable : (prefixWord ++ tailWord_4572886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572886).length < 2 ^ (prefixWord ++ tailWord_4572886).sum := by decide
  have hdescent : baseEnd_4572886 < baseStart_4572886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572911 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 2, 5]
def baseStart_4572911 : Nat := 118140960795 + 4572911 * 2 ^ 59
def prefixEnd_4572911 : Nat := 4983230072969 + 3 ^ 40 * 4572911 * 2
def baseEnd_4572911 : Nat := 782700444410821066127357

theorem tailTrace_4572911 : CollatzResearch.WordTrace tailWord_4572911 prefixEnd_4572911 782700444410821066127357 := by
  unfold tailWord_4572911
  simp only [CollatzResearch.WordTrace]
  refine ⟨166787766336131912866038587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111191844224087941910692391 166787766336131912866038587)
  ·
    refine ⟨250181649504197869299057881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166787766336131912866038587 250181649504197869299057881)
    ·
      refine ⟨187636237128148401974293411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250181649504197869299057881 187636237128148401974293411)
      ·
        refine ⟨281454355692222602961440117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187636237128148401974293411 281454355692222602961440117)
        ·
          refine ⟨26386345846145869027635011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 281454355692222602961440117 26386345846145869027635011)
          ·
            refine ⟨39579518769218803541452517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26386345846145869027635011 39579518769218803541452517)
            ·
              refine ⟨7421159769228525664022347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39579518769218803541452517 7421159769228525664022347)
              ·
                refine ⟨11131739653842788496033521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7421159769228525664022347 11131739653842788496033521)
                ·
                  refine ⟨8348804740382091372025141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11131739653842788496033521 8348804740382091372025141)
                  ·
                    refine ⟨782700444410821066127357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8348804740382091372025141 782700444410821066127357)
                    ·
                      rfl

theorem cell23_4572911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 5].length) (baseStart_4572911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572911 prefixEnd_4572911 := by exact prefixLift 4572911
  have htrace : WordTrace (prefixWord ++ tailWord_4572911) baseStart_4572911 baseEnd_4572911 := by
    simpa [prefixWord, tailWord_4572911, baseEnd_4572911] using wordTrace_append hprefix tailTrace_4572911
  have hstable : (prefixWord ++ tailWord_4572911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572911).length < 2 ^ (prefixWord ++ tailWord_4572911).sum := by decide
  have hdescent : baseEnd_4572911 < baseStart_4572911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572931 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 4]
def baseStart_4572931 : Nat := 118140960795 + 4572931 * 2 ^ 59
def prefixEnd_4572931 : Nat := 4983230072969 + 3 ^ 40 * 4572931 * 2
def baseEnd_4572931 : Nat := 2348111602845553120131979

theorem tailTrace_4572931 : CollatzResearch.WordTrace tailWord_4572931 prefixEnd_4572931 2348111602845553120131979 := by
  unfold tailWord_4572931
  simp only [CollatzResearch.WordTrace]
  refine ⟨166788495796059456281766647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111192330530706304187844431 166788495796059456281766647)
  ·
    refine ⟨250182743694089184422649971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166788495796059456281766647 250182743694089184422649971)
    ·
      refine ⟨375274115541133776633974957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250182743694089184422649971 375274115541133776633974957)
      ·
        refine ⟨140727793327925166237740609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 375274115541133776633974957 140727793327925166237740609)
        ·
          refine ⟨105545844995943874678305457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140727793327925166237740609 105545844995943874678305457)
          ·
            refine ⟨79159383746957906008729093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105545844995943874678305457 79159383746957906008729093)
            ·
              refine ⟨14842384452554607376636705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79159383746957906008729093 14842384452554607376636705)
              ·
                refine ⟨11131788339415955532477529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14842384452554607376636705 11131788339415955532477529)
                ·
                  refine ⟨8348841254561966649358147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11131788339415955532477529 8348841254561966649358147)
                  ·
                    refine ⟨12523261881842949974037221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8348841254561966649358147 12523261881842949974037221)
                    ·
                      refine ⟨2348111602845553120131979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12523261881842949974037221 2348111602845553120131979)
                      ·
                        rfl

theorem cell23_4572931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_4572931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572931 prefixEnd_4572931 := by exact prefixLift 4572931
  have htrace : WordTrace (prefixWord ++ tailWord_4572931) baseStart_4572931 baseEnd_4572931 := by
    simpa [prefixWord, tailWord_4572931, baseEnd_4572931] using wordTrace_append hprefix tailTrace_4572931
  have hstable : (prefixWord ++ tailWord_4572931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572931).length < 2 ^ (prefixWord ++ tailWord_4572931).sum := by decide
  have hdescent : baseEnd_4572931 < baseStart_4572931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4572968 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_4572968 : Nat := 118140960795 + 4572968 * 2 ^ 59
def prefixEnd_4572968 : Nat := 4983230072969 + 3 ^ 40 * 4572968 * 2
def baseEnd_4572968 : Nat := 2348130601629769475369309

theorem tailTrace_4572968 : CollatzResearch.WordTrace tailWord_4572968 prefixEnd_4572968 2348130601629769475369309 := by
  unfold tailWord_4572968
  simp only [CollatzResearch.WordTrace]
  refine ⟨83394922648462705800431779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111193230197950274400575705 83394922648462705800431779)
  ·
    refine ⟨125092383972694058700647669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83394922648462705800431779 125092383972694058700647669)
    ·
      refine ⟨11727410997440068003185719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125092383972694058700647669 11727410997440068003185719)
      ·
        refine ⟨17591116496160102004778579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11727410997440068003185719 17591116496160102004778579)
        ·
          refine ⟨26386674744240153007167869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17591116496160102004778579 26386674744240153007167869)
          ·
            refine ⟨9895003029090057377687951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26386674744240153007167869 9895003029090057377687951)
            ·
              refine ⟨14842504543635086066531927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9895003029090057377687951 14842504543635086066531927)
              ·
                refine ⟨22263756815452629099797891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14842504543635086066531927 22263756815452629099797891)
                ·
                  refine ⟨33395635223178943649696837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22263756815452629099797891 33395635223178943649696837)
                  ·
                    refine ⟨6261681604346051934318157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33395635223178943649696837 6261681604346051934318157)
                    ·
                      refine ⟨2348130601629769475369309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6261681604346051934318157 2348130601629769475369309)
                      ·
                        rfl

theorem cell23_4572968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_4572968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4572968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4572968 prefixEnd_4572968 := by exact prefixLift 4572968
  have htrace : WordTrace (prefixWord ++ tailWord_4572968) baseStart_4572968 baseEnd_4572968 := by
    simpa [prefixWord, tailWord_4572968, baseEnd_4572968] using wordTrace_append hprefix tailTrace_4572968
  have hstable : (prefixWord ++ tailWord_4572968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4572968).length < 2 ^ (prefixWord ++ tailWord_4572968).sum := by decide
  have hdescent : baseEnd_4572968 < baseStart_4572968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4572968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573018 : List Nat := [3, 1, 1, 2, 1, 3, 4, 2, 1, 5]
def baseStart_4573018 : Nat := 118140960795 + 4573018 * 2 ^ 59
def prefixEnd_4573018 : Nat := 4983230072969 + 3 ^ 40 * 4573018 * 2
def baseEnd_4573018 : Nat := 782718758554164759914693

theorem tailTrace_4573018 : CollatzResearch.WordTrace tailWord_4573018 prefixEnd_4573018 782718758554164759914693 := by
  unfold tailWord_4573018
  simp only [CollatzResearch.WordTrace]
  refine ⟨41697917236686067535045927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111194445964496180093455805 41697917236686067535045927)
  ·
    refine ⟨62546875855029101302568891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41697917236686067535045927 62546875855029101302568891)
    ·
      refine ⟨93820313782543651953853337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62546875855029101302568891 93820313782543651953853337)
      ·
        refine ⟨70365235336907738965390003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93820313782543651953853337 70365235336907738965390003)
        ·
          refine ⟨105547853005361608448085005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70365235336907738965390003 105547853005361608448085005)
          ·
            refine ⟨39580444877010603168031877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105547853005361608448085005 39580444877010603168031877)
            ·
              refine ⟨7421333414439488094005977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39580444877010603168031877 7421333414439488094005977)
              ·
                refine ⟨5566000060829616070504483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7421333414439488094005977 5566000060829616070504483)
                ·
                  refine ⟨8349000091244424105756725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5566000060829616070504483 8349000091244424105756725)
                  ·
                    refine ⟨782718758554164759914693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8349000091244424105756725 782718758554164759914693)
                    ·
                      rfl

theorem cell23_4573018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_4573018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573018 prefixEnd_4573018 := by exact prefixLift 4573018
  have htrace : WordTrace (prefixWord ++ tailWord_4573018) baseStart_4573018 baseEnd_4573018 := by
    simpa [prefixWord, tailWord_4573018, baseEnd_4573018] using wordTrace_append hprefix tailTrace_4573018
  have hstable : (prefixWord ++ tailWord_4573018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573018).length < 2 ^ (prefixWord ++ tailWord_4573018).sum := by decide
  have hdescent : baseEnd_4573018 < baseStart_4573018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573031 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 3, 6]
def baseStart_4573031 : Nat := 118140960795 + 4573031 * 2 ^ 59
def prefixEnd_4573031 : Nat := 4983230072969 + 3 ^ 40 * 4573031 * 2
def baseEnd_4573031 : Nat := 782720983637000909627173

theorem tailTrace_4573031 : CollatzResearch.WordTrace tailWord_4573031 prefixEnd_4573031 782720983637000909627173 := by
  unfold tailWord_4573031
  simp only [CollatzResearch.WordTrace]
  refine ⟨166792143095697173360406947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111194762063798115573604631 166792143095697173360406947)
  ·
    refine ⟨250188214643545760040610421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166792143095697173360406947 250188214643545760040610421)
    ·
      refine ⟨23455145122832415003807227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 250188214643545760040610421 23455145122832415003807227)
      ·
        refine ⟨35182717684248622505710841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23455145122832415003807227 35182717684248622505710841)
        ·
          refine ⟨26387038263186466879283131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35182717684248622505710841 26387038263186466879283131)
          ·
            refine ⟨39580557394779700318924697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26387038263186466879283131 39580557394779700318924697)
            ·
              refine ⟨29685418046084775239193523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39580557394779700318924697 29685418046084775239193523)
              ·
                refine ⟨44528127069127162858790285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29685418046084775239193523 44528127069127162858790285)
                ·
                  refine ⟨16698047650922686072046357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44528127069127162858790285 16698047650922686072046357)
                  ·
                    refine ⟨782720983637000909627173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16698047650922686072046357 782720983637000909627173)
                    ·
                      rfl

theorem cell23_4573031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_4573031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573031 prefixEnd_4573031 := by exact prefixLift 4573031
  have htrace : WordTrace (prefixWord ++ tailWord_4573031) baseStart_4573031 baseEnd_4573031 := by
    simpa [prefixWord, tailWord_4573031, baseEnd_4573031] using wordTrace_append hprefix tailTrace_4573031
  have hstable : (prefixWord ++ tailWord_4573031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573031).length < 2 ^ (prefixWord ++ tailWord_4573031).sum := by decide
  have hdescent : baseEnd_4573031 < baseStart_4573031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573061 : List Nat := [1, 3, 1, 1, 3, 2, 4, 8]
def baseStart_4573061 : Nat := 118140960795 + 4573061 * 2 ^ 59
def prefixEnd_4573061 : Nat := 4983230072969 + 3 ^ 40 * 4573061 * 2
def baseEnd_4573061 : Nat := 86969568715949541166903

theorem tailTrace_4573061 : CollatzResearch.WordTrace tailWord_4573061 prefixEnd_4573061 86969568715949541166903 := by
  unfold tailWord_4573061
  simp only [CollatzResearch.WordTrace]
  refine ⟨166793237285588488483999037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111195491523725658989332691 166793237285588488483999037)
  ·
    refine ⟨62547463982095683181499639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166793237285588488483999037 62547463982095683181499639)
    ·
      refine ⟨93821195973143524772249459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62547463982095683181499639 93821195973143524772249459)
      ·
        refine ⟨140731793959715287158374189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93821195973143524772249459 140731793959715287158374189)
        ·
          refine ⟨52774422734893232684390321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140731793959715287158374189 52774422734893232684390321)
          ·
            refine ⟨39580817051169924513292741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52774422734893232684390321 39580817051169924513292741)
            ·
              refine ⟨7421403197094360846242389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39580817051169924513292741 7421403197094360846242389)
              ·
                refine ⟨86969568715949541166903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7421403197094360846242389 86969568715949541166903)
                ·
                  rfl

theorem cell23_4573061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 8].length) (baseStart_4573061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573061 prefixEnd_4573061 := by exact prefixLift 4573061
  have htrace : WordTrace (prefixWord ++ tailWord_4573061) baseStart_4573061 baseEnd_4573061 := by
    simpa [prefixWord, tailWord_4573061, baseEnd_4573061] using wordTrace_append hprefix tailTrace_4573061
  have hstable : (prefixWord ++ tailWord_4573061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573061).length < 2 ^ (prefixWord ++ tailWord_4573061).sum := by decide
  have hdescent : baseEnd_4573061 < baseStart_4573061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573092 : List Nat := [2, 3, 1, 2, 1, 4, 3, 1, 1, 2, 3]
def baseStart_4573092 : Nat := 118140960795 + 4573092 * 2 ^ 59
def prefixEnd_4573092 : Nat := 4983230072969 + 3 ^ 40 * 4573092 * 2
def baseEnd_4573092 : Nat := 2348194273230926990218739

theorem tailTrace_4573092 : CollatzResearch.WordTrace tailWord_4573092 prefixEnd_4573092 2348194273230926990218739 := by
  unfold tailWord_4573092
  simp only [CollatzResearch.WordTrace]
  refine ⟨83397183974238090389188765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111196245298984120518918353 83397183974238090389188765)
  ·
    refine ⟨31273943990339283895945787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83397183974238090389188765 31273943990339283895945787)
    ·
      refine ⟨46910915985508925843918681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31273943990339283895945787 46910915985508925843918681)
      ·
        refine ⟨35183186989131694382939011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46910915985508925843918681 35183186989131694382939011)
        ·
          refine ⟨52774780483697541574408517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35183186989131694382939011 52774780483697541574408517)
          ·
            refine ⟨9895271340693289045201597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52774780483697541574408517 9895271340693289045201597)
            ·
              refine ⟨3710726752759983391950599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9895271340693289045201597 3710726752759983391950599)
              ·
                refine ⟨5566090129139975087925899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710726752759983391950599 5566090129139975087925899)
                ·
                  refine ⟨8349135193709962631888849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5566090129139975087925899 8349135193709962631888849)
                  ·
                    refine ⟨6261851395282471973916637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8349135193709962631888849 6261851395282471973916637)
                    ·
                      refine ⟨2348194273230926990218739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6261851395282471973916637 2348194273230926990218739)
                      ·
                        rfl

theorem cell23_4573092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_4573092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573092 prefixEnd_4573092 := by exact prefixLift 4573092
  have htrace : WordTrace (prefixWord ++ tailWord_4573092) baseStart_4573092 baseEnd_4573092 := by
    simpa [prefixWord, tailWord_4573092, baseEnd_4573092] using wordTrace_append hprefix tailTrace_4573092
  have hstable : (prefixWord ++ tailWord_4573092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573092).length < 2 ^ (prefixWord ++ tailWord_4573092).sum := by decide
  have hdescent : baseEnd_4573092 < baseStart_4573092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573149 : List Nat := [1, 4, 3, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_4573149 : Nat := 118140960795 + 4573149 * 2 ^ 59
def prefixEnd_4573149 : Nat := 4983230072969 + 3 ^ 40 * 4573149 * 2
def baseEnd_4573149 : Nat := 2348223541628233267205977

theorem tailTrace_4573149 : CollatzResearch.WordTrace tailWord_4573149 prefixEnd_4573149 2348223541628233267205977 := by
  unfold tailWord_4573149
  simp only [CollatzResearch.WordTrace]
  refine ⟨166796446909269679513202501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111197631272846453008801667 166796446909269679513202501)
  ·
    refine ⟨31274333795488064908725469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166796446909269679513202501 31274333795488064908725469)
    ·
      refine ⟨11727875173308024340772051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31274333795488064908725469 11727875173308024340772051)
      ·
        refine ⟨17591812759962036511158077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11727875173308024340772051 17591812759962036511158077)
        ·
          refine ⟨6596929784985763691684279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17591812759962036511158077 6596929784985763691684279)
          ·
            refine ⟨9895394677478645537526419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6596929784985763691684279 9895394677478645537526419)
            ·
              refine ⟨14843092016217968306289629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9895394677478645537526419 14843092016217968306289629)
              ·
                refine ⟨5566159506081738114858611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14843092016217968306289629 5566159506081738114858611)
                ·
                  refine ⟨8349239259122607172287917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5566159506081738114858611 8349239259122607172287917)
                  ·
                    refine ⟨3130964722170977689607969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8349239259122607172287917 3130964722170977689607969)
                    ·
                      refine ⟨2348223541628233267205977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3130964722170977689607969 2348223541628233267205977)
                      ·
                        rfl

theorem cell23_4573149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_4573149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573149 prefixEnd_4573149 := by exact prefixLift 4573149
  have htrace : WordTrace (prefixWord ++ tailWord_4573149) baseStart_4573149 baseEnd_4573149 := by
    simpa [prefixWord, tailWord_4573149, baseEnd_4573149] using wordTrace_append hprefix tailTrace_4573149
  have hstable : (prefixWord ++ tailWord_4573149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573149).length < 2 ^ (prefixWord ++ tailWord_4573149).sum := by decide
  have hdescent : baseEnd_4573149 < baseStart_4573149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573162 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_4573162 : Nat := 118140960795 + 4573162 * 2 ^ 59
def prefixEnd_4573162 : Nat := 4983230072969 + 3 ^ 40 * 4573162 * 2
def baseEnd_4573162 : Nat := 2348230216876741716343417

theorem tailTrace_4573162 : CollatzResearch.WordTrace tailWord_4573162 prefixEnd_4573162 2348230216876741716343417 := by
  unfold tailWord_4573162
  simp only [CollatzResearch.WordTrace]
  refine ⟨41699230264555645683356435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111197947372148388488950493 41699230264555645683356435)
  ·
    refine ⟨62548845396833468525034653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41699230264555645683356435 62548845396833468525034653)
    ·
      refine ⟨23455817023812550696887995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62548845396833468525034653 23455817023812550696887995)
      ·
        refine ⟨35183725535718826045331993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23455817023812550696887995 35183725535718826045331993)
        ·
          refine ⟨26387794151789119533998995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35183725535718826045331993 26387794151789119533998995)
          ·
            refine ⟨39581691227683679300998493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26387794151789119533998995 39581691227683679300998493)
            ·
              refine ⟨14843134210381379737874435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39581691227683679300998493 14843134210381379737874435)
              ·
                refine ⟨22264701315572069606811653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14843134210381379737874435 22264701315572069606811653)
                ·
                  refine ⟨4174631496669763051277185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22264701315572069606811653 4174631496669763051277185)
                  ·
                    refine ⟨3130973622502322288457889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4174631496669763051277185 3130973622502322288457889)
                    ·
                      refine ⟨2348230216876741716343417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3130973622502322288457889 2348230216876741716343417)
                      ·
                        rfl

theorem cell23_4573162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_4573162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573162 prefixEnd_4573162 := by exact prefixLift 4573162
  have htrace : WordTrace (prefixWord ++ tailWord_4573162) baseStart_4573162 baseEnd_4573162 := by
    simpa [prefixWord, tailWord_4573162, baseEnd_4573162] using wordTrace_append hprefix tailTrace_4573162
  have hstable : (prefixWord ++ tailWord_4573162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573162).length < 2 ^ (prefixWord ++ tailWord_4573162).sum := by decide
  have hdescent : baseEnd_4573162 < baseStart_4573162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573198 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_4573198 : Nat := 118140960795 + 4573198 * 2 ^ 59
def prefixEnd_4573198 : Nat := 4983230072969 + 3 ^ 40 * 4573198 * 2
def baseEnd_4573198 : Nat := 782749567393434525164417

theorem tailTrace_4573198 : CollatzResearch.WordTrace tailWord_4573198 prefixEnd_4573198 782749567393434525164417 := by
  unfold tailWord_4573198
  simp only [CollatzResearch.WordTrace]
  refine ⟨20849779260761520110217031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111198822724061440587824165 20849779260761520110217031)
  ·
    refine ⟨31274668891142280165325547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20849779260761520110217031 31274668891142280165325547)
    ·
      refine ⟨46912003336713420247988321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31274668891142280165325547 46912003336713420247988321)
      ·
        refine ⟨35184002502535065185991241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46912003336713420247988321 35184002502535065185991241)
        ·
          refine ⟨26388001876901298889493431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35184002502535065185991241 26388001876901298889493431)
          ·
            refine ⟨39582002815351948334240147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26388001876901298889493431 39582002815351948334240147)
            ·
              refine ⟨59373004223027922501360221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39582002815351948334240147 59373004223027922501360221)
              ·
                refine ⟨22264876583635470938010083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59373004223027922501360221 22264876583635470938010083)
                ·
                  refine ⟨33397314875453206407015125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22264876583635470938010083 33397314875453206407015125)
                  ·
                    refine ⟨782749567393434525164417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33397314875453206407015125 782749567393434525164417)
                    ·
                      rfl

theorem cell23_4573198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_4573198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573198 prefixEnd_4573198 := by exact prefixLift 4573198
  have htrace : WordTrace (prefixWord ++ tailWord_4573198) baseStart_4573198 baseEnd_4573198 := by
    simpa [prefixWord, tailWord_4573198, baseEnd_4573198] using wordTrace_append hprefix tailTrace_4573198
  have hstable : (prefixWord ++ tailWord_4573198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573198).length < 2 ^ (prefixWord ++ tailWord_4573198).sum := by decide
  have hdescent : baseEnd_4573198 < baseStart_4573198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573208 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_4573208 : Nat := 118140960795 + 4573208 * 2 ^ 59
def prefixEnd_4573208 : Nat := 4983230072969 + 3 ^ 40 * 4573208 * 2
def baseEnd_4573208 : Nat := 2348253836986848536368205

theorem tailTrace_4573208 : CollatzResearch.WordTrace tailWord_4573208 prefixEnd_4573208 2348253836986848536368205 := by
  unfold tailWord_4573208
  simp only [CollatzResearch.WordTrace]
  refine ⟨83399299408027966294800139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111199065877370621726400185 83399299408027966294800139)
  ·
    refine ⟨125098949112041949442200209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83399299408027966294800139 125098949112041949442200209)
    ·
      refine ⟨93824211834031462081650157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125098949112041949442200209 93824211834031462081650157)
      ·
        refine ⟨35184079437761798280618809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93824211834031462081650157 35184079437761798280618809)
        ·
          refine ⟨26388059578321348710464107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35184079437761798280618809 26388059578321348710464107)
          ·
            refine ⟨39582089367482023065696161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26388059578321348710464107 39582089367482023065696161)
            ·
              refine ⟨29686567025611517299272121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39582089367482023065696161 29686567025611517299272121)
              ·
                refine ⟨22264925269208637974454091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29686567025611517299272121 22264925269208637974454091)
                ·
                  refine ⟨33397387903812956961681137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22264925269208637974454091 33397387903812956961681137)
                  ·
                    refine ⟨25048040927859717721260853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33397387903812956961681137 25048040927859717721260853)
                    ·
                      refine ⟨2348253836986848536368205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25048040927859717721260853 2348253836986848536368205)
                      ·
                        rfl

theorem cell23_4573208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_4573208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573208 prefixEnd_4573208 := by exact prefixLift 4573208
  have htrace : WordTrace (prefixWord ++ tailWord_4573208) baseStart_4573208 baseEnd_4573208 := by
    simpa [prefixWord, tailWord_4573208, baseEnd_4573208] using wordTrace_append hprefix tailTrace_4573208
  have hstable : (prefixWord ++ tailWord_4573208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573208).length < 2 ^ (prefixWord ++ tailWord_4573208).sum := by decide
  have hdescent : baseEnd_4573208 < baseStart_4573208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573235 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 2, 4, 2]
def baseStart_4573235 : Nat := 118140960795 + 4573235 * 2 ^ 59
def prefixEnd_4573235 : Nat := 4983230072969 + 3 ^ 40 * 4573235 * 2
def baseEnd_4573235 : Nat := 2348267700964519930730581

theorem tailTrace_4573235 : CollatzResearch.WordTrace tailWord_4573235 prefixEnd_4573235 2348267700964519930730581 := by
  unfold tailWord_4573235
  simp only [CollatzResearch.WordTrace]
  refine ⟨166799583586958116200833159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111199722391305410800555439 166799583586958116200833159)
  ·
    refine ⟨250199375380437174301249739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166799583586958116200833159 250199375380437174301249739)
    ·
      refine ⟨375299063070655761451874609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250199375380437174301249739 375299063070655761451874609)
      ·
        refine ⟨281474297302991821088905957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375299063070655761451874609 281474297302991821088905957)
        ·
          refine ⟨52776430744310966454169867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 281474297302991821088905957 52776430744310966454169867)
          ·
            refine ⟨79164646116466449681254801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52776430744310966454169867 79164646116466449681254801)
            ·
              refine ⟨59373484587349837260941101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79164646116466449681254801 59373484587349837260941101)
              ·
                refine ⟨22265056720256188972852913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59373484587349837260941101 22265056720256188972852913)
                ·
                  refine ⟨16698792540192141729639685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22265056720256188972852913 16698792540192141729639685)
                  ·
                    refine ⟨3131023601286026574307441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16698792540192141729639685 3131023601286026574307441)
                    ·
                      refine ⟨2348267700964519930730581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3131023601286026574307441 2348267700964519930730581)
                      ·
                        rfl

theorem cell23_4573235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 4, 2].length) (baseStart_4573235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573235 prefixEnd_4573235 := by exact prefixLift 4573235
  have htrace : WordTrace (prefixWord ++ tailWord_4573235) baseStart_4573235 baseEnd_4573235 := by
    simpa [prefixWord, tailWord_4573235, baseEnd_4573235] using wordTrace_append hprefix tailTrace_4573235
  have hstable : (prefixWord ++ tailWord_4573235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573235).length < 2 ^ (prefixWord ++ tailWord_4573235).sum := by decide
  have hdescent : baseEnd_4573235 < baseStart_4573235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573245 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_4573245 : Nat := 118140960795 + 4573245 * 2 ^ 59
def prefixEnd_4573245 : Nat := 4983230072969 + 3 ^ 40 * 4573245 * 2
def baseEnd_4573245 : Nat := 782757611923688297201845

theorem tailTrace_4573245 : CollatzResearch.WordTrace tailWord_4573245 prefixEnd_4573245 782757611923688297201845 := by
  unfold tailWord_4573245
  simp only [CollatzResearch.WordTrace]
  refine ⟨166799948316921887908697189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111199965544614591939131459 166799948316921887908697189)
  ·
    refine ⟨31274990309422853982880723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166799948316921887908697189 31274990309422853982880723)
    ·
      refine ⟨46912485464134280974321085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31274990309422853982880723 46912485464134280974321085)
      ·
        refine ⟨17592182049050355365370407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46912485464134280974321085 17592182049050355365370407)
        ·
          refine ⟨26388273073575533048055611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17592182049050355365370407 26388273073575533048055611)
          ·
            refine ⟨39582409610363299572083417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26388273073575533048055611 39582409610363299572083417)
            ·
              refine ⟨29686807207772474679062563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39582409610363299572083417 29686807207772474679062563)
              ·
                refine ⟨44530210811658712018593845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29686807207772474679062563 44530210811658712018593845)
                ·
                  refine ⟨4174707263593004251743173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44530210811658712018593845 4174707263593004251743173)
                  ·
                    refine ⟨782757611923688297201845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4174707263593004251743173 782757611923688297201845)
                    ·
                      rfl

theorem cell23_4573245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_4573245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573245 prefixEnd_4573245 := by exact prefixLift 4573245
  have htrace : WordTrace (prefixWord ++ tailWord_4573245) baseStart_4573245 baseEnd_4573245 := by
    simpa [prefixWord, tailWord_4573245, baseEnd_4573245] using wordTrace_append hprefix tailTrace_4573245
  have hstable : (prefixWord ++ tailWord_4573245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573245).length < 2 ^ (prefixWord ++ tailWord_4573245).sum := by decide
  have hdescent : baseEnd_4573245 < baseStart_4573245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573305 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 3, 5]
def baseStart_4573305 : Nat := 118140960795 + 4573305 * 2 ^ 59
def prefixEnd_4573305 : Nat := 4983230072969 + 3 ^ 40 * 4573305 * 2
def baseEnd_4573305 : Nat := 782767881536778218951753

theorem tailTrace_4573305 : CollatzResearch.WordTrace tailWord_4573305 prefixEnd_4573305 782767881536778218951753 := by
  unfold tailWord_4573305
  simp only [CollatzResearch.WordTrace]
  refine ⟨166802136696704518155881369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111201424464469678770587579 166802136696704518155881369)
  ·
    refine ⟨125101602522528388616911027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166802136696704518155881369 125101602522528388616911027)
    ·
      refine ⟨187652403783792582925366541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125101602522528388616911027 187652403783792582925366541)
      ·
        refine ⟨70369651418922218597012453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187652403783792582925366541 70369651418922218597012453)
        ·
          refine ⟨13194309641047915986939835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70369651418922218597012453 13194309641047915986939835)
          ·
            refine ⟨19791464461571873980409753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13194309641047915986939835 19791464461571873980409753)
            ·
              refine ⟨14843598346178905485307315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19791464461571873980409753 14843598346178905485307315)
              ·
                refine ⟨22265397519268358227960973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14843598346178905485307315 22265397519268358227960973)
                ·
                  refine ⟨8349524069725634335485365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22265397519268358227960973 8349524069725634335485365)
                  ·
                    refine ⟨782767881536778218951753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8349524069725634335485365 782767881536778218951753)
                    ·
                      rfl

theorem cell23_4573305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 5].length) (baseStart_4573305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573305 prefixEnd_4573305 := by exact prefixLift 4573305
  have htrace : WordTrace (prefixWord ++ tailWord_4573305) baseStart_4573305 baseEnd_4573305 := by
    simpa [prefixWord, tailWord_4573305, baseEnd_4573305] using wordTrace_append hprefix tailTrace_4573305
  have hstable : (prefixWord ++ tailWord_4573305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573305).length < 2 ^ (prefixWord ++ tailWord_4573305).sum := by decide
  have hdescent : baseEnd_4573305 < baseStart_4573305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573319 : List Nat := [1, 1, 4, 2, 1, 1, 3, 5, 1, 1, 3]
def baseStart_4573319 : Nat := 118140960795 + 4573319 * 2 ^ 59
def prefixEnd_4573319 : Nat := 4983230072969 + 3 ^ 40 * 4573319 * 2
def baseEnd_4573319 : Nat := 2348310833339497602080195

theorem tailTrace_4573319 : CollatzResearch.WordTrace tailWord_4573319 prefixEnd_4573319 2348310833339497602080195 := by
  unfold tailWord_4573319
  simp only [CollatzResearch.WordTrace]
  refine ⟨166802647318653798546891011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111201764879102532364594007 166802647318653798546891011)
  ·
    refine ⟨250203970977980697820336517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166802647318653798546891011 250203970977980697820336517)
    ·
      refine ⟨46913244558371380841313097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 250203970977980697820336517 46913244558371380841313097)
      ·
        refine ⟨35184933418778535630984823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46913244558371380841313097 35184933418778535630984823)
        ·
          refine ⟨52777400128167803446477235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35184933418778535630984823 52777400128167803446477235)
          ·
            refine ⟨79166100192251705169715853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52777400128167803446477235 79166100192251705169715853)
            ·
              refine ⟨29687287572094389438643445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79166100192251705169715853 29687287572094389438643445)
              ·
                refine ⟨2783183209883849009872823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29687287572094389438643445 2783183209883849009872823)
                ·
                  refine ⟨4174774814825773514809235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2783183209883849009872823 4174774814825773514809235)
                  ·
                    refine ⟨6262162222238660272213853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4174774814825773514809235 6262162222238660272213853)
                    ·
                      refine ⟨2348310833339497602080195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6262162222238660272213853 2348310833339497602080195)
                      ·
                        rfl

theorem cell23_4573319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_4573319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573319 prefixEnd_4573319 := by exact prefixLift 4573319
  have htrace : WordTrace (prefixWord ++ tailWord_4573319) baseStart_4573319 baseEnd_4573319 := by
    simpa [prefixWord, tailWord_4573319, baseEnd_4573319] using wordTrace_append hprefix tailTrace_4573319
  have hstable : (prefixWord ++ tailWord_4573319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573319).length < 2 ^ (prefixWord ++ tailWord_4573319).sum := by decide
  have hdescent : baseEnd_4573319 < baseStart_4573319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573322 : List Nat := [3, 1, 2, 3, 1, 3, 1, 3, 1, 5]
def baseStart_4573322 : Nat := 118140960795 + 4573322 * 2 ^ 59
def prefixEnd_4573322 : Nat := 4983230072969 + 3 ^ 40 * 4573322 * 2
def baseEnd_4573322 : Nat := 782770791260487030114227

theorem tailTrace_4573322 : CollatzResearch.WordTrace tailWord_4573322 prefixEnd_4573322 782770791260487030114227 := by
  unfold tailWord_4573322
  simp only [CollatzResearch.WordTrace]
  refine ⟨41700689184410732514812555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111201837825095286706166813 41700689184410732514812555)
  ·
    refine ⟨62551033776616098772218833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41700689184410732514812555 62551033776616098772218833)
    ·
      refine ⟨46913275332462074079164125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62551033776616098772218833 46913275332462074079164125)
      ·
        refine ⟨17592478249673277779686547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46913275332462074079164125 17592478249673277779686547)
        ·
          refine ⟨26388717374509916669529821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17592478249673277779686547 26388717374509916669529821)
          ·
            refine ⟨9895769015441218751073683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26388717374509916669529821 9895769015441218751073683)
            ·
              refine ⟨14843653523161828126610525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9895769015441218751073683 14843653523161828126610525)
              ·
                refine ⟨5566370071185685547478947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14843653523161828126610525 5566370071185685547478947)
                ·
                  refine ⟨8349555106778528321218421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5566370071185685547478947 8349555106778528321218421)
                  ·
                    refine ⟨782770791260487030114227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8349555106778528321218421 782770791260487030114227)
                    ·
                      rfl

theorem cell23_4573322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_4573322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573322 prefixEnd_4573322 := by exact prefixLift 4573322
  have htrace : WordTrace (prefixWord ++ tailWord_4573322) baseStart_4573322 baseEnd_4573322 := by
    simpa [prefixWord, tailWord_4573322, baseEnd_4573322] using wordTrace_append hprefix tailTrace_4573322
  have hstable : (prefixWord ++ tailWord_4573322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573322).length < 2 ^ (prefixWord ++ tailWord_4573322).sum := by decide
  have hdescent : baseEnd_4573322 < baseStart_4573322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573345 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_4573345 : Nat := 118140960795 + 4573345 * 2 ^ 59
def prefixEnd_4573345 : Nat := 4983230072969 + 3 ^ 40 * 4573345 * 2
def baseEnd_4573345 : Nat := 2348324183836514500355075

theorem tailTrace_4573345 : CollatzResearch.WordTrace tailWord_4573345 prefixEnd_4573345 2348324183836514500355075 := by
  unfold tailWord_4573345
  simp only [CollatzResearch.WordTrace]
  refine ⟨166803595616559604987337489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111202397077706403324891659 166803595616559604987337489)
  ·
    refine ⟨125102696712419703740503117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166803595616559604987337489 125102696712419703740503117)
    ·
      refine ⟨46913511267157388902688669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125102696712419703740503117 46913511267157388902688669)
      ·
        refine ⟨17592566725184020838508251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46913511267157388902688669 17592566725184020838508251)
        ·
          refine ⟨26388850087776031257762377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17592566725184020838508251 26388850087776031257762377)
          ·
            refine ⟨19791637565832023443321783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26388850087776031257762377 19791637565832023443321783)
            ·
              refine ⟨29687456348748035164982675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19791637565832023443321783 29687456348748035164982675)
              ·
                refine ⟨44531184523122052747474013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29687456348748035164982675 44531184523122052747474013)
                ·
                  refine ⟨16699194196170769780302755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44531184523122052747474013 16699194196170769780302755)
                  ·
                    refine ⟨25048791294256154670454133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16699194196170769780302755 25048791294256154670454133)
                    ·
                      refine ⟨2348324183836514500355075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25048791294256154670454133 2348324183836514500355075)
                      ·
                        rfl

theorem cell23_4573345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_4573345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573345 prefixEnd_4573345 := by exact prefixLift 4573345
  have htrace : WordTrace (prefixWord ++ tailWord_4573345) baseStart_4573345 baseEnd_4573345 := by
    simpa [prefixWord, tailWord_4573345, baseEnd_4573345] using wordTrace_append hprefix tailTrace_4573345
  have hstable : (prefixWord ++ tailWord_4573345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573345).length < 2 ^ (prefixWord ++ tailWord_4573345).sum := by decide
  have hdescent : baseEnd_4573345 < baseStart_4573345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573375 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 3]
def baseStart_4573375 : Nat := 118140960795 + 4573375 * 2 ^ 59
def prefixEnd_4573375 : Nat := 4983230072969 + 3 ^ 40 * 4573375 * 2
def baseEnd_4573375 : Nat := 2348339588256149382979937

theorem tailTrace_4573375 : CollatzResearch.WordTrace tailWord_4573375 prefixEnd_4573375 2348339588256149382979937 := by
  unfold tailWord_4573375
  simp only [CollatzResearch.WordTrace]
  refine ⟨166804689806450920110929579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111203126537633946740619719 166804689806450920110929579)
  ·
    refine ⟨250207034709676380166394369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166804689806450920110929579 250207034709676380166394369)
    ·
      refine ⟨187655276032257285124795777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250207034709676380166394369 187655276032257285124795777)
      ·
        refine ⟨140741457024192963843596833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187655276032257285124795777 140741457024192963843596833)
        ·
          refine ⟨105556092768144722882697625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140741457024192963843596833 105556092768144722882697625)
          ·
            refine ⟨79167069576108542162023219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105556092768144722882697625 79167069576108542162023219)
            ·
              refine ⟨118750604364162813243034829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79167069576108542162023219 118750604364162813243034829)
              ·
                refine ⟨44531476636561054966138061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118750604364162813243034829 44531476636561054966138061)
                ·
                  refine ⟨16699303738710395612301773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44531476636561054966138061 16699303738710395612301773)
                  ·
                    refine ⟨6262238902016398354613165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16699303738710395612301773 6262238902016398354613165)
                    ·
                      refine ⟨2348339588256149382979937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6262238902016398354613165 2348339588256149382979937)
                      ·
                        rfl

theorem cell23_4573375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_4573375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573375 prefixEnd_4573375 := by exact prefixLift 4573375
  have htrace : WordTrace (prefixWord ++ tailWord_4573375) baseStart_4573375 baseEnd_4573375 := by
    simpa [prefixWord, tailWord_4573375, baseEnd_4573375] using wordTrace_append hprefix tailTrace_4573375
  have hstable : (prefixWord ++ tailWord_4573375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573375).length < 2 ^ (prefixWord ++ tailWord_4573375).sum := by decide
  have hdescent : baseEnd_4573375 < baseStart_4573375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573409 : List Nat := [1, 2, 3, 1, 3, 1, 3, 3, 2, 1, 3]
def baseStart_4573409 : Nat := 118140960795 + 4573409 * 2 ^ 59
def prefixEnd_4573409 : Nat := 4983230072969 + 3 ^ 40 * 4573409 * 2
def baseEnd_4573409 : Nat := 2348357046598402249954781

theorem tailTrace_4573409 : CollatzResearch.WordTrace tailWord_4573409 prefixEnd_4573409 2348357046598402249954781 := by
  unfold tailWord_4573409
  simp only [CollatzResearch.WordTrace]
  refine ⟨166805929888327743917667281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111203953258885162611778187 166805929888327743917667281)
  ·
    refine ⟨125104447416245807938250461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166805929888327743917667281 125104447416245807938250461)
    ·
      refine ⟨46914167781092177976843923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125104447416245807938250461 46914167781092177976843923)
      ·
        refine ⟨70371251671638266965265885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46914167781092177976843923 70371251671638266965265885)
        ·
          refine ⟨26389219376864350111974707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70371251671638266965265885 26389219376864350111974707)
          ·
            refine ⟨39583829065296525167962061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26389219376864350111974707 39583829065296525167962061)
            ·
              refine ⟨14843935899486196937985773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39583829065296525167962061 14843935899486196937985773)
              ·
                refine ⟨5566475962307323851744665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14843935899486196937985773 5566475962307323851744665)
                ·
                  refine ⟨4174856971730492888808499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5566475962307323851744665 4174856971730492888808499)
                  ·
                    refine ⟨6262285457595739333212749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4174856971730492888808499 6262285457595739333212749)
                    ·
                      refine ⟨2348357046598402249954781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6262285457595739333212749 2348357046598402249954781)
                      ·
                        rfl

theorem cell23_4573409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_4573409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573409 prefixEnd_4573409 := by exact prefixLift 4573409
  have htrace : WordTrace (prefixWord ++ tailWord_4573409) baseStart_4573409 baseEnd_4573409 := by
    simpa [prefixWord, tailWord_4573409, baseEnd_4573409] using wordTrace_append hprefix tailTrace_4573409
  have hstable : (prefixWord ++ tailWord_4573409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573409).length < 2 ^ (prefixWord ++ tailWord_4573409).sum := by decide
  have hdescent : baseEnd_4573409 < baseStart_4573409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573410 : List Nat := [3, 3, 4, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4573410 : Nat := 118140960795 + 4573410 * 2 ^ 59
def prefixEnd_4573410 : Nat := 4983230072969 + 3 ^ 40 * 4573410 * 2
def baseEnd_4573410 : Nat := 2348357560079056746042277

theorem tailTrace_4573410 : CollatzResearch.WordTrace tailWord_4573410 prefixEnd_4573410 2348357560079056746042277 := by
  unfold tailWord_4573410
  simp only [CollatzResearch.WordTrace]
  refine ⟨41701491590331030272113421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111203977574216080725635789 41701491590331030272113421)
  ·
    refine ⟨15638059346374136352042533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41701491590331030272113421 15638059346374136352042533)
    ·
      refine ⟨2932136127445150566007975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15638059346374136352042533 2932136127445150566007975)
      ·
        refine ⟨4398204191167725849011963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2932136127445150566007975 4398204191167725849011963)
        ·
          refine ⟨6597306286751588773517945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4398204191167725849011963 6597306286751588773517945)
          ·
            refine ⟨4947979715063691580138459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6597306286751588773517945 4947979715063691580138459)
            ·
              refine ⟨7421969572595537370207689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4947979715063691580138459 7421969572595537370207689)
              ·
                refine ⟨5566477179446653027655767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7421969572595537370207689 5566477179446653027655767)
                ·
                  refine ⟨8349715769169979541483651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5566477179446653027655767 8349715769169979541483651)
                  ·
                    refine ⟨12524573653754969312225477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8349715769169979541483651 12524573653754969312225477)
                    ·
                      refine ⟨2348357560079056746042277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12524573653754969312225477 2348357560079056746042277)
                      ·
                        rfl

theorem cell23_4573410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4573410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573410 prefixEnd_4573410 := by exact prefixLift 4573410
  have htrace : WordTrace (prefixWord ++ tailWord_4573410) baseStart_4573410 baseEnd_4573410 := by
    simpa [prefixWord, tailWord_4573410, baseEnd_4573410] using wordTrace_append hprefix tailTrace_4573410
  have hstable : (prefixWord ++ tailWord_4573410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573410).length < 2 ^ (prefixWord ++ tailWord_4573410).sum := by decide
  have hdescent : baseEnd_4573410 < baseStart_4573410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573435 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 3]
def baseStart_4573435 : Nat := 118140960795 + 4573435 * 2 ^ 59
def prefixEnd_4573435 : Nat := 4983230072969 + 3 ^ 40 * 4573435 * 2
def baseEnd_4573435 : Nat := 2348370397095419148229661

theorem tailTrace_4573435 : CollatzResearch.WordTrace tailWord_4573435 prefixEnd_4573435 2348370397095419148229661 := by
  unfold tailWord_4573435
  simp only [CollatzResearch.WordTrace]
  refine ⟨166806878186233550358113759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111204585457489033572075839 166806878186233550358113759)
  ·
    refine ⟨250210317279350325537170639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166806878186233550358113759 250210317279350325537170639)
    ·
      refine ⟨375315475919025488305755959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250210317279350325537170639 375315475919025488305755959)
      ·
        refine ⟨562973213878538232458633939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375315475919025488305755959 562973213878538232458633939)
        ·
          refine ⟨844459820817807348687950909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562973213878538232458633939 844459820817807348687950909)
          ·
            refine ⟨316672432806677755757981591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 844459820817807348687950909 316672432806677755757981591)
            ·
              refine ⟨475008649210016633636972387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316672432806677755757981591 475008649210016633636972387)
              ·
                refine ⟨712512973815024950455458581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 475008649210016633636972387 712512973815024950455458581)
                ·
                  refine ⟨33399045647579294552599621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 712512973815024950455458581 33399045647579294552599621)
                  ·
                    refine ⟨6262321058921117728612429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33399045647579294552599621 6262321058921117728612429)
                    ·
                      refine ⟨2348370397095419148229661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6262321058921117728612429 2348370397095419148229661)
                      ·
                        rfl

theorem cell23_4573435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 3].length) (baseStart_4573435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573435 prefixEnd_4573435 := by exact prefixLift 4573435
  have htrace : WordTrace (prefixWord ++ tailWord_4573435) baseStart_4573435 baseEnd_4573435 := by
    simpa [prefixWord, tailWord_4573435, baseEnd_4573435] using wordTrace_append hprefix tailTrace_4573435
  have hstable : (prefixWord ++ tailWord_4573435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573435).length < 2 ^ (prefixWord ++ tailWord_4573435).sum := by decide
  have hdescent : baseEnd_4573435 < baseStart_4573435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573466 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2]
def baseStart_4573466 : Nat := 118140960795 + 4573466 * 2 ^ 59
def prefixEnd_4573466 : Nat := 4983230072969 + 3 ^ 40 * 4573466 * 2
def baseEnd_4573466 : Nat := 2348386314995708526942019

theorem tailTrace_4573466 : CollatzResearch.WordTrace tailWord_4573466 prefixEnd_4573466 2348386314995708526942019 := by
  unfold tailWord_4573466
  simp only [CollatzResearch.WordTrace]
  refine ⟨41702002212280310663123063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111205339232747495101661501 41702002212280310663123063)
  ·
    refine ⟨62553003318420465994684595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41702002212280310663123063 62553003318420465994684595)
    ·
      refine ⟨93829504977630698992026893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62553003318420465994684595 93829504977630698992026893)
      ·
        refine ⟨35186064366611512122010085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93829504977630698992026893 35186064366611512122010085)
        ·
          refine ⟨6597387068739658522876891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35186064366611512122010085 6597387068739658522876891)
          ·
            refine ⟨9896080603109487784315337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6597387068739658522876891 9896080603109487784315337)
            ·
              refine ⟨7422060452332115838236503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9896080603109487784315337 7422060452332115838236503)
              ·
                refine ⟨11133090678498173757354755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7422060452332115838236503 11133090678498173757354755)
                ·
                  refine ⟨16699636017747260636032133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11133090678498173757354755 16699636017747260636032133)
                  ·
                    refine ⟨3131181753327611369256025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16699636017747260636032133 3131181753327611369256025)
                    ·
                      refine ⟨2348386314995708526942019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3131181753327611369256025 2348386314995708526942019)
                      ·
                        rfl

theorem cell23_4573466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_4573466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573466 prefixEnd_4573466 := by exact prefixLift 4573466
  have htrace : WordTrace (prefixWord ++ tailWord_4573466) baseStart_4573466 baseEnd_4573466 := by
    simpa [prefixWord, tailWord_4573466, baseEnd_4573466] using wordTrace_append hprefix tailTrace_4573466
  have hstable : (prefixWord ++ tailWord_4573466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573466).length < 2 ^ (prefixWord ++ tailWord_4573466).sum := by decide
  have hdescent : baseEnd_4573466 < baseStart_4573466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573472 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 7]
def baseStart_4573472 : Nat := 118140960795 + 4573472 * 2 ^ 59
def prefixEnd_4573472 : Nat := 4983230072969 + 3 ^ 40 * 4573472 * 2
def baseEnd_4573472 : Nat := 260932155097737278162999

theorem tailTrace_4573472 : CollatzResearch.WordTrace tailWord_4573472 prefixEnd_4573472 260932155097737278162999 := by
  unfold tailWord_4573472
  simp only [CollatzResearch.WordTrace]
  refine ⟨83404113843549752838605335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111205485124733003784807113 83404113843549752838605335)
  ·
    refine ⟨125106170765324629257908003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83404113843549752838605335 125106170765324629257908003)
    ·
      refine ⟨187659256147986943886862005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125106170765324629257908003 187659256147986943886862005)
      ·
        refine ⟨17593055263873775989393313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 187659256147986943886862005 17593055263873775989393313)
        ·
          refine ⟨13194791447905331992044985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17593055263873775989393313 13194791447905331992044985)
          ·
            refine ⟨9896093585928998994033739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13194791447905331992044985 9896093585928998994033739)
            ·
              refine ⟨14844140378893498491050609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9896093585928998994033739 14844140378893498491050609)
              ·
                refine ⟨11133105284170123868287957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14844140378893498491050609 11133105284170123868287957)
                ·
                  refine ⟨260932155097737278162999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11133105284170123868287957 260932155097737278162999)
                  ·
                    rfl

theorem cell23_4573472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 7].length) (baseStart_4573472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573472 prefixEnd_4573472 := by exact prefixLift 4573472
  have htrace : WordTrace (prefixWord ++ tailWord_4573472) baseStart_4573472 baseEnd_4573472 := by
    simpa [prefixWord, tailWord_4573472, baseEnd_4573472] using wordTrace_append hprefix tailTrace_4573472
  have hstable : (prefixWord ++ tailWord_4573472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573472).length < 2 ^ (prefixWord ++ tailWord_4573472).sum := by decide
  have hdescent : baseEnd_4573472 < baseStart_4573472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573495 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_4573495 : Nat := 118140960795 + 4573495 * 2 ^ 59
def prefixEnd_4573495 : Nat := 4983230072969 + 3 ^ 40 * 4573495 * 2
def baseEnd_4573495 : Nat := 2348401205934688913479385

theorem tailTrace_4573495 : CollatzResearch.WordTrace tailWord_4573495 prefixEnd_4573495 2348401205934688913479385 := by
  unfold tailWord_4573495
  simp only [CollatzResearch.WordTrace]
  refine ⟨166809066566016180605297939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111206044377344120403531959 166809066566016180605297939)
  ·
    refine ⟨250213599849024270907946909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166809066566016180605297939 250213599849024270907946909)
    ·
      refine ⟨93830099943384101590480091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250213599849024270907946909 93830099943384101590480091)
      ·
        refine ⟨140745149915076152385720137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93830099943384101590480091 140745149915076152385720137)
        ·
          refine ⟨105558862436307114289290103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140745149915076152385720137 105558862436307114289290103)
          ·
            refine ⟨158338293654460671433935155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105558862436307114289290103 158338293654460671433935155)
            ·
              refine ⟨237507440481691007150902733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158338293654460671433935155 237507440481691007150902733)
              ·
                refine ⟨89065290180634127681588525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237507440481691007150902733 89065290180634127681588525)
                ·
                  refine ⟨33399483817737797880595697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89065290180634127681588525 33399483817737797880595697)
                  ·
                    refine ⟨25049612863303348410446773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33399483817737797880595697 25049612863303348410446773)
                    ·
                      refine ⟨2348401205934688913479385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25049612863303348410446773 2348401205934688913479385)
                      ·
                        rfl

theorem cell23_4573495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_4573495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573495 prefixEnd_4573495 := by exact prefixLift 4573495
  have htrace : WordTrace (prefixWord ++ tailWord_4573495) baseStart_4573495 baseEnd_4573495 := by
    simpa [prefixWord, tailWord_4573495, baseEnd_4573495] using wordTrace_append hprefix tailTrace_4573495
  have hstable : (prefixWord ++ tailWord_4573495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573495).length < 2 ^ (prefixWord ++ tailWord_4573495).sum := by decide
  have hdescent : baseEnd_4573495 < baseStart_4573495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573522 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_4573522 : Nat := 118140960795 + 4573522 * 2 ^ 59
def prefixEnd_4573522 : Nat := 4983230072969 + 3 ^ 40 * 4573522 * 2
def baseEnd_4573522 : Nat := 2348415069912360307841761

theorem tailTrace_4573522 : CollatzResearch.WordTrace tailWord_4573522 prefixEnd_4573522 2348415069912360307841761 := by
  unfold tailWord_4573522
  simp only [CollatzResearch.WordTrace]
  refine ⟨41702512834229591054132705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111206700891278909477687213 41702512834229591054132705)
  ·
    refine ⟨31276884625672193290599529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41702512834229591054132705 31276884625672193290599529)
    ·
      refine ⟨23457663469254144967949647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31276884625672193290599529 23457663469254144967949647)
      ·
        refine ⟨35186495203881217451924471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23457663469254144967949647 35186495203881217451924471)
        ·
          refine ⟨52779742805821826177886707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35186495203881217451924471 52779742805821826177886707)
          ·
            refine ⟨79169614208732739266830061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52779742805821826177886707 79169614208732739266830061)
            ·
              refine ⟨29688605328274777225061273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79169614208732739266830061 29688605328274777225061273)
              ·
                refine ⟨22266453996206082918795955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29688605328274777225061273 22266453996206082918795955)
                ·
                  refine ⟨33399680994309124378193933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22266453996206082918795955 33399680994309124378193933)
                  ·
                    refine ⟨12524880372865921641822725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33399680994309124378193933 12524880372865921641822725)
                    ·
                      refine ⟨2348415069912360307841761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12524880372865921641822725 2348415069912360307841761)
                      ·
                        rfl

theorem cell23_4573522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_4573522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573522 prefixEnd_4573522 := by exact prefixLift 4573522
  have htrace : WordTrace (prefixWord ++ tailWord_4573522) baseStart_4573522 baseEnd_4573522 := by
    simpa [prefixWord, tailWord_4573522, baseEnd_4573522] using wordTrace_append hprefix tailTrace_4573522
  have hstable : (prefixWord ++ tailWord_4573522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573522).length < 2 ^ (prefixWord ++ tailWord_4573522).sum := by decide
  have hdescent : baseEnd_4573522 < baseStart_4573522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573545 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 10]
def baseStart_4573545 : Nat := 118140960795 + 4573545 * 2 ^ 59
def prefixEnd_4573545 : Nat := 4983230072969 + 3 ^ 40 * 4573545 * 2
def baseEnd_4573545 : Nat := 260936319996379301983795

theorem tailTrace_4573545 : CollatzResearch.WordTrace tailWord_4573545 prefixEnd_4573545 260936319996379301983795 := by
  unfold tailWord_4573545
  simp only [CollatzResearch.WordTrace]
  refine ⟨166810890215835039144618089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111207260143890026096412059 166810890215835039144618089)
  ·
    refine ⟨125108167661876279358463567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166810890215835039144618089 125108167661876279358463567)
    ·
      refine ⟨187662251492814419037695351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125108167661876279358463567 187662251492814419037695351)
      ·
        refine ⟨281493377239221628556543027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187662251492814419037695351 281493377239221628556543027)
        ·
          refine ⟨422240065858832442834814541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281493377239221628556543027 422240065858832442834814541)
          ·
            refine ⟨158340024697062166063055453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 422240065858832442834814541 158340024697062166063055453)
            ·
              refine ⟨59377509261398312273645795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158340024697062166063055453 59377509261398312273645795)
              ·
                refine ⟨89066263892097468410468693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59377509261398312273645795 89066263892097468410468693)
                ·
                  refine ⟨260936319996379301983795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 89066263892097468410468693 260936319996379301983795)
                  ·
                    rfl

theorem cell23_4573545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 10].length) (baseStart_4573545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573545 prefixEnd_4573545 := by exact prefixLift 4573545
  have htrace : WordTrace (prefixWord ++ tailWord_4573545) baseStart_4573545 baseEnd_4573545 := by
    simpa [prefixWord, tailWord_4573545, baseEnd_4573545] using wordTrace_append hprefix tailTrace_4573545
  have hstable : (prefixWord ++ tailWord_4573545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573545).length < 2 ^ (prefixWord ++ tailWord_4573545).sum := by decide
  have hdescent : baseEnd_4573545 < baseStart_4573545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573579 : List Nat := [1, 1, 1, 1, 4, 4, 4, 1, 6]
def baseStart_4573579 : Nat := 118140960795 + 4573579 * 2 ^ 59
def prefixEnd_4573579 : Nat := 4983230072969 + 3 ^ 40 * 4573579 * 2
def baseEnd_4573579 : Nat := 260938259812185176092111

theorem tailTrace_4573579 : CollatzResearch.WordTrace tailWord_4573579 prefixEnd_4573579 260938259812185176092111 := by
  unfold tailWord_4573579
  simp only [CollatzResearch.WordTrace]
  refine ⟨166812130297711862951355791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111208086865141241967570527 166812130297711862951355791)
  ·
    refine ⟨250218195446567794427033687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166812130297711862951355791 250218195446567794427033687)
    ·
      refine ⟨375327293169851691640550531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250218195446567794427033687 375327293169851691640550531)
      ·
        refine ⟨562990939754777537460825797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375327293169851691640550531 562990939754777537460825797)
        ·
          refine ⟨105560801204020788273904837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 562990939754777537460825797 105560801204020788273904837)
          ·
            refine ⟨19792650225753897801357157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105560801204020788273904837 19792650225753897801357157)
            ·
              refine ⟨3711121917328855837754467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19792650225753897801357157 3711121917328855837754467)
              ·
                refine ⟨5566682875993283756631701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3711121917328855837754467 5566682875993283756631701)
                ·
                  refine ⟨260938259812185176092111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5566682875993283756631701 260938259812185176092111)
                  ·
                    rfl

theorem cell23_4573579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 6].length) (baseStart_4573579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573579 prefixEnd_4573579 := by exact prefixLift 4573579
  have htrace : WordTrace (prefixWord ++ tailWord_4573579) baseStart_4573579 baseEnd_4573579 := by
    simpa [prefixWord, tailWord_4573579, baseEnd_4573579] using wordTrace_append hprefix tailTrace_4573579
  have hstable : (prefixWord ++ tailWord_4573579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573579).length < 2 ^ (prefixWord ++ tailWord_4573579).sum := by decide
  have hdescent : baseEnd_4573579 < baseStart_4573579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573589 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 5, 1, 3]
def baseStart_4573589 : Nat := 118140960795 + 4573589 * 2 ^ 59
def prefixEnd_4573589 : Nat := 4983230072969 + 3 ^ 40 * 4573589 * 2
def baseEnd_4573589 : Nat := 2348449473116211545703953

theorem tailTrace_4573589 : CollatzResearch.WordTrace tailWord_4573589 prefixEnd_4573589 2348449473116211545703953 := by
  unfold tailWord_4573589
  simp only [CollatzResearch.WordTrace]
  refine ⟨166812495027675634659219821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111208330018450423106146547 166812495027675634659219821)
  ·
    refine ⟨62554685635378362997207433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166812495027675634659219821 62554685635378362997207433)
    ·
      refine ⟨46916014226533772247905575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62554685635378362997207433 46916014226533772247905575)
      ·
        refine ⟨70374021339800658371858363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46916014226533772247905575 70374021339800658371858363)
        ·
          refine ⟨105561032009700987557787545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70374021339800658371858363 105561032009700987557787545)
          ·
            refine ⟨79170774007275740668340659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105561032009700987557787545 79170774007275740668340659)
            ·
              refine ⟨118756161010913611002510989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79170774007275740668340659 118756161010913611002510989)
              ·
                refine ⟨44533560379092604125941621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118756161010913611002510989 44533560379092604125941621)
                ·
                  refine ⟨4175021285539931636807027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44533560379092604125941621 4175021285539931636807027)
                  ·
                    refine ⟨6262531928309897455210541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4175021285539931636807027 6262531928309897455210541)
                    ·
                      refine ⟨2348449473116211545703953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6262531928309897455210541 2348449473116211545703953)
                      ·
                        rfl

theorem cell23_4573589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_4573589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573589 prefixEnd_4573589 := by exact prefixLift 4573589
  have htrace : WordTrace (prefixWord ++ tailWord_4573589) baseStart_4573589 baseEnd_4573589 := by
    simpa [prefixWord, tailWord_4573589, baseEnd_4573589] using wordTrace_append hprefix tailTrace_4573589
  have hstable : (prefixWord ++ tailWord_4573589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573589).length < 2 ^ (prefixWord ++ tailWord_4573589).sum := by decide
  have hdescent : baseEnd_4573589 < baseStart_4573589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573623 : List Nat := [1, 1, 3, 1, 3, 4, 1, 4, 1, 1, 3]
def baseStart_4573623 : Nat := 118140960795 + 4573623 * 2 ^ 59
def prefixEnd_4573623 : Nat := 4983230072969 + 3 ^ 40 * 4573623 * 2
def baseEnd_4573623 : Nat := 2348466931458464412678797

theorem tailTrace_4573623 : CollatzResearch.WordTrace tailWord_4573623 prefixEnd_4573623 2348466931458464412678797 := by
  unfold tailWord_4573623
  simp only [CollatzResearch.WordTrace]
  refine ⟨166813735109552458465957523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111209156739701638977305015 166813735109552458465957523)
  ·
    refine ⟨250220602664328687698936285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166813735109552458465957523 250220602664328687698936285)
    ·
      refine ⟨93832725999123257887101107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250220602664328687698936285 93832725999123257887101107)
      ·
        refine ⟨140749088998684886830651661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93832725999123257887101107 140749088998684886830651661)
        ·
          refine ⟨52780908374506832561494373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140749088998684886830651661 52780908374506832561494373)
          ·
            refine ⟨9896420320220031105280195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52780908374506832561494373 9896420320220031105280195)
            ·
              refine ⟨14844630480330046657920293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9896420320220031105280195 14844630480330046657920293)
              ·
                refine ⟨2783368215061883748360055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14844630480330046657920293 2783368215061883748360055)
                ·
                  refine ⟨4175052322592825622540083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2783368215061883748360055 4175052322592825622540083)
                  ·
                    refine ⟨6262578483889238433810125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4175052322592825622540083 6262578483889238433810125)
                    ·
                      refine ⟨2348466931458464412678797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6262578483889238433810125 2348466931458464412678797)
                      ·
                        rfl

theorem cell23_4573623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 1, 1, 3].length) (baseStart_4573623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573623 prefixEnd_4573623 := by exact prefixLift 4573623
  have htrace : WordTrace (prefixWord ++ tailWord_4573623) baseStart_4573623 baseEnd_4573623 := by
    simpa [prefixWord, tailWord_4573623, baseEnd_4573623] using wordTrace_append hprefix tailTrace_4573623
  have hstable : (prefixWord ++ tailWord_4573623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573623).length < 2 ^ (prefixWord ++ tailWord_4573623).sum := by decide
  have hdescent : baseEnd_4573623 < baseStart_4573623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573629 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_4573629 : Nat := 118140960795 + 4573629 * 2 ^ 59
def prefixEnd_4573629 : Nat := 4983230072969 + 3 ^ 40 * 4573629 * 2
def baseEnd_4573629 : Nat := 2348470012342391389203769

theorem tailTrace_4573629 : CollatzResearch.WordTrace tailWord_4573629 prefixEnd_4573629 2348470012342391389203769 := by
  unfold tailWord_4573629
  simp only [CollatzResearch.WordTrace]
  refine ⟨166813953947530721490675941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111209302631687147660450627 166813953947530721490675941)
  ·
    refine ⟨31277616365162010279501739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166813953947530721490675941 31277616365162010279501739)
    ·
      refine ⟨46916424547743015419252609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31277616365162010279501739 46916424547743015419252609)
      ·
        refine ⟨35187318410807261564439457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46916424547743015419252609 35187318410807261564439457)
        ·
          refine ⟨26390488808105446173329593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35187318410807261564439457 26390488808105446173329593)
          ·
            refine ⟨19792866606079084629997195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26390488808105446173329593 19792866606079084629997195)
            ·
              refine ⟨29689299909118626944995793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19792866606079084629997195 29689299909118626944995793)
              ·
                refine ⟨22266974931838970208746845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29689299909118626944995793 22266974931838970208746845)
                ·
                  refine ⟨8350115599439613828280067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22266974931838970208746845 8350115599439613828280067)
                  ·
                    refine ⟨12525173399159420742420101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8350115599439613828280067 12525173399159420742420101)
                    ·
                      refine ⟨2348470012342391389203769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12525173399159420742420101 2348470012342391389203769)
                      ·
                        rfl

theorem cell23_4573629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_4573629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573629 prefixEnd_4573629 := by exact prefixLift 4573629
  have htrace : WordTrace (prefixWord ++ tailWord_4573629) baseStart_4573629 baseEnd_4573629 := by
    simpa [prefixWord, tailWord_4573629, baseEnd_4573629] using wordTrace_append hprefix tailTrace_4573629
  have hstable : (prefixWord ++ tailWord_4573629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573629).length < 2 ^ (prefixWord ++ tailWord_4573629).sum := by decide
  have hdescent : baseEnd_4573629 < baseStart_4573629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573632 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 5]
def baseStart_4573632 : Nat := 118140960795 + 4573632 * 2 ^ 59
def prefixEnd_4573632 : Nat := 4983230072969 + 3 ^ 40 * 4573632 * 2
def baseEnd_4573632 : Nat := 2348471552784354877466255

theorem tailTrace_4573632 : CollatzResearch.WordTrace tailWord_4573632 prefixEnd_4573632 2348471552784354877466255 := by
  unfold tailWord_4573632
  simp only [CollatzResearch.WordTrace]
  refine ⟨83407031683259926501517575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111209375577679902002023433 83407031683259926501517575)
  ·
    refine ⟨125110547524889889752276363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83407031683259926501517575 125110547524889889752276363)
    ·
      refine ⟨187665821287334834628414545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125110547524889889752276363 187665821287334834628414545)
      ·
        refine ⟨140749365965501125971310909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187665821287334834628414545 140749365965501125971310909)
        ·
          refine ⟨52781012237062922239241591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140749365965501125971310909 52781012237062922239241591)
          ·
            refine ⟨79171518355594383358862387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52781012237062922239241591 79171518355594383358862387)
            ·
              refine ⟨118757277533391575038293581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79171518355594383358862387 118757277533391575038293581)
              ·
                refine ⟨44533979075021840639360093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118757277533391575038293581 44533979075021840639360093)
                ·
                  refine ⟨16700242153133190239760035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44533979075021840639360093 16700242153133190239760035)
                  ·
                    refine ⟨25050363229699785359640053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16700242153133190239760035 25050363229699785359640053)
                    ·
                      refine ⟨2348471552784354877466255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25050363229699785359640053 2348471552784354877466255)
                      ·
                        rfl

theorem cell23_4573632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_4573632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573632 prefixEnd_4573632 := by exact prefixLift 4573632
  have htrace : WordTrace (prefixWord ++ tailWord_4573632) baseStart_4573632 baseEnd_4573632 := by
    simpa [prefixWord, tailWord_4573632, baseEnd_4573632] using wordTrace_append hprefix tailTrace_4573632
  have hstable : (prefixWord ++ tailWord_4573632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573632).length < 2 ^ (prefixWord ++ tailWord_4573632).sum := by decide
  have hdescent : baseEnd_4573632 < baseStart_4573632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573639 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 1, 6]
def baseStart_4573639 : Nat := 118140960795 + 4573639 * 2 ^ 59
def prefixEnd_4573639 : Nat := 4983230072969 + 3 ^ 40 * 4573639 * 2
def baseEnd_4573639 : Nat := 782825049049645450026241

theorem tailTrace_4573639 : CollatzResearch.WordTrace tailWord_4573639 prefixEnd_4573639 782825049049645450026241 := by
  unfold tailWord_4573639
  simp only [CollatzResearch.WordTrace]
  refine ⟨166814318677494493198539971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111209545784996328799026647 166814318677494493198539971)
  ·
    refine ⟨250221478016241739797809957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166814318677494493198539971 250221478016241739797809957)
    ·
      refine ⟨46916527128045326212089367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 250221478016241739797809957 46916527128045326212089367)
      ·
        refine ⟨70374790692067989318134051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46916527128045326212089367 70374790692067989318134051)
        ·
          refine ⟨105562186038101983977201077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70374790692067989318134051 105562186038101983977201077)
          ·
            refine ⟨9896454941072060997862601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105562186038101983977201077 9896454941072060997862601)
            ·
              refine ⟨7422341205804045748396951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9896454941072060997862601 7422341205804045748396951)
              ·
                refine ⟨11133511808706068622595427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7422341205804045748396951 11133511808706068622595427)
                ·
                  refine ⟨16700267713059102933893141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11133511808706068622595427 16700267713059102933893141)
                  ·
                    refine ⟨782825049049645450026241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16700267713059102933893141 782825049049645450026241)
                    ·
                      rfl

theorem cell23_4573639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_4573639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573639 prefixEnd_4573639 := by exact prefixLift 4573639
  have htrace : WordTrace (prefixWord ++ tailWord_4573639) baseStart_4573639 baseEnd_4573639 := by
    simpa [prefixWord, tailWord_4573639, baseEnd_4573639] using wordTrace_append hprefix tailTrace_4573639
  have hstable : (prefixWord ++ tailWord_4573639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573639).length < 2 ^ (prefixWord ++ tailWord_4573639).sum := by decide
  have hdescent : baseEnd_4573639 < baseStart_4573639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573663 : List Nat := [1, 1, 2, 3, 3, 4, 2, 1, 1, 1, 4]
def baseStart_4573663 : Nat := 118140960795 + 4573663 * 2 ^ 59
def prefixEnd_4573663 : Nat := 4983230072969 + 3 ^ 40 * 4573663 * 2
def baseEnd_4573663 : Nat := 2348487470684644256178613

theorem tailTrace_4573663 : CollatzResearch.WordTrace tailWord_4573663 prefixEnd_4573663 2348487470684644256178613 := by
  unfold tailWord_4573663
  simp only [CollatzResearch.WordTrace]
  refine ⟨166815194029407545297413643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111210129352938363531609095 166815194029407545297413643)
  ·
    refine ⟨250222791044111317946120465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166815194029407545297413643 250222791044111317946120465)
    ·
      refine ⟨187667093283083488459590349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250222791044111317946120465 187667093283083488459590349)
      ·
        refine ⟨70375159981156308172346381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187667093283083488459590349 70375159981156308172346381)
        ·
          refine ⟨26390684992933615564629893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70375159981156308172346381 26390684992933615564629893)
          ·
            refine ⟨4948253436175052918368105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26390684992933615564629893 4948253436175052918368105)
            ·
              refine ⟨3711190077131289688776079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4948253436175052918368105 3711190077131289688776079)
              ·
                refine ⟨5566785115696934533164119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3711190077131289688776079 5566785115696934533164119)
                ·
                  refine ⟨8350177673545401799746179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5566785115696934533164119 8350177673545401799746179)
                  ·
                    refine ⟨12525266510318102699619269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8350177673545401799746179 12525266510318102699619269)
                    ·
                      refine ⟨2348487470684644256178613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12525266510318102699619269 2348487470684644256178613)
                      ·
                        rfl

theorem cell23_4573663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_4573663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573663 prefixEnd_4573663 := by exact prefixLift 4573663
  have htrace : WordTrace (prefixWord ++ tailWord_4573663) baseStart_4573663 baseEnd_4573663 := by
    simpa [prefixWord, tailWord_4573663, baseEnd_4573663] using wordTrace_append hprefix tailTrace_4573663
  have hstable : (prefixWord ++ tailWord_4573663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573663).length < 2 ^ (prefixWord ++ tailWord_4573663).sum := by decide
  have hdescent : baseEnd_4573663 < baseStart_4573663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573669 : List Nat := [1, 3, 1, 5, 2, 1, 10]
def baseStart_4573669 : Nat := 118140960795 + 4573669 * 2 ^ 59
def prefixEnd_4573669 : Nat := 4983230072969 + 3 ^ 40 * 4573669 * 2
def baseEnd_4573669 : Nat := 28993710513192237440785

theorem tailTrace_4573669 : CollatzResearch.WordTrace tailWord_4573669 prefixEnd_4573669 28993710513192237440785 := by
  unfold tailWord_4573669
  simp only [CollatzResearch.WordTrace]
  refine ⟨166815412867385808322132061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111210275244923872214754707 166815412867385808322132061)
  ·
    refine ⟨62555779825269678120799523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166815412867385808322132061 62555779825269678120799523)
    ·
      refine ⟨93833669737904517181199285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62555779825269678120799523 93833669737904517181199285)
      ·
        refine ⟨8796906537928548485737433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93833669737904517181199285 8796906537928548485737433)
        ·
          refine ⟨6597679903446411364303075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8796906537928548485737433 6597679903446411364303075)
          ·
            refine ⟨9896519855169617046454613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6597679903446411364303075 9896519855169617046454613)
            ·
              refine ⟨28993710513192237440785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9896519855169617046454613 28993710513192237440785)
              ·
                rfl

theorem cell23_4573669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 10].length) (baseStart_4573669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573669 prefixEnd_4573669 := by exact prefixLift 4573669
  have htrace : WordTrace (prefixWord ++ tailWord_4573669) baseStart_4573669 baseEnd_4573669 := by
    simpa [prefixWord, tailWord_4573669, baseEnd_4573669] using wordTrace_append hprefix tailTrace_4573669
  have hstable : (prefixWord ++ tailWord_4573669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573669).length < 2 ^ (prefixWord ++ tailWord_4573669).sum := by decide
  have hdescent : baseEnd_4573669 < baseStart_4573669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573703 : List Nat := [1, 1, 4, 3, 4, 1, 2, 7]
def baseStart_4573703 : Nat := 118140960795 + 4573703 * 2 ^ 59
def prefixEnd_4573703 : Nat := 4983230072969 + 3 ^ 40 * 4573703 * 2
def baseEnd_4573703 : Nat := 86981778144845337025127

theorem tailTrace_4573703 : CollatzResearch.WordTrace tailWord_4573703 prefixEnd_4573703 86981778144845337025127 := by
  unfold tailWord_4573703
  simp only [CollatzResearch.WordTrace]
  refine ⟨166816652949262632128869763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111211101966175088085913175 166816652949262632128869763)
  ·
    refine ⟨250224979423893948193304645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166816652949262632128869763 250224979423893948193304645)
    ·
      refine ⟨46917183641980115286244621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 250224979423893948193304645 46917183641980115286244621)
      ·
        refine ⟨17593943865742543232341733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46917183641980115286244621 17593943865742543232341733)
        ·
          refine ⟨3298864474826726856064075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17593943865742543232341733 3298864474826726856064075)
          ·
            refine ⟨4948296712240090284096113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3298864474826726856064075 4948296712240090284096113)
            ·
              refine ⟨3711222534180067713072085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4948296712240090284096113 3711222534180067713072085)
              ·
                refine ⟨86981778144845337025127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3711222534180067713072085 86981778144845337025127)
                ·
                  rfl

theorem cell23_4573703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 7].length) (baseStart_4573703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573703 prefixEnd_4573703 := by exact prefixLift 4573703
  have htrace : WordTrace (prefixWord ++ tailWord_4573703) baseStart_4573703 baseEnd_4573703 := by
    simpa [prefixWord, tailWord_4573703, baseEnd_4573703] using wordTrace_append hprefix tailTrace_4573703
  have hstable : (prefixWord ++ tailWord_4573703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573703).length < 2 ^ (prefixWord ++ tailWord_4573703).sum := by decide
  have hdescent : baseEnd_4573703 < baseStart_4573703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573741 : List Nat := [1, 5, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_4573741 : Nat := 118140960795 + 4573741 * 2 ^ 59
def prefixEnd_4573741 : Nat := 4983230072969 + 3 ^ 40 * 4573741 * 2
def baseEnd_4573741 : Nat := 782842507391898317001085

theorem tailTrace_4573741 : CollatzResearch.WordTrace tailWord_4573741 prefixEnd_4573741 782842507391898317001085 := by
  unfold tailWord_4573741
  simp only [CollatzResearch.WordTrace]
  refine ⟨166818038923124964618753077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111212025948749976412502051 166818038923124964618753077)
  ·
    refine ⟨15639191149042965433008101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166818038923124964618753077 15639191149042965433008101)
    ·
      refine ⟨2932348340445556018689019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15639191149042965433008101 2932348340445556018689019)
      ·
        refine ⟨4398522510668334028033529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2932348340445556018689019 4398522510668334028033529)
        ·
          refine ⟨3298891883001250521025147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4398522510668334028033529 3298891883001250521025147)
          ·
            refine ⟨4948337824501875781537721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3298891883001250521025147 4948337824501875781537721)
            ·
              refine ⟨3711253368376406836153291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4948337824501875781537721 3711253368376406836153291)
              ·
                refine ⟨5566880052564610254229937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3711253368376406836153291 5566880052564610254229937)
                ·
                  refine ⟨4175160039423457690672453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5566880052564610254229937 4175160039423457690672453)
                  ·
                    refine ⟨782842507391898317001085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4175160039423457690672453 782842507391898317001085)
                    ·
                      rfl

theorem cell23_4573741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_4573741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573741 prefixEnd_4573741 := by exact prefixLift 4573741
  have htrace : WordTrace (prefixWord ++ tailWord_4573741) baseStart_4573741 baseEnd_4573741 := by
    simpa [prefixWord, tailWord_4573741, baseEnd_4573741] using wordTrace_append hprefix tailTrace_4573741
  have hstable : (prefixWord ++ tailWord_4573741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573741).length < 2 ^ (prefixWord ++ tailWord_4573741).sum := by decide
  have hdescent : baseEnd_4573741 < baseStart_4573741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573749 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_4573749 : Nat := 118140960795 + 4573749 * 2 ^ 59
def prefixEnd_4573749 : Nat := 4983230072969 + 3 ^ 40 * 4573749 * 2
def baseEnd_4573749 : Nat := 2348531630020930919703217

theorem tailTrace_4573749 : CollatzResearch.WordTrace tailWord_4573749 prefixEnd_4573749 2348531630020930919703217 := by
  unfold tailWord_4573749
  simp only [CollatzResearch.WordTrace]
  refine ⟨166818330707095981985044301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111212220471397321323362867 166818330707095981985044301)
  ·
    refine ⟨62556874015160993244391613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166818330707095981985044301 62556874015160993244391613)
    ·
      refine ⟨23458827755685372466646855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62556874015160993244391613 23458827755685372466646855)
      ·
        refine ⟨35188241633528058699970283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23458827755685372466646855 35188241633528058699970283)
        ·
          refine ⟨52782362450292088049955425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35188241633528058699970283 52782362450292088049955425)
          ·
            refine ⟨39586771837719066037466569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52782362450292088049955425 39586771837719066037466569)
            ·
              refine ⟨29690078878289299528099927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39586771837719066037466569 29690078878289299528099927)
              ·
                refine ⟨44535118317433949292149891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29690078878289299528099927 44535118317433949292149891)
                ·
                  refine ⟨66802677476150923938224837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44535118317433949292149891 66802677476150923938224837)
                  ·
                    refine ⟨12525502026778298238417157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66802677476150923938224837 12525502026778298238417157)
                    ·
                      refine ⟨2348531630020930919703217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12525502026778298238417157 2348531630020930919703217)
                      ·
                        rfl

theorem cell23_4573749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_4573749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573749 prefixEnd_4573749 := by exact prefixLift 4573749
  have htrace : WordTrace (prefixWord ++ tailWord_4573749) baseStart_4573749 baseEnd_4573749 := by
    simpa [prefixWord, tailWord_4573749, baseEnd_4573749] using wordTrace_append hprefix tailTrace_4573749
  have hstable : (prefixWord ++ tailWord_4573749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573749).length < 2 ^ (prefixWord ++ tailWord_4573749).sum := by decide
  have hdescent : baseEnd_4573749 < baseStart_4573749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573769 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 6, 3, 3]
def baseStart_4573769 : Nat := 118140960795 + 4573769 * 2 ^ 59
def prefixEnd_4573769 : Nat := 4983230072969 + 3 ^ 40 * 4573769 * 2
def baseEnd_4573769 : Nat := 2348541899634020841453125

theorem tailTrace_4573769 : CollatzResearch.WordTrace tailWord_4573769 prefixEnd_4573769 2348541899634020841453125 := by
  unfold tailWord_4573769
  simp only [CollatzResearch.WordTrace]
  refine ⟨166819060167023525400772361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111212706778015683600514907 166819060167023525400772361)
  ·
    refine ⟨125114295125267644050579271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166819060167023525400772361 125114295125267644050579271)
    ·
      refine ⟨187671442687901466075868907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125114295125267644050579271 187671442687901466075868907)
      ·
        refine ⟨281507164031852199113803361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187671442687901466075868907 281507164031852199113803361)
        ·
          refine ⟨211130373023889149335352521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281507164031852199113803361 211130373023889149335352521)
          ·
            refine ⟨158347779767916862001514391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211130373023889149335352521 158347779767916862001514391)
            ·
              refine ⟨237521669651875293002271587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158347779767916862001514391 237521669651875293002271587)
              ·
                refine ⟨356282504477812939503407381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237521669651875293002271587 356282504477812939503407381)
                ·
                  refine ⟨16700742397397481539222221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 356282504477812939503407381 16700742397397481539222221)
                  ·
                    refine ⟨6262778399024055577208333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16700742397397481539222221 6262778399024055577208333)
                    ·
                      refine ⟨2348541899634020841453125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6262778399024055577208333 2348541899634020841453125)
                      ·
                        rfl

theorem cell23_4573769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 3, 3].length) (baseStart_4573769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573769 prefixEnd_4573769 := by exact prefixLift 4573769
  have htrace : WordTrace (prefixWord ++ tailWord_4573769) baseStart_4573769 baseEnd_4573769 := by
    simpa [prefixWord, tailWord_4573769, baseEnd_4573769] using wordTrace_append hprefix tailTrace_4573769
  have hstable : (prefixWord ++ tailWord_4573769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573769).length < 2 ^ (prefixWord ++ tailWord_4573769).sum := by decide
  have hdescent : baseEnd_4573769 < baseStart_4573769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573793 : List Nat := [1, 2, 3, 1, 1, 4, 4, 2, 5]
def baseStart_4573793 : Nat := 118140960795 + 4573793 * 2 ^ 59
def prefixEnd_4573793 : Nat := 4983230072969 + 3 ^ 40 * 4573793 * 2
def baseEnd_4573793 : Nat := 260950469241080971950335

theorem tailTrace_4573793 : CollatzResearch.WordTrace tailWord_4573793 prefixEnd_4573793 260950469241080971950335 := by
  unfold tailWord_4573793
  simp only [CollatzResearch.WordTrace]
  refine ⟨166819935518936577499646033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111213290345957718333097355 166819935518936577499646033)
  ·
    refine ⟨125114951639202433124734525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166819935518936577499646033 125114951639202433124734525)
    ·
      refine ⟨46918106864700912421775447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125114951639202433124734525 46918106864700912421775447)
      ·
        refine ⟨70377160297051368632663171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46918106864700912421775447 70377160297051368632663171)
        ·
          refine ⟨105565740445577052948994757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70377160297051368632663171 105565740445577052948994757)
          ·
            refine ⟨19793576333545697427936517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105565740445577052948994757 19793576333545697427936517)
            ·
              refine ⟨3711295562539818267738097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19793576333545697427936517 3711295562539818267738097)
              ·
                refine ⟨2783471671904863700803573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3711295562539818267738097 2783471671904863700803573)
                ·
                  refine ⟨260950469241080971950335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2783471671904863700803573 260950469241080971950335)
                  ·
                    rfl

theorem cell23_4573793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 5].length) (baseStart_4573793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573793 prefixEnd_4573793 := by exact prefixLift 4573793
  have htrace : WordTrace (prefixWord ++ tailWord_4573793) baseStart_4573793 baseEnd_4573793 := by
    simpa [prefixWord, tailWord_4573793, baseEnd_4573793] using wordTrace_append hprefix tailTrace_4573793
  have hstable : (prefixWord ++ tailWord_4573793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573793).length < 2 ^ (prefixWord ++ tailWord_4573793).sum := by decide
  have hdescent : baseEnd_4573793 < baseStart_4573793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573796 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2]
def baseStart_4573796 : Nat := 118140960795 + 4573796 * 2 ^ 59
def prefixEnd_4573796 : Nat := 4983230072969 + 3 ^ 40 * 4573796 * 2
def baseEnd_4573796 : Nat := 2348555763611692235815501

theorem tailTrace_4573796 : CollatzResearch.WordTrace tailWord_4573796 prefixEnd_4573796 2348555763611692235815501 := by
  unfold tailWord_4573796
  simp only [CollatzResearch.WordTrace]
  refine ⟨83410022468962854506002621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111213363291950472674670161 83410022468962854506002621)
  ·
    refine ⟨31278758425861070439750983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83410022468962854506002621 31278758425861070439750983)
    ·
      refine ⟨46918137638791605659626475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31278758425861070439750983 46918137638791605659626475)
      ·
        refine ⟨70377206458187408489439713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46918137638791605659626475 70377206458187408489439713)
        ·
          refine ⟨52782904843640556367079785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70377206458187408489439713 52782904843640556367079785)
          ·
            refine ⟨39587178632730417275309839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52782904843640556367079785 39587178632730417275309839)
            ·
              refine ⟨59380767949095625912964759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39587178632730417275309839 59380767949095625912964759)
              ·
                refine ⟨89071151923643438869447139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59380767949095625912964759 89071151923643438869447139)
                ·
                  refine ⟨133606727885465158304170709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89071151923643438869447139 133606727885465158304170709)
                  ·
                    refine ⟨3131407684815589647754001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 133606727885465158304170709 3131407684815589647754001)
                    ·
                      refine ⟨2348555763611692235815501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3131407684815589647754001 2348555763611692235815501)
                      ·
                        rfl

theorem cell23_4573796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_4573796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573796 prefixEnd_4573796 := by exact prefixLift 4573796
  have htrace : WordTrace (prefixWord ++ tailWord_4573796) baseStart_4573796 baseEnd_4573796 := by
    simpa [prefixWord, tailWord_4573796, baseEnd_4573796] using wordTrace_append hprefix tailTrace_4573796
  have hstable : (prefixWord ++ tailWord_4573796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573796).length < 2 ^ (prefixWord ++ tailWord_4573796).sum := by decide
  have hdescent : baseEnd_4573796 < baseStart_4573796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573849 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 8]
def baseStart_4573849 : Nat := 118140960795 + 4573849 * 2 ^ 59
def prefixEnd_4573849 : Nat := 4983230072969 + 3 ^ 40 * 4573849 * 2
def baseEnd_4573849 : Nat := 260953664231820058716973

theorem tailTrace_4573849 : CollatzResearch.WordTrace tailWord_4573849 prefixEnd_4573849 260953664231820058716973 := by
  unfold tailWord_4573849
  simp only [CollatzResearch.WordTrace]
  refine ⟨166821978006733699063684601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111214652004489132709123067 166821978006733699063684601)
  ·
    refine ⟨125116483505050274297763451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166821978006733699063684601 125116483505050274297763451)
    ·
      refine ⟨187674725257575411446645177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125116483505050274297763451 187674725257575411446645177)
      ·
        refine ⟨140756043943181558584983883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187674725257575411446645177 140756043943181558584983883)
        ·
          refine ⟨211134065914772337877475825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140756043943181558584983883 211134065914772337877475825)
          ·
            refine ⟨158350549436079253408106869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211134065914772337877475825 158350549436079253408106869)
            ·
              refine ⟨14845364009632430007010019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158350549436079253408106869 14845364009632430007010019)
              ·
                refine ⟨22268046014448645010515029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14845364009632430007010019 22268046014448645010515029)
                ·
                  refine ⟨260953664231820058716973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22268046014448645010515029 260953664231820058716973)
                  ·
                    rfl

theorem cell23_4573849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 8].length) (baseStart_4573849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573849 prefixEnd_4573849 := by exact prefixLift 4573849
  have htrace : WordTrace (prefixWord ++ tailWord_4573849) baseStart_4573849 baseEnd_4573849 := by
    simpa [prefixWord, tailWord_4573849, baseEnd_4573849] using wordTrace_append hprefix tailTrace_4573849
  have hstable : (prefixWord ++ tailWord_4573849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573849).length < 2 ^ (prefixWord ++ tailWord_4573849).sum := by decide
  have hdescent : baseEnd_4573849 < baseStart_4573849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573870 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_4573870 : Nat := 118140960795 + 4573870 * 2 ^ 59
def prefixEnd_4573870 : Nat := 4983230072969 + 3 ^ 40 * 4573870 * 2
def baseEnd_4573870 : Nat := 782864587060041648763387

theorem tailTrace_4573870 : CollatzResearch.WordTrace tailWord_4573870 prefixEnd_4573870 782864587060041648763387 := by
  unfold tailWord_4573870
  simp only [CollatzResearch.WordTrace]
  refine ⟨20852842992457202456274883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111215162626438413100132709 20852842992457202456274883)
  ·
    refine ⟨31279264488685803684412325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20852842992457202456274883 31279264488685803684412325)
    ·
      refine ⟨5864862091628588190827311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31279264488685803684412325 5864862091628588190827311)
      ·
        refine ⟨8797293137442882286240967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5864862091628588190827311 8797293137442882286240967)
        ·
          refine ⟨13195939706164323429361451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8797293137442882286240967 13195939706164323429361451)
          ·
            refine ⟨19793909559246485144042177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13195939706164323429361451 19793909559246485144042177)
            ·
              refine ⟨14845432169434863858031633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19793909559246485144042177 14845432169434863858031633)
              ·
                refine ⟨11134074127076147893523725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14845432169434863858031633 11134074127076147893523725)
                ·
                  refine ⟨4175277797653555460071397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11134074127076147893523725 4175277797653555460071397)
                  ·
                    refine ⟨782864587060041648763387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4175277797653555460071397 782864587060041648763387)
                    ·
                      rfl

theorem cell23_4573870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_4573870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573870 prefixEnd_4573870 := by exact prefixLift 4573870
  have htrace : WordTrace (prefixWord ++ tailWord_4573870) baseStart_4573870 baseEnd_4573870 := by
    simpa [prefixWord, tailWord_4573870, baseEnd_4573870] using wordTrace_append hprefix tailTrace_4573870
  have hstable : (prefixWord ++ tailWord_4573870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573870).length < 2 ^ (prefixWord ++ tailWord_4573870).sum := by decide
  have hdescent : baseEnd_4573870 < baseStart_4573870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573933 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_4573933 : Nat := 118140960795 + 4573933 * 2 ^ 59
def prefixEnd_4573933 : Nat := 4983230072969 + 3 ^ 40 * 4573933 * 2
def baseEnd_4573933 : Nat := 2348626110461358199802371

theorem tailTrace_4573933 : CollatzResearch.WordTrace tailWord_4573933 prefixEnd_4573933 2348626110461358199802371 := by
  unfold tailWord_4573933
  simp only [CollatzResearch.WordTrace]
  refine ⟨166825041738429381409742453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111216694492286254273161635 166825041738429381409742453)
  ·
    refine ⟨15639847662977754507163355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166825041738429381409742453 15639847662977754507163355)
    ·
      refine ⟨23459771494466631760745033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15639847662977754507163355 23459771494466631760745033)
      ·
        refine ⟨17594828620849973820558775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23459771494466631760745033 17594828620849973820558775)
        ·
          refine ⟨26392242931274960730838163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17594828620849973820558775 26392242931274960730838163)
          ·
            refine ⟨39588364396912441096257245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26392242931274960730838163 39588364396912441096257245)
            ·
              refine ⟨14845636648842165411096467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39588364396912441096257245 14845636648842165411096467)
              ·
                refine ⟨22268454973263248116644701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14845636648842165411096467 22268454973263248116644701)
                ·
                  refine ⟨8350670614973718043741763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22268454973263248116644701 8350670614973718043741763)
                  ·
                    refine ⟨12526005922460577065612645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8350670614973718043741763 12526005922460577065612645)
                    ·
                      refine ⟨2348626110461358199802371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12526005922460577065612645 2348626110461358199802371)
                      ·
                        rfl

theorem cell23_4573933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_4573933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573933 prefixEnd_4573933 := by exact prefixLift 4573933
  have htrace : WordTrace (prefixWord ++ tailWord_4573933) baseStart_4573933 baseEnd_4573933 := by
    simpa [prefixWord, tailWord_4573933, baseEnd_4573933] using wordTrace_append hprefix tailTrace_4573933
  have hstable : (prefixWord ++ tailWord_4573933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573933).length < 2 ^ (prefixWord ++ tailWord_4573933).sum := by decide
  have hdescent : baseEnd_4573933 < baseStart_4573933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573946 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_4573946 : Nat := 118140960795 + 4573946 * 2 ^ 59
def prefixEnd_4573946 : Nat := 4983230072969 + 3 ^ 40 * 4573946 * 2
def baseEnd_4573946 : Nat := 2348632785709866648939811

theorem tailTrace_4573946 : CollatzResearch.WordTrace tailWord_4573946 prefixEnd_4573946 2348632785709866648939811 := by
  unfold tailWord_4573946
  simp only [CollatzResearch.WordTrace]
  refine ⟨41706378971845571157491423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111217010591588189753310461 41706378971845571157491423)
  ·
    refine ⟨62559568457768356736237135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41706378971845571157491423 62559568457768356736237135)
    ·
      refine ⟨93839352686652535104355703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62559568457768356736237135 93839352686652535104355703)
      ·
        refine ⟨140759029029978802656533555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93839352686652535104355703 140759029029978802656533555)
        ·
          refine ⟨211138543544968203984800333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140759029029978802656533555 211138543544968203984800333)
          ·
            refine ⟨79176953829363076494300125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211138543544968203984800333 79176953829363076494300125)
            ·
              refine ⟨29691357686011153685362547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79176953829363076494300125 29691357686011153685362547)
              ·
                refine ⟨44537036529016730528043821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29691357686011153685362547 44537036529016730528043821)
                ·
                  refine ⟨16701388698381273948016433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44537036529016730528043821 16701388698381273948016433)
                  ·
                    refine ⟨12526041523785955461012325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16701388698381273948016433 12526041523785955461012325)
                    ·
                      refine ⟨2348632785709866648939811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12526041523785955461012325 2348632785709866648939811)
                      ·
                        rfl

theorem cell23_4573946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_4573946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573946 prefixEnd_4573946 := by exact prefixLift 4573946
  have htrace : WordTrace (prefixWord ++ tailWord_4573946) baseStart_4573946 baseEnd_4573946 := by
    simpa [prefixWord, tailWord_4573946, baseEnd_4573946] using wordTrace_append hprefix tailTrace_4573946
  have hstable : (prefixWord ++ tailWord_4573946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573946).length < 2 ^ (prefixWord ++ tailWord_4573946).sum := by decide
  have hdescent : baseEnd_4573946 < baseStart_4573946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573960 : List Nat := [2, 1, 3, 2, 2, 3, 2, 2, 2, 4]
def baseStart_4573960 : Nat := 118140960795 + 4573960 * 2 ^ 59
def prefixEnd_4573960 : Nat := 4983230072969 + 3 ^ 40 * 4573960 * 2
def baseEnd_4573960 : Nat := 782879991479676531388249

theorem tailTrace_4573960 : CollatzResearch.WordTrace tailWord_4573960 prefixEnd_4573960 782879991479676531388249 := by
  unfold tailWord_4573960
  simp only [CollatzResearch.WordTrace]
  refine ⟨83413013254665782510487667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111217351006221043347316889 83413013254665782510487667)
  ·
    refine ⟨125119519881998673765731501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83413013254665782510487667 125119519881998673765731501)
    ·
      refine ⟨46919819955749502662149313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125119519881998673765731501 46919819955749502662149313)
      ·
        refine ⟨35189864966812126996611985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46919819955749502662149313 35189864966812126996611985)
        ·
          refine ⟨26392398725109095247458989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35189864966812126996611985 26392398725109095247458989)
          ·
            refine ⟨9897149521915910717797121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26392398725109095247458989 9897149521915910717797121)
            ·
              refine ⟨7422862141436933038347841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9897149521915910717797121 7422862141436933038347841)
              ·
                refine ⟨5567146606077699778760881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7422862141436933038347841 5567146606077699778760881)
                ·
                  refine ⟨4175359954558274834070661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5567146606077699778760881 4175359954558274834070661)
                  ·
                    refine ⟨782879991479676531388249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4175359954558274834070661 782879991479676531388249)
                    ·
                      rfl

theorem cell23_4573960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_4573960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573960 prefixEnd_4573960 := by exact prefixLift 4573960
  have htrace : WordTrace (prefixWord ++ tailWord_4573960) baseStart_4573960 baseEnd_4573960 := by
    simpa [prefixWord, tailWord_4573960, baseEnd_4573960] using wordTrace_append hprefix tailTrace_4573960
  have hstable : (prefixWord ++ tailWord_4573960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573960).length < 2 ^ (prefixWord ++ tailWord_4573960).sum := by decide
  have hdescent : baseEnd_4573960 < baseStart_4573960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573967 : List Nat := [1, 1, 2, 1, 1, 1, 7, 4, 1, 2, 2]
def baseStart_4573967 : Nat := 118140960795 + 4573967 * 2 ^ 59
def prefixEnd_4573967 : Nat := 4983230072969 + 3 ^ 40 * 4573967 * 2
def baseEnd_4573967 : Nat := 2348643568803611066777215

theorem tailTrace_4573967 : CollatzResearch.WordTrace tailWord_4573967 prefixEnd_4573967 2348643568803611066777215 := by
  unfold tailWord_4573967
  simp only [CollatzResearch.WordTrace]
  refine ⟨166826281820306205216480155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111217521213537470144320103 166826281820306205216480155)
  ·
    refine ⟨250239422730459307824720233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166826281820306205216480155 250239422730459307824720233)
    ·
      refine ⟨187679567047844480868540175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250239422730459307824720233 187679567047844480868540175)
      ·
        refine ⟨281519350571766721302810263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187679567047844480868540175 281519350571766721302810263)
        ·
          refine ⟨422279025857650081954215395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281519350571766721302810263 422279025857650081954215395)
          ·
            refine ⟨633418538786475122931323093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422279025857650081954215395 633418538786475122931323093)
            ·
              refine ⟨14845747002808010693702885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 633418538786475122931323093 14845747002808010693702885)
              ·
                refine ⟨2783577563026502005069291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14845747002808010693702885 2783577563026502005069291)
                ·
                  refine ⟨4175366344539753007603937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2783577563026502005069291 4175366344539753007603937)
                  ·
                    refine ⟨3131524758404814755702953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4175366344539753007603937 3131524758404814755702953)
                    ·
                      refine ⟨2348643568803611066777215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3131524758404814755702953 2348643568803611066777215)
                      ·
                        rfl

theorem cell23_4573967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 1, 2, 2].length) (baseStart_4573967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573967 prefixEnd_4573967 := by exact prefixLift 4573967
  have htrace : WordTrace (prefixWord ++ tailWord_4573967) baseStart_4573967 baseEnd_4573967 := by
    simpa [prefixWord, tailWord_4573967, baseEnd_4573967] using wordTrace_append hprefix tailTrace_4573967
  have hstable : (prefixWord ++ tailWord_4573967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573967).length < 2 ^ (prefixWord ++ tailWord_4573967).sum := by decide
  have hdescent : baseEnd_4573967 < baseStart_4573967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573983 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 3]
def baseStart_4573983 : Nat := 118140960795 + 4573983 * 2 ^ 59
def prefixEnd_4573983 : Nat := 4983230072969 + 3 ^ 40 * 4573983 * 2
def baseEnd_4573983 : Nat := 2348651784494083004177141

theorem tailTrace_4573983 : CollatzResearch.WordTrace tailWord_4573983 prefixEnd_4573983 2348651784494083004177141 := by
  unfold tailWord_4573983
  simp only [CollatzResearch.WordTrace]
  refine ⟨166826865388248239949062603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111217910258832159966041735 166826865388248239949062603)
  ·
    refine ⟨250240298082372359923593905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166826865388248239949062603 250240298082372359923593905)
    ·
      refine ⟨187680223561779269942695429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250240298082372359923593905 187680223561779269942695429)
      ·
        refine ⟨35190041917833613114255393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187680223561779269942695429 35190041917833613114255393)
        ·
          refine ⟨26392531438375209835691545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35190041917833613114255393 26392531438375209835691545)
          ·
            refine ⟨19794398578781407376768659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26392531438375209835691545 19794398578781407376768659)
            ·
              refine ⟨29691597868172111065152989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19794398578781407376768659 29691597868172111065152989)
              ·
                refine ⟨11134349200564541649432371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29691597868172111065152989 11134349200564541649432371)
                ·
                  refine ⟨16701523800846812474148557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11134349200564541649432371 16701523800846812474148557)
                  ·
                    refine ⟨6263071425317554677805709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16701523800846812474148557 6263071425317554677805709)
                    ·
                      refine ⟨2348651784494083004177141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6263071425317554677805709 2348651784494083004177141)
                      ·
                        rfl

theorem cell23_4573983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_4573983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573983 prefixEnd_4573983 := by exact prefixLift 4573983
  have htrace : WordTrace (prefixWord ++ tailWord_4573983) baseStart_4573983 baseEnd_4573983 := by
    simpa [prefixWord, tailWord_4573983, baseEnd_4573983] using wordTrace_append hprefix tailTrace_4573983
  have hstable : (prefixWord ++ tailWord_4573983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573983).length < 2 ^ (prefixWord ++ tailWord_4573983).sum := by decide
  have hdescent : baseEnd_4573983 < baseStart_4573983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4573996 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_4573996 : Nat := 118140960795 + 4573996 * 2 ^ 59
def prefixEnd_4573996 : Nat := 4983230072969 + 3 ^ 40 * 4573996 * 2
def baseEnd_4573996 : Nat := 2348658459742591453314581

theorem tailTrace_4573996 : CollatzResearch.WordTrace tailWord_4573996 prefixEnd_4573996 2348658459742591453314581 := by
  unfold tailWord_4573996
  simp only [CollatzResearch.WordTrace]
  refine ⟨83413669768600571584642921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111218226358134095446190561 83413669768600571584642921)
  ·
    refine ⟨62560252326450428688482191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83413669768600571584642921 62560252326450428688482191)
    ·
      refine ⟨93840378489675643032723287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62560252326450428688482191 93840378489675643032723287)
      ·
        refine ⟨140760567734513464549084931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93840378489675643032723287 140760567734513464549084931)
        ·
          refine ⟨211140851601770196823627397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140760567734513464549084931 211140851601770196823627397)
          ·
            refine ⟨39588909675331911904430137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 211140851601770196823627397 39588909675331911904430137)
            ·
              refine ⟨29691682256498933928322603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39588909675331911904430137 29691682256498933928322603)
              ·
                refine ⟨44537523384748400892483905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29691682256498933928322603 44537523384748400892483905)
                ·
                  refine ⟨33403142538561300669362929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44537523384748400892483905 33403142538561300669362929)
                  ·
                    refine ⟨25052356903920975502022197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33403142538561300669362929 25052356903920975502022197)
                    ·
                      refine ⟨2348658459742591453314581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25052356903920975502022197 2348658459742591453314581)
                      ·
                        rfl

theorem cell23_4573996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_4573996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4573996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4573996 prefixEnd_4573996 := by exact prefixLift 4573996
  have htrace : WordTrace (prefixWord ++ tailWord_4573996) baseStart_4573996 baseEnd_4573996 := by
    simpa [prefixWord, tailWord_4573996, baseEnd_4573996] using wordTrace_append hprefix tailTrace_4573996
  have hstable : (prefixWord ++ tailWord_4573996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4573996).length < 2 ^ (prefixWord ++ tailWord_4573996).sum := by decide
  have hdescent : baseEnd_4573996 < baseStart_4573996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4573996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574026 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_4574026 : Nat := 118140960795 + 4574026 * 2 ^ 59
def prefixEnd_4574026 : Nat := 4983230072969 + 3 ^ 40 * 4574026 * 2
def baseEnd_4574026 : Nat := 2348673864162226335939443

theorem tailTrace_4574026 : CollatzResearch.WordTrace tailWord_4574026 prefixEnd_4574026 2348673864162226335939443 := by
  unfold tailWord_4574026
  simp only [CollatzResearch.WordTrace]
  refine ⟨41707108431773114573219483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111218955818061638861918621 41707108431773114573219483)
  ·
    refine ⟨62560662647659671859829225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41707108431773114573219483 62560662647659671859829225)
    ·
      refine ⟨46920496985744753894871919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62560662647659671859829225 46920496985744753894871919)
      ·
        refine ⟨70380745478617130842307879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46920496985744753894871919 70380745478617130842307879)
        ·
          refine ⟨105571118217925696263461819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70380745478617130842307879 105571118217925696263461819)
          ·
            refine ⟨158356677326888544395192729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105571118217925696263461819 158356677326888544395192729)
            ·
              refine ⟨118767507995166408296394547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158356677326888544395192729 118767507995166408296394547)
              ·
                refine ⟨178151261992749612444591821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118767507995166408296394547 178151261992749612444591821)
                ·
                  refine ⟨66806723247281104666721933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178151261992749612444591821 66806723247281104666721933)
                  ·
                    refine ⟨25052521217730414250020725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66806723247281104666721933 25052521217730414250020725)
                    ·
                      refine ⟨2348673864162226335939443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25052521217730414250020725 2348673864162226335939443)
                      ·
                        rfl

theorem cell23_4574026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_4574026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574026 prefixEnd_4574026 := by exact prefixLift 4574026
  have htrace : WordTrace (prefixWord ++ tailWord_4574026) baseStart_4574026 baseEnd_4574026 := by
    simpa [prefixWord, tailWord_4574026, baseEnd_4574026] using wordTrace_append hprefix tailTrace_4574026
  have hstable : (prefixWord ++ tailWord_4574026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574026).length < 2 ^ (prefixWord ++ tailWord_4574026).sum := by decide
  have hdescent : baseEnd_4574026 < baseStart_4574026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574044 : List Nat := [2, 2, 4, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_4574044 : Nat := 118140960795 + 4574044 * 2 ^ 59
def prefixEnd_4574044 : Nat := 4983230072969 + 3 ^ 40 * 4574044 * 2
def baseEnd_4574044 : Nat := 2348683106814007265514361

theorem tailTrace_4574044 : CollatzResearch.WordTrace tailWord_4574044 prefixEnd_4574044 2348683106814007265514361 := by
  unfold tailWord_4574044
  simp only [CollatzResearch.WordTrace]
  refine ⟨83414545120513623683516593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111219393494018164911355457 83414545120513623683516593)
  ·
    refine ⟨62560908840385217762637445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83414545120513623683516593 62560908840385217762637445)
    ·
      refine ⟨11730170407572228330494521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62560908840385217762637445 11730170407572228330494521)
      ·
        refine ⟨8797627805679171247870891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11730170407572228330494521 8797627805679171247870891)
        ·
          refine ⟨13196441708518756871806337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8797627805679171247870891 13196441708518756871806337)
          ·
            refine ⟨9897331281389067653854753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13196441708518756871806337 9897331281389067653854753)
            ·
              refine ⟨7422998461041800740391065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9897331281389067653854753 7422998461041800740391065)
              ·
                refine ⟨5567248845781350555293299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7422998461041800740391065 5567248845781350555293299)
                ·
                  refine ⟨8350873268672025832939949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5567248845781350555293299 8350873268672025832939949)
                  ·
                    refine ⟨3131577475752009687352481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8350873268672025832939949 3131577475752009687352481)
                    ·
                      refine ⟨2348683106814007265514361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3131577475752009687352481 2348683106814007265514361)
                      ·
                        rfl

theorem cell23_4574044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_4574044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574044 prefixEnd_4574044 := by exact prefixLift 4574044
  have htrace : WordTrace (prefixWord ++ tailWord_4574044) baseStart_4574044 baseEnd_4574044 := by
    simpa [prefixWord, tailWord_4574044, baseEnd_4574044] using wordTrace_append hprefix tailTrace_4574044
  have hstable : (prefixWord ++ tailWord_4574044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574044).length < 2 ^ (prefixWord ++ tailWord_4574044).sum := by decide
  have hdescent : baseEnd_4574044 < baseStart_4574044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574123 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 5, 4]
def baseStart_4574123 : Nat := 118140960795 + 4574123 * 2 ^ 59
def prefixEnd_4574123 : Nat := 4983230072969 + 3 ^ 40 * 4574123 * 2
def baseEnd_4574123 : Nat := 782907890595237485475499

theorem tailTrace_4574123 : CollatzResearch.WordTrace tailWord_4574123 prefixEnd_4574123 782907890595237485475499 := by
  unfold tailWord_4574123
  simp only [CollatzResearch.WordTrace]
  refine ⟨166831971607741043859159023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111221314405160695906106015 166831971607741043859159023)
  ·
    refine ⟨250247957411611565788738535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166831971607741043859159023 250247957411611565788738535)
    ·
      refine ⟨375371936117417348683107803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250247957411611565788738535 375371936117417348683107803)
      ·
        refine ⟨563057904176126023024661705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375371936117417348683107803 563057904176126023024661705)
        ·
          refine ⟨422293428132094517268496279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563057904176126023024661705 422293428132094517268496279)
          ·
            refine ⟨633440142198141775902744419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422293428132094517268496279 633440142198141775902744419)
            ·
              refine ⟨950160213297212663854116629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633440142198141775902744419 950160213297212663854116629)
              ·
                refine ⟨44538759998306843618161717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 950160213297212663854116629 44538759998306843618161717)
                ·
                  refine ⟨4175508749841266589202661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44538759998306843618161717 4175508749841266589202661)
                  ·
                    refine ⟨782907890595237485475499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4175508749841266589202661 782907890595237485475499)
                    ·
                      rfl

theorem cell23_4574123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 4].length) (baseStart_4574123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574123 prefixEnd_4574123 := by exact prefixLift 4574123
  have htrace : WordTrace (prefixWord ++ tailWord_4574123) baseStart_4574123 baseEnd_4574123 := by
    simpa [prefixWord, tailWord_4574123, baseEnd_4574123] using wordTrace_append hprefix tailTrace_4574123
  have hstable : (prefixWord ++ tailWord_4574123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574123).length < 2 ^ (prefixWord ++ tailWord_4574123).sum := by decide
  have hdescent : baseEnd_4574123 < baseStart_4574123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574133 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_4574133 : Nat := 118140960795 + 4574133 * 2 ^ 59
def prefixEnd_4574133 : Nat := 4983230072969 + 3 ^ 40 * 4574133 * 2
def baseEnd_4574133 : Nat := 2348728806592257417301451

theorem tailTrace_4574133 : CollatzResearch.WordTrace tailWord_4574133 prefixEnd_4574133 2348728806592257417301451 := by
  unfold tailWord_4574133
  simp only [CollatzResearch.WordTrace]
  refine ⟨166832336337704815567023053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111221557558469877044682035 166832336337704815567023053)
  ·
    refine ⟨62562126126639305837633645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166832336337704815567023053 62562126126639305837633645)
    ·
      refine ⟨23460797297489739689112617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62562126126639305837633645 23460797297489739689112617)
      ·
        refine ⟨17595597973117304766834463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23460797297489739689112617 17595597973117304766834463)
        ·
          refine ⟨26393396959675957150251695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17595597973117304766834463 26393396959675957150251695)
          ·
            refine ⟨39590095439513935725377543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26393396959675957150251695 39590095439513935725377543)
            ·
              refine ⟨59385143159270903588066315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39590095439513935725377543 59385143159270903588066315)
              ·
                refine ⟨89077714738906355382099473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59385143159270903588066315 89077714738906355382099473)
                ·
                  refine ⟨66808286054179766536574605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89077714738906355382099473 66808286054179766536574605)
                  ·
                    refine ⟨25053107270317412451215477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66808286054179766536574605 25053107270317412451215477)
                    ·
                      refine ⟨2348728806592257417301451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25053107270317412451215477 2348728806592257417301451)
                      ·
                        rfl

theorem cell23_4574133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_4574133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574133 prefixEnd_4574133 := by exact prefixLift 4574133
  have htrace : WordTrace (prefixWord ++ tailWord_4574133) baseStart_4574133 baseEnd_4574133 := by
    simpa [prefixWord, tailWord_4574133, baseEnd_4574133] using wordTrace_append hprefix tailTrace_4574133
  have hstable : (prefixWord ++ tailWord_4574133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574133).length < 2 ^ (prefixWord ++ tailWord_4574133).sum := by decide
  have hdescent : baseEnd_4574133 < baseStart_4574133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574231 : List Nat := [1, 1, 3, 5, 1, 1, 3, 3, 1, 1, 3]
def baseStart_4574231 : Nat := 118140960795 + 4574231 * 2 ^ 59
def prefixEnd_4574231 : Nat := 4983230072969 + 3 ^ 40 * 4574231 * 2
def baseEnd_4574231 : Nat := 2348779127696398033876001

theorem tailTrace_4574231 : CollatzResearch.WordTrace tailWord_4574231 prefixEnd_4574231 2348779127696398033876001 := by
  unfold tailWord_4574231
  simp only [CollatzResearch.WordTrace]
  refine ⟨166835910691349778304090547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111223940460899852202727031 166835910691349778304090547)
  ·
    refine ⟨250253866037024667456135821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166835910691349778304090547 250253866037024667456135821)
    ·
      refine ⟨93845199763884250296050933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250253866037024667456135821 93845199763884250296050933)
      ·
        refine ⟨8797987477864148465254775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93845199763884250296050933 8797987477864148465254775)
        ·
          refine ⟨13196981216796222697882163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8797987477864148465254775 13196981216796222697882163)
          ·
            refine ⟨19795471825194334046823245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13196981216796222697882163 19795471825194334046823245)
            ·
              refine ⟨7423301934447875267558717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19795471825194334046823245 7423301934447875267558717)
              ·
                refine ⟨2783738225417953225334519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7423301934447875267558717 2783738225417953225334519)
                ·
                  refine ⟨4175607338126929838001779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2783738225417953225334519 4175607338126929838001779)
                  ·
                    refine ⟨6263411007190394757002669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4175607338126929838001779 6263411007190394757002669)
                    ·
                      refine ⟨2348779127696398033876001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6263411007190394757002669 2348779127696398033876001)
                      ·
                        rfl

theorem cell23_4574231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_4574231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574231 prefixEnd_4574231 := by exact prefixLift 4574231
  have htrace : WordTrace (prefixWord ++ tailWord_4574231) baseStart_4574231 baseEnd_4574231 := by
    simpa [prefixWord, tailWord_4574231, baseEnd_4574231] using wordTrace_append hprefix tailTrace_4574231
  have hstable : (prefixWord ++ tailWord_4574231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574231).length < 2 ^ (prefixWord ++ tailWord_4574231).sum := by decide
  have hdescent : baseEnd_4574231 < baseStart_4574231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574243 : List Nat := [1, 1, 1, 4, 3, 2, 11]
def baseStart_4574243 : Nat := 118140960795 + 4574243 * 2 ^ 59
def prefixEnd_4574243 : Nat := 4983230072969 + 3 ^ 40 * 4574243 * 2
def baseEnd_4574243 : Nat := 28997349252645086258345

theorem tailTrace_4574243 : CollatzResearch.WordTrace tailWord_4574243 prefixEnd_4574243 28997349252645086258345 := by
  unfold tailWord_4574243
  simp only [CollatzResearch.WordTrace]
  refine ⟨166836348367306304353527383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111224232244870869569018255 166836348367306304353527383)
  ·
    refine ⟨250254522550959456530291075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166836348367306304353527383 250254522550959456530291075)
    ·
      refine ⟨375381783826439184795436613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250254522550959456530291075 375381783826439184795436613)
      ·
        refine ⟨70384084467457347149144365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 375381783826439184795436613 70384084467457347149144365)
        ·
          refine ⟨26394031675296505180929137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70384084467457347149144365 26394031675296505180929137)
          ·
            refine ⟨19795523756472378885696853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26394031675296505180929137 19795523756472378885696853)
            ·
              refine ⟨28997349252645086258345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19795523756472378885696853 28997349252645086258345)
              ·
                rfl

theorem cell23_4574243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 11].length) (baseStart_4574243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574243 prefixEnd_4574243 := by exact prefixLift 4574243
  have htrace : WordTrace (prefixWord ++ tailWord_4574243) baseStart_4574243 baseEnd_4574243 := by
    simpa [prefixWord, tailWord_4574243, baseEnd_4574243] using wordTrace_append hprefix tailTrace_4574243
  have hstable : (prefixWord ++ tailWord_4574243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574243).length < 2 ^ (prefixWord ++ tailWord_4574243).sum := by decide
  have hdescent : baseEnd_4574243 < baseStart_4574243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574263 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_4574263 : Nat := 118140960795 + 4574263 * 2 ^ 59
def prefixEnd_4574263 : Nat := 4983230072969 + 3 ^ 40 * 4574263 * 2
def baseEnd_4574263 : Nat := 2348795559077341908675853

theorem tailTrace_4574263 : CollatzResearch.WordTrace tailWord_4574263 prefixEnd_4574263 2348795559077341908675853 := by
  unfold tailWord_4574263
  simp only [CollatzResearch.WordTrace]
  refine ⟨166837077827233847769255443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111224718551489231846170295 166837077827233847769255443)
  ·
    refine ⟨250255616740850771653883165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166837077827233847769255443 250255616740850771653883165)
    ·
      refine ⟨93845856277819039370206187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250255616740850771653883165 93845856277819039370206187)
      ·
        refine ⟨140768784416728559055309281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93845856277819039370206187 140768784416728559055309281)
        ·
          refine ⟨105576588312546419291481961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140768784416728559055309281 105576588312546419291481961)
          ·
            refine ⟨79182441234409814468611471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105576588312546419291481961 79182441234409814468611471)
            ·
              refine ⟨118773661851614721702917207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79182441234409814468611471 118773661851614721702917207)
              ·
                refine ⟨178160492777422082554375811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118773661851614721702917207 178160492777422082554375811)
                ·
                  refine ⟨267240739166133123831563717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178160492777422082554375811 267240739166133123831563717)
                  ·
                    refine ⟨50107638593649960718418197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 267240739166133123831563717 50107638593649960718418197)
                    ·
                      refine ⟨2348795559077341908675853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50107638593649960718418197 2348795559077341908675853)
                      ·
                        rfl

theorem cell23_4574263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_4574263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574263 prefixEnd_4574263 := by exact prefixLift 4574263
  have htrace : WordTrace (prefixWord ++ tailWord_4574263) baseStart_4574263 baseEnd_4574263 := by
    simpa [prefixWord, tailWord_4574263, baseEnd_4574263] using wordTrace_append hprefix tailTrace_4574263
  have hstable : (prefixWord ++ tailWord_4574263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574263).length < 2 ^ (prefixWord ++ tailWord_4574263).sum := by decide
  have hdescent : baseEnd_4574263 < baseStart_4574263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574264 : List Nat := [2, 1, 2, 1, 5, 1, 4, 1, 2, 4]
def baseStart_4574264 : Nat := 118140960795 + 4574264 * 2 ^ 59
def prefixEnd_4574264 : Nat := 4983230072969 + 3 ^ 40 * 4574264 * 2
def baseEnd_4574264 : Nat := 782932024185998801587783

theorem tailTrace_4574264 : CollatzResearch.WordTrace tailWord_4574264 prefixEnd_4574264 782932024185998801587783 := by
  unfold tailWord_4574264
  simp only [CollatzResearch.WordTrace]
  refine ⟨83418557150115112470020923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111224742866820149960027897 83418557150115112470020923)
  ·
    refine ⟨125127835725172668705031385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83418557150115112470020923 125127835725172668705031385)
    ·
      refine ⟨93845876793879501528773539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125127835725172668705031385 93845876793879501528773539)
      ·
        refine ⟨140768815190819252293160309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93845876793879501528773539 140768815190819252293160309)
        ·
          refine ⟨13197076424139304902483779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140768815190819252293160309 13197076424139304902483779)
          ·
            refine ⟨19795614636208957353725669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13197076424139304902483779 19795614636208957353725669)
            ·
              refine ⟨3711677744289179503823563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19795614636208957353725669 3711677744289179503823563)
              ·
                refine ⟨5567516616433769255735345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3711677744289179503823563 5567516616433769255735345)
                ·
                  refine ⟨4175637462325326941801509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5567516616433769255735345 4175637462325326941801509)
                  ·
                    refine ⟨782932024185998801587783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4175637462325326941801509 782932024185998801587783)
                    ·
                      rfl

theorem cell23_4574264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_4574264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574264 prefixEnd_4574264 := by exact prefixLift 4574264
  have htrace : WordTrace (prefixWord ++ tailWord_4574264) baseStart_4574264 baseEnd_4574264 := by
    simpa [prefixWord, tailWord_4574264, baseEnd_4574264] using wordTrace_append hprefix tailTrace_4574264
  have hstable : (prefixWord ++ tailWord_4574264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574264).length < 2 ^ (prefixWord ++ tailWord_4574264).sum := by decide
  have hdescent : baseEnd_4574264 < baseStart_4574264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574294 : List Nat := [5, 2, 2, 1, 3, 10]
def baseStart_4574294 : Nat := 118140960795 + 4574294 * 2 ^ 59
def prefixEnd_4574294 : Nat := 4983230072969 + 3 ^ 40 * 4574294 * 2
def baseEnd_4574294 : Nat := 9665890851759799536577

theorem tailTrace_4574294 : CollatzResearch.WordTrace tailWord_4574294 prefixEnd_4574294 9665890851759799536577 := by
  unfold tailWord_4574294
  simp only [CollatzResearch.WordTrace]
  refine ⟨10427388030632596253977121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111225472326747693375755957 10427388030632596253977121)
  ·
    refine ⟨7820541022974447190482841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10427388030632596253977121 7820541022974447190482841)
    ·
      refine ⟨5865405767230835392862131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7820541022974447190482841 5865405767230835392862131)
      ·
        refine ⟨8798108650846253089293197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5865405767230835392862131 8798108650846253089293197)
        ·
          refine ⟨3299290744067344908484949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8798108650846253089293197 3299290744067344908484949)
          ·
            refine ⟨9665890851759799536577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3299290744067344908484949 9665890851759799536577)
            ·
              rfl

theorem cell23_4574294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 10].length) (baseStart_4574294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574294 prefixEnd_4574294 := by exact prefixLift 4574294
  have htrace : WordTrace (prefixWord ++ tailWord_4574294) baseStart_4574294 baseEnd_4574294 := by
    simpa [prefixWord, tailWord_4574294, baseEnd_4574294] using wordTrace_append hprefix tailTrace_4574294
  have hstable : (prefixWord ++ tailWord_4574294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574294).length < 2 ^ (prefixWord ++ tailWord_4574294).sum := by decide
  have hdescent : baseEnd_4574294 < baseStart_4574294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574304 : List Nat := [2, 1, 1, 3, 2, 2, 4, 2, 2, 1, 3]
def baseStart_4574304 : Nat := 118140960795 + 4574304 * 2 ^ 59
def prefixEnd_4574304 : Nat := 4983230072969 + 3 ^ 40 * 4574304 * 2
def baseEnd_4574304 : Nat := 2348816611784176248263165

theorem tailTrace_4574304 : CollatzResearch.WordTrace tailWord_4574304 prefixEnd_4574304 2348816611784176248263165 := by
  unfold tailWord_4574304
  simp only [CollatzResearch.WordTrace]
  refine ⟨83419286610042655885748983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111225715480056874514331977 83419286610042655885748983)
  ·
    refine ⟨125128929915063983828623475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83419286610042655885748983 125128929915063983828623475)
    ·
      refine ⟨187693394872595975742935213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125128929915063983828623475 187693394872595975742935213)
      ·
        refine ⟨70385023077223490903600705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187693394872595975742935213 70385023077223490903600705)
        ·
          refine ⟨52788767307917618177700529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70385023077223490903600705 52788767307917618177700529)
          ·
            refine ⟨39591575480938213633275397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52788767307917618177700529 39591575480938213633275397)
            ·
              refine ⟨7423420402675915056239137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39591575480938213633275397 7423420402675915056239137)
              ·
                refine ⟨5567565302006936292179353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7423420402675915056239137 5567565302006936292179353)
                ·
                  refine ⟨4175673976505202219134515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5567565302006936292179353 4175673976505202219134515)
                  ·
                    refine ⟨6263510964757803328701773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4175673976505202219134515 6263510964757803328701773)
                    ·
                      refine ⟨2348816611784176248263165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6263510964757803328701773 2348816611784176248263165)
                      ·
                        rfl

theorem cell23_4574304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_4574304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574304 prefixEnd_4574304 := by exact prefixLift 4574304
  have htrace : WordTrace (prefixWord ++ tailWord_4574304) baseStart_4574304 baseEnd_4574304 := by
    simpa [prefixWord, tailWord_4574304, baseEnd_4574304] using wordTrace_append hprefix tailTrace_4574304
  have hstable : (prefixWord ++ tailWord_4574304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574304).length < 2 ^ (prefixWord ++ tailWord_4574304).sum := by decide
  have hdescent : baseEnd_4574304 < baseStart_4574304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574314 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_4574314 : Nat := 118140960795 + 4574314 * 2 ^ 59
def prefixEnd_4574314 : Nat := 4983230072969 + 3 ^ 40 * 4574314 * 2
def baseEnd_4574314 : Nat := 2348821746590721209138119

theorem tailTrace_4574314 : CollatzResearch.WordTrace tailWord_4574314 prefixEnd_4574314 2348821746590721209138119 := by
  unfold tailWord_4574314
  simp only [CollatzResearch.WordTrace]
  refine ⟨41709734487512270869840499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111225958633366055652907997 41709734487512270869840499)
  ·
    refine ⟨62564601731268406304760749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41709734487512270869840499 62564601731268406304760749)
    ·
      refine ⟨23461725649225652364285281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62564601731268406304760749 23461725649225652364285281)
      ·
        refine ⟨17596294236919239273213961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23461725649225652364285281 17596294236919239273213961)
        ·
          refine ⟨13197220677689429454910471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17596294236919239273213961 13197220677689429454910471)
          ·
            refine ⟨19795831016534144182365707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13197220677689429454910471 19795831016534144182365707)
            ·
              refine ⟨29693746524801216273548561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19795831016534144182365707 29693746524801216273548561)
              ·
                refine ⟨22270309893600912205161421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29693746524801216273548561 22270309893600912205161421)
                ·
                  refine ⟨8351366210100342076935533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22270309893600912205161421 8351366210100342076935533)
                  ·
                    refine ⟨3131762328787628278850825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8351366210100342076935533 3131762328787628278850825)
                    ·
                      refine ⟨2348821746590721209138119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3131762328787628278850825 2348821746590721209138119)
                      ·
                        rfl

theorem cell23_4574314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_4574314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574314 prefixEnd_4574314 := by exact prefixLift 4574314
  have htrace : WordTrace (prefixWord ++ tailWord_4574314) baseStart_4574314 baseEnd_4574314 := by
    simpa [prefixWord, tailWord_4574314, baseEnd_4574314] using wordTrace_append hprefix tailTrace_4574314
  have hstable : (prefixWord ++ tailWord_4574314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574314).length < 2 ^ (prefixWord ++ tailWord_4574314).sum := by decide
  have hdescent : baseEnd_4574314 < baseStart_4574314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574320 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 2, 6]
def baseStart_4574320 : Nat := 118140960795 + 4574320 * 2 ^ 59
def prefixEnd_4574320 : Nat := 4983230072969 + 3 ^ 40 * 4574320 * 2
def baseEnd_4574320 : Nat := 782941609158216061887697

theorem tailTrace_4574320 : CollatzResearch.WordTrace tailWord_4574320 prefixEnd_4574320 782941609158216061887697 := by
  unfold tailWord_4574320
  simp only [CollatzResearch.WordTrace]
  refine ⟨83419578394013673252040207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111226104525351564336053609 83419578394013673252040207)
  ·
    refine ⟨125129367591020509878060311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83419578394013673252040207 125129367591020509878060311)
    ·
      refine ⟨187694051386530764817090467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125129367591020509878060311 187694051386530764817090467)
      ·
        refine ⟨281541077079796147225635701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187694051386530764817090467 281541077079796147225635701)
        ·
          refine ⟨26394475976230888802403347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 281541077079796147225635701 26394475976230888802403347)
          ·
            refine ⟨39591713964346333203605021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26394475976230888802403347 39591713964346333203605021)
            ·
              refine ⟨14846892736629874951351883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39591713964346333203605021 14846892736629874951351883)
              ·
                refine ⟨22270339104944812427027825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14846892736629874951351883 22270339104944812427027825)
                ·
                  refine ⟨16702754328708609320270869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22270339104944812427027825 16702754328708609320270869)
                  ·
                    refine ⟨782941609158216061887697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16702754328708609320270869 782941609158216061887697)
                    ·
                      rfl

theorem cell23_4574320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 2, 6].length) (baseStart_4574320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574320 prefixEnd_4574320 := by exact prefixLift 4574320
  have htrace : WordTrace (prefixWord ++ tailWord_4574320) baseStart_4574320 baseEnd_4574320 := by
    simpa [prefixWord, tailWord_4574320, baseEnd_4574320] using wordTrace_append hprefix tailTrace_4574320
  have hstable : (prefixWord ++ tailWord_4574320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574320).length < 2 ^ (prefixWord ++ tailWord_4574320).sum := by decide
  have hdescent : baseEnd_4574320 < baseStart_4574320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574378 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_4574378 : Nat := 118140960795 + 4574378 * 2 ^ 59
def prefixEnd_4574378 : Nat := 4983230072969 + 3 ^ 40 * 4574378 * 2
def baseEnd_4574378 : Nat := 2348854609352608958737825

theorem tailTrace_4574378 : CollatzResearch.WordTrace tailWord_4574378 prefixEnd_4574378 2348854609352608958737825 := by
  unfold tailWord_4574378
  simp only [CollatzResearch.WordTrace]
  refine ⟨41710318055454305602422947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111227514814544814939794525 41710318055454305602422947)
  ·
    refine ⟨62565477083181458403634421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41710318055454305602422947 62565477083181458403634421)
    ·
      refine ⟨5865513476548261725340727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62565477083181458403634421 5865513476548261725340727)
      ·
        refine ⟨8798270214822392588011091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5865513476548261725340727 8798270214822392588011091)
        ·
          refine ⟨13197405322233588882016637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8798270214822392588011091 13197405322233588882016637)
          ·
            refine ⟨4949026995837595830756239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13197405322233588882016637 4949026995837595830756239)
            ·
              refine ⟨7423540493756393746134359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4949026995837595830756239 7423540493756393746134359)
              ·
                refine ⟨11135310740634590619201539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7423540493756393746134359 11135310740634590619201539)
                ·
                  refine ⟨16702966110951885928802309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11135310740634590619201539 16702966110951885928802309)
                  ·
                    refine ⟨3131806145803478611650433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16702966110951885928802309 3131806145803478611650433)
                    ·
                      refine ⟨2348854609352608958737825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3131806145803478611650433 2348854609352608958737825)
                      ·
                        rfl

theorem cell23_4574378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_4574378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574378 prefixEnd_4574378 := by exact prefixLift 4574378
  have htrace : WordTrace (prefixWord ++ tailWord_4574378) baseStart_4574378 baseEnd_4574378 := by
    simpa [prefixWord, tailWord_4574378, baseEnd_4574378] using wordTrace_append hprefix tailTrace_4574378
  have hstable : (prefixWord ++ tailWord_4574378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574378).length < 2 ^ (prefixWord ++ tailWord_4574378).sum := by decide
  have hdescent : baseEnd_4574378 < baseStart_4574378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574380 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 6, 5]
def baseStart_4574380 : Nat := 118140960795 + 4574380 * 2 ^ 59
def prefixEnd_4574380 : Nat := 4983230072969 + 3 ^ 40 * 4574380 * 2
def baseEnd_4574380 : Nat := 782951878771305983637605

theorem tailTrace_4574380 : CollatzResearch.WordTrace tailWord_4574380 prefixEnd_4574380 782951878771305983637605 := by
  unfold tailWord_4574380
  simp only [CollatzResearch.WordTrace]
  refine ⟨83420672583904988375632297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111227563445206651167509729 83420672583904988375632297)
  ·
    refine ⟨62565504437928741281724223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83420672583904988375632297 62565504437928741281724223)
    ·
      refine ⟨93848256656893111922586335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62565504437928741281724223 93848256656893111922586335)
      ·
        refine ⟨140772384985339667883879503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93848256656893111922586335 140772384985339667883879503)
        ·
          refine ⟨211158577478009501825819255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140772384985339667883879503 211158577478009501825819255)
          ·
            refine ⟨316737866217014252738728883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211158577478009501825819255 316737866217014252738728883)
            ·
              refine ⟨475106799325521379108093325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316737866217014252738728883 475106799325521379108093325)
              ·
                refine ⟨178165049747070517165534997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 475106799325521379108093325 178165049747070517165534997)
                ·
                  refine ⟨8351486706893930492134453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 178165049747070517165534997 8351486706893930492134453)
                  ·
                    refine ⟨782951878771305983637605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8351486706893930492134453 782951878771305983637605)
                    ·
                      rfl

theorem cell23_4574380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_4574380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574380 prefixEnd_4574380 := by exact prefixLift 4574380
  have htrace : WordTrace (prefixWord ++ tailWord_4574380) baseStart_4574380 baseEnd_4574380 := by
    simpa [prefixWord, tailWord_4574380, baseEnd_4574380] using wordTrace_append hprefix tailTrace_4574380
  have hstable : (prefixWord ++ tailWord_4574380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574380).length < 2 ^ (prefixWord ++ tailWord_4574380).sum := by decide
  have hdescent : baseEnd_4574380 < baseStart_4574380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574387 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 2, 5, 2]
def baseStart_4574387 : Nat := 118140960795 + 4574387 * 2 ^ 59
def prefixEnd_4574387 : Nat := 4983230072969 + 3 ^ 40 * 4574387 * 2
def baseEnd_4574387 : Nat := 2348859230678499423525283

theorem tailTrace_4574387 : CollatzResearch.WordTrace tailWord_4574387 prefixEnd_4574387 2348859230678499423525283 := by
  unfold tailWord_4574387
  simp only [CollatzResearch.WordTrace]
  refine ⟨166841600478784616946769415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111227733652523077964512943 166841600478784616946769415)
  ·
    refine ⟨250262400718176925420154123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166841600478784616946769415 250262400718176925420154123)
    ·
      refine ⟨375393601077265388130231185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250262400718176925420154123 375393601077265388130231185)
      ·
        refine ⟨281545200807949041097673389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375393601077265388130231185 281545200807949041097673389)
        ·
          refine ⟨105579450302980890411627521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 281545200807949041097673389 105579450302980890411627521)
          ·
            refine ⟨79184587727235667808720641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105579450302980890411627521 79184587727235667808720641)
            ·
              refine ⟨59388440795426750856540481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79184587727235667808720641 59388440795426750856540481)
              ·
                refine ⟨44541330596570063142405361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59388440795426750856540481 44541330596570063142405361)
                ·
                  refine ⟨33405997947427547356804021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44541330596570063142405361 33405997947427547356804021)
                  ·
                    refine ⟨3131812307571332564700377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33405997947427547356804021 3131812307571332564700377)
                    ·
                      refine ⟨2348859230678499423525283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3131812307571332564700377 2348859230678499423525283)
                      ·
                        rfl

theorem cell23_4574387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 5, 2].length) (baseStart_4574387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574387 prefixEnd_4574387 := by exact prefixLift 4574387
  have htrace : WordTrace (prefixWord ++ tailWord_4574387) baseStart_4574387 baseEnd_4574387 := by
    simpa [prefixWord, tailWord_4574387, baseEnd_4574387] using wordTrace_append hprefix tailTrace_4574387
  have hstable : (prefixWord ++ tailWord_4574387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574387).length < 2 ^ (prefixWord ++ tailWord_4574387).sum := by decide
  have hdescent : baseEnd_4574387 < baseStart_4574387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574401 : List Nat := [1, 2, 6, 1, 1, 1, 3, 3, 5]
def baseStart_4574401 : Nat := 118140960795 + 4574401 * 2 ^ 59
def prefixEnd_4574401 : Nat := 4983230072969 + 3 ^ 40 * 4574401 * 2
def baseEnd_4574401 : Nat := 260985157711962485416691

theorem tailTrace_4574401 : CollatzResearch.WordTrace tailWord_4574401 prefixEnd_4574401 260985157711962485416691 := by
  unfold tailWord_4574401
  simp only [CollatzResearch.WordTrace]
  refine ⟨166842111100733897337779057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111228074067155931558519371 166842111100733897337779057)
  ·
    refine ⟨125131583325550423003334293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166842111100733897337779057 125131583325550423003334293)
    ·
      refine ⟨5865542968385176078281295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 125131583325550423003334293 5865542968385176078281295)
      ·
        refine ⟨8798314452577764117421943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5865542968385176078281295 8798314452577764117421943)
        ·
          refine ⟨13197471678866646176132915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8798314452577764117421943 13197471678866646176132915)
          ·
            refine ⟨19796207518299969264199373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13197471678866646176132915 19796207518299969264199373)
            ·
              refine ⟨7423577819362488474074765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19796207518299969264199373 7423577819362488474074765)
              ·
                refine ⟨2783841682260933177778037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7423577819362488474074765 2783841682260933177778037)
                ·
                  refine ⟨260985157711962485416691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2783841682260933177778037 260985157711962485416691)
                  ·
                    rfl

theorem cell23_4574401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 3, 5].length) (baseStart_4574401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574401 prefixEnd_4574401 := by exact prefixLift 4574401
  have htrace : WordTrace (prefixWord ++ tailWord_4574401) baseStart_4574401 baseEnd_4574401 := by
    simpa [prefixWord, tailWord_4574401, baseEnd_4574401] using wordTrace_append hprefix tailTrace_4574401
  have hstable : (prefixWord ++ tailWord_4574401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574401).length < 2 ^ (prefixWord ++ tailWord_4574401).sum := by decide
  have hdescent : baseEnd_4574401 < baseStart_4574401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574414 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_4574414 : Nat := 118140960795 + 4574414 * 2 ^ 59
def prefixEnd_4574414 : Nat := 4983230072969 + 3 ^ 40 * 4574414 * 2
def baseEnd_4574414 : Nat := 782957698218723605962553

theorem tailTrace_4574414 : CollatzResearch.WordTrace tailWord_4574414 prefixEnd_4574414 782957698218723605962553 := by
  unfold tailWord_4574414
  simp only [CollatzResearch.WordTrace]
  refine ⟨20855323156210850069750287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111228390166457867038668197 20855323156210850069750287)
  ·
    refine ⟨31282984734316275104625431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20855323156210850069750287 31282984734316275104625431)
    ·
      refine ⟨46924477101474412656938147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31282984734316275104625431 46924477101474412656938147)
      ·
        refine ⟨70386715652211618985407221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46924477101474412656938147 70386715652211618985407221)
        ·
          refine ⟨6598754592394839279881927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70386715652211618985407221 6598754592394839279881927)
          ·
            refine ⟨9898131888592258919822891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6598754592394839279881927 9898131888592258919822891)
            ·
              refine ⟨14847197832888388379734337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9898131888592258919822891 14847197832888388379734337)
              ·
                refine ⟨11135398374666291284800753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14847197832888388379734337 11135398374666291284800753)
                ·
                  refine ⟨8351548780999718463600565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11135398374666291284800753 8351548780999718463600565)
                  ·
                    refine ⟨782957698218723605962553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8351548780999718463600565 782957698218723605962553)
                    ·
                      rfl

theorem cell23_4574414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_4574414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574414 prefixEnd_4574414 := by exact prefixLift 4574414
  have htrace : WordTrace (prefixWord ++ tailWord_4574414) baseStart_4574414 baseEnd_4574414 := by
    simpa [prefixWord, tailWord_4574414, baseEnd_4574414] using wordTrace_append hprefix tailTrace_4574414
  have hstable : (prefixWord ++ tailWord_4574414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574414).length < 2 ^ (prefixWord ++ tailWord_4574414).sum := by decide
  have hdescent : baseEnd_4574414 < baseStart_4574414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574478 : List Nat := [4, 1, 1, 2, 1, 3, 4, 2, 1, 4]
def baseStart_4574478 : Nat := 118140960795 + 4574478 * 2 ^ 59
def prefixEnd_4574478 : Nat := 4983230072969 + 3 ^ 40 * 4574478 * 2
def baseEnd_4574478 : Nat := 782968652472686189162455

theorem tailTrace_4574478 : CollatzResearch.WordTrace tailWord_4574478 prefixEnd_4574478 782968652472686189162455 := by
  unfold tailWord_4574478
  simp only [CollatzResearch.WordTrace]
  refine ⟨20855614940181867436041511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111229946347636626325554725 20855614940181867436041511)
  ·
    refine ⟨31283422410272801154062267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20855614940181867436041511 31283422410272801154062267)
    ·
      refine ⟨46925133615409201731093401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31283422410272801154062267 46925133615409201731093401)
      ·
        refine ⟨35193850211556901298320051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46925133615409201731093401 35193850211556901298320051)
        ·
          refine ⟨52790775317335351947480077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35193850211556901298320051 52790775317335351947480077)
          ·
            refine ⟨19796540744000756980305029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52790775317335351947480077 19796540744000756980305029)
            ·
              refine ⟨3711851389500141933807193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19796540744000756980305029 3711851389500141933807193)
              ·
                refine ⟨2783888542125106450355395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3711851389500141933807193 2783888542125106450355395)
                ·
                  refine ⟨4175832813187659675533093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2783888542125106450355395 4175832813187659675533093)
                  ·
                    refine ⟨782968652472686189162455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4175832813187659675533093 782968652472686189162455)
                    ·
                      rfl

theorem cell23_4574478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_4574478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574478 prefixEnd_4574478 := by exact prefixLift 4574478
  have htrace : WordTrace (prefixWord ++ tailWord_4574478) baseStart_4574478 baseEnd_4574478 := by
    simpa [prefixWord, tailWord_4574478, baseEnd_4574478] using wordTrace_append hprefix tailTrace_4574478
  have hstable : (prefixWord ++ tailWord_4574478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574478).length < 2 ^ (prefixWord ++ tailWord_4574478).sum := by decide
  have hdescent : baseEnd_4574478 < baseStart_4574478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574487 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 5, 5]
def baseStart_4574487 : Nat := 118140960795 + 4574487 * 2 ^ 59
def prefixEnd_4574487 : Nat := 4983230072969 + 3 ^ 40 * 4574487 * 2
def baseEnd_4574487 : Nat := 782970192914649677424941

theorem tailTrace_4574487 : CollatzResearch.WordTrace tailWord_4574487 prefixEnd_4574487 782970192914649677424941 := by
  unfold tailWord_4574487
  simp only [CollatzResearch.WordTrace]
  refine ⟨166845247778422334025409715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111230165185614889350273143 166845247778422334025409715)
  ·
    refine ⟨250267871667633501038114573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166845247778422334025409715 250267871667633501038114573)
    ·
      refine ⟨93850451875362562889292965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250267871667633501038114573 93850451875362562889292965)
      ·
        refine ⟨17596959726630480541742431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93850451875362562889292965 17596959726630480541742431)
        ·
          refine ⟨26395439589945720812613647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17596959726630480541742431 26395439589945720812613647)
          ·
            refine ⟨39593159384918581218920471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26395439589945720812613647 39593159384918581218920471)
            ·
              refine ⟨59389739077377871828380707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39593159384918581218920471 59389739077377871828380707)
              ·
                refine ⟨89084608616066807742571061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59389739077377871828380707 89084608616066807742571061)
                ·
                  refine ⟨8351682057756263225866037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89084608616066807742571061 8351682057756263225866037)
                  ·
                    refine ⟨782970192914649677424941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8351682057756263225866037 782970192914649677424941)
                    ·
                      rfl

theorem cell23_4574487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_4574487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574487 prefixEnd_4574487 := by exact prefixLift 4574487
  have htrace : WordTrace (prefixWord ++ tailWord_4574487) baseStart_4574487 baseEnd_4574487 := by
    simpa [prefixWord, tailWord_4574487, baseEnd_4574487] using wordTrace_append hprefix tailTrace_4574487
  have hstable : (prefixWord ++ tailWord_4574487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574487).length < 2 ^ (prefixWord ++ tailWord_4574487).sum := by decide
  have hdescent : baseEnd_4574487 < baseStart_4574487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574501 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 3, 1, 3]
def baseStart_4574501 : Nat := 118140960795 + 4574501 * 2 ^ 59
def prefixEnd_4574501 : Nat := 4983230072969 + 3 ^ 40 * 4574501 * 2
def baseEnd_4574501 : Nat := 2348917767473111977499759

theorem tailTrace_4574501 : CollatzResearch.WordTrace tailWord_4574501 prefixEnd_4574501 2348917767473111977499759 := by
  unfold tailWord_4574501
  simp only [CollatzResearch.WordTrace]
  refine ⟨166845758400371614416419357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111230505600247742944279571 166845758400371614416419357)
  ·
    refine ⟨62567159400139355406157259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166845758400371614416419357 62567159400139355406157259)
    ·
      refine ⟨93850739100209033109235889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62567159400139355406157259 93850739100209033109235889)
      ·
        refine ⟨70388054325156774831926917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93850739100209033109235889 70388054325156774831926917)
        ·
          refine ⟨13197760185966895280986297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70388054325156774831926917 13197760185966895280986297)
          ·
            refine ⟨9898320139475171460739723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13197760185966895280986297 9898320139475171460739723)
            ·
              refine ⟨14847480209212757191109585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9898320139475171460739723 14847480209212757191109585)
              ·
                refine ⟨11135610156909567893332189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14847480209212757191109585 11135610156909567893332189)
                ·
                  refine ⟨4175853808841087959999571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11135610156909567893332189 4175853808841087959999571)
                  ·
                    refine ⟨6263780713261631939999357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4175853808841087959999571 6263780713261631939999357)
                    ·
                      refine ⟨2348917767473111977499759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6263780713261631939999357 2348917767473111977499759)
                      ·
                        rfl

theorem cell23_4574501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_4574501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574501 prefixEnd_4574501 := by exact prefixLift 4574501
  have htrace : WordTrace (prefixWord ++ tailWord_4574501) baseStart_4574501 baseEnd_4574501 := by
    simpa [prefixWord, tailWord_4574501, baseEnd_4574501] using wordTrace_append hprefix tailTrace_4574501
  have hstable : (prefixWord ++ tailWord_4574501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574501).length < 2 ^ (prefixWord ++ tailWord_4574501).sum := by decide
  have hdescent : baseEnd_4574501 < baseStart_4574501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574504 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 3, 5]
def baseStart_4574504 : Nat := 118140960795 + 4574504 * 2 ^ 59
def prefixEnd_4574504 : Nat := 4983230072969 + 3 ^ 40 * 4574504 * 2
def baseEnd_4574504 : Nat := 782973102638358488587415

theorem tailTrace_4574504 : CollatzResearch.WordTrace tailWord_4574504 prefixEnd_4574504 782973102638358488587415 := by
  unfold tailWord_4574504
  simp only [CollatzResearch.WordTrace]
  refine ⟨83422933909680372964389283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111230578546240497285852377 83422933909680372964389283)
  ·
    refine ⟨125134400864520559446583925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83422933909680372964389283 125134400864520559446583925)
    ·
      refine ⟨11731350081048802448117243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125134400864520559446583925 11731350081048802448117243)
      ·
        refine ⟨17597025121573203672175865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11731350081048802448117243 17597025121573203672175865)
        ·
          refine ⟨13197768841179902754131899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17597025121573203672175865 13197768841179902754131899)
          ·
            refine ⟨19796653261769854131197849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13197768841179902754131899 19796653261769854131197849)
            ·
              refine ⟨14847489946327390598398387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19796653261769854131197849 14847489946327390598398387)
              ·
                refine ⟨22271234919491085897597581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14847489946327390598398387 22271234919491085897597581)
                ·
                  refine ⟨8351713094809157211599093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22271234919491085897597581 8351713094809157211599093)
                  ·
                    refine ⟨782973102638358488587415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8351713094809157211599093 782973102638358488587415)
                    ·
                      rfl

theorem cell23_4574504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_4574504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574504 prefixEnd_4574504 := by exact prefixLift 4574504
  have htrace : WordTrace (prefixWord ++ tailWord_4574504) baseStart_4574504 baseEnd_4574504 := by
    simpa [prefixWord, tailWord_4574504, baseEnd_4574504] using wordTrace_append hprefix tailTrace_4574504
  have hstable : (prefixWord ++ tailWord_4574504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574504).length < 2 ^ (prefixWord ++ tailWord_4574504).sum := by decide
  have hdescent : baseEnd_4574504 < baseStart_4574504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574521 : List Nat := [1, 2, 1, 6, 2, 1, 1, 3, 1, 5]
def baseStart_4574521 : Nat := 118140960795 + 4574521 * 2 ^ 59
def prefixEnd_4574521 : Nat := 4983230072969 + 3 ^ 40 * 4574521 * 2
def baseEnd_4574521 : Nat := 782976012362067299749889

theorem tailTrace_4574521 : CollatzResearch.WordTrace tailWord_4574521 prefixEnd_4574521 782976012362067299749889 := by
  unfold tailWord_4574521
  simp only [CollatzResearch.WordTrace]
  refine ⟨166846487860299157832147417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111230991906866105221431611 166846487860299157832147417)
  ·
    refine ⟨125134865895224368374110563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166846487860299157832147417 125134865895224368374110563)
    ·
      refine ⟨187702298842836552561165845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125134865895224368374110563 187702298842836552561165845)
      ·
        refine ⟨8798545258257963401304649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 187702298842836552561165845 8798545258257963401304649)
        ·
          refine ⟨6598908943693472550978487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8798545258257963401304649 6598908943693472550978487)
          ·
            refine ⟨9898363415540208826467731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6598908943693472550978487 9898363415540208826467731)
            ·
              refine ⟨14847545123310313239701597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9898363415540208826467731 14847545123310313239701597)
              ·
                refine ⟨5567829421241367464888099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14847545123310313239701597 5567829421241367464888099)
                ·
                  refine ⟨8351744131862051197332149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5567829421241367464888099 8351744131862051197332149)
                  ·
                    refine ⟨782976012362067299749889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8351744131862051197332149 782976012362067299749889)
                    ·
                      rfl

theorem cell23_4574521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 5].length) (baseStart_4574521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574521 prefixEnd_4574521 := by exact prefixLift 4574521
  have htrace : WordTrace (prefixWord ++ tailWord_4574521) baseStart_4574521 baseEnd_4574521 := by
    simpa [prefixWord, tailWord_4574521, baseEnd_4574521] using wordTrace_append hprefix tailTrace_4574521
  have hstable : (prefixWord ++ tailWord_4574521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574521).length < 2 ^ (prefixWord ++ tailWord_4574521).sum := by decide
  have hdescent : baseEnd_4574521 < baseStart_4574521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574537 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 3, 2, 4]
def baseStart_4574537 : Nat := 118140960795 + 4574537 * 2 ^ 59
def prefixEnd_4574537 : Nat := 4983230072969 + 3 ^ 40 * 4574537 * 2
def baseEnd_4574537 : Nat := 2348936252776673836649593

theorem tailTrace_4574537 : CollatzResearch.WordTrace tailWord_4574537 prefixEnd_4574537 2348936252776673836649593 := by
  unfold tailWord_4574537
  simp only [CollatzResearch.WordTrace]
  refine ⟨166847071428241192564729865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111231380952160795043153243 166847071428241192564729865)
  ·
    refine ⟨125135303571180894423547399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166847071428241192564729865 125135303571180894423547399)
    ·
      refine ⟨187702955356771341635321099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125135303571180894423547399 187702955356771341635321099)
      ·
        refine ⟨281554433035157012452981649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187702955356771341635321099 281554433035157012452981649)
        ·
          refine ⟨211165824776367759339736237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281554433035157012452981649 211165824776367759339736237)
          ·
            refine ⟨79187184291137909752401089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211165824776367759339736237 79187184291137909752401089)
            ·
              refine ⟨59390388218353432314300817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79187184291137909752401089 59390388218353432314300817)
              ·
                refine ⟨44542791163765074235725613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59390388218353432314300817 44542791163765074235725613)
                ·
                  refine ⟨16703546686411902838397105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44542791163765074235725613 16703546686411902838397105)
                  ·
                    refine ⟨12527660014808927128797829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16703546686411902838397105 12527660014808927128797829)
                    ·
                      refine ⟨2348936252776673836649593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12527660014808927128797829 2348936252776673836649593)
                      ·
                        rfl

theorem cell23_4574537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_4574537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574537 prefixEnd_4574537 := by exact prefixLift 4574537
  have htrace : WordTrace (prefixWord ++ tailWord_4574537) baseStart_4574537 baseEnd_4574537 := by
    simpa [prefixWord, tailWord_4574537, baseEnd_4574537] using wordTrace_append hprefix tailTrace_4574537
  have hstable : (prefixWord ++ tailWord_4574537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574537).length < 2 ^ (prefixWord ++ tailWord_4574537).sum := by decide
  have hdescent : baseEnd_4574537 < baseStart_4574537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574554 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4]
def baseStart_4574554 : Nat := 118140960795 + 4574554 * 2 ^ 59
def prefixEnd_4574554 : Nat := 4983230072969 + 3 ^ 40 * 4574554 * 2
def baseEnd_4574554 : Nat := 2348944981947800270137015

theorem tailTrace_4574554 : CollatzResearch.WordTrace tailWord_4574554 prefixEnd_4574554 2348944981947800270137015 := by
  unfold tailWord_4574554
  simp only [CollatzResearch.WordTrace]
  refine ⟨41711922867294901117024679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111231794312786402978732477 41711922867294901117024679)
  ·
    refine ⟨62567884300942351675537019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41711922867294901117024679 62567884300942351675537019)
    ·
      refine ⟨93851826451413527513305529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62567884300942351675537019 93851826451413527513305529)
      ·
        refine ⟨70388869838560145634979147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93851826451413527513305529 70388869838560145634979147)
        ·
          refine ⟨105583304757840218452468721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70388869838560145634979147 105583304757840218452468721)
          ·
            refine ⟨79187478568380163839351541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105583304757840218452468721 79187478568380163839351541)
            ·
              refine ⟨7423826115785640359939207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79187478568380163839351541 7423826115785640359939207)
              ·
                refine ⟨11135739173678460539908811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7423826115785640359939207 11135739173678460539908811)
                ·
                  refine ⟨16703608760517690809863217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11135739173678460539908811 16703608760517690809863217)
                  ·
                    refine ⟨12527706570388268107397413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16703608760517690809863217 12527706570388268107397413)
                    ·
                      refine ⟨2348944981947800270137015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12527706570388268107397413 2348944981947800270137015)
                      ·
                        rfl

theorem cell23_4574554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_4574554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574554 prefixEnd_4574554 := by exact prefixLift 4574554
  have htrace : WordTrace (prefixWord ++ tailWord_4574554) baseStart_4574554 baseEnd_4574554 := by
    simpa [prefixWord, tailWord_4574554, baseEnd_4574554] using wordTrace_append hprefix tailTrace_4574554
  have hstable : (prefixWord ++ tailWord_4574554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574554).length < 2 ^ (prefixWord ++ tailWord_4574554).sum := by decide
  have hdescent : baseEnd_4574554 < baseStart_4574554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574564 : List Nat := [2, 3, 1, 1, 3, 2, 4, 7]
def baseStart_4574564 : Nat := 118140960795 + 4574564 * 2 ^ 59
def prefixEnd_4574564 : Nat := 4983230072969 + 3 ^ 40 * 4574564 * 2
def baseEnd_4574564 : Nat := 86998152472383156704147

theorem tailTrace_4574564 : CollatzResearch.WordTrace tailWord_4574564 prefixEnd_4574564 86998152472383156704147 := by
  unfold tailWord_4574564
  simp only [CollatzResearch.WordTrace]
  refine ⟨83424028099571688087981373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111232037466095584117308497 83424028099571688087981373)
  ·
    refine ⟨31284010537339383032993015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83424028099571688087981373 31284010537339383032993015)
    ·
      refine ⟨46926015806009074549489523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31284010537339383032993015 46926015806009074549489523)
      ·
        refine ⟨70389023709013611824234285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46926015806009074549489523 70389023709013611824234285)
        ·
          refine ⟨26395883890880104434087857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70389023709013611824234285 26395883890880104434087857)
          ·
            refine ⟨19796912918160078325565893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26395883890880104434087857 19796912918160078325565893)
            ·
              refine ⟨3711921172155014686043605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19796912918160078325565893 3711921172155014686043605)
              ·
                refine ⟨86998152472383156704147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3711921172155014686043605 86998152472383156704147)
                ·
                  rfl

theorem cell23_4574564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 7].length) (baseStart_4574564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574564 prefixEnd_4574564 := by exact prefixLift 4574564
  have htrace : WordTrace (prefixWord ++ tailWord_4574564) baseStart_4574564 baseEnd_4574564 := by
    simpa [prefixWord, tailWord_4574564, baseEnd_4574564] using wordTrace_append hprefix tailTrace_4574564
  have hstable : (prefixWord ++ tailWord_4574564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574564).length < 2 ^ (prefixWord ++ tailWord_4574564).sum := by decide
  have hdescent : baseEnd_4574564 < baseStart_4574564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574581 : List Nat := [1, 3, 4, 1, 4, 1, 9]
def baseStart_4574581 : Nat := 118140960795 + 4574581 * 2 ^ 59
def prefixEnd_4574581 : Nat := 4983230072969 + 3 ^ 40 * 4574581 * 2
def baseEnd_4574581 : Nat := 28999491925005823018511

theorem tailTrace_4574581 : CollatzResearch.WordTrace tailWord_4574581 prefixEnd_4574581 28999491925005823018511 := by
  unfold tailWord_4574581
  simp only [CollatzResearch.WordTrace]
  refine ⟨166848676240081788079331597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111232450826721192052887731 166848676240081788079331597)
  ·
    refine ⟨62568253590030670529749349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166848676240081788079331597 62568253590030670529749349)
    ·
      refine ⟨11731547548130750724328003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62568253590030670529749349 11731547548130750724328003)
      ·
        refine ⟨17597321322196126086492005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11731547548130750724328003 17597321322196126086492005)
        ·
          refine ⟨3299497747911773641217251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17597321322196126086492005 3299497747911773641217251)
          ·
            refine ⟨4949246621867660461825877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3299497747911773641217251 4949246621867660461825877)
            ·
              refine ⟨28999491925005823018511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4949246621867660461825877 28999491925005823018511)
              ·
                rfl

theorem cell23_4574581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 9].length) (baseStart_4574581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574581 prefixEnd_4574581 := by exact prefixLift 4574581
  have htrace : WordTrace (prefixWord ++ tailWord_4574581) baseStart_4574581 baseEnd_4574581 := by
    simpa [prefixWord, tailWord_4574581, baseEnd_4574581] using wordTrace_append hprefix tailTrace_4574581
  have hstable : (prefixWord ++ tailWord_4574581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574581).length < 2 ^ (prefixWord ++ tailWord_4574581).sum := by decide
  have hdescent : baseEnd_4574581 < baseStart_4574581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574587 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 5]
def baseStart_4574587 : Nat := 118140960795 + 4574587 * 2 ^ 59
def prefixEnd_4574587 : Nat := 4983230072969 + 3 ^ 40 * 4574587 * 2
def baseEnd_4574587 : Nat := 2348961926809398641024363

theorem tailTrace_4574587 : CollatzResearch.WordTrace tailWord_4574587 prefixEnd_4574587 2348961926809398641024363 := by
  unfold tailWord_4574587
  simp only [CollatzResearch.WordTrace]
  refine ⟨166848895078060051104050015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111232596718706700736033343 166848895078060051104050015)
  ·
    refine ⟨250273342617090076656075023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166848895078060051104050015 250273342617090076656075023)
    ·
      refine ⟨375410013925635114984112535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250273342617090076656075023 375410013925635114984112535)
      ·
        refine ⟨563115020888452672476168803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375410013925635114984112535 563115020888452672476168803)
        ·
          refine ⟨844672531332679008714253205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563115020888452672476168803 844672531332679008714253205)
          ·
            refine ⟨39594024906219328533480619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 844672531332679008714253205 39594024906219328533480619)
            ·
              refine ⟨59391037359328992800220929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39594024906219328533480619 59391037359328992800220929)
              ·
                refine ⟨44543278019496744600165697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59391037359328992800220929 44543278019496744600165697)
                ·
                  refine ⟨33407458514622558450124273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44543278019496744600165697 33407458514622558450124273)
                  ·
                    refine ⟨25055593885966918837593205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33407458514622558450124273 25055593885966918837593205)
                    ·
                      refine ⟨2348961926809398641024363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25055593885966918837593205 2348961926809398641024363)
                      ·
                        rfl

theorem cell23_4574587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 5].length) (baseStart_4574587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574587 prefixEnd_4574587 := by exact prefixLift 4574587
  have htrace : WordTrace (prefixWord ++ tailWord_4574587) baseStart_4574587 baseEnd_4574587 := by
    simpa [prefixWord, tailWord_4574587, baseEnd_4574587] using wordTrace_append hprefix tailTrace_4574587
  have hstable : (prefixWord ++ tailWord_4574587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574587).length < 2 ^ (prefixWord ++ tailWord_4574587).sum := by decide
  have hdescent : baseEnd_4574587 < baseStart_4574587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574648 : List Nat := [2, 1, 2, 1, 2, 2, 3, 4, 2, 2, 2]
def baseStart_4574648 : Nat := 118140960795 + 4574648 * 2 ^ 59
def prefixEnd_4574648 : Nat := 4983230072969 + 3 ^ 40 * 4574648 * 2
def baseEnd_4574648 : Nat := 2348993249129322902361583

theorem tailTrace_4574648 : CollatzResearch.WordTrace tailWord_4574648 prefixEnd_4574648 2348993249129322902361583 := by
  unfold tailWord_4574648
  simp only [CollatzResearch.WordTrace]
  refine ⟨83425559965419529261010299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111234079953892705681347065 83425559965419529261010299)
  ·
    refine ⟨125138339948129293891515449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83425559965419529261010299 125138339948129293891515449)
    ·
      refine ⟨93853754961096970418636587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125138339948129293891515449 93853754961096970418636587)
      ·
        refine ⟨140780632441645455627954881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93853754961096970418636587 140780632441645455627954881)
        ·
          refine ⟨105585474331234091720966161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140780632441645455627954881 105585474331234091720966161)
          ·
            refine ⟨79189105748425568790724621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105585474331234091720966161 79189105748425568790724621)
            ·
              refine ⟨29695914655659588296521733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79189105748425568790724621 29695914655659588296521733)
              ·
                refine ⟨5567983997936172805597825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29695914655659588296521733 5567983997936172805597825)
                ·
                  refine ⟨4175987998452129604198369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5567983997936172805597825 4175987998452129604198369)
                  ·
                    refine ⟨3131990998839097203148777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4175987998452129604198369 3131990998839097203148777)
                    ·
                      refine ⟨2348993249129322902361583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3131990998839097203148777 2348993249129322902361583)
                      ·
                        rfl

theorem cell23_4574648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 2, 2, 2].length) (baseStart_4574648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574648 prefixEnd_4574648 := by exact prefixLift 4574648
  have htrace : WordTrace (prefixWord ++ tailWord_4574648) baseStart_4574648 baseEnd_4574648 := by
    simpa [prefixWord, tailWord_4574648, baseEnd_4574648] using wordTrace_append hprefix tailTrace_4574648
  have hstable : (prefixWord ++ tailWord_4574648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574648).length < 2 ^ (prefixWord ++ tailWord_4574648).sum := by decide
  have hdescent : baseEnd_4574648 < baseStart_4574648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574654 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 7]
def baseStart_4574654 : Nat := 118140960795 + 4574654 * 2 ^ 59
def prefixEnd_4574654 : Nat := 4983230072969 + 3 ^ 40 * 4574654 * 2
def baseEnd_4574654 : Nat := 260999592223694430987395

theorem tailTrace_4574654 : CollatzResearch.WordTrace tailWord_4574654 prefixEnd_4574654 260999592223694430987395 := by
  unfold tailWord_4574654
  simp only [CollatzResearch.WordTrace]
  refine ⟨20856417346102165193342377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111234225845878214364492677 20856417346102165193342377)
  ·
    refine ⟨15642313009576623895006783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20856417346102165193342377 15642313009576623895006783)
    ·
      refine ⟨23463469514364935842510175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15642313009576623895006783 23463469514364935842510175)
      ·
        refine ⟨35195204271547403763765263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23463469514364935842510175 35195204271547403763765263)
        ·
          refine ⟨52792806407321105645647895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35195204271547403763765263 52792806407321105645647895)
          ·
            refine ⟨79189209610981658468471843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52792806407321105645647895 79189209610981658468471843)
            ·
              refine ⟨118783814416472487702707765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79189209610981658468471843 118783814416472487702707765)
              ·
                refine ⟨11135982601544295722128853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118783814416472487702707765 11135982601544295722128853)
                ·
                  refine ⟨260999592223694430987395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11135982601544295722128853 260999592223694430987395)
                  ·
                    rfl

theorem cell23_4574654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_4574654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574654 prefixEnd_4574654 := by exact prefixLift 4574654
  have htrace : WordTrace (prefixWord ++ tailWord_4574654) baseStart_4574654 baseEnd_4574654 := by
    simpa [prefixWord, tailWord_4574654, baseEnd_4574654] using wordTrace_append hprefix tailTrace_4574654
  have hstable : (prefixWord ++ tailWord_4574654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574654).length < 2 ^ (prefixWord ++ tailWord_4574654).sum := by decide
  have hdescent : baseEnd_4574654 < baseStart_4574654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574741 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_4574741 : Nat := 118140960795 + 4574741 * 2 ^ 59
def prefixEnd_4574741 : Nat := 4983230072969 + 3 ^ 40 * 4574741 * 2
def baseEnd_4574741 : Nat := 2349041002830191038498655

theorem tailTrace_4574741 : CollatzResearch.WordTrace tailWord_4574741 prefixEnd_4574741 2349041002830191038498655 := by
  unfold tailWord_4574741
  simp only [CollatzResearch.WordTrace]
  refine ⟨166854511919502135405156077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111236341279668090270104051 166854511919502135405156077)
  ·
    refine ⟨62570441969813300776933529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166854511919502135405156077 62570441969813300776933529)
    ·
      refine ⟨46927831477359975582700147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62570441969813300776933529 46927831477359975582700147)
      ·
        refine ⟨70391747216039963374050221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46927831477359975582700147 70391747216039963374050221)
        ·
          refine ⟨26396905206014986265268833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70391747216039963374050221 26396905206014986265268833)
          ·
            refine ⟨19797678904511239698951625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26396905206014986265268833 19797678904511239698951625)
            ·
              refine ⟨14848259178383429774213719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19797678904511239698951625 14848259178383429774213719)
              ·
                refine ⟨22272388767575144661320579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14848259178383429774213719 22272388767575144661320579)
                ·
                  refine ⟨33408583151362716991980869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22272388767575144661320579 33408583151362716991980869)
                  ·
                    refine ⟨6264109340880509435996413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33408583151362716991980869 6264109340880509435996413)
                    ·
                      refine ⟨2349041002830191038498655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6264109340880509435996413 2349041002830191038498655)
                      ·
                        rfl

theorem cell23_4574741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_4574741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574741 prefixEnd_4574741 := by exact prefixLift 4574741
  have htrace : WordTrace (prefixWord ++ tailWord_4574741) baseStart_4574741 baseEnd_4574741 := by
    simpa [prefixWord, tailWord_4574741, baseEnd_4574741] using wordTrace_append hprefix tailTrace_4574741
  have hstable : (prefixWord ++ tailWord_4574741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574741).length < 2 ^ (prefixWord ++ tailWord_4574741).sum := by decide
  have hdescent : baseEnd_4574741 < baseStart_4574741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574805 : List Nat := [1, 3, 2, 2, 1, 1, 1, 7, 1, 1, 3]
def baseStart_4574805 : Nat := 118140960795 + 4574805 * 2 ^ 59
def prefixEnd_4574805 : Nat := 4983230072969 + 3 ^ 40 * 4574805 * 2
def baseEnd_4574805 : Nat := 2349073865592078788098361

theorem tailTrace_4574805 : CollatzResearch.WordTrace tailWord_4574805 prefixEnd_4574805 2349073865592078788098361 := by
  unfold tailWord_4574805
  simp only [CollatzResearch.WordTrace]
  refine ⟨166856846191270274335485869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111237897460846849556990579 166856846191270274335485869)
  ·
    refine ⟨62571317321726352875807201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166856846191270274335485869 62571317321726352875807201)
    ·
      refine ⟨46928487991294764656855401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62571317321726352875807201 46928487991294764656855401)
      ·
        refine ⟨35196365993471073492641551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46928487991294764656855401 35196365993471073492641551)
        ·
          refine ⟨52794548990206610238962327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35196365993471073492641551 52794548990206610238962327)
          ·
            refine ⟨79191823485309915358443491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52794548990206610238962327 79191823485309915358443491)
            ·
              refine ⟨118787735227964873037665237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79191823485309915358443491 118787735227964873037665237)
              ·
                refine ⟨2784087544405426711820279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 118787735227964873037665237 2784087544405426711820279)
                ·
                  refine ⟨4176131316608140067730419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2784087544405426711820279 4176131316608140067730419)
                  ·
                    refine ⟨6264196974912210101595629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4176131316608140067730419 6264196974912210101595629)
                    ·
                      refine ⟨2349073865592078788098361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6264196974912210101595629 2349073865592078788098361)
                      ·
                        rfl

theorem cell23_4574805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_4574805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574805 prefixEnd_4574805 := by exact prefixLift 4574805
  have htrace : WordTrace (prefixWord ++ tailWord_4574805) baseStart_4574805 baseEnd_4574805 := by
    simpa [prefixWord, tailWord_4574805, baseEnd_4574805] using wordTrace_append hprefix tailTrace_4574805
  have hstable : (prefixWord ++ tailWord_4574805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574805).length < 2 ^ (prefixWord ++ tailWord_4574805).sum := by decide
  have hdescent : baseEnd_4574805 < baseStart_4574805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574838 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_4574838 : Nat := 118140960795 + 4574838 * 2 ^ 59
def prefixEnd_4574838 : Nat := 4983230072969 + 3 ^ 40 * 4574838 * 2
def baseEnd_4574838 : Nat := 783030270151225719661903

theorem tailTrace_4574838 : CollatzResearch.WordTrace tailWord_4574838 prefixEnd_4574838 783030270151225719661903 := by
  unfold tailWord_4574838
  simp only [CollatzResearch.WordTrace]
  refine ⟨10428628112509420060714823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111238699866767147314291445 10428628112509420060714823)
  ·
    refine ⟨15642942168764130091072235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10428628112509420060714823 15642942168764130091072235)
    ·
      refine ⟨23464413253146195136608353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15642942168764130091072235 23464413253146195136608353)
      ·
        refine ⟨17598309939859646352456265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23464413253146195136608353 17598309939859646352456265)
        ·
          refine ⟨13198732454894734764342199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17598309939859646352456265 13198732454894734764342199)
          ·
            refine ⟨19798098682342102146513299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13198732454894734764342199 19798098682342102146513299)
            ·
              refine ⟨29697148023513153219769949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19798098682342102146513299 29697148023513153219769949)
              ·
                refine ⟨11136430508817432457413731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29697148023513153219769949 11136430508817432457413731)
                ·
                  refine ⟨16704645763226148686120597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11136430508817432457413731 16704645763226148686120597)
                  ·
                    refine ⟨783030270151225719661903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16704645763226148686120597 783030270151225719661903)
                    ·
                      rfl

theorem cell23_4574838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_4574838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574838 prefixEnd_4574838 := by exact prefixLift 4574838
  have htrace : WordTrace (prefixWord ++ tailWord_4574838) baseStart_4574838 baseEnd_4574838 := by
    simpa [prefixWord, tailWord_4574838, baseEnd_4574838] using wordTrace_append hprefix tailTrace_4574838
  have hstable : (prefixWord ++ tailWord_4574838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574838).length < 2 ^ (prefixWord ++ tailWord_4574838).sum := by decide
  have hdescent : baseEnd_4574838 < baseStart_4574838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574845 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 5, 2, 2]
def baseStart_4574845 : Nat := 118140960795 + 4574845 * 2 ^ 59
def prefixEnd_4574845 : Nat := 4983230072969 + 3 ^ 40 * 4574845 * 2
def baseEnd_4574845 : Nat := 2349094404818258631598177

theorem tailTrace_4574845 : CollatzResearch.WordTrace tailWord_4574845 prefixEnd_4574845 2349094404818258631598177 := by
  unfold tailWord_4574845
  simp only [CollatzResearch.WordTrace]
  refine ⟨166858305111125361166941989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111238870074083574111294659 166858305111125361166941989)
  ·
    refine ⟨31285932208336005218801623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166858305111125361166941989 31285932208336005218801623)
    ·
      refine ⟨46928898312504007828202435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31285932208336005218801623 46928898312504007828202435)
      ·
        refine ⟨70393347468756011742303653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46928898312504007828202435 70393347468756011742303653)
        ·
          refine ⟨13198752650391752201681935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70393347468756011742303653 13198752650391752201681935)
          ·
            refine ⟨19798128975587628302522903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13198752650391752201681935 19798128975587628302522903)
            ·
              refine ⟨29697193463381442453784355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19798128975587628302522903 29697193463381442453784355)
              ·
                refine ⟨44545790195072163680676533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29697193463381442453784355 44545790195072163680676533)
                ·
                  refine ⟨4176167830788015345063425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44545790195072163680676533 4176167830788015345063425)
                  ·
                    refine ⟨3132125873091011508797569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4176167830788015345063425 3132125873091011508797569)
                    ·
                      refine ⟨2349094404818258631598177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3132125873091011508797569 2349094404818258631598177)
                      ·
                        rfl

theorem cell23_4574845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_4574845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574845 prefixEnd_4574845 := by exact prefixLift 4574845
  have htrace : WordTrace (prefixWord ++ tailWord_4574845) baseStart_4574845 baseEnd_4574845 := by
    simpa [prefixWord, tailWord_4574845, baseEnd_4574845] using wordTrace_append hprefix tailTrace_4574845
  have hstable : (prefixWord ++ tailWord_4574845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574845).length < 2 ^ (prefixWord ++ tailWord_4574845).sum := by decide
  have hdescent : baseEnd_4574845 < baseStart_4574845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574848 : List Nat := [2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 3]
def baseStart_4574848 : Nat := 118140960795 + 4574848 * 2 ^ 59
def prefixEnd_4574848 : Nat := 4983230072969 + 3 ^ 40 * 4574848 * 2
def baseEnd_4574848 : Nat := 2349095945260222119860663

theorem tailTrace_4574848 : CollatzResearch.WordTrace tailWord_4574848 prefixEnd_4574848 2349095945260222119860663 := by
  unfold tailWord_4574848
  simp only [CollatzResearch.WordTrace]
  refine ⟨83429207265057246339650599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111238943020076328452867465 83429207265057246339650599)
  ·
    refine ⟨125143810897585869509475899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83429207265057246339650599 125143810897585869509475899)
    ·
      refine ⟨187715716346378804264213849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125143810897585869509475899 187715716346378804264213849)
      ·
        refine ⟨140786787259784103198160387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187715716346378804264213849 140786787259784103198160387)
        ·
          refine ⟨211180180889676154797240581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140786787259784103198160387 211180180889676154797240581)
          ·
            refine ⟨39596283916814279024482609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 211180180889676154797240581 39596283916814279024482609)
            ·
              refine ⟨29697212937610709268361957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39596283916814279024482609 29697212937610709268361957)
              ·
                refine ⟨5568227425802007987817867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29697212937610709268361957 5568227425802007987817867)
                ·
                  refine ⟨8352341138703011981726801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5568227425802007987817867 8352341138703011981726801)
                  ·
                    refine ⟨6264255854027258986295101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8352341138703011981726801 6264255854027258986295101)
                    ·
                      refine ⟨2349095945260222119860663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6264255854027258986295101 2349095945260222119860663)
                      ·
                        rfl

theorem cell23_4574848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_4574848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574848 prefixEnd_4574848 := by exact prefixLift 4574848
  have htrace : WordTrace (prefixWord ++ tailWord_4574848) baseStart_4574848 baseEnd_4574848 := by
    simpa [prefixWord, tailWord_4574848, baseEnd_4574848] using wordTrace_append hprefix tailTrace_4574848
  have hstable : (prefixWord ++ tailWord_4574848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574848).length < 2 ^ (prefixWord ++ tailWord_4574848).sum := by decide
  have hdescent : baseEnd_4574848 < baseStart_4574848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574858 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_4574858 : Nat := 118140960795 + 4574858 * 2 ^ 59
def prefixEnd_4574858 : Nat := 4983230072969 + 3 ^ 40 * 4574858 * 2
def baseEnd_4574858 : Nat := 2349101080066767080735617

theorem tailTrace_4574858 : CollatzResearch.WordTrace tailWord_4574858 prefixEnd_4574858 2349101080066767080735617 := by
  unfold tailWord_4574858
  simp only [CollatzResearch.WordTrace]
  refine ⟨41714694815019566096791307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111239186173385509591443485 41714694815019566096791307)
  ·
    refine ⟨62572042222529349145186961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41714694815019566096791307 62572042222529349145186961)
    ·
      refine ⟨46929031666897011858890221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62572042222529349145186961 46929031666897011858890221)
      ·
        refine ⟨17598386875086379447083833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46929031666897011858890221 17598386875086379447083833)
        ·
          refine ⟨13198790156314784585312875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17598386875086379447083833 13198790156314784585312875)
          ·
            refine ⟨19798185234472176877969313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13198790156314784585312875 19798185234472176877969313)
            ·
              refine ⟨14848638925854132658476985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19798185234472176877969313 14848638925854132658476985)
              ·
                refine ⟨11136479194390599493857739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14848638925854132658476985 11136479194390599493857739)
                ·
                  refine ⟨16704718791585899240786609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11136479194390599493857739 16704718791585899240786609)
                  ·
                    refine ⟨12528539093689424430589957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16704718791585899240786609 12528539093689424430589957)
                    ·
                      refine ⟨2349101080066767080735617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12528539093689424430589957 2349101080066767080735617)
                      ·
                        rfl

theorem cell23_4574858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_4574858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574858 prefixEnd_4574858 := by exact prefixLift 4574858
  have htrace : WordTrace (prefixWord ++ tailWord_4574858) baseStart_4574858 baseEnd_4574858 := by
    simpa [prefixWord, tailWord_4574858, baseEnd_4574858] using wordTrace_append hprefix tailTrace_4574858
  have hstable : (prefixWord ++ tailWord_4574858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574858).length < 2 ^ (prefixWord ++ tailWord_4574858).sum := by decide
  have hdescent : baseEnd_4574858 < baseStart_4574858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574862 : List Nat := [4, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4]
def baseStart_4574862 : Nat := 118140960795 + 4574862 * 2 ^ 59
def prefixEnd_4574862 : Nat := 4983230072969 + 3 ^ 40 * 4574862 * 2
def baseEnd_4574862 : Nat := 2349103133989385065085599

theorem tailTrace_4574862 : CollatzResearch.WordTrace tailWord_4574862 prefixEnd_4574862 2349103133989385065085599 := by
  unfold tailWord_4574862
  simp only [CollatzResearch.WordTrace]
  refine ⟨20857365644007971633788855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111239283434709182046873893 20857365644007971633788855)
  ·
    refine ⟨31286048466011957450683283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20857365644007971633788855 31286048466011957450683283)
    ·
      refine ⟨46929072699017936176024925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31286048466011957450683283 46929072699017936176024925)
      ·
        refine ⟨17598402262131726066009347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46929072699017936176024925 17598402262131726066009347)
        ·
          refine ⟨26397603393197589099014021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17598402262131726066009347 26397603393197589099014021)
          ·
            refine ⟨4949550636224547956065129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26397603393197589099014021 4949550636224547956065129)
            ·
              refine ⟨3712162977168410967048847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4949550636224547956065129 3712162977168410967048847)
              ·
                refine ⟨5568244465752616450573271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3712162977168410967048847 5568244465752616450573271)
                ·
                  refine ⟨8352366698628924675859907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5568244465752616450573271 8352366698628924675859907)
                  ·
                    refine ⟨12528550047943387013789861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8352366698628924675859907 12528550047943387013789861)
                    ·
                      refine ⟨2349103133989385065085599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12528550047943387013789861 2349103133989385065085599)
                      ·
                        rfl

theorem cell23_4574862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_4574862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574862 prefixEnd_4574862 := by exact prefixLift 4574862
  have htrace : WordTrace (prefixWord ++ tailWord_4574862) baseStart_4574862 baseEnd_4574862 := by
    simpa [prefixWord, tailWord_4574862, baseEnd_4574862] using wordTrace_append hprefix tailTrace_4574862
  have hstable : (prefixWord ++ tailWord_4574862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574862).length < 2 ^ (prefixWord ++ tailWord_4574862).sum := by decide
  have hdescent : baseEnd_4574862 < baseStart_4574862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574868 : List Nat := [2, 4, 2, 2, 2, 1, 10]
def baseStart_4574868 : Nat := 118140960795 + 4574868 * 2 ^ 59
def prefixEnd_4574868 : Nat := 4983230072969 + 3 ^ 40 * 4574868 * 2
def baseEnd_4574868 : Nat := 29001311294732247427291

theorem tailTrace_4574868 : CollatzResearch.WordTrace tailWord_4574868 prefixEnd_4574868 29001311294732247427291 := by
  unfold tailWord_4574868
  simp only [CollatzResearch.WordTrace]
  refine ⟨83429571995021018047514629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111239429326694690730019505 83429571995021018047514629)
  ·
    refine ⟨15643044749066440883908993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83429571995021018047514629 15643044749066440883908993)
    ·
      refine ⟨11732283561799830662931745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15643044749066440883908993 11732283561799830662931745)
      ·
        refine ⟨8799212671349872997198809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11732283561799830662931745 8799212671349872997198809)
        ·
          refine ⟨6599409503512404747899107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8799212671349872997198809 6599409503512404747899107)
          ·
            refine ⟨9899114255268607121848661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6599409503512404747899107 9899114255268607121848661)
            ·
              refine ⟨29001311294732247427291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9899114255268607121848661 29001311294732247427291)
              ·
                rfl

theorem cell23_4574868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 10].length) (baseStart_4574868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574868 prefixEnd_4574868 := by exact prefixLift 4574868
  have htrace : WordTrace (prefixWord ++ tailWord_4574868) baseStart_4574868 baseEnd_4574868 := by
    simpa [prefixWord, tailWord_4574868, baseEnd_4574868] using wordTrace_append hprefix tailTrace_4574868
  have hstable : (prefixWord ++ tailWord_4574868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574868).length < 2 ^ (prefixWord ++ tailWord_4574868).sum := by decide
  have hdescent : baseEnd_4574868 < baseStart_4574868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574879 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 3, 2, 2]
def baseStart_4574879 : Nat := 118140960795 + 4574879 * 2 ^ 59
def prefixEnd_4574879 : Nat := 4983230072969 + 3 ^ 40 * 4574879 * 2
def baseEnd_4574879 : Nat := 2349111863160511498573021

theorem tailTrace_4574879 : CollatzResearch.WordTrace tailWord_4574879 prefixEnd_4574879 2349111863160511498573021 := by
  unfold tailWord_4574879
  simp only [CollatzResearch.WordTrace]
  refine ⟨166859545193002184973679691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111239696795334789982453127 166859545193002184973679691)
  ·
    refine ⟨250289317789503277460519537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166859545193002184973679691 250289317789503277460519537)
    ·
      refine ⟨187716988342127458095389653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250289317789503277460519537 187716988342127458095389653)
      ·
        refine ⟨4399616914268612299110695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 187716988342127458095389653 4399616914268612299110695)
        ·
          refine ⟨6599425371402918448666043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4399616914268612299110695 6599425371402918448666043)
          ·
            refine ⟨9899138057104377672999065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6599425371402918448666043 9899138057104377672999065)
            ·
              refine ⟨7424353542828283254749299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9899138057104377672999065 7424353542828283254749299)
              ·
                refine ⟨11136530314242424882123949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7424353542828283254749299 11136530314242424882123949)
                ·
                  refine ⟨4176198867840909330796481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11136530314242424882123949 4176198867840909330796481)
                  ·
                    refine ⟨3132149150880681998097361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4176198867840909330796481 3132149150880681998097361)
                    ·
                      refine ⟨2349111863160511498573021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3132149150880681998097361 2349111863160511498573021)
                      ·
                        rfl

theorem cell23_4574879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_4574879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574879 prefixEnd_4574879 := by exact prefixLift 4574879
  have htrace : WordTrace (prefixWord ++ tailWord_4574879) baseStart_4574879 baseEnd_4574879 := by
    simpa [prefixWord, tailWord_4574879, baseEnd_4574879] using wordTrace_append hprefix tailTrace_4574879
  have hstable : (prefixWord ++ tailWord_4574879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574879).length < 2 ^ (prefixWord ++ tailWord_4574879).sum := by decide
  have hdescent : baseEnd_4574879 < baseStart_4574879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574902 : List Nat := [5, 1, 3, 1, 1, 3, 2, 7]
def baseStart_4574902 : Nat := 118140960795 + 4574902 * 2 ^ 59
def prefixEnd_4574902 : Nat := 4983230072969 + 3 ^ 40 * 4574902 * 2
def baseEnd_4574902 : Nat := 87004580489465366984645

theorem tailTrace_4574902 : CollatzResearch.WordTrace tailWord_4574902 prefixEnd_4574902 87004580489465366984645 := by
  unfold tailWord_4574902
  simp only [CollatzResearch.WordTrace]
  refine ⟨10428774004494928743860435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111240256047945906601177973 10428774004494928743860435)
  ·
    refine ⟨15643161006742393115790653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10428774004494928743860435 15643161006742393115790653)
    ·
      refine ⟨5866185377528397418421495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15643161006742393115790653 5866185377528397418421495)
      ·
        refine ⟨8799278066292596127632243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5866185377528397418421495 8799278066292596127632243)
        ·
          refine ⟨13198917099438894191448365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8799278066292596127632243 13198917099438894191448365)
          ·
            refine ⟨4949593912289585321793137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13198917099438894191448365 4949593912289585321793137)
            ·
              refine ⟨3712195434217188991344853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4949593912289585321793137 3712195434217188991344853)
              ·
                refine ⟨87004580489465366984645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3712195434217188991344853 87004580489465366984645)
                ·
                  rfl

theorem cell23_4574902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_4574902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574902 prefixEnd_4574902 := by exact prefixLift 4574902
  have htrace : WordTrace (prefixWord ++ tailWord_4574902) baseStart_4574902 baseEnd_4574902 := by
    simpa [prefixWord, tailWord_4574902, baseEnd_4574902] using wordTrace_append hprefix tailTrace_4574902
  have hstable : (prefixWord ++ tailWord_4574902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574902).length < 2 ^ (prefixWord ++ tailWord_4574902).sum := by decide
  have hdescent : baseEnd_4574902 < baseStart_4574902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574905 : List Nat := [1, 2, 1, 4, 1, 1, 3, 4, 1, 3, 2]
def baseStart_4574905 : Nat := 118140960795 + 4574905 * 2 ^ 59
def prefixEnd_4574905 : Nat := 4983230072969 + 3 ^ 40 * 4574905 * 2
def baseEnd_4574905 : Nat := 2349125213657528396847901

theorem tailTrace_4574905 : CollatzResearch.WordTrace tailWord_4574905 prefixEnd_4574905 2349125213657528396847901 := by
  unfold tailWord_4574905
  simp only [CollatzResearch.WordTrace]
  refine ⟨166860493490907991414126169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111240328993938660942750779 166860493490907991414126169)
  ·
    refine ⟨125145370118180993560594627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166860493490907991414126169 125145370118180993560594627)
    ·
      refine ⟨187718055177271490340891941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125145370118180993560594627 187718055177271490340891941)
      ·
        refine ⟨35197135345738404438917239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187718055177271490340891941 35197135345738404438917239)
        ·
          refine ⟨52795703018607606658375859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35197135345738404438917239 52795703018607606658375859)
          ·
            refine ⟨79193554527911409987563789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52795703018607606658375859 79193554527911409987563789)
            ·
              refine ⟨29697582947966778745336421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79193554527911409987563789 29697582947966778745336421)
              ·
                refine ⟨5568296802743771014750579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29697582947966778745336421 5568296802743771014750579)
                ·
                  refine ⟨8352445204115656522125869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5568296802743771014750579 8352445204115656522125869)
                  ·
                    refine ⟨3132166951543371195797201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8352445204115656522125869 3132166951543371195797201)
                    ·
                      refine ⟨2349125213657528396847901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3132166951543371195797201 2349125213657528396847901)
                      ·
                        rfl

theorem cell23_4574905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_4574905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574905 prefixEnd_4574905 := by exact prefixLift 4574905
  have htrace : WordTrace (prefixWord ++ tailWord_4574905) baseStart_4574905 baseEnd_4574905 := by
    simpa [prefixWord, tailWord_4574905, baseEnd_4574905] using wordTrace_append hprefix tailTrace_4574905
  have hstable : (prefixWord ++ tailWord_4574905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574905).length < 2 ^ (prefixWord ++ tailWord_4574905).sum := by decide
  have hdescent : baseEnd_4574905 < baseStart_4574905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574935 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 4, 2, 2]
def baseStart_4574935 : Nat := 118140960795 + 4574935 * 2 ^ 59
def prefixEnd_4574935 : Nat := 4983230072969 + 3 ^ 40 * 4574935 * 2
def baseEnd_4574935 : Nat := 2349140618077163279472763

theorem tailTrace_4574935 : CollatzResearch.WordTrace tailWord_4574935 prefixEnd_4574935 2349140618077163279472763 := by
  unfold tailWord_4574935
  simp only [CollatzResearch.WordTrace]
  refine ⟨166861587680799306537718259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111241058453866204358478839 166861587680799306537718259)
  ·
    refine ⟨250292381521198959806577389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166861587680799306537718259 250292381521198959806577389)
    ·
      refine ⟨93859643070449609927466521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250292381521198959806577389 93859643070449609927466521)
      ·
        refine ⟨70394732302837207445599891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93859643070449609927466521 70394732302837207445599891)
        ·
          refine ⟨105592098454255811168399837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70394732302837207445599891 105592098454255811168399837)
          ·
            refine ⟨39597036920345929188149939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105592098454255811168399837 39597036920345929188149939)
            ·
              refine ⟨59395555380518893782224909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39597036920345929188149939 59395555380518893782224909)
              ·
                refine ⟨22273333267694585168334341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59395555380518893782224909 22273333267694585168334341)
                ·
                  refine ⟨4176249987692734719062689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22273333267694585168334341 4176249987692734719062689)
                  ·
                    refine ⟨3132187490769551039297017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4176249987692734719062689 3132187490769551039297017)
                    ·
                      refine ⟨2349140618077163279472763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3132187490769551039297017 2349140618077163279472763)
                      ·
                        rfl

theorem cell23_4574935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_4574935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574935 prefixEnd_4574935 := by exact prefixLift 4574935
  have htrace : WordTrace (prefixWord ++ tailWord_4574935) baseStart_4574935 baseEnd_4574935 := by
    simpa [prefixWord, tailWord_4574935, baseEnd_4574935] using wordTrace_append hprefix tailTrace_4574935
  have hstable : (prefixWord ++ tailWord_4574935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574935).length < 2 ^ (prefixWord ++ tailWord_4574935).sum := by decide
  have hdescent : baseEnd_4574935 < baseStart_4574935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4574988 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 2, 5]
def baseStart_4574988 : Nat := 118140960795 + 4574988 * 2 ^ 59
def prefixEnd_4574988 : Nat := 4983230072969 + 3 ^ 40 * 4574988 * 2
def baseEnd_4574988 : Nat := 783055944183950524036673

theorem tailTrace_4574988 : CollatzResearch.WordTrace tailWord_4574988 prefixEnd_4574988 783055944183950524036673 := by
  unfold tailWord_4574988
  simp only [CollatzResearch.WordTrace]
  refine ⟨83431760374803648294698809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111242347166404864392931745 83431760374803648294698809)
  ·
    refine ⟨62573820281102736221024107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83431760374803648294698809 62573820281102736221024107)
    ·
      refine ⟨93860730421654104331536161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62573820281102736221024107 93860730421654104331536161)
      ·
        refine ⟨70395547816240578248652121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93860730421654104331536161 70395547816240578248652121)
        ·
          refine ⟨52796660862180433686489091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70395547816240578248652121 52796660862180433686489091)
          ·
            refine ⟨79194991293270650529733637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52796660862180433686489091 79194991293270650529733637)
            ·
              refine ⟨14849060867488246974325057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79194991293270650529733637 14849060867488246974325057)
              ·
                refine ⟨11136795650616185230743793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14849060867488246974325057 11136795650616185230743793)
                ·
                  refine ⟨8352596737962138923057845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11136795650616185230743793 8352596737962138923057845)
                  ·
                    refine ⟨783055944183950524036673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8352596737962138923057845 783055944183950524036673)
                    ·
                      rfl

theorem cell23_4574988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_4574988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4574988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4574988 prefixEnd_4574988 := by exact prefixLift 4574988
  have htrace : WordTrace (prefixWord ++ tailWord_4574988) baseStart_4574988 baseEnd_4574988 := by
    simpa [prefixWord, tailWord_4574988, baseEnd_4574988] using wordTrace_append hprefix tailTrace_4574988
  have hstable : (prefixWord ++ tailWord_4574988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4574988).length < 2 ^ (prefixWord ++ tailWord_4574988).sum := by decide
  have hdescent : baseEnd_4574988 < baseStart_4574988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4574988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575008 : List Nat := [2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 4]
def baseStart_4575008 : Nat := 118140960795 + 4575008 * 2 ^ 59
def prefixEnd_4575008 : Nat := 4983230072969 + 3 ^ 40 * 4575008 * 2
def baseEnd_4575008 : Nat := 2349178102164941493859927

theorem tailTrace_4575008 : CollatzResearch.WordTrace tailWord_4575008 prefixEnd_4575008 2349178102164941493859927 := by
  unfold tailWord_4575008
  simp only [CollatzResearch.WordTrace]
  refine ⟨83432125104767420002562839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111242833473023226670083785 83432125104767420002562839)
  ·
    refine ⟨125148187657151130003844259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83432125104767420002562839 125148187657151130003844259)
    ·
      refine ⟨187722281485726695005766389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125148187657151130003844259 187722281485726695005766389)
      ·
        refine ⟨17598963889286877656790599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 187722281485726695005766389 17598963889286877656790599)
        ·
          refine ⟨26398445833930316485185899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17598963889286877656790599 26398445833930316485185899)
          ·
            refine ⟨39597668750895474727778849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26398445833930316485185899 39597668750895474727778849)
            ·
              refine ⟨29698251563171606045834137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39597668750895474727778849 29698251563171606045834137)
              ·
                refine ⟨22273688672378704534375603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29698251563171606045834137 22273688672378704534375603)
                ·
                  refine ⟨33410533008568056801563405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22273688672378704534375603 33410533008568056801563405)
                  ·
                    refine ⟨12528949878213021300586277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33410533008568056801563405 12528949878213021300586277)
                    ·
                      refine ⟨2349178102164941493859927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12528949878213021300586277 2349178102164941493859927)
                      ·
                        rfl

theorem cell23_4575008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_4575008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575008 prefixEnd_4575008 := by exact prefixLift 4575008
  have htrace : WordTrace (prefixWord ++ tailWord_4575008) baseStart_4575008 baseEnd_4575008 := by
    simpa [prefixWord, tailWord_4575008, baseEnd_4575008] using wordTrace_append hprefix tailTrace_4575008
  have hstable : (prefixWord ++ tailWord_4575008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575008).length < 2 ^ (prefixWord ++ tailWord_4575008).sum := by decide
  have hdescent : baseEnd_4575008 < baseStart_4575008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575025 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 2, 1, 4]
def baseStart_4575025 : Nat := 118140960795 + 4575025 * 2 ^ 59
def prefixEnd_4575025 : Nat := 4983230072969 + 3 ^ 40 * 4575025 * 2
def baseEnd_4575025 : Nat := 2349186831336067927347349

theorem tailTrace_4575025 : CollatzResearch.WordTrace tailWord_4575025 prefixEnd_4575025 2349186831336067927347349 := by
  unfold tailWord_4575025
  simp only [CollatzResearch.WordTrace]
  refine ⟨166864870250473251908494529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111243246833648834605663019 166864870250473251908494529)
  ·
    refine ⟨125148652687854938931370897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166864870250473251908494529 125148652687854938931370897)
    ·
      refine ⟨93861489515891204198528173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125148652687854938931370897 93861489515891204198528173)
      ·
        refine ⟨35198058568459201574448065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93861489515891204198528173 35198058568459201574448065)
        ·
          refine ⟨26398543926344401180836049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35198058568459201574448065 26398543926344401180836049)
          ·
            refine ⟨19798907944758300885627037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26398543926344401180836049 19798907944758300885627037)
            ·
              refine ⟨7424590479284362832110139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19798907944758300885627037 7424590479284362832110139)
              ·
                refine ⟨11136885718926544248165209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7424590479284362832110139 11136885718926544248165209)
                ·
                  refine ⟨8352664289194908186123907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11136885718926544248165209 8352664289194908186123907)
                  ·
                    refine ⟨12528996433792362279185861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8352664289194908186123907 12528996433792362279185861)
                    ·
                      refine ⟨2349186831336067927347349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12528996433792362279185861 2349186831336067927347349)
                      ·
                        rfl

theorem cell23_4575025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_4575025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575025 prefixEnd_4575025 := by exact prefixLift 4575025
  have htrace : WordTrace (prefixWord ++ tailWord_4575025) baseStart_4575025 baseEnd_4575025 := by
    simpa [prefixWord, tailWord_4575025, baseEnd_4575025] using wordTrace_append hprefix tailTrace_4575025
  have hstable : (prefixWord ++ tailWord_4575025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575025).length < 2 ^ (prefixWord ++ tailWord_4575025).sum := by decide
  have hdescent : baseEnd_4575025 < baseStart_4575025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575048 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 8]
def baseStart_4575048 : Nat := 118140960795 + 4575048 * 2 ^ 59
def prefixEnd_4575048 : Nat := 4983230072969 + 3 ^ 40 * 4575048 * 2
def baseEnd_4575048 : Nat := 261022071265680148595527

theorem tailTrace_4575048 : CollatzResearch.WordTrace tailWord_4575048 prefixEnd_4575048 261022071265680148595527 := by
  unfold tailWord_4575048
  simp only [CollatzResearch.WordTrace]
  refine ⟨83432854564694963418290899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111243806086259951224387865 83432854564694963418290899)
  ·
    refine ⟨125149281847042445127436349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83432854564694963418290899 125149281847042445127436349)
    ·
      refine ⟨46930980692640916922788631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125149281847042445127436349 46930980692640916922788631)
      ·
        refine ⟨70396471038961375384182947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46930980692640916922788631 70396471038961375384182947)
        ·
          refine ⟨105594706558442063076274421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70396471038961375384182947 105594706558442063076274421)
          ·
            refine ⟨9899503739853943413400727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105594706558442063076274421 9899503739853943413400727)
            ·
              refine ⟨14849255609780915120101091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9899503739853943413400727 14849255609780915120101091)
              ·
                refine ⟨22273883414671372680151637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14849255609780915120101091 22273883414671372680151637)
                ·
                  refine ⟨261022071265680148595527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22273883414671372680151637 261022071265680148595527)
                  ·
                    rfl

theorem cell23_4575048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 8].length) (baseStart_4575048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575048 prefixEnd_4575048 := by exact prefixLift 4575048
  have htrace : WordTrace (prefixWord ++ tailWord_4575048) baseStart_4575048 baseEnd_4575048 := by
    simpa [prefixWord, tailWord_4575048, baseEnd_4575048] using wordTrace_append hprefix tailTrace_4575048
  have hstable : (prefixWord ++ tailWord_4575048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575048).length < 2 ^ (prefixWord ++ tailWord_4575048).sum := by decide
  have hdescent : baseEnd_4575048 < baseStart_4575048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575052 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 3, 4]
def baseStart_4575052 : Nat := 118140960795 + 4575052 * 2 ^ 59
def prefixEnd_4575052 : Nat := 4983230072969 + 3 ^ 40 * 4575052 * 2
def baseEnd_4575052 : Nat := 783066898437913107236575

theorem tailTrace_4575052 : CollatzResearch.WordTrace tailWord_4575052 prefixEnd_4575052 783066898437913107236575 := by
  unfold tailWord_4575052
  simp only [CollatzResearch.WordTrace]
  refine ⟨83432927510687717759863705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111243903347583623679818273 83432927510687717759863705)
  ·
    refine ⟨62574695633015788319897779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83432927510687717759863705 62574695633015788319897779)
    ·
      refine ⟨93862043449523682479846669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62574695633015788319897779 93862043449523682479846669)
      ·
        refine ⟨35198266293571380929942501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93862043449523682479846669 35198266293571380929942501)
        ·
          refine ⟨6599674930044633924364219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35198266293571380929942501 6599674930044633924364219)
          ·
            refine ⟨9899512395066950886546329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6599674930044633924364219 9899512395066950886546329)
            ·
              refine ⟨7424634296300213164909747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9899512395066950886546329 7424634296300213164909747)
              ·
                refine ⟨11136951444450319747364621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7424634296300213164909747 11136951444450319747364621)
                ·
                  refine ⟨4176356791668869905261733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11136951444450319747364621 4176356791668869905261733)
                  ·
                    refine ⟨783066898437913107236575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4176356791668869905261733 783066898437913107236575)
                    ·
                      rfl

theorem cell23_4575052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_4575052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575052 prefixEnd_4575052 := by exact prefixLift 4575052
  have htrace : WordTrace (prefixWord ++ tailWord_4575052) baseStart_4575052 baseEnd_4575052 := by
    simpa [prefixWord, tailWord_4575052, baseEnd_4575052] using wordTrace_append hprefix tailTrace_4575052
  have hstable : (prefixWord ++ tailWord_4575052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575052).length < 2 ^ (prefixWord ++ tailWord_4575052).sum := by decide
  have hdescent : baseEnd_4575052 < baseStart_4575052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575065 : List Nat := [1, 2, 1, 2, 2, 3, 5, 1, 6]
def baseStart_4575065 : Nat := 118140960795 + 4575065 * 2 ^ 59
def prefixEnd_4575065 : Nat := 4983230072969 + 3 ^ 40 * 4575065 * 2
def baseEnd_4575065 : Nat := 261023041173583085649685

theorem tailTrace_4575065 : CollatzResearch.WordTrace tailWord_4575065 prefixEnd_4575065 261023041173583085649685 := by
  unfold tailWord_4575065
  simp only [CollatzResearch.WordTrace]
  refine ⟨166866329170328338739950649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111244219446885559159967099 166866329170328338739950649)
  ·
    refine ⟨125149746877746254054962987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166866329170328338739950649 125149746877746254054962987)
    ·
      refine ⟨187724620316619381082444481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125149746877746254054962987 187724620316619381082444481)
      ·
        refine ⟨140793465237464535811833361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187724620316619381082444481 140793465237464535811833361)
        ·
          refine ⟨105595098928098401858875021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140793465237464535811833361 105595098928098401858875021)
          ·
            refine ⟨39598162098036900697078133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105595098928098401858875021 39598162098036900697078133)
            ·
              refine ⟨3712327696690959440351075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39598162098036900697078133 3712327696690959440351075)
              ·
                refine ⟨5568491545036439160526613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3712327696690959440351075 5568491545036439160526613)
                ·
                  refine ⟨261023041173583085649685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5568491545036439160526613 261023041173583085649685)
                  ·
                    rfl

theorem cell23_4575065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 6].length) (baseStart_4575065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575065 prefixEnd_4575065 := by exact prefixLift 4575065
  have htrace : WordTrace (prefixWord ++ tailWord_4575065) baseStart_4575065 baseEnd_4575065 := by
    simpa [prefixWord, tailWord_4575065, baseEnd_4575065] using wordTrace_append hprefix tailTrace_4575065
  have hstable : (prefixWord ++ tailWord_4575065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575065).length < 2 ^ (prefixWord ++ tailWord_4575065).sum := by decide
  have hdescent : baseEnd_4575065 < baseStart_4575065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575086 : List Nat := [4, 1, 2, 3, 1, 3, 1, 3, 1, 4]
def baseStart_4575086 : Nat := 118140960795 + 4575086 * 2 ^ 59
def prefixEnd_4575086 : Nat := 4983230072969 + 3 ^ 40 * 4575086 * 2
def baseEnd_4575086 : Nat := 783072717885330729561523

theorem tailTrace_4575086 : CollatzResearch.WordTrace tailWord_4575086 prefixEnd_4575086 783072717885330729561523 := by
  unfold tailWord_4575086
  simp only [CollatzResearch.WordTrace]
  refine ⟨20858386887906532415808139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111244730068834839550976741 20858386887906532415808139)
  ·
    refine ⟨31287580331859798623712209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20858386887906532415808139 31287580331859798623712209)
    ·
      refine ⟨23465685248894848967784157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31287580331859798623712209 23465685248894848967784157)
      ·
        refine ⟨8799631968335568362919059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23465685248894848967784157 8799631968335568362919059)
        ·
          refine ⟨13199447952503352544378589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8799631968335568362919059 13199447952503352544378589)
          ·
            refine ⟨4949792982188757204141971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13199447952503352544378589 4949792982188757204141971)
            ·
              refine ⟨7424689473283135806212957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4949792982188757204141971 7424689473283135806212957)
              ·
                refine ⟨2784258552481175927329859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7424689473283135806212957 2784258552481175927329859)
                ·
                  refine ⟨4176387828721763890994789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2784258552481175927329859 4176387828721763890994789)
                  ·
                    refine ⟨783072717885330729561523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4176387828721763890994789 783072717885330729561523)
                    ·
                      rfl

theorem cell23_4575086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_4575086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575086 prefixEnd_4575086 := by exact prefixLift 4575086
  have htrace : WordTrace (prefixWord ++ tailWord_4575086) baseStart_4575086 baseEnd_4575086 := by
    simpa [prefixWord, tailWord_4575086, baseEnd_4575086] using wordTrace_append hprefix tailTrace_4575086
  have hstable : (prefixWord ++ tailWord_4575086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575086).length < 2 ^ (prefixWord ++ tailWord_4575086).sum := by decide
  have hdescent : baseEnd_4575086 < baseStart_4575086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575132 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4575132 : Nat := 118140960795 + 4575132 * 2 ^ 59
def prefixEnd_4575132 : Nat := 4983230072969 + 3 ^ 40 * 4575132 * 2
def baseEnd_4575132 : Nat := 2349241773766099008709357

theorem tailTrace_4575132 : CollatzResearch.WordTrace tailWord_4575132 prefixEnd_4575132 2349241773766099008709357 := by
  unfold tailWord_4575132
  simp only [CollatzResearch.WordTrace]
  refine ⟨83434386430542804591319825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111245848574057072788426433 83434386430542804591319825)
  ·
    refine ⟨62575789822907103443489869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83434386430542804591319825 62575789822907103443489869)
    ·
      refine ⟨23465921183590163791308701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62575789822907103443489869 23465921183590163791308701)
      ·
        refine ⟨8799720443846311421740763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23465921183590163791308701 8799720443846311421740763)
        ·
          refine ⟨13199580665769467132611145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8799720443846311421740763 13199580665769467132611145)
          ·
            refine ⟨9899685499327100349458359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13199580665769467132611145 9899685499327100349458359)
            ·
              refine ⟨14849528248990650524187539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9899685499327100349458359 14849528248990650524187539)
              ·
                refine ⟨22274292373485975786281309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14849528248990650524187539 22274292373485975786281309)
                ·
                  refine ⟨8352859640057240919855491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22274292373485975786281309 8352859640057240919855491)
                  ·
                    refine ⟨12529289460085861379783237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8352859640057240919855491 12529289460085861379783237)
                    ·
                      refine ⟨2349241773766099008709357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12529289460085861379783237 2349241773766099008709357)
                      ·
                        rfl

theorem cell23_4575132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4575132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575132 prefixEnd_4575132 := by exact prefixLift 4575132
  have htrace : WordTrace (prefixWord ++ tailWord_4575132) baseStart_4575132 baseEnd_4575132 := by
    simpa [prefixWord, tailWord_4575132, baseEnd_4575132] using wordTrace_append hprefix tailTrace_4575132
  have hstable : (prefixWord ++ tailWord_4575132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575132).length < 2 ^ (prefixWord ++ tailWord_4575132).sum := by decide
  have hdescent : baseEnd_4575132 < baseStart_4575132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575168 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 1, 9]
def baseStart_4575168 : Nat := 118140960795 + 4575168 * 2 ^ 59
def prefixEnd_4575168 : Nat := 4983230072969 + 3 ^ 40 * 4575168 * 2
def baseEnd_4575168 : Nat := 783086753023220289286397

theorem tailTrace_4575168 : CollatzResearch.WordTrace tailWord_4575168 prefixEnd_4575168 783086753023220289286397 := by
  unfold tailWord_4575168
  simp only [CollatzResearch.WordTrace]
  refine ⟨83435042944477593665475079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111246723925970124887300105 83435042944477593665475079)
  ·
    refine ⟨125152564416716390498212619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83435042944477593665475079 125152564416716390498212619)
    ·
      refine ⟨187728846625074585747318929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125152564416716390498212619 187728846625074585747318929)
      ·
        refine ⟨140796634968805939310489197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187728846625074585747318929 140796634968805939310489197)
        ·
          refine ⟨52798738113302227241433449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140796634968805939310489197 52798738113302227241433449)
          ·
            refine ⟨39599053584976670431075087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52798738113302227241433449 39599053584976670431075087)
            ·
              refine ⟨59398580377465005646612631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39599053584976670431075087 59398580377465005646612631)
              ·
                refine ⟨89097870566197508469918947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59398580377465005646612631 89097870566197508469918947)
                ·
                  refine ⟨133646805849296262704878421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89097870566197508469918947 133646805849296262704878421)
                  ·
                    refine ⟨783086753023220289286397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 133646805849296262704878421 783086753023220289286397)
                    ·
                      rfl

theorem cell23_4575168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_4575168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575168 prefixEnd_4575168 := by exact prefixLift 4575168
  have htrace : WordTrace (prefixWord ++ tailWord_4575168) baseStart_4575168 baseEnd_4575168 := by
    simpa [prefixWord, tailWord_4575168, baseEnd_4575168] using wordTrace_append hprefix tailTrace_4575168
  have hstable : (prefixWord ++ tailWord_4575168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575168).length < 2 ^ (prefixWord ++ tailWord_4575168).sum := by decide
  have hdescent : baseEnd_4575168 < baseStart_4575168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575182 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_4575182 : Nat := 118140960795 + 4575182 * 2 ^ 59
def prefixEnd_4575182 : Nat := 4983230072969 + 3 ^ 40 * 4575182 * 2
def baseEnd_4575182 : Nat := 2349267447798823813084127

theorem tailTrace_4575182 : CollatzResearch.WordTrace tailWord_4575182 prefixEnd_4575182 2349267447798823813084127 := by
  unfold tailWord_4575182
  simp only [CollatzResearch.WordTrace]
  refine ⟨20858824563863058465244975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111247064340602978481306533 20858824563863058465244975)
  ·
    refine ⟨31288236845794587697867463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20858824563863058465244975 31288236845794587697867463)
    ·
      refine ⟨46932355268691881546801195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31288236845794587697867463 46932355268691881546801195)
      ·
        refine ⟨70398532903037822320201793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46932355268691881546801195 70398532903037822320201793)
        ·
          refine ⟨52798899677278366740151345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70398532903037822320201793 52798899677278366740151345)
          ·
            refine ⟨39599174757958775055113509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52798899677278366740151345 39599174757958775055113509)
            ·
              refine ⟨7424845267117270322833783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39599174757958775055113509 7424845267117270322833783)
              ·
                refine ⟨11137267900675905484250675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7424845267117270322833783 11137267900675905484250675)
                ·
                  refine ⟨16705901851013858226376013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11137267900675905484250675 16705901851013858226376013)
                  ·
                    refine ⟨6264713194130196834891005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16705901851013858226376013 6264713194130196834891005)
                    ·
                      refine ⟨2349267447798823813084127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6264713194130196834891005 2349267447798823813084127)
                      ·
                        rfl

theorem cell23_4575182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_4575182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575182 prefixEnd_4575182 := by exact prefixLift 4575182
  have htrace : WordTrace (prefixWord ++ tailWord_4575182) baseStart_4575182 baseEnd_4575182 := by
    simpa [prefixWord, tailWord_4575182, baseEnd_4575182] using wordTrace_append hprefix tailTrace_4575182
  have hstable : (prefixWord ++ tailWord_4575182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575182).length < 2 ^ (prefixWord ++ tailWord_4575182).sum := by decide
  have hdescent : baseEnd_4575182 < baseStart_4575182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575192 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 3, 3, 2]
def baseStart_4575192 : Nat := 118140960795 + 4575192 * 2 ^ 59
def prefixEnd_4575192 : Nat := 4983230072969 + 3 ^ 40 * 4575192 * 2
def baseEnd_4575192 : Nat := 2349272582605368773959081

theorem tailTrace_4575192 : CollatzResearch.WordTrace tailWord_4575192 prefixEnd_4575192 2349272582605368773959081 := by
  unfold tailWord_4575192
  simp only [CollatzResearch.WordTrace]
  refine ⟨83435480620434119714911915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111247307493912159619882553 83435480620434119714911915)
  ·
    refine ⟨125153220930651179572367873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83435480620434119714911915 125153220930651179572367873)
    ·
      refine ⟨93864915697988384679275905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125153220930651179572367873 93864915697988384679275905)
      ·
        refine ⟨70398686773491288509456929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93864915697988384679275905 70398686773491288509456929)
        ·
          refine ⟨52799015080118466382092697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70398686773491288509456929 52799015080118466382092697)
          ·
            refine ⟨39599261310088849786569523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52799015080118466382092697 39599261310088849786569523)
            ·
              refine ⟨59398891965133274679854285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39599261310088849786569523 59398891965133274679854285)
              ·
                refine ⟨22274584486924978004945357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59398891965133274679854285 22274584486924978004945357)
                ·
                  refine ⟨8352969182596866751854509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22274584486924978004945357 8352969182596866751854509)
                  ·
                    refine ⟨3132363443473825031945441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8352969182596866751854509 3132363443473825031945441)
                    ·
                      refine ⟨2349272582605368773959081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3132363443473825031945441 2349272582605368773959081)
                      ·
                        rfl

theorem cell23_4575192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_4575192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575192 prefixEnd_4575192 := by exact prefixLift 4575192
  have htrace : WordTrace (prefixWord ++ tailWord_4575192) baseStart_4575192 baseEnd_4575192 := by
    simpa [prefixWord, tailWord_4575192, baseEnd_4575192] using wordTrace_append hprefix tailTrace_4575192
  have hstable : (prefixWord ++ tailWord_4575192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575192).length < 2 ^ (prefixWord ++ tailWord_4575192).sum := by decide
  have hdescent : baseEnd_4575192 < baseStart_4575192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575239 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 1, 4, 2]
def baseStart_4575239 : Nat := 118140960795 + 4575239 * 2 ^ 59
def prefixEnd_4575239 : Nat := 4983230072969 + 3 ^ 40 * 4575239 * 2
def baseEnd_4575239 : Nat := 2349296716196130090071365

theorem tailTrace_4575239 : CollatzResearch.WordTrace tailWord_4575239 prefixEnd_4575239 2349296716196130090071365 := by
  unfold tailWord_4575239
  simp only [CollatzResearch.WordTrace]
  refine ⟨166872675471697966456784771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111248450314465310971189847 166872675471697966456784771)
  ·
    refine ⟨250309013207546949685177157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166872675471697966456784771 250309013207546949685177157)
    ·
      refine ⟨46932939976415053065970717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 250309013207546949685177157 46932939976415053065970717)
      ·
        refine ⟨17599852491155644899739019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46932939976415053065970717 17599852491155644899739019)
        ·
          refine ⟨26399778736733467349608529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17599852491155644899739019 26399778736733467349608529)
          ·
            refine ⟨19799834052550100512206397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26399778736733467349608529 19799834052550100512206397)
            ·
              refine ⟨7424937769706287692077399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19799834052550100512206397 7424937769706287692077399)
              ·
                refine ⟨11137406654559431538116099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7424937769706287692077399 11137406654559431538116099)
                ·
                  refine ⟨16706109981839147307174149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11137406654559431538116099 16706109981839147307174149)
                  ·
                    refine ⟨3132395621594840120095153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16706109981839147307174149 3132395621594840120095153)
                    ·
                      refine ⟨2349296716196130090071365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3132395621594840120095153 2349296716196130090071365)
                      ·
                        rfl

theorem cell23_4575239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_4575239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575239 prefixEnd_4575239 := by exact prefixLift 4575239
  have htrace : WordTrace (prefixWord ++ tailWord_4575239) baseStart_4575239 baseEnd_4575239 := by
    simpa [prefixWord, tailWord_4575239, baseEnd_4575239] using wordTrace_append hprefix tailTrace_4575239
  have hstable : (prefixWord ++ tailWord_4575239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575239).length < 2 ^ (prefixWord ++ tailWord_4575239).sum := by decide
  have hdescent : baseEnd_4575239 < baseStart_4575239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575285 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_4575285 : Nat := 118140960795 + 4575285 * 2 ^ 59
def prefixEnd_4575285 : Nat := 4983230072969 + 3 ^ 40 * 4575285 * 2
def baseEnd_4575285 : Nat := 2349320336306236910096153

theorem tailTrace_4575285 : CollatzResearch.WordTrace tailWord_4575285 prefixEnd_4575285 2349320336306236910096153 := by
  unfold tailWord_4575285
  simp only [CollatzResearch.WordTrace]
  refine ⟨166874353229531316312959309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111249568819687544208639539 166874353229531316312959309)
  ·
    refine ⟨62577882461074243617359741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166874353229531316312959309 62577882461074243617359741)
    ·
      refine ⟨23466705922902841356509903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62577882461074243617359741 23466705922902841356509903)
      ·
        refine ⟨35200058884354262034764855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23466705922902841356509903 35200058884354262034764855)
        ·
          refine ⟨52800088326531393052147283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35200058884354262034764855 52800088326531393052147283)
          ·
            refine ⟨79200132489797089578220925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52800088326531393052147283 79200132489797089578220925)
            ·
              refine ⟨29700049683673908591832847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79200132489797089578220925 29700049683673908591832847)
              ·
                refine ⟨44550074525510862887749271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29700049683673908591832847 44550074525510862887749271)
                ·
                  refine ⟨66825111788266294331623907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44550074525510862887749271 66825111788266294331623907)
                  ·
                    refine ⟨100237667682399441497435861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66825111788266294331623907 100237667682399441497435861)
                    ·
                      refine ⟨2349320336306236910096153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100237667682399441497435861 2349320336306236910096153)
                      ·
                        rfl

theorem cell23_4575285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_4575285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575285 prefixEnd_4575285 := by exact prefixLift 4575285
  have htrace : WordTrace (prefixWord ++ tailWord_4575285) baseStart_4575285 baseEnd_4575285 := by
    simpa [prefixWord, tailWord_4575285, baseEnd_4575285] using wordTrace_append hprefix tailTrace_4575285
  have hstable : (prefixWord ++ tailWord_4575285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575285).length < 2 ^ (prefixWord ++ tailWord_4575285).sum := by decide
  have hdescent : baseEnd_4575285 < baseStart_4575285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575295 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 4]
def baseStart_4575295 : Nat := 118140960795 + 4575295 * 2 ^ 59
def prefixEnd_4575295 : Nat := 4983230072969 + 3 ^ 40 * 4575295 * 2
def baseEnd_4575295 : Nat := 2349325471112781870971107

theorem tailTrace_4575295 : CollatzResearch.WordTrace tailWord_4575295 prefixEnd_4575295 2349325471112781870971107 := by
  unfold tailWord_4575295
  simp only [CollatzResearch.WordTrace]
  refine ⟨166874717959495088020823339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111249811972996725347215559 166874717959495088020823339)
  ·
    refine ⟨250312076939242632031235009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166874717959495088020823339 250312076939242632031235009)
    ·
      refine ⟨187734057704431974023426257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250312076939242632031235009 187734057704431974023426257)
      ·
        refine ⟨140800543278323980517569693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187734057704431974023426257 140800543278323980517569693)
        ·
          refine ⟨52800203729371492694088635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140800543278323980517569693 52800203729371492694088635)
          ·
            refine ⟨79200305594057239041132953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52800203729371492694088635 79200305594057239041132953)
            ·
              refine ⟨59400229195542929280849715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79200305594057239041132953 59400229195542929280849715)
              ·
                refine ⟨89100343793314393921274573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59400229195542929280849715 89100343793314393921274573)
                ·
                  refine ⟨33412628922492897720477965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89100343793314393921274573 33412628922492897720477965)
                  ·
                    refine ⟨12529735845934836645179237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33412628922492897720477965 12529735845934836645179237)
                    ·
                      refine ⟨2349325471112781870971107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12529735845934836645179237 2349325471112781870971107)
                      ·
                        rfl

theorem cell23_4575295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_4575295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575295 prefixEnd_4575295 := by exact prefixLift 4575295
  have htrace : WordTrace (prefixWord ++ tailWord_4575295) baseStart_4575295 baseEnd_4575295 := by
    simpa [prefixWord, tailWord_4575295, baseEnd_4575295] using wordTrace_append hprefix tailTrace_4575295
  have hstable : (prefixWord ++ tailWord_4575295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575295).length < 2 ^ (prefixWord ++ tailWord_4575295).sum := by decide
  have hdescent : baseEnd_4575295 < baseStart_4575295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575309 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_4575309 : Nat := 118140960795 + 4575309 * 2 ^ 59
def prefixEnd_4575309 : Nat := 4983230072969 + 3 ^ 40 * 4575309 * 2
def baseEnd_4575309 : Nat := 783110886613981605398681

theorem tailTrace_4575309 : CollatzResearch.WordTrace tailWord_4575309 prefixEnd_4575309 783110886613981605398681 := by
  unfold tailWord_4575309
  simp only [CollatzResearch.WordTrace]
  refine ⟨166875228581444368411832981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111250152387629578941221987 166875228581444368411832981)
  ·
    refine ⟨7822276339755204769304671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 166875228581444368411832981 7822276339755204769304671)
    ·
      refine ⟨11733414509632807153957007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7822276339755204769304671 11733414509632807153957007)
      ·
        refine ⟨17600121764449210730935511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11733414509632807153957007 17600121764449210730935511)
        ·
          refine ⟨26400182646673816096403267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17600121764449210730935511 26400182646673816096403267)
          ·
            refine ⟨39600273970010724144604901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26400182646673816096403267 39600273970010724144604901)
            ·
              refine ⟨7425051369377010777113419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39600273970010724144604901 7425051369377010777113419)
              ·
                refine ⟨11137577054065516165670129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7425051369377010777113419 11137577054065516165670129)
                ·
                  refine ⟨8353182790549137124252597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11137577054065516165670129 8353182790549137124252597)
                  ·
                    refine ⟨783110886613981605398681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8353182790549137124252597 783110886613981605398681)
                    ·
                      rfl

theorem cell23_4575309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_4575309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575309 prefixEnd_4575309 := by exact prefixLift 4575309
  have htrace : WordTrace (prefixWord ++ tailWord_4575309) baseStart_4575309 baseEnd_4575309 := by
    simpa [prefixWord, tailWord_4575309, baseEnd_4575309] using wordTrace_append hprefix tailTrace_4575309
  have hstable : (prefixWord ++ tailWord_4575309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575309).length < 2 ^ (prefixWord ++ tailWord_4575309).sum := by decide
  have hdescent : baseEnd_4575309 < baseStart_4575309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575312 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 6, 4, 2]
def baseStart_4575312 : Nat := 118140960795 + 4575312 * 2 ^ 59
def prefixEnd_4575312 : Nat := 4983230072969 + 3 ^ 40 * 4575312 * 2
def baseEnd_4575312 : Nat := 2349334200283908304458529

theorem tailTrace_4575312 : CollatzResearch.WordTrace tailWord_4575312 prefixEnd_4575312 2349334200283908304458529 := by
  unfold tailWord_4575312
  simp only [CollatzResearch.WordTrace]
  refine ⟨83437669000216749962096095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111250225333622333282794793 83437669000216749962096095)
  ·
    refine ⟨125156503500325124943144143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83437669000216749962096095 125156503500325124943144143)
    ·
      refine ⟨187734755250487687414716215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125156503500325124943144143 187734755250487687414716215)
      ·
        refine ⟨281602132875731531122074323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187734755250487687414716215 281602132875731531122074323)
        ·
          refine ⟨422403199313597296683111485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281602132875731531122074323 422403199313597296683111485)
          ·
            refine ⟨158401199742598986256166807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 422403199313597296683111485 158401199742598986256166807)
            ·
              refine ⟨237601799613898479384250211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158401199742598986256166807 237601799613898479384250211)
              ·
                refine ⟨356402699420847719076375317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237601799613898479384250211 356402699420847719076375317)
                ·
                  refine ⟨16706376535352236831705093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 356402699420847719076375317 16706376535352236831705093)
                  ·
                    refine ⟨3132445600378544405944705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16706376535352236831705093 3132445600378544405944705)
                    ·
                      refine ⟨2349334200283908304458529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3132445600378544405944705 2349334200283908304458529)
                      ·
                        rfl

theorem cell23_4575312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6, 4, 2].length) (baseStart_4575312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575312 prefixEnd_4575312 := by exact prefixLift 4575312
  have htrace : WordTrace (prefixWord ++ tailWord_4575312) baseStart_4575312 baseEnd_4575312 := by
    simpa [prefixWord, tailWord_4575312, baseEnd_4575312] using wordTrace_append hprefix tailTrace_4575312
  have hstable : (prefixWord ++ tailWord_4575312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575312).length < 2 ^ (prefixWord ++ tailWord_4575312).sum := by decide
  have hdescent : baseEnd_4575312 < baseStart_4575312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575330 : List Nat := [3, 3, 2, 2, 3, 1, 2, 2, 5]
def baseStart_4575330 : Nat := 118140960795 + 4575330 * 2 ^ 59
def prefixEnd_4575330 : Nat := 4983230072969 + 3 ^ 40 * 4575330 * 2
def baseEnd_4575330 : Nat := 261038160326187692670383

theorem tailTrace_4575330 : CollatzResearch.WordTrace tailWord_4575330 prefixEnd_4575330 261038160326187692670383 := by
  unfold tailWord_4575330
  simp only [CollatzResearch.WordTrace]
  refine ⟨41718998628592072249586861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111250663009578859332231629 41718998628592072249586861)
  ·
    refine ⟨15644624485722027093595073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41718998628592072249586861 15644624485722027093595073)
    ·
      refine ⟨11733468364291520320196305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15644624485722027093595073 11733468364291520320196305)
      ·
        refine ⟨8800101273218640240147229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11733468364291520320196305 8800101273218640240147229)
        ·
          refine ⟨3300037977456990090055211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8800101273218640240147229 3300037977456990090055211)
          ·
            refine ⟨4950056966185485135082817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300037977456990090055211 4950056966185485135082817)
            ·
              refine ⟨3712542724639113851312113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4950056966185485135082817 3712542724639113851312113)
              ·
                refine ⟨2784407043479335388484085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3712542724639113851312113 2784407043479335388484085)
                ·
                  refine ⟨261038160326187692670383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2784407043479335388484085 261038160326187692670383)
                  ·
                    rfl

theorem cell23_4575330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_4575330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575330 prefixEnd_4575330 := by exact prefixLift 4575330
  have htrace : WordTrace (prefixWord ++ tailWord_4575330) baseStart_4575330 baseEnd_4575330 := by
    simpa [prefixWord, tailWord_4575330, baseEnd_4575330] using wordTrace_append hprefix tailTrace_4575330
  have hstable : (prefixWord ++ tailWord_4575330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575330).length < 2 ^ (prefixWord ++ tailWord_4575330).sum := by decide
  have hdescent : baseEnd_4575330 < baseStart_4575330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575386 : List Nat := [3, 1, 1, 5, 2, 2, 1, 2, 6]
def baseStart_4575386 : Nat := 118140960795 + 4575386 * 2 ^ 59
def prefixEnd_4575386 : Nat := 4983230072969 + 3 ^ 40 * 4575386 * 2
def baseEnd_4575386 : Nat := 261041355316926779437021

theorem tailTrace_4575386 : CollatzResearch.WordTrace tailWord_4575386 prefixEnd_4575386 261041355316926779437021 := by
  unfold tailWord_4575386
  simp only [CollatzResearch.WordTrace]
  refine ⟨41719509250541352640596503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111252024668110273708257341 41719509250541352640596503)
  ·
    refine ⟨62579263875812028960894755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41719509250541352640596503 62579263875812028960894755)
    ·
      refine ⟨93868895813718043441342133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62579263875812028960894755 93868895813718043441342133)
      ·
        refine ⟨8800208982536066572625825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93868895813718043441342133 8800208982536066572625825)
        ·
          refine ⟨6600156736902049929469369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8800208982536066572625825 6600156736902049929469369)
          ·
            refine ⟨4950117552676537447102027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6600156736902049929469369 4950117552676537447102027)
            ·
              refine ⟨7425176329014806170653041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4950117552676537447102027 7425176329014806170653041)
              ·
                refine ⟨5568882246761104627989781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7425176329014806170653041 5568882246761104627989781)
                ·
                  refine ⟨261041355316926779437021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5568882246761104627989781 261041355316926779437021)
                  ·
                    rfl

theorem cell23_4575386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 6].length) (baseStart_4575386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575386 prefixEnd_4575386 := by exact prefixLift 4575386
  have htrace : WordTrace (prefixWord ++ tailWord_4575386) baseStart_4575386 baseEnd_4575386 := by
    simpa [prefixWord, tailWord_4575386, baseEnd_4575386] using wordTrace_append hprefix tailTrace_4575386
  have hstable : (prefixWord ++ tailWord_4575386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575386).length < 2 ^ (prefixWord ++ tailWord_4575386).sum := by decide
  have hdescent : baseEnd_4575386 < baseStart_4575386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575395 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 2, 10]
def baseStart_4575395 : Nat := 118140960795 + 4575395 * 2 ^ 59
def prefixEnd_4575395 : Nat := 4983230072969 + 3 ^ 40 * 4575395 * 2
def baseEnd_4575395 : Nat := 783125606392743826573549

theorem tailTrace_4575395 : CollatzResearch.WordTrace tailWord_4575395 prefixEnd_4575395 783125606392743826573549 := by
  unfold tailWord_4575395
  simp only [CollatzResearch.WordTrace]
  refine ⟨166878365259132805099463639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111252243506088536732975759 166878365259132805099463639)
  ·
    refine ⟨250317547888699207649195459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166878365259132805099463639 250317547888699207649195459)
    ·
      refine ⟨375476321833048811473793189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250317547888699207649195459 375476321833048811473793189)
      ·
        refine ⟨70401810343696652151336223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 375476321833048811473793189 70401810343696652151336223)
        ·
          refine ⟨105602715515544978227004335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70401810343696652151336223 105602715515544978227004335)
          ·
            refine ⟨158404073273317467340506503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105602715515544978227004335 158404073273317467340506503)
            ·
              refine ⟨237606109909976201010759755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158404073273317467340506503 237606109909976201010759755)
              ·
                refine ⟨356409164864964301516139633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237606109909976201010759755 356409164864964301516139633)
                ·
                  refine ⟨267306873648723226137104725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 356409164864964301516139633 267306873648723226137104725)
                  ·
                    refine ⟨783125606392743826573549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 267306873648723226137104725 783125606392743826573549)
                    ·
                      rfl

theorem cell23_4575395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 10].length) (baseStart_4575395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575395 prefixEnd_4575395 := by exact prefixLift 4575395
  have htrace : WordTrace (prefixWord ++ tailWord_4575395) baseStart_4575395 baseEnd_4575395 := by
    simpa [prefixWord, tailWord_4575395, baseEnd_4575395] using wordTrace_append hprefix tailTrace_4575395
  have hstable : (prefixWord ++ tailWord_4575395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575395).length < 2 ^ (prefixWord ++ tailWord_4575395).sum := by decide
  have hdescent : baseEnd_4575395 < baseStart_4575395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575419 : List Nat := [1, 1, 1, 1, 1, 2, 8, 2, 1, 1, 4]
def baseStart_4575419 : Nat := 118140960795 + 4575419 * 2 ^ 59
def prefixEnd_4575419 : Nat := 4983230072969 + 3 ^ 40 * 4575419 * 2
def baseEnd_4575419 : Nat := 2349389142713939385820537

theorem tailTrace_4575419 : CollatzResearch.WordTrace tailWord_4575419 prefixEnd_4575419 2349389142713939385820537 := by
  unfold tailWord_4575419
  simp only [CollatzResearch.WordTrace]
  refine ⟨166879240611045857198337311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111252827074030571465558207 166879240611045857198337311)
  ·
    refine ⟨250318860916568785797505967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166879240611045857198337311 250318860916568785797505967)
    ·
      refine ⟨375478291374853178696258951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250318860916568785797505967 375478291374853178696258951)
      ·
        refine ⟨563217437062279768044388427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375478291374853178696258951 563217437062279768044388427)
        ·
          refine ⟨844826155593419652066582641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563217437062279768044388427 844826155593419652066582641)
          ·
            refine ⟨633619616695064739049936981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 844826155593419652066582641 633619616695064739049936981)
            ·
              refine ⟨7425229883145289910741449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 633619616695064739049936981 7425229883145289910741449)
              ·
                refine ⟨5568922412358967433056087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7425229883145289910741449 5568922412358967433056087)
                ·
                  refine ⟨8353383618538451149584131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5568922412358967433056087 8353383618538451149584131)
                  ·
                    refine ⟨12530075427807676724376197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8353383618538451149584131 12530075427807676724376197)
                    ·
                      refine ⟨2349389142713939385820537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12530075427807676724376197 2349389142713939385820537)
                      ·
                        rfl

theorem cell23_4575419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 1, 4].length) (baseStart_4575419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575419 prefixEnd_4575419 := by exact prefixLift 4575419
  have htrace : WordTrace (prefixWord ++ tailWord_4575419) baseStart_4575419 baseEnd_4575419 := by
    simpa [prefixWord, tailWord_4575419, baseEnd_4575419] using wordTrace_append hprefix tailTrace_4575419
  have hstable : (prefixWord ++ tailWord_4575419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575419).length < 2 ^ (prefixWord ++ tailWord_4575419).sum := by decide
  have hdescent : baseEnd_4575419 < baseStart_4575419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575432 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_4575432 : Nat := 118140960795 + 4575432 * 2 ^ 59
def prefixEnd_4575432 : Nat := 4983230072969 + 3 ^ 40 * 4575432 * 2
def baseEnd_4575432 : Nat := 2349395817962447834957977

theorem tailTrace_4575432 : CollatzResearch.WordTrace tailWord_4575432 prefixEnd_4575432 2349395817962447834957977 := by
  unfold tailWord_4575432
  simp only [CollatzResearch.WordTrace]
  refine ⟨83439857379999380209280275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111253143173332506945707033 83439857379999380209280275)
  ·
    refine ⟨125159786069999070313920413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83439857379999380209280275 125159786069999070313920413)
    ·
      refine ⟨46934919776249651367720155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125159786069999070313920413 46934919776249651367720155)
      ·
        refine ⟨70402379664374477051580233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46934919776249651367720155 70402379664374477051580233)
        ·
          refine ⟨52801784748280857788685175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70402379664374477051580233 52801784748280857788685175)
          ·
            refine ⟨79202677122421286683027763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52801784748280857788685175 79202677122421286683027763)
            ·
              refine ⟨118804015683631930024541645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79202677122421286683027763 118804015683631930024541645)
              ·
                refine ⟨44551505881361973759203117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118804015683631930024541645 44551505881361973759203117)
                ·
                  refine ⟨16706814705510740159701169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44551505881361973759203117 16706814705510740159701169)
                  ·
                    refine ⟨12530111029133055119775877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16706814705510740159701169 12530111029133055119775877)
                    ·
                      refine ⟨2349395817962447834957977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12530111029133055119775877 2349395817962447834957977)
                      ·
                        rfl

theorem cell23_4575432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_4575432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575432 prefixEnd_4575432 := by exact prefixLift 4575432
  have htrace : WordTrace (prefixWord ++ tailWord_4575432) baseStart_4575432 baseEnd_4575432 := by
    simpa [prefixWord, tailWord_4575432, baseEnd_4575432] using wordTrace_append hprefix tailTrace_4575432
  have hstable : (prefixWord ++ tailWord_4575432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575432).length < 2 ^ (prefixWord ++ tailWord_4575432).sum := by decide
  have hdescent : baseEnd_4575432 < baseStart_4575432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575439 : List Nat := [1, 1, 2, 1, 1, 3, 3, 5, 1, 2, 3]
def baseStart_4575439 : Nat := 118140960795 + 4575439 * 2 ^ 59
def prefixEnd_4575439 : Nat := 4983230072969 + 3 ^ 40 * 4575439 * 2
def baseEnd_4575439 : Nat := 2349399412327029307570445

theorem tailTrace_4575439 : CollatzResearch.WordTrace tailWord_4575439 prefixEnd_4575439 2349399412327029307570445 := by
  unfold tailWord_4575439
  simp only [CollatzResearch.WordTrace]
  refine ⟨166879970070973400614065371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111253313380648933742710247 166879970070973400614065371)
  ·
    refine ⟨250319955106460100921098057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166879970070973400614065371 250319955106460100921098057)
    ·
      refine ⟨187739966329845075690823543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250319955106460100921098057 187739966329845075690823543)
      ·
        refine ⟨281609949494767613536235315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187739966329845075690823543 281609949494767613536235315)
        ·
          refine ⟨422414924242151420304352973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281609949494767613536235315 422414924242151420304352973)
          ·
            refine ⟨158405596590806782614132365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 422414924242151420304352973 158405596590806782614132365)
            ·
              refine ⟨59402098721552543480299637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158405596590806782614132365 59402098721552543480299637)
              ·
                refine ⟨5568946755145550951278091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59402098721552543480299637 5568946755145550951278091)
                ·
                  refine ⟨8353420132718326426917137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5568946755145550951278091 8353420132718326426917137)
                  ·
                    refine ⟨6265065099538744820187853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8353420132718326426917137 6265065099538744820187853)
                    ·
                      refine ⟨2349399412327029307570445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6265065099538744820187853 2349399412327029307570445)
                      ·
                        rfl

theorem cell23_4575439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 2, 3].length) (baseStart_4575439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575439 prefixEnd_4575439 := by exact prefixLift 4575439
  have htrace : WordTrace (prefixWord ++ tailWord_4575439) baseStart_4575439 baseEnd_4575439 := by
    simpa [prefixWord, tailWord_4575439, baseEnd_4575439] using wordTrace_append hprefix tailTrace_4575439
  have hstable : (prefixWord ++ tailWord_4575439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575439).length < 2 ^ (prefixWord ++ tailWord_4575439).sum := by decide
  have hdescent : baseEnd_4575439 < baseStart_4575439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575442 : List Nat := [3, 2, 2, 2, 1, 2, 11]
def baseStart_4575442 : Nat := 118140960795 + 4575442 * 2 ^ 59
def prefixEnd_4575442 : Nat := 4983230072969 + 3 ^ 40 * 4575442 * 2
def baseEnd_4575442 : Nat := 29004950034185096244851

theorem tailTrace_4575442 : CollatzResearch.WordTrace tailWord_4575442 prefixEnd_4575442 29004950034185096244851 := by
  unfold tailWord_4575442
  simp only [CollatzResearch.WordTrace]
  refine ⟨41720019872490633031606145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111253386326641688084283053 41720019872490633031606145)
  ·
    refine ⟨31290014904367974773704609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41720019872490633031606145 31290014904367974773704609)
    ·
      refine ⟨23467511178275981080278457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31290014904367974773704609 23467511178275981080278457)
      ·
        refine ⟨17600633383706985810208843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23467511178275981080278457 17600633383706985810208843)
        ·
          refine ⟨26400950075560478715313265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17600633383706985810208843 26400950075560478715313265)
          ·
            refine ⟨19800712556670359036484949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26400950075560478715313265 19800712556670359036484949)
            ·
              refine ⟨29004950034185096244851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19800712556670359036484949 29004950034185096244851)
              ·
                rfl

theorem cell23_4575442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 11].length) (baseStart_4575442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575442 prefixEnd_4575442 := by exact prefixLift 4575442
  have htrace : WordTrace (prefixWord ++ tailWord_4575442) baseStart_4575442 baseEnd_4575442 := by
    simpa [prefixWord, tailWord_4575442, baseEnd_4575442] using wordTrace_append hprefix tailTrace_4575442
  have hstable : (prefixWord ++ tailWord_4575442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575442).length < 2 ^ (prefixWord ++ tailWord_4575442).sum := by decide
  have hdescent : baseEnd_4575442 < baseStart_4575442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575463 : List Nat := [1, 1, 5, 3, 1, 1, 4, 1, 2, 4]
def baseStart_4575463 : Nat := 118140960795 + 4575463 * 2 ^ 59
def prefixEnd_4575463 : Nat := 4983230072969 + 3 ^ 40 * 4575463 * 2
def baseEnd_4575463 : Nat := 783137245287579071223445

theorem tailTrace_4575463 : CollatzResearch.WordTrace tailWord_4575463 prefixEnd_4575463 783137245287579071223445 := by
  unfold tailWord_4575463
  simp only [CollatzResearch.WordTrace]
  refine ⟨166880845422886452712939043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111253896948590968475292695 166880845422886452712939043)
  ·
    refine ⟨250321268134329679069408565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166880845422886452712939043 250321268134329679069408565)
    ·
      refine ⟨23467618887593407412757053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 250321268134329679069408565 23467618887593407412757053)
      ·
        refine ⟨8800357082847527779783895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23467618887593407412757053 8800357082847527779783895)
        ·
          refine ⟨13200535624271291669675843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8800357082847527779783895 13200535624271291669675843)
          ·
            refine ⟨19800803436406937504513765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13200535624271291669675843 19800803436406937504513765)
            ·
              refine ⟨3712650644326300782096331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19800803436406937504513765 3712650644326300782096331)
              ·
                refine ⟨5568975966489451173144497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3712650644326300782096331 5568975966489451173144497)
                ·
                  refine ⟨4176731974867088379858373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5568975966489451173144497 4176731974867088379858373)
                  ·
                    refine ⟨783137245287579071223445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4176731974867088379858373 783137245287579071223445)
                    ·
                      rfl

theorem cell23_4575463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_4575463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575463 prefixEnd_4575463 := by exact prefixLift 4575463
  have htrace : WordTrace (prefixWord ++ tailWord_4575463) baseStart_4575463 baseEnd_4575463 := by
    simpa [prefixWord, tailWord_4575463, baseEnd_4575463] using wordTrace_append hprefix tailTrace_4575463
  have hstable : (prefixWord ++ tailWord_4575463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575463).length < 2 ^ (prefixWord ++ tailWord_4575463).sum := by decide
  have hdescent : baseEnd_4575463 < baseStart_4575463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575486 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_4575486 : Nat := 118140960795 + 4575486 * 2 ^ 59
def prefixEnd_4575486 : Nat := 4983230072969 + 3 ^ 40 * 4575486 * 2
def baseEnd_4575486 : Nat := 2349423545917790623682729

theorem tailTrace_4575486 : CollatzResearch.WordTrace tailWord_4575486 prefixEnd_4575486 2349423545917790623682729 := by
  unfold tailWord_4575486
  simp only [CollatzResearch.WordTrace]
  refine ⟨20860210537725390955128289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111254456201202085094017541 20860210537725390955128289)
  ·
    refine ⟨15645157903294043216346217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20860210537725390955128289 15645157903294043216346217)
    ·
      refine ⟨11733868427470532412259663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15645157903294043216346217 11733868427470532412259663)
      ·
        refine ⟨17600802641205798618389495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11733868427470532412259663 17600802641205798618389495)
        ·
          refine ⟨26401203961808697927584243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17600802641205798618389495 26401203961808697927584243)
          ·
            refine ⟨39601805942713046891376365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26401203961808697927584243 39601805942713046891376365)
            ·
              refine ⟨14850677228517392584266137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39601805942713046891376365 14850677228517392584266137)
              ·
                refine ⟨11138007921388044438199603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14850677228517392584266137 11138007921388044438199603)
                ·
                  refine ⟨16707011882082066657299405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11138007921388044438199603 16707011882082066657299405)
                  ·
                    refine ⟨6265129455780774996487277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16707011882082066657299405 6265129455780774996487277)
                    ·
                      refine ⟨2349423545917790623682729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6265129455780774996487277 2349423545917790623682729)
                      ·
                        rfl

theorem cell23_4575486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_4575486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575486 prefixEnd_4575486 := by exact prefixLift 4575486
  have htrace : WordTrace (prefixWord ++ tailWord_4575486) baseStart_4575486 baseEnd_4575486 := by
    simpa [prefixWord, tailWord_4575486, baseEnd_4575486] using wordTrace_append hprefix tailTrace_4575486
  have hstable : (prefixWord ++ tailWord_4575486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575486).length < 2 ^ (prefixWord ++ tailWord_4575486).sum := by decide
  have hdescent : baseEnd_4575486 < baseStart_4575486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575490 : List Nat := [3, 4, 1, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_4575490 : Nat := 118140960795 + 4575490 * 2 ^ 59
def prefixEnd_4575490 : Nat := 4983230072969 + 3 ^ 40 * 4575490 * 2
def baseEnd_4575490 : Nat := 2349425599840408608032711

theorem tailTrace_4575490 : CollatzResearch.WordTrace tailWord_4575490 prefixEnd_4575490 2349425599840408608032711 := by
  unfold tailWord_4575490
  simp only [CollatzResearch.WordTrace]
  refine ⟨41720457548447159081042981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111254553462525757549447949 41720457548447159081042981)
  ·
    refine ⟨7822585790333842327695559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41720457548447159081042981 7822585790333842327695559)
    ·
      refine ⟨11733878685500763491543339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7822585790333842327695559 11733878685500763491543339)
      ·
        refine ⟨17600818028251145237315009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11733878685500763491543339 17600818028251145237315009)
        ·
          refine ⟨13200613521188358927986257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17600818028251145237315009 13200613521188358927986257)
          ·
            refine ⟨9900460140891269195989693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13200613521188358927986257 9900460140891269195989693)
            ·
              refine ⟨3712672552834225948496135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9900460140891269195989693 3712672552834225948496135)
              ·
                refine ⟨5569008829251338922744203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3712672552834225948496135 5569008829251338922744203)
                ·
                  refine ⟨8353513243877008384116305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5569008829251338922744203 8353513243877008384116305)
                  ·
                    refine ⟨6265134932907756288087229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8353513243877008384116305 6265134932907756288087229)
                    ·
                      refine ⟨2349425599840408608032711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6265134932907756288087229 2349425599840408608032711)
                      ·
                        rfl

theorem cell23_4575490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_4575490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575490 prefixEnd_4575490 := by exact prefixLift 4575490
  have htrace : WordTrace (prefixWord ++ tailWord_4575490) baseStart_4575490 baseEnd_4575490 := by
    simpa [prefixWord, tailWord_4575490, baseEnd_4575490] using wordTrace_append hprefix tailTrace_4575490
  have hstable : (prefixWord ++ tailWord_4575490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575490).length < 2 ^ (prefixWord ++ tailWord_4575490).sum := by decide
  have hdescent : baseEnd_4575490 < baseStart_4575490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575519 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 2, 6]
def baseStart_4575519 : Nat := 118140960795 + 4575519 * 2 ^ 59
def prefixEnd_4575519 : Nat := 4983230072969 + 3 ^ 40 * 4575519 * 2
def baseEnd_4575519 : Nat := 783146830259796331523359

theorem tailTrace_4575519 : CollatzResearch.WordTrace tailWord_4575519 prefixEnd_4575519 783146830259796331523359 := by
  unfold tailWord_4575519
  simp only [CollatzResearch.WordTrace]
  refine ⟨166882887910683574276977611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111255258607122382851318407 166882887910683574276977611)
  ·
    refine ⟨250324331866025361415466417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166882887910683574276977611 250324331866025361415466417)
    ·
      refine ⟨187743248899519021061599813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250324331866025361415466417 187743248899519021061599813)
      ·
        refine ⟨35201859168659816449049965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187743248899519021061599813 35201859168659816449049965)
        ·
          refine ⟨13200697188247431168393737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35201859168659816449049965 13200697188247431168393737)
          ·
            refine ⟨9900522891185573376295303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13200697188247431168393737 9900522891185573376295303)
            ·
              refine ⟨14850784336778360064442955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9900522891185573376295303 14850784336778360064442955)
              ·
                refine ⟨22276176505167540096664433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14850784336778360064442955 22276176505167540096664433)
                ·
                  refine ⟨16707132378875655072498325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22276176505167540096664433 16707132378875655072498325)
                  ·
                    refine ⟨783146830259796331523359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16707132378875655072498325 783146830259796331523359)
                    ·
                      rfl

theorem cell23_4575519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 6].length) (baseStart_4575519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575519 prefixEnd_4575519 := by exact prefixLift 4575519
  have htrace : WordTrace (prefixWord ++ tailWord_4575519) baseStart_4575519 baseEnd_4575519 := by
    simpa [prefixWord, tailWord_4575519, baseEnd_4575519] using wordTrace_append hprefix tailTrace_4575519
  have hstable : (prefixWord ++ tailWord_4575519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575519).length < 2 ^ (prefixWord ++ tailWord_4575519).sum := by decide
  have hdescent : baseEnd_4575519 < baseStart_4575519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575532 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 9]
def baseStart_4575532 : Nat := 118140960795 + 4575532 * 2 ^ 59
def prefixEnd_4575532 : Nat := 4983230072969 + 3 ^ 40 * 4575532 * 2
def baseEnd_4575532 : Nat := 261049685114210827078613

theorem tailTrace_4575532 : CollatzResearch.WordTrace tailWord_4575532 prefixEnd_4575532 261049685114210827078613 := by
  unfold tailWord_4575532
  simp only [CollatzResearch.WordTrace]
  refine ⟨83441681029818238748600425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111255574706424318331467233 83441681029818238748600425)
  ·
    refine ⟨62581260772363679061450319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83441681029818238748600425 62581260772363679061450319)
    ·
      refine ⟨93871891158545518592175479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62581260772363679061450319 93871891158545518592175479)
      ·
        refine ⟨140807836737818277888263219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93871891158545518592175479 140807836737818277888263219)
        ·
          refine ⟨211211755106727416832394829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140807836737818277888263219 211211755106727416832394829)
          ·
            refine ⟨79204408165022781312148061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211211755106727416832394829 79204408165022781312148061)
            ·
              refine ⟨29701653061883542992055523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79204408165022781312148061 29701653061883542992055523)
              ·
                refine ⟨44552479592825314488083285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29701653061883542992055523 44552479592825314488083285)
                ·
                  refine ⟨261049685114210827078613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44552479592825314488083285 261049685114210827078613)
                  ·
                    rfl

theorem cell23_4575532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_4575532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575532 prefixEnd_4575532 := by exact prefixLift 4575532
  have htrace : WordTrace (prefixWord ++ tailWord_4575532) baseStart_4575532 baseEnd_4575532 := by
    simpa [prefixWord, tailWord_4575532, baseEnd_4575532] using wordTrace_append hprefix tailTrace_4575532
  have hstable : (prefixWord ++ tailWord_4575532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575532).length < 2 ^ (prefixWord ++ tailWord_4575532).sum := by decide
  have hdescent : baseEnd_4575532 < baseStart_4575532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575559 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_4575559 : Nat := 118140960795 + 4575559 * 2 ^ 59
def prefixEnd_4575559 : Nat := 4983230072969 + 3 ^ 40 * 4575559 * 2
def baseEnd_4575559 : Nat := 2349461030005568838069893

theorem tailTrace_4575559 : CollatzResearch.WordTrace tailWord_4575559 prefixEnd_4575559 2349461030005568838069893 := by
  unfold tailWord_4575559
  simp only [CollatzResearch.WordTrace]
  refine ⟨166884346830538661108433731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111256231220359107405622487 166884346830538661108433731)
  ·
    refine ⟨250326520245807991662650597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166884346830538661108433731 250326520245807991662650597)
    ·
      refine ⟨46936222546088998436746987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 250326520245807991662650597 46936222546088998436746987)
      ·
        refine ⟨70404333819133497655120481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46936222546088998436746987 70404333819133497655120481)
        ·
          refine ⟨52803250364350123241340361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70404333819133497655120481 52803250364350123241340361)
          ·
            refine ⟨39602437773262592431005271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52803250364350123241340361 39602437773262592431005271)
            ·
              refine ⟨59403656659893888646507907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39602437773262592431005271 59403656659893888646507907)
              ·
                refine ⟨89105484989840832969761861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59403656659893888646507907 89105484989840832969761861)
                ·
                  refine ⟨16707278435595156181830349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89105484989840832969761861 16707278435595156181830349)
                  ·
                    refine ⟨6265229413348183568186381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16707278435595156181830349 6265229413348183568186381)
                    ·
                      refine ⟨2349461030005568838069893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6265229413348183568186381 2349461030005568838069893)
                      ·
                        rfl

theorem cell23_4575559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_4575559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575559 prefixEnd_4575559 := by exact prefixLift 4575559
  have htrace : WordTrace (prefixWord ++ tailWord_4575559) baseStart_4575559 baseEnd_4575559 := by
    simpa [prefixWord, tailWord_4575559, baseEnd_4575559] using wordTrace_append hprefix tailTrace_4575559
  have hstable : (prefixWord ++ tailWord_4575559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575559).length < 2 ^ (prefixWord ++ tailWord_4575559).sum := by decide
  have hdescent : baseEnd_4575559 < baseStart_4575559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575677 : List Nat := [1, 4, 1, 2, 2, 4, 2, 2, 1, 4]
def baseStart_4575677 : Nat := 118140960795 + 4575677 * 2 ^ 59
def prefixEnd_4575677 : Nat := 4983230072969 + 3 ^ 40 * 4575677 * 2
def baseEnd_4575677 : Nat := 783173873574266458798117

theorem tailTrace_4575677 : CollatzResearch.WordTrace tailWord_4575677 prefixEnd_4575677 783173873574266458798117 := by
  unfold tailWord_4575677
  simp only [CollatzResearch.WordTrace]
  refine ⟨166888650644111167261229285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111259100429407444840819523 166888650644111167261229285)
  ·
    refine ⟨31291621995770843861480491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166888650644111167261229285 31291621995770843861480491)
    ·
      refine ⟨46937432993656265792220737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31291621995770843861480491 46937432993656265792220737)
      ·
        refine ⟨35203074745242199344165553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46937432993656265792220737 35203074745242199344165553)
        ·
          refine ⟨26402306058931649508124165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35203074745242199344165553 26402306058931649508124165)
          ·
            refine ⟨4950432386049684282773281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26402306058931649508124165 4950432386049684282773281)
            ·
              refine ⟨3712824289537263212079961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4950432386049684282773281 3712824289537263212079961)
              ·
                refine ⟨2784618217152947409059971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3712824289537263212079961 2784618217152947409059971)
                ·
                  refine ⟨4176927325729421113589957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2784618217152947409059971 4176927325729421113589957)
                  ·
                    refine ⟨783173873574266458798117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4176927325729421113589957 783173873574266458798117)
                    ·
                      rfl

theorem cell23_4575677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_4575677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575677 prefixEnd_4575677 := by exact prefixLift 4575677
  have htrace : WordTrace (prefixWord ++ tailWord_4575677) baseStart_4575677 baseEnd_4575677 := by
    simpa [prefixWord, tailWord_4575677, baseEnd_4575677] using wordTrace_append hprefix tailTrace_4575677
  have hstable : (prefixWord ++ tailWord_4575677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575677).length < 2 ^ (prefixWord ++ tailWord_4575677).sum := by decide
  have hdescent : baseEnd_4575677 < baseStart_4575677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575700 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_4575700 : Nat := 118140960795 + 4575700 * 2 ^ 59
def prefixEnd_4575700 : Nat := 4983230072969 + 3 ^ 40 * 4575700 * 2
def baseEnd_4575700 : Nat := 2349533430777852786406745

theorem tailTrace_4575700 : CollatzResearch.WordTrace tailWord_4575700 prefixEnd_4575700 2349533430777852786406745 := by
  unfold tailWord_4575700
  simp only [CollatzResearch.WordTrace]
  refine ⟨83444744761513921094658277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111259659682018561459544369 83444744761513921094658277)
  ·
    refine ⟨15645889642783860205248427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83444744761513921094658277 15645889642783860205248427)
    ·
      refine ⟨23468834464175790307872641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15645889642783860205248427 23468834464175790307872641)
      ·
        refine ⟨17601625848131842730904481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23468834464175790307872641 17601625848131842730904481)
        ·
          refine ⟨13201219386098882048178361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17601625848131842730904481 13201219386098882048178361)
          ·
            refine ⟨9900914539574161536133771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13201219386098882048178361 9900914539574161536133771)
            ·
              refine ⟨14851371809361242304200657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9900914539574161536133771 14851371809361242304200657)
              ·
                refine ⟨11138528857020931728150493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14851371809361242304200657 11138528857020931728150493)
                ·
                  refine ⟨4176948321382849398056435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11138528857020931728150493 4176948321382849398056435)
                  ·
                    refine ⟨6265422482074274097084653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4176948321382849398056435 6265422482074274097084653)
                    ·
                      refine ⟨2349533430777852786406745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6265422482074274097084653 2349533430777852786406745)
                      ·
                        rfl

theorem cell23_4575700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_4575700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575700 prefixEnd_4575700 := by exact prefixLift 4575700
  have htrace : WordTrace (prefixWord ++ tailWord_4575700) baseStart_4575700 baseEnd_4575700 := by
    simpa [prefixWord, tailWord_4575700, baseEnd_4575700] using wordTrace_append hprefix tailTrace_4575700
  have hstable : (prefixWord ++ tailWord_4575700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575700).length < 2 ^ (prefixWord ++ tailWord_4575700).sum := by decide
  have hdescent : baseEnd_4575700 < baseStart_4575700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575706 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4]
def baseStart_4575706 : Nat := 118140960795 + 4575706 * 2 ^ 59
def prefixEnd_4575706 : Nat := 4983230072969 + 3 ^ 40 * 4575706 * 2
def baseEnd_4575706 : Nat := 2349536511661779762931717

theorem tailTrace_4575706 : CollatzResearch.WordTrace tailWord_4575706 prefixEnd_4575706 2349536511661779762931717 := by
  unfold tailWord_4575706
  simp only [CollatzResearch.WordTrace]
  refine ⟨41722427090251526303508743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111259805574004070142689981 41722427090251526303508743)
  ·
    refine ⟨62583640635377289455263115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41722427090251526303508743 62583640635377289455263115)
    ·
      refine ⟨93875460953065934182894673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62583640635377289455263115 93875460953065934182894673)
      ·
        refine ⟨70406595714799450637171005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93875460953065934182894673 70406595714799450637171005)
        ·
          refine ⟨26402473393049793988939127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70406595714799450637171005 26402473393049793988939127)
          ·
            refine ⟨39603710089574690983408691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26402473393049793988939127 39603710089574690983408691)
            ·
              refine ⟨59405565134362036475113037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39603710089574690983408691 59405565134362036475113037)
              ·
                refine ⟨22277086925385763678167389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59405565134362036475113037 22277086925385763678167389)
                ·
                  refine ⟨8353907597019661379312771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22277086925385763678167389 8353907597019661379312771)
                  ·
                    refine ⟨12530861395529492068969157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8353907597019661379312771 12530861395529492068969157)
                    ·
                      refine ⟨2349536511661779762931717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12530861395529492068969157 2349536511661779762931717)
                      ·
                        rfl

theorem cell23_4575706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_4575706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575706 prefixEnd_4575706 := by exact prefixLift 4575706
  have htrace : WordTrace (prefixWord ++ tailWord_4575706) baseStart_4575706 baseEnd_4575706 := by
    simpa [prefixWord, tailWord_4575706, baseEnd_4575706] using wordTrace_append hprefix tailTrace_4575706
  have hstable : (prefixWord ++ tailWord_4575706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575706).length < 2 ^ (prefixWord ++ tailWord_4575706).sum := by decide
  have hdescent : baseEnd_4575706 < baseStart_4575706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575720 : List Nat := [2, 1, 4, 1, 1, 5, 2, 1, 1, 5]
def baseStart_4575720 : Nat := 118140960795 + 4575720 * 2 ^ 59
def prefixEnd_4575720 : Nat := 4983230072969 + 3 ^ 40 * 4575720 * 2
def baseEnd_4575720 : Nat := 783181233463647569385551

theorem tailTrace_4575720 : CollatzResearch.WordTrace tailWord_4575720 prefixEnd_4575720 783181233463647569385551 := by
  unfold tailWord_4575720
  simp only [CollatzResearch.WordTrace]
  refine ⟨83445109491477692802522307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111260145988636923736696409 83445109491477692802522307)
  ·
    refine ⟨125167664237216539203783461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83445109491477692802522307 125167664237216539203783461)
    ·
      refine ⟨23468937044478101100709399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125167664237216539203783461 23468937044478101100709399)
      ·
        refine ⟨35203405566717151651064099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23468937044478101100709399 35203405566717151651064099)
        ·
          refine ⟨52805108350075727476596149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35203405566717151651064099 52805108350075727476596149)
          ·
            refine ⟨4950478907819599450930889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52805108350075727476596149 4950478907819599450930889)
            ·
              refine ⟨3712859180864699588198167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4950478907819599450930889 3712859180864699588198167)
              ·
                refine ⟨5569288771297049382297251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3712859180864699588198167 5569288771297049382297251)
                ·
                  refine ⟨8353933156945574073445877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5569288771297049382297251 8353933156945574073445877)
                  ·
                    refine ⟨783181233463647569385551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8353933156945574073445877 783181233463647569385551)
                    ·
                      rfl

theorem cell23_4575720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_4575720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575720 prefixEnd_4575720 := by exact prefixLift 4575720
  have htrace : WordTrace (prefixWord ++ tailWord_4575720) baseStart_4575720 baseEnd_4575720 := by
    simpa [prefixWord, tailWord_4575720, baseEnd_4575720] using wordTrace_append hprefix tailTrace_4575720
  have hstable : (prefixWord ++ tailWord_4575720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575720).length < 2 ^ (prefixWord ++ tailWord_4575720).sum := by decide
  have hdescent : baseEnd_4575720 < baseStart_4575720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575723 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 5, 2, 2]
def baseStart_4575723 : Nat := 118140960795 + 4575723 * 2 ^ 59
def prefixEnd_4575723 : Nat := 4983230072969 + 3 ^ 40 * 4575723 * 2
def baseEnd_4575723 : Nat := 2349545240832906196419139

theorem tailTrace_4575723 : CollatzResearch.WordTrace tailWord_4575723 prefixEnd_4575723 2349545240832906196419139 := by
  unfold tailWord_4575723
  simp only [CollatzResearch.WordTrace]
  refine ⟨166890328401944517117403823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111260218934629678078269215 166890328401944517117403823)
  ·
    refine ⟨250335492602916775676105735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166890328401944517117403823 250335492602916775676105735)
    ·
      refine ⟨375503238904375163514158603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250335492602916775676105735 375503238904375163514158603)
      ·
        refine ⟨563254858356562745271237905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375503238904375163514158603 563254858356562745271237905)
        ·
          refine ⟨422441143767422058953428429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563254858356562745271237905 422441143767422058953428429)
          ·
            refine ⟨158415428912783272107535661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 422441143767422058953428429 158415428912783272107535661)
            ·
              refine ⟨59405785842293727040325873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158415428912783272107535661 59405785842293727040325873)
              ·
                refine ⟨44554339381720295280244405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59405785842293727040325873 44554339381720295280244405)
                ·
                  refine ⟨4176969317036277682522913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44554339381720295280244405 4176969317036277682522913)
                  ·
                    refine ⟨3132726987777208261892185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4176969317036277682522913 3132726987777208261892185)
                    ·
                      refine ⟨2349545240832906196419139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3132726987777208261892185 2349545240832906196419139)
                      ·
                        rfl

theorem cell23_4575723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 2, 2].length) (baseStart_4575723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575723 prefixEnd_4575723 := by exact prefixLift 4575723
  have htrace : WordTrace (prefixWord ++ tailWord_4575723) baseStart_4575723 baseEnd_4575723 := by
    simpa [prefixWord, tailWord_4575723, baseEnd_4575723] using wordTrace_append hprefix tailTrace_4575723
  have hstable : (prefixWord ++ tailWord_4575723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575723).length < 2 ^ (prefixWord ++ tailWord_4575723).sum := by decide
  have hdescent : baseEnd_4575723 < baseStart_4575723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575729 : List Nat := [1, 2, 2, 2, 3, 1, 12]
def baseStart_4575729 : Nat := 118140960795 + 4575729 * 2 ^ 59
def prefixEnd_4575729 : Nat := 4983230072969 + 3 ^ 40 * 4575729 * 2
def baseEnd_4575729 : Nat := 29006769403911520653631

theorem tailTrace_4575729 : CollatzResearch.WordTrace tailWord_4575729 prefixEnd_4575729 29006769403911520653631 := by
  unfold tailWord_4575729
  simp only [CollatzResearch.WordTrace]
  refine ⟨166890547239922780142122241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111260364826615186761414827 166890547239922780142122241)
  ·
    refine ⟨125167910429942085106591681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166890547239922780142122241 125167910429942085106591681)
    ·
      refine ⟨93875932822456563829943761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125167910429942085106591681 93875932822456563829943761)
      ·
        refine ⟨70406949616842422872457821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93875932822456563829943761 70406949616842422872457821)
        ·
          refine ⟨26402606106315908577171683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70406949616842422872457821 26402606106315908577171683)
          ·
            refine ⟨39603909159473862865757525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26402606106315908577171683 39603909159473862865757525)
            ·
              refine ⟨29006769403911520653631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 39603909159473862865757525 29006769403911520653631)
              ·
                rfl

theorem cell23_4575729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 12].length) (baseStart_4575729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575729 prefixEnd_4575729 := by exact prefixLift 4575729
  have htrace : WordTrace (prefixWord ++ tailWord_4575729) baseStart_4575729 baseEnd_4575729 := by
    simpa [prefixWord, tailWord_4575729, baseEnd_4575729] using wordTrace_append hprefix tailTrace_4575729
  have hstable : (prefixWord ++ tailWord_4575729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575729).length < 2 ^ (prefixWord ++ tailWord_4575729).sum := by decide
  have hdescent : baseEnd_4575729 < baseStart_4575729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575757 : List Nat := [1, 7, 1, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_4575757 : Nat := 118140960795 + 4575757 * 2 ^ 59
def prefixEnd_4575757 : Nat := 4983230072969 + 3 ^ 40 * 4575757 * 2
def baseEnd_4575757 : Nat := 2349562699175159063393983

theorem tailTrace_4575757 : CollatzResearch.WordTrace tailWord_4575757 prefixEnd_4575757 2349562699175159063393983 := by
  unfold tailWord_4575757
  simp only [CollatzResearch.WordTrace]
  refine ⟨166891568483821340924141525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111261045655880893949427683 166891568483821340924141525)
  ·
    refine ⟨3911521136339562677909567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 166891568483821340924141525 3911521136339562677909567)
    ·
      refine ⟨5867281704509344016864351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911521136339562677909567 5867281704509344016864351)
      ·
        refine ⟨8800922556764016025296527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5867281704509344016864351 8800922556764016025296527)
        ·
          refine ⟨13201383835146024037944791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8800922556764016025296527 13201383835146024037944791)
          ·
            refine ⟨19802075752719036056917187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13201383835146024037944791 19802075752719036056917187)
            ·
              refine ⟨29703113629078554085375781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19802075752719036056917187 29703113629078554085375781)
              ·
                refine ⟨5569333805452228891007959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29703113629078554085375781 5569333805452228891007959)
                ·
                  refine ⟨8354000708178343336511939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5569333805452228891007959 8354000708178343336511939)
                  ·
                    refine ⟨12531001062267515004767909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8354000708178343336511939 12531001062267515004767909)
                    ·
                      refine ⟨2349562699175159063393983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12531001062267515004767909 2349562699175159063393983)
                      ·
                        rfl

theorem cell23_4575757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_4575757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575757 prefixEnd_4575757 := by exact prefixLift 4575757
  have htrace : WordTrace (prefixWord ++ tailWord_4575757) baseStart_4575757 baseEnd_4575757 := by
    simpa [prefixWord, tailWord_4575757, baseEnd_4575757] using wordTrace_append hprefix tailTrace_4575757
  have hstable : (prefixWord ++ tailWord_4575757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575757).length < 2 ^ (prefixWord ++ tailWord_4575757).sum := by decide
  have hdescent : baseEnd_4575757 < baseStart_4575757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575759 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 4, 7]
def baseStart_4575759 : Nat := 118140960795 + 4575759 * 2 ^ 59
def prefixEnd_4575759 : Nat := 4983230072969 + 3 ^ 40 * 4575759 * 2
def baseEnd_4575759 : Nat := 783187908712156018522991

theorem tailTrace_4575759 : CollatzResearch.WordTrace tailWord_4575759 prefixEnd_4575759 783187908712156018522991 := by
  unfold tailWord_4575759
  simp only [CollatzResearch.WordTrace]
  refine ⟨166891641429814095265714331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111261094286542730177142887 166891641429814095265714331)
  ·
    refine ⟨250337462144721142898571497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166891641429814095265714331 250337462144721142898571497)
    ·
      refine ⟨187753096608540857173928623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250337462144721142898571497 187753096608540857173928623)
      ·
        refine ⟨281629644912811285760892935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187753096608540857173928623 281629644912811285760892935)
        ·
          refine ⟨422444467369216928641339403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281629644912811285760892935 422444467369216928641339403)
          ·
            refine ⟨633666701053825392962009105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422444467369216928641339403 633666701053825392962009105)
            ·
              refine ⟨475250025790369044721506829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633666701053825392962009105 475250025790369044721506829)
              ·
                refine ⟨178218759671388391770565061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 475250025790369044721506829 178218759671388391770565061)
                ·
                  refine ⟨33416017438385323456980949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178218759671388391770565061 33416017438385323456980949)
                  ·
                    refine ⟨783187908712156018522991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33416017438385323456980949 783187908712156018522991)
                    ·
                      rfl

theorem cell23_4575759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_4575759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575759 prefixEnd_4575759 := by exact prefixLift 4575759
  have htrace : WordTrace (prefixWord ++ tailWord_4575759) baseStart_4575759 baseEnd_4575759 := by
    simpa [prefixWord, tailWord_4575759, baseEnd_4575759] using wordTrace_append hprefix tailTrace_4575759
  have hstable : (prefixWord ++ tailWord_4575759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575759).length < 2 ^ (prefixWord ++ tailWord_4575759).sum := by decide
  have hdescent : baseEnd_4575759 < baseStart_4575759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575780 : List Nat := [2, 3, 1, 5, 2, 1, 9]
def baseStart_4575780 : Nat := 118140960795 + 4575780 * 2 ^ 59
def prefixEnd_4575780 : Nat := 4983230072969 + 3 ^ 40 * 4575780 * 2
def baseEnd_4575780 : Nat := 29007092706545833005017

theorem tailTrace_4575780 : CollatzResearch.WordTrace tailWord_4575780 prefixEnd_4575780 29007092706545833005017 := by
  unfold tailWord_4575780
  simp only [CollatzResearch.WordTrace]
  refine ⟨83446203681369007926114397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111261604908492010568152529 83446203681369007926114397)
  ·
    refine ⟨31292326380513377972292899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83446203681369007926114397 31292326380513377972292899)
    ·
      refine ⟨46938489570770066958439349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31292326380513377972292899 46938489570770066958439349)
      ·
        refine ⟨4400483397259693777353689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46938489570770066958439349 4400483397259693777353689)
        ·
          refine ⟨3300362547944770333015267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4400483397259693777353689 3300362547944770333015267)
          ·
            refine ⟨4950543821917155499522901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300362547944770333015267 4950543821917155499522901)
            ·
              refine ⟨29007092706545833005017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4950543821917155499522901 29007092706545833005017)
              ·
                rfl

theorem cell23_4575780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 9].length) (baseStart_4575780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575780 prefixEnd_4575780 := by exact prefixLift 4575780
  have htrace : WordTrace (prefixWord ++ tailWord_4575780) baseStart_4575780 baseEnd_4575780 := by
    simpa [prefixWord, tailWord_4575780, baseEnd_4575780] using wordTrace_append hprefix tailTrace_4575780
  have hstable : (prefixWord ++ tailWord_4575780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575780).length < 2 ^ (prefixWord ++ tailWord_4575780).sum := by decide
  have hdescent : baseEnd_4575780 < baseStart_4575780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575898 : List Nat := [3, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2]
def baseStart_4575898 : Nat := 118140960795 + 4575898 * 2 ^ 59
def prefixEnd_4575898 : Nat := 4983230072969 + 3 ^ 40 * 4575898 * 2
def baseEnd_4575898 : Nat := 2349635099947443011730835

theorem tailTrace_4575898 : CollatzResearch.WordTrace tailWord_4575898 prefixEnd_4575898 2349635099947443011730835 := by
  unfold tailWord_4575898
  simp only [CollatzResearch.WordTrace]
  refine ⟨41724177794077630501256087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111264474117540348003349565 41724177794077630501256087)
  ·
    refine ⟨62586266691116445751884131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41724177794077630501256087 62586266691116445751884131)
    ·
      refine ⟨93879400036674668627826197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62586266691116445751884131 93879400036674668627826197)
      ·
        refine ⟨4400596876719125091929353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93879400036674668627826197 4400596876719125091929353)
        ·
          refine ⟨3300447657539343818947015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4400596876719125091929353 3300447657539343818947015)
          ·
            refine ⟨4950671486309015728420523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300447657539343818947015 4950671486309015728420523)
            ·
              refine ⟨7426007229463523592630785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4950671486309015728420523 7426007229463523592630785)
              ·
                refine ⟨5569505422097642694473089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7426007229463523592630785 5569505422097642694473089)
                ·
                  refine ⟨4177129066573232020854817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5569505422097642694473089 4177129066573232020854817)
                  ·
                    refine ⟨3132846799929924015641113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4177129066573232020854817 3132846799929924015641113)
                    ·
                      refine ⟨2349635099947443011730835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3132846799929924015641113 2349635099947443011730835)
                      ·
                        rfl

theorem cell23_4575898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_4575898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575898 prefixEnd_4575898 := by exact prefixLift 4575898
  have htrace : WordTrace (prefixWord ++ tailWord_4575898) baseStart_4575898 baseEnd_4575898 := by
    simpa [prefixWord, tailWord_4575898, baseEnd_4575898] using wordTrace_append hprefix tailTrace_4575898
  have hstable : (prefixWord ++ tailWord_4575898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575898).length < 2 ^ (prefixWord ++ tailWord_4575898).sum := by decide
  have hdescent : baseEnd_4575898 < baseStart_4575898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575913 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 3, 4]
def baseStart_4575913 : Nat := 118140960795 + 4575913 * 2 ^ 59
def prefixEnd_4575913 : Nat := 4983230072969 + 3 ^ 40 * 4575913 * 2
def baseEnd_4575913 : Nat := 783214267385753484347755

theorem tailTrace_4575913 : CollatzResearch.WordTrace tailWord_4575913 prefixEnd_4575913 783214267385753484347755 := by
  unfold tailWord_4575913
  simp only [CollatzResearch.WordTrace]
  refine ⟨166897258271256179566820393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111264838847504119711213595 166897258271256179566820393)
  ·
    refine ⟨125172943703442134675115295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166897258271256179566820393 125172943703442134675115295)
    ·
      refine ⟨187759415555163202012672943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125172943703442134675115295 187759415555163202012672943)
      ·
        refine ⟨281639123332744803019009415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187759415555163202012672943 281639123332744803019009415)
        ·
          refine ⟨422458684999117204528514123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281639123332744803019009415 422458684999117204528514123)
          ·
            refine ⟨633688027498675806792771185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422458684999117204528514123 633688027498675806792771185)
            ·
              refine ⟨475266020624006855094578389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633688027498675806792771185 475266020624006855094578389)
              ·
                refine ⟨11139047358375160666279181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 475266020624006855094578389 11139047358375160666279181)
                ·
                  refine ⟨4177142759390685249854693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11139047358375160666279181 4177142759390685249854693)
                  ·
                    refine ⟨783214267385753484347755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4177142759390685249854693 783214267385753484347755)
                    ·
                      rfl

theorem cell23_4575913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 4].length) (baseStart_4575913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575913 prefixEnd_4575913 := by exact prefixLift 4575913
  have htrace : WordTrace (prefixWord ++ tailWord_4575913) baseStart_4575913 baseEnd_4575913 := by
    simpa [prefixWord, tailWord_4575913, baseEnd_4575913] using wordTrace_append hprefix tailTrace_4575913
  have hstable : (prefixWord ++ tailWord_4575913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575913).length < 2 ^ (prefixWord ++ tailWord_4575913).sum := by decide
  have hdescent : baseEnd_4575913 < baseStart_4575913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575923 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 3]
def baseStart_4575923 : Nat := 118140960795 + 4575923 * 2 ^ 59
def prefixEnd_4575923 : Nat := 4983230072969 + 3 ^ 40 * 4575923 * 2
def baseEnd_4575923 : Nat := 2349647936963805413918219

theorem tailTrace_4575923 : CollatzResearch.WordTrace tailWord_4575923 prefixEnd_4575923 2349647936963805413918219 := by
  unfold tailWord_4575923
  simp only [CollatzResearch.WordTrace]
  refine ⟨166897623001219951274684423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111265082000813300849789615 166897623001219951274684423)
  ·
    refine ⟨250346434501829926912026635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166897623001219951274684423 250346434501829926912026635)
    ·
      refine ⟨375519651752744890368039953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250346434501829926912026635 375519651752744890368039953)
      ·
        refine ⟨281639738814558667776029965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375519651752744890368039953 281639738814558667776029965)
        ·
          refine ⟨105614902055459500416011237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 281639738814558667776029965 105614902055459500416011237)
          ·
            refine ⟨19802794135398656328002107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105614902055459500416011237 19802794135398656328002107)
            ·
              refine ⟨29704191203097984492003161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19802794135398656328002107 29704191203097984492003161)
              ·
                refine ⟨22278143402323488369002371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29704191203097984492003161 22278143402323488369002371)
                ·
                  refine ⟨33417215103485232553503557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22278143402323488369002371 33417215103485232553503557)
                  ·
                    refine ⟨6265727831903481103781917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33417215103485232553503557 6265727831903481103781917)
                    ·
                      refine ⟨2349647936963805413918219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6265727831903481103781917 2349647936963805413918219)
                      ·
                        rfl

theorem cell23_4575923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 3].length) (baseStart_4575923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575923 prefixEnd_4575923 := by exact prefixLift 4575923
  have htrace : WordTrace (prefixWord ++ tailWord_4575923) baseStart_4575923 baseEnd_4575923 := by
    simpa [prefixWord, tailWord_4575923, baseEnd_4575923] using wordTrace_append hprefix tailTrace_4575923
  have hstable : (prefixWord ++ tailWord_4575923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575923).length < 2 ^ (prefixWord ++ tailWord_4575923).sum := by decide
  have hdescent : baseEnd_4575923 < baseStart_4575923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575940 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_4575940 : Nat := 118140960795 + 4575940 * 2 ^ 59
def prefixEnd_4575940 : Nat := 4983230072969 + 3 ^ 40 * 4575940 * 2
def baseEnd_4575940 : Nat := 2349656666134931847405641

theorem tailTrace_4575940 : CollatzResearch.WordTrace tailWord_4575940 prefixEnd_4575940 2349656666134931847405641 := by
  unfold tailWord_4575940
  simp only [CollatzResearch.WordTrace]
  refine ⟨83449121521079181589026637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111265495361438908785368849 83449121521079181589026637)
  ·
    refine ⟨31293420570404693095884989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83449121521079181589026637 31293420570404693095884989)
    ·
      refine ⟨11735032713901759910956871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31293420570404693095884989 11735032713901759910956871)
      ·
        refine ⟨17602549070852639866435307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11735032713901759910956871 17602549070852639866435307)
        ·
          refine ⟨26403823606278959799652961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17602549070852639866435307 26403823606278959799652961)
          ·
            refine ⟨19802867704709219849739721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26403823606278959799652961 19802867704709219849739721)
            ·
              refine ⟨14852150778531914887304791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19802867704709219849739721 14852150778531914887304791)
              ·
                refine ⟨22278226167797872330957187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14852150778531914887304791 22278226167797872330957187)
                ·
                  refine ⟨33417339251696808496435781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22278226167797872330957187 33417339251696808496435781)
                  ·
                    refine ⟨6265751109693151593081709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33417339251696808496435781 6265751109693151593081709)
                    ·
                      refine ⟨2349656666134931847405641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6265751109693151593081709 2349656666134931847405641)
                      ·
                        rfl

theorem cell23_4575940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_4575940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575940 prefixEnd_4575940 := by exact prefixLift 4575940
  have htrace : WordTrace (prefixWord ++ tailWord_4575940) baseStart_4575940 baseEnd_4575940 := by
    simpa [prefixWord, tailWord_4575940, baseEnd_4575940] using wordTrace_append hprefix tailTrace_4575940
  have hstable : (prefixWord ++ tailWord_4575940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575940).length < 2 ^ (prefixWord ++ tailWord_4575940).sum := by decide
  have hdescent : baseEnd_4575940 < baseStart_4575940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575964 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 3, 4]
def baseStart_4575964 : Nat := 118140960795 + 4575964 * 2 ^ 59
def prefixEnd_4575964 : Nat := 4983230072969 + 3 ^ 40 * 4575964 * 2
def baseEnd_4575964 : Nat := 783222996556879917835177

theorem tailTrace_4575964 : CollatzResearch.WordTrace tailWord_4575964 prefixEnd_4575964 783222996556879917835177 := by
  unfold tailWord_4575964
  simp only [CollatzResearch.WordTrace]
  refine ⟨83449559197035707638463473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111266078929380943517951297 83449559197035707638463473)
  ·
    refine ⟨62587169397776780728847605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83449559197035707638463473 62587169397776780728847605)
    ·
      refine ⟨5867547131041573193329463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62587169397776780728847605 5867547131041573193329463)
      ·
        refine ⟨8801320696562359789994195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5867547131041573193329463 8801320696562359789994195)
        ·
          refine ⟨13201981044843539684991293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8801320696562359789994195 13201981044843539684991293)
          ·
            refine ⟨4950742891816327381871735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13201981044843539684991293 4950742891816327381871735)
            ·
              refine ⟨7426114337724491072807603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4950742891816327381871735 7426114337724491072807603)
              ·
                refine ⟨11139171506586736609211405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7426114337724491072807603 11139171506586736609211405)
                ·
                  refine ⟨4177189314970026228454277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11139171506586736609211405 4177189314970026228454277)
                  ·
                    refine ⟨783222996556879917835177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4177189314970026228454277 783222996556879917835177)
                    ·
                      rfl

theorem cell23_4575964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_4575964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575964 prefixEnd_4575964 := by exact prefixLift 4575964
  have htrace : WordTrace (prefixWord ++ tailWord_4575964) baseStart_4575964 baseEnd_4575964 := by
    simpa [prefixWord, tailWord_4575964, baseEnd_4575964] using wordTrace_append hprefix tailTrace_4575964
  have hstable : (prefixWord ++ tailWord_4575964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575964).length < 2 ^ (prefixWord ++ tailWord_4575964).sum := by decide
  have hdescent : baseEnd_4575964 < baseStart_4575964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575980 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 6, 3, 2]
def baseStart_4575980 : Nat := 118140960795 + 4575980 * 2 ^ 59
def prefixEnd_4575980 : Nat := 4983230072969 + 3 ^ 40 * 4575980 * 2
def baseEnd_4575980 : Nat := 2349677205361111690905457

theorem tailTrace_4575980 : CollatzResearch.WordTrace tailWord_4575980 prefixEnd_4575980 2349677205361111690905457 := by
  unfold tailWord_4575980
  simp only [CollatzResearch.WordTrace]
  refine ⟨83449850981006725004754697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111266467974675633339672929 83449850981006725004754697)
  ·
    refine ⟨62587388235755043753566023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83449850981006725004754697 62587388235755043753566023)
    ·
      refine ⟨93881082353632565630349035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62587388235755043753566023 93881082353632565630349035)
      ·
        refine ⟨140821623530448848445523553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93881082353632565630349035 140821623530448848445523553)
        ·
          refine ⟨105616217647836636334142665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140821623530448848445523553 105616217647836636334142665)
          ·
            refine ⟨79212163235877477250606999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105616217647836636334142665 79212163235877477250606999)
            ·
              refine ⟨118818244853816215875910499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79212163235877477250606999 118818244853816215875910499)
              ·
                refine ⟨178227367280724323813865749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118818244853816215875910499 178227367280724323813865749)
                ·
                  refine ⟨8354407841283952678774957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 178227367280724323813865749 8354407841283952678774957)
                  ·
                    refine ⟨3132902940481482254540609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8354407841283952678774957 3132902940481482254540609)
                    ·
                      refine ⟨2349677205361111690905457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3132902940481482254540609 2349677205361111690905457)
                      ·
                        rfl

theorem cell23_4575980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 3, 2].length) (baseStart_4575980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575980 prefixEnd_4575980 := by exact prefixLift 4575980
  have htrace : WordTrace (prefixWord ++ tailWord_4575980) baseStart_4575980 baseEnd_4575980 := by
    simpa [prefixWord, tailWord_4575980, baseEnd_4575980] using wordTrace_append hprefix tailTrace_4575980
  have hstable : (prefixWord ++ tailWord_4575980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575980).length < 2 ^ (prefixWord ++ tailWord_4575980).sum := by decide
  have hdescent : baseEnd_4575980 < baseStart_4575980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575990 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_4575990 : Nat := 118140960795 + 4575990 * 2 ^ 59
def prefixEnd_4575990 : Nat := 4983230072969 + 3 ^ 40 * 4575990 * 2
def baseEnd_4575990 : Nat := 783227446722552217260137

theorem tailTrace_4575990 : CollatzResearch.WordTrace tailWord_4575990 prefixEnd_4575990 783227446722552217260137 := by
  unfold tailWord_4575990
  simp only [CollatzResearch.WordTrace]
  refine ⟨10431254168248576357335839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111266711127984814478248949 10431254168248576357335839)
  ·
    refine ⟨15646881252372864536003759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10431254168248576357335839 15646881252372864536003759)
    ·
      refine ⟨23470321878559296804005639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15646881252372864536003759 23470321878559296804005639)
      ·
        refine ⟨35205482817838945206008459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23470321878559296804005639 35205482817838945206008459)
        ·
          refine ⟨52808224226758417809012689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35205482817838945206008459 52808224226758417809012689)
          ·
            refine ⟨39606168170068813356759517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52808224226758417809012689 39606168170068813356759517)
            ·
              refine ⟨14852313063775805008784819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39606168170068813356759517 14852313063775805008784819)
              ·
                refine ⟨22278469595663707513177229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14852313063775805008784819 22278469595663707513177229)
                ·
                  refine ⟨8354426098373890317441461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22278469595663707513177229 8354426098373890317441461)
                  ·
                    refine ⟨783227446722552217260137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8354426098373890317441461 783227446722552217260137)
                    ·
                      rfl

theorem cell23_4575990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_4575990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575990 prefixEnd_4575990 := by exact prefixLift 4575990
  have htrace : WordTrace (prefixWord ++ tailWord_4575990) baseStart_4575990 baseEnd_4575990 := by
    simpa [prefixWord, tailWord_4575990, baseEnd_4575990] using wordTrace_append hprefix tailTrace_4575990
  have hstable : (prefixWord ++ tailWord_4575990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575990).length < 2 ^ (prefixWord ++ tailWord_4575990).sum := by decide
  have hdescent : baseEnd_4575990 < baseStart_4575990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4575997 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 2, 3, 2]
def baseStart_4575997 : Nat := 118140960795 + 4575997 * 2 ^ 59
def prefixEnd_4575997 : Nat := 4983230072969 + 3 ^ 40 * 4575997 * 2
def baseEnd_4575997 : Nat := 2349685934532238124392879

theorem tailTrace_4575997 : CollatzResearch.WordTrace tailWord_4575997 prefixEnd_4575997 2349685934532238124392879 := by
  unfold tailWord_4575997
  simp only [CollatzResearch.WordTrace]
  refine ⟨166900322002951861912878245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111266881335301241275252163 166900322002951861912878245)
  ·
    refine ⟨31293810375553474108664671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166900322002951861912878245 31293810375553474108664671)
    ·
      refine ⟨46940715563330211162997007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31293810375553474108664671 46940715563330211162997007)
      ·
        refine ⟨70411073344995316744495511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46940715563330211162997007 70411073344995316744495511)
        ·
          refine ⟨105616610017492975116743267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70411073344995316744495511 105616610017492975116743267)
          ·
            refine ⟨158424915026239462675114901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105616610017492975116743267 158424915026239462675114901)
            ·
              refine ⟨7426167891854974812896011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 158424915026239462675114901 7426167891854974812896011)
              ·
                refine ⟨11139251837782462219344017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7426167891854974812896011 11139251837782462219344017)
                ·
                  refine ⟨8354438878336846664508013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11139251837782462219344017 8354438878336846664508013)
                  ·
                    refine ⟨3132914579376317499190505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8354438878336846664508013 3132914579376317499190505)
                    ·
                      refine ⟨2349685934532238124392879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3132914579376317499190505 2349685934532238124392879)
                      ·
                        rfl

theorem cell23_4575997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_4575997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4575997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4575997 prefixEnd_4575997 := by exact prefixLift 4575997
  have htrace : WordTrace (prefixWord ++ tailWord_4575997) baseStart_4575997 baseEnd_4575997 := by
    simpa [prefixWord, tailWord_4575997, baseEnd_4575997] using wordTrace_append hprefix tailTrace_4575997
  have hstable : (prefixWord ++ tailWord_4575997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4575997).length < 2 ^ (prefixWord ++ tailWord_4575997).sum := by decide
  have hdescent : baseEnd_4575997 < baseStart_4575997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4575997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576004 : List Nat := [2, 3, 2, 2, 1, 1, 2, 5, 1, 1, 3]
def baseStart_4576004 : Nat := 118140960795 + 4576004 * 2 ^ 59
def prefixEnd_4576004 : Nat := 4983230072969 + 3 ^ 40 * 4576004 * 2
def baseEnd_4576004 : Nat := 2349689528896819597005347

theorem tailTrace_4576004 : CollatzResearch.WordTrace tailWord_4576004 prefixEnd_4576004 2349689528896819597005347 := by
  unfold tailWord_4576004
  simp only [CollatzResearch.WordTrace]
  refine ⟨83450288656963251054191533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111267051542617668072255377 83450288656963251054191533)
  ·
    refine ⟨31293858246361219145321825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83450288656963251054191533 31293858246361219145321825)
    ·
      refine ⟨23470393684770914358991369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31293858246361219145321825 23470393684770914358991369)
      ·
        refine ⟨17602795263578185769243527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23470393684770914358991369 17602795263578185769243527)
        ·
          refine ⟨26404192895367278653865291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17602795263578185769243527 26404192895367278653865291)
          ·
            refine ⟨39606289343050917980797937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26404192895367278653865291 39606289343050917980797937)
            ·
              refine ⟨29704717007288188485598453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39606289343050917980797937 29704717007288188485598453)
              ·
                refine ⟨2784817219433267670524855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29704717007288188485598453 2784817219433267670524855)
                ·
                  refine ⟨4177225829149901505787283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2784817219433267670524855 4177225829149901505787283)
                  ·
                    refine ⟨6265838743724852258680925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4177225829149901505787283 6265838743724852258680925)
                    ·
                      refine ⟨2349689528896819597005347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6265838743724852258680925 2349689528896819597005347)
                      ·
                        rfl

theorem cell23_4576004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_4576004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576004 prefixEnd_4576004 := by exact prefixLift 4576004
  have htrace : WordTrace (prefixWord ++ tailWord_4576004) baseStart_4576004 baseEnd_4576004 := by
    simpa [prefixWord, tailWord_4576004, baseEnd_4576004] using wordTrace_append hprefix tailTrace_4576004
  have hstable : (prefixWord ++ tailWord_4576004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576004).length < 2 ^ (prefixWord ++ tailWord_4576004).sum := by decide
  have hdescent : baseEnd_4576004 < baseStart_4576004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576050 : List Nat := [3, 2, 1, 1, 3, 1, 5, 7]
def baseStart_4576050 : Nat := 118140960795 + 4576050 * 2 ^ 59
def prefixEnd_4576050 : Nat := 4983230072969 + 3 ^ 40 * 4576050 * 2
def baseEnd_4576050 : Nat := 87026412926182459890005

theorem tailTrace_4576050 : CollatzResearch.WordTrace tailWord_4576050 prefixEnd_4576050 87026412926182459890005 := by
  unfold tailWord_4576050
  simp only [CollatzResearch.WordTrace]
  refine ⟨41725563767939962991139401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111268170047839901309705069 41725563767939962991139401)
  ·
    refine ⟨31294172825954972243354551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41725563767939962991139401 31294172825954972243354551)
    ·
      refine ⟨46941259238932458365031827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31294172825954972243354551 46941259238932458365031827)
      ·
        refine ⟨70411888858398687547547741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46941259238932458365031827 70411888858398687547547741)
        ·
          refine ⟨26404458321899507830330403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70411888858398687547547741 26404458321899507830330403)
          ·
            refine ⟨39606687482849261745495605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26404458321899507830330403 39606687482849261745495605)
            ·
              refine ⟨3713126951517118288640213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39606687482849261745495605 3713126951517118288640213)
              ·
                refine ⟨87026412926182459890005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3713126951517118288640213 87026412926182459890005)
                ·
                  rfl

theorem cell23_4576050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 7].length) (baseStart_4576050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576050 prefixEnd_4576050 := by exact prefixLift 4576050
  have htrace : WordTrace (prefixWord ++ tailWord_4576050) baseStart_4576050 baseEnd_4576050 := by
    simpa [prefixWord, tailWord_4576050, baseEnd_4576050] using wordTrace_append hprefix tailTrace_4576050
  have hstable : (prefixWord ++ tailWord_4576050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576050).length < 2 ^ (prefixWord ++ tailWord_4576050).sum := by decide
  have hdescent : baseEnd_4576050 < baseStart_4576050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576061 : List Nat := [1, 4, 1, 4, 2, 2, 2, 1, 1, 1, 4]
def baseStart_4576061 : Nat := 118140960795 + 4576061 * 2 ^ 59
def prefixEnd_4576061 : Nat := 4983230072969 + 3 ^ 40 * 4576061 * 2
def baseEnd_4576061 : Nat := 2349718797294125873992585

theorem tailTrace_4576061 : CollatzResearch.WordTrace tailWord_4576061 prefixEnd_4576061 2349718797294125873992585 := by
  unfold tailWord_4576061
  simp only [CollatzResearch.WordTrace]
  refine ⟨166902656274720000843208037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111268437516480000562138691 166902656274720000843208037)
  ·
    refine ⟨31294248051510000158101507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166902656274720000843208037 31294248051510000158101507)
    ·
      refine ⟨46941372077265000237152261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31294248051510000158101507 46941372077265000237152261)
      ·
        refine ⟨8801507264487187544466049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46941372077265000237152261 8801507264487187544466049)
        ·
          refine ⟨6601130448365390658349537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8801507264487187544466049 6601130448365390658349537)
          ·
            refine ⟨4950847836274042993762153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6601130448365390658349537 4950847836274042993762153)
            ·
              refine ⟨3713135877205532245321615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4950847836274042993762153 3713135877205532245321615)
              ·
                refine ⟨5569703815808298367982423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3713135877205532245321615 5569703815808298367982423)
                ·
                  refine ⟨8354555723712447551973635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5569703815808298367982423 8354555723712447551973635)
                  ·
                    refine ⟨12531833585568671327960453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8354555723712447551973635 12531833585568671327960453)
                    ·
                      refine ⟨2349718797294125873992585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12531833585568671327960453 2349718797294125873992585)
                      ·
                        rfl

theorem cell23_4576061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_4576061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576061 prefixEnd_4576061 := by exact prefixLift 4576061
  have htrace : WordTrace (prefixWord ++ tailWord_4576061) baseStart_4576061 baseEnd_4576061 := by
    simpa [prefixWord, tailWord_4576061, baseEnd_4576061] using wordTrace_append hprefix tailTrace_4576061
  have hstable : (prefixWord ++ tailWord_4576061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576061).length < 2 ^ (prefixWord ++ tailWord_4576061).sum := by decide
  have hdescent : baseEnd_4576061 < baseStart_4576061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576083 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 4]
def baseStart_4576083 : Nat := 118140960795 + 4576083 * 2 ^ 59
def prefixEnd_4576083 : Nat := 4983230072969 + 3 ^ 40 * 4576083 * 2
def baseEnd_4576083 : Nat := 2349730093868524787917483

theorem tailTrace_4576083 : CollatzResearch.WordTrace tailWord_4576083 prefixEnd_4576083 2349730093868524787917483 := by
  unfold tailWord_4576083
  simp only [CollatzResearch.WordTrace]
  refine ⟨166903458680640298600508903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111268972453760199067005935 166903458680640298600508903)
  ·
    refine ⟨250355188020960447900763355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166903458680640298600508903 250355188020960447900763355)
    ·
      refine ⟨375532782031440671851145033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250355188020960447900763355 375532782031440671851145033)
      ·
        refine ⟨281649586523580503888358775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375532782031440671851145033 281649586523580503888358775)
        ·
          refine ⟨422474379785370755832538163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281649586523580503888358775 422474379785370755832538163)
          ·
            refine ⟨633711569678056133748807245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422474379785370755832538163 633711569678056133748807245)
            ·
              refine ⟨237641838629271050155802717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 633711569678056133748807245 237641838629271050155802717)
              ·
                refine ⟨89115689485976643808426019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237641838629271050155802717 89115689485976643808426019)
                ·
                  refine ⟨133673534228964965712639029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89115689485976643808426019 133673534228964965712639029)
                  ·
                    refine ⟨12531893833965465535559909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 133673534228964965712639029 12531893833965465535559909)
                    ·
                      refine ⟨2349730093868524787917483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12531893833965465535559909 2349730093868524787917483)
                      ·
                        rfl

theorem cell23_4576083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_4576083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576083 prefixEnd_4576083 := by exact prefixLift 4576083
  have htrace : WordTrace (prefixWord ++ tailWord_4576083) baseStart_4576083 baseEnd_4576083 := by
    simpa [prefixWord, tailWord_4576083, baseEnd_4576083] using wordTrace_append hprefix tailTrace_4576083
  have hstable : (prefixWord ++ tailWord_4576083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576083).length < 2 ^ (prefixWord ++ tailWord_4576083).sum := by decide
  have hdescent : baseEnd_4576083 < baseStart_4576083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576104 : List Nat := [2, 1, 4, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_4576104 : Nat := 118140960795 + 4576104 * 2 ^ 59
def prefixEnd_4576104 : Nat := 4983230072969 + 3 ^ 40 * 4576104 * 2
def baseEnd_4576104 : Nat := 2349740876962269205754887

theorem tailTrace_4576104 : CollatzResearch.WordTrace tailWord_4576104 prefixEnd_4576104 2349740876962269205754887 := by
  unfold tailWord_4576104
  simp only [CollatzResearch.WordTrace]
  refine ⟨83452112306782109593511683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111269483075709479458015577 83452112306782109593511683)
  ·
    refine ⟨125178168460173164390267525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83452112306782109593511683 125178168460173164390267525)
    ·
      refine ⟨23470906586282468323175161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125178168460173164390267525 23470906586282468323175161)
      ·
        refine ⟨17603179939711851242381371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23470906586282468323175161 17603179939711851242381371)
        ·
          refine ⟨26404769909567776863572057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17603179939711851242381371 26404769909567776863572057)
          ·
            refine ⟨19803577432175832647679043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26404769909567776863572057 19803577432175832647679043)
            ·
              refine ⟨29705366148263748971518565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19803577432175832647679043 29705366148263748971518565)
              ·
                refine ⟨5569756152799452932159731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29705366148263748971518565 5569756152799452932159731)
                ·
                  refine ⟨8354634229199179398239597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5569756152799452932159731 8354634229199179398239597)
                  ·
                    refine ⟨3132987835949692274339849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8354634229199179398239597 3132987835949692274339849)
                    ·
                      refine ⟨2349740876962269205754887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3132987835949692274339849 2349740876962269205754887)
                      ·
                        rfl

theorem cell23_4576104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_4576104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576104 prefixEnd_4576104 := by exact prefixLift 4576104
  have htrace : WordTrace (prefixWord ++ tailWord_4576104) baseStart_4576104 baseEnd_4576104 := by
    simpa [prefixWord, tailWord_4576104, baseEnd_4576104] using wordTrace_append hprefix tailTrace_4576104
  have hstable : (prefixWord ++ tailWord_4576104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576104).length < 2 ^ (prefixWord ++ tailWord_4576104).sum := by decide
  have hdescent : baseEnd_4576104 < baseStart_4576104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576123 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 9]
def baseStart_4576123 : Nat := 118140960795 + 4576123 * 2 ^ 59
def prefixEnd_4576123 : Nat := 4983230072969 + 3 ^ 40 * 4576123 * 2
def baseEnd_4576123 : Nat := 261083403677189403490811

theorem tailTrace_4576123 : CollatzResearch.WordTrace tailWord_4576123 prefixEnd_4576123 261083403677189403490811 := by
  unfold tailWord_4576123
  simp only [CollatzResearch.WordTrace]
  refine ⟨166904917600495385431965023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111269945066996923621310015 166904917600495385431965023)
  ·
    refine ⟨250357376400743078147947535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166904917600495385431965023 250357376400743078147947535)
    ·
      refine ⟨375536064601114617221921303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250357376400743078147947535 375536064601114617221921303)
      ·
        refine ⟨563304096901671925832881955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375536064601114617221921303 563304096901671925832881955)
        ·
          refine ⟨844956145352507888749322933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563304096901671925832881955 844956145352507888749322933)
          ·
            refine ⟨79214638626797614570249025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 844956145352507888749322933 79214638626797614570249025)
            ·
              refine ⟨59410978970098210927686769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79214638626797614570249025 59410978970098210927686769)
              ·
                refine ⟨44558234227573658195765077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59410978970098210927686769 44558234227573658195765077)
                ·
                  refine ⟨261083403677189403490811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44558234227573658195765077 261083403677189403490811)
                  ·
                    rfl

theorem cell23_4576123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 9].length) (baseStart_4576123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576123 prefixEnd_4576123 := by exact prefixLift 4576123
  have htrace : WordTrace (prefixWord ++ tailWord_4576123) baseStart_4576123 baseEnd_4576123 := by
    simpa [prefixWord, tailWord_4576123, baseEnd_4576123] using wordTrace_append hprefix tailTrace_4576123
  have hstable : (prefixWord ++ tailWord_4576123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576123).length < 2 ^ (prefixWord ++ tailWord_4576123).sum := by decide
  have hdescent : baseEnd_4576123 < baseStart_4576123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576140 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 7]
def baseStart_4576140 : Nat := 118140960795 + 4576140 * 2 ^ 59
def prefixEnd_4576140 : Nat := 4983230072969 + 3 ^ 40 * 4576140 * 2
def baseEnd_4576140 : Nat := 261084373585092340544969

theorem tailTrace_4576140 : CollatzResearch.WordTrace tailWord_4576140 prefixEnd_4576140 261084373585092340544969 := by
  unfold tailWord_4576140
  simp only [CollatzResearch.WordTrace]
  refine ⟨83452768820716898667666937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111270358427622531556889249 83452768820716898667666937)
  ·
    refine ⟨62589576615537674000750203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83452768820716898667666937 62589576615537674000750203)
    ·
      refine ⟨93884364923306511001125305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62589576615537674000750203 93884364923306511001125305)
      ·
        refine ⟨70413273692479883250843979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93884364923306511001125305 70413273692479883250843979)
        ·
          refine ⟨105619910538719824876265969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70413273692479883250843979 105619910538719824876265969)
          ·
            refine ⟨79214932904039868657199477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105619910538719824876265969 79214932904039868657199477)
            ·
              refine ⟨7426399959753737686612451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79214932904039868657199477 7426399959753737686612451)
              ·
                refine ⟨11139599939630606529918677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7426399959753737686612451 11139599939630606529918677)
                ·
                  refine ⟨261084373585092340544969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11139599939630606529918677 261084373585092340544969)
                  ·
                    rfl

theorem cell23_4576140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 7].length) (baseStart_4576140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576140 prefixEnd_4576140 := by exact prefixLift 4576140
  have htrace : WordTrace (prefixWord ++ tailWord_4576140) baseStart_4576140 baseEnd_4576140 := by
    simpa [prefixWord, tailWord_4576140, baseEnd_4576140] using wordTrace_append hprefix tailTrace_4576140
  have hstable : (prefixWord ++ tailWord_4576140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576140).length < 2 ^ (prefixWord ++ tailWord_4576140).sum := by decide
  have hdescent : baseEnd_4576140 < baseStart_4576140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576207 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 1, 6, 2]
def baseStart_4576207 : Nat := 118140960795 + 4576207 * 2 ^ 59
def prefixEnd_4576207 : Nat := 4983230072969 + 3 ^ 40 * 4576207 * 2
def baseEnd_4576207 : Nat := 2349793765469682302766913

theorem tailTrace_4576207 : CollatzResearch.WordTrace tailWord_4576207 prefixEnd_4576207 2349793765469682302766913 := by
  unfold tailWord_4576207
  simp only [CollatzResearch.WordTrace]
  refine ⟨166907981332191067778022875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111271987554794045185348583 166907981332191067778022875)
  ·
    refine ⟨250361971998286601667034313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166907981332191067778022875 250361971998286601667034313)
    ·
      refine ⟨187771478998714951250275735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250361971998286601667034313 187771478998714951250275735)
      ·
        refine ⟨281657218498072426875413603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187771478998714951250275735 281657218498072426875413603)
        ·
          refine ⟨422485827747108640313120405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281657218498072426875413603 422485827747108640313120405)
          ·
            refine ⟨19804023175645717514677519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 422485827747108640313120405 19804023175645717514677519)
            ·
              refine ⟨29706034763468576272016279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19804023175645717514677519 29706034763468576272016279)
              ·
                refine ⟨44559052145202864408024419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29706034763468576272016279 44559052145202864408024419)
                ·
                  refine ⟨66838578217804296612036629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44559052145202864408024419 66838578217804296612036629)
                  ·
                    refine ⟨3133058353959576403689217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 66838578217804296612036629 3133058353959576403689217)
                    ·
                      refine ⟨2349793765469682302766913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3133058353959576403689217 2349793765469682302766913)
                      ·
                        rfl

theorem cell23_4576207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 6, 2].length) (baseStart_4576207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576207 prefixEnd_4576207 := by exact prefixLift 4576207
  have htrace : WordTrace (prefixWord ++ tailWord_4576207) baseStart_4576207 baseEnd_4576207 := by
    simpa [prefixWord, tailWord_4576207, baseEnd_4576207] using wordTrace_append hprefix tailTrace_4576207
  have hstable : (prefixWord ++ tailWord_4576207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576207).length < 2 ^ (prefixWord ++ tailWord_4576207).sum := by decide
  have hdescent : baseEnd_4576207 < baseStart_4576207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576217 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 5, 4]
def baseStart_4576217 : Nat := 118140960795 + 4576217 * 2 ^ 59
def prefixEnd_4576217 : Nat := 4983230072969 + 3 ^ 40 * 4576217 * 2
def baseEnd_4576217 : Nat := 783266300092075754547289

theorem tailTrace_4576217 : CollatzResearch.WordTrace tailWord_4576217 prefixEnd_4576217 783266300092075754547289 := by
  unfold tailWord_4576217
  simp only [CollatzResearch.WordTrace]
  refine ⟨166908346062154839485886905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111272230708103226323924603 166908346062154839485886905)
  ·
    refine ⟨125181259546616129614415179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166908346062154839485886905 125181259546616129614415179)
    ·
      refine ⟨187771889319924194421622769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125181259546616129614415179 187771889319924194421622769)
      ·
        refine ⟨140828916989943145816217077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187771889319924194421622769 140828916989943145816217077)
        ·
          refine ⟨13202710967807169920270351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140828916989943145816217077 13202710967807169920270351)
          ·
            refine ⟨19804066451710754880405527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13202710967807169920270351 19804066451710754880405527)
            ·
              refine ⟨29706099677566132320608291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19804066451710754880405527 29706099677566132320608291)
              ·
                refine ⟨44559149516349198480912437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29706099677566132320608291 44559149516349198480912437)
                ·
                  refine ⟨4177420267157737357585541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44559149516349198480912437 4177420267157737357585541)
                  ·
                    refine ⟨783266300092075754547289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4177420267157737357585541 783266300092075754547289)
                    ·
                      rfl

theorem cell23_4576217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 4].length) (baseStart_4576217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576217 prefixEnd_4576217 := by exact prefixLift 4576217
  have htrace : WordTrace (prefixWord ++ tailWord_4576217) baseStart_4576217 baseEnd_4576217 := by
    simpa [prefixWord, tailWord_4576217, baseEnd_4576217] using wordTrace_append hprefix tailTrace_4576217
  have hstable : (prefixWord ++ tailWord_4576217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576217).length < 2 ^ (prefixWord ++ tailWord_4576217).sum := by decide
  have hdescent : baseEnd_4576217 < baseStart_4576217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576227 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 3]
def baseStart_4576227 : Nat := 118140960795 + 4576227 * 2 ^ 59
def prefixEnd_4576227 : Nat := 4983230072969 + 3 ^ 40 * 4576227 * 2
def baseEnd_4576227 : Nat := 2349804035082772224516821

theorem tailTrace_4576227 : CollatzResearch.WordTrace tailWord_4576227 prefixEnd_4576227 2349804035082772224516821 := by
  unfold tailWord_4576227
  simp only [CollatzResearch.WordTrace]
  refine ⟨166908710792118611193750935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111272473861412407462500623 166908710792118611193750935)
  ·
    refine ⟨250363066188177916790626403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166908710792118611193750935 250363066188177916790626403)
    ·
      refine ⟨375544599282266875185939605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250363066188177916790626403 375544599282266875185939605)
      ·
        refine ⟨17603653091356259774340919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 375544599282266875185939605 17603653091356259774340919)
        ·
          refine ⟨26405479637034389661511379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17603653091356259774340919 26405479637034389661511379)
          ·
            refine ⟨39608219455551584492267069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26405479637034389661511379 39608219455551584492267069)
            ·
              refine ⟨14853082295831844184600151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39608219455551584492267069 14853082295831844184600151)
              ·
                refine ⟨22279623443747766276900227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14853082295831844184600151 22279623443747766276900227)
                ·
                  refine ⟨33419435165621649415350341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22279623443747766276900227 33419435165621649415350341)
                  ·
                    refine ⟨6266144093554059265378189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33419435165621649415350341 6266144093554059265378189)
                    ·
                      refine ⟨2349804035082772224516821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6266144093554059265378189 2349804035082772224516821)
                      ·
                        rfl

theorem cell23_4576227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_4576227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576227 prefixEnd_4576227 := by exact prefixLift 4576227
  have htrace : WordTrace (prefixWord ++ tailWord_4576227) baseStart_4576227 baseEnd_4576227 := by
    simpa [prefixWord, tailWord_4576227, baseEnd_4576227] using wordTrace_append hprefix tailTrace_4576227
  have hstable : (prefixWord ++ tailWord_4576227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576227).length < 2 ^ (prefixWord ++ tailWord_4576227).sum := by decide
  have hdescent : baseEnd_4576227 < baseStart_4576227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576264 : List Nat := [2, 1, 3, 2, 1, 4, 3, 1, 6]
def baseStart_4576264 : Nat := 118140960795 + 4576264 * 2 ^ 59
def prefixEnd_4576264 : Nat := 4983230072969 + 3 ^ 40 * 4576264 * 2
def baseEnd_4576264 : Nat := 261091448207443175528239

theorem tailTrace_4576264 : CollatzResearch.WordTrace tailWord_4576264 prefixEnd_4576264 261091448207443175528239 := by
  unfold tailWord_4576264
  simp only [CollatzResearch.WordTrace]
  refine ⟨83455030146492283256423923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111273373528656377675231897 83455030146492283256423923)
  ·
    refine ⟨125182545219738424884635885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83455030146492283256423923 125182545219738424884635885)
    ·
      refine ⟨46943454457401909331738457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125182545219738424884635885 46943454457401909331738457)
      ·
        refine ⟨35207590843051431998803843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46943454457401909331738457 35207590843051431998803843)
        ·
          refine ⟨52811386264577147998205765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35207590843051431998803843 52811386264577147998205765)
          ·
            refine ⟨9902134924608215249663581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52811386264577147998205765 9902134924608215249663581)
            ·
              refine ⟨3713300596728080718623843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9902134924608215249663581 3713300596728080718623843)
              ·
                refine ⟨5569950895092121077935765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3713300596728080718623843 5569950895092121077935765)
                ·
                  refine ⟨261091448207443175528239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5569950895092121077935765 261091448207443175528239)
                  ·
                    rfl

theorem cell23_4576264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 6].length) (baseStart_4576264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576264 prefixEnd_4576264 := by exact prefixLift 4576264
  have htrace : WordTrace (prefixWord ++ tailWord_4576264) baseStart_4576264 baseEnd_4576264 := by
    simpa [prefixWord, tailWord_4576264, baseEnd_4576264] using wordTrace_append hprefix tailTrace_4576264
  have hstable : (prefixWord ++ tailWord_4576264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576264).length < 2 ^ (prefixWord ++ tailWord_4576264).sum := by decide
  have hdescent : baseEnd_4576264 < baseStart_4576264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576285 : List Nat := [1, 4, 2, 2, 4, 1, 1, 3, 1, 4]
def baseStart_4576285 : Nat := 118140960795 + 4576285 * 2 ^ 59
def prefixEnd_4576285 : Nat := 4983230072969 + 3 ^ 40 * 4576285 * 2
def baseEnd_4576285 : Nat := 783277938986910999197185

theorem tailTrace_4576285 : CollatzResearch.WordTrace tailWord_4576285 prefixEnd_4576285 783277938986910999197185 := by
  unfold tailWord_4576285
  simp only [CollatzResearch.WordTrace]
  refine ⟨166910826225908487099362309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111273884150605658066241539 166910826225908487099362309)
  ·
    refine ⟨31295779917357841331130433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166910826225908487099362309 31295779917357841331130433)
    ·
      refine ⟨23471834938018380998347825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31295779917357841331130433 23471834938018380998347825)
      ·
        refine ⟨17603876203513785748760869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23471834938018380998347825 17603876203513785748760869)
        ·
          refine ⟨3300726788158834827892663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17603876203513785748760869 3300726788158834827892663)
          ·
            refine ⟨4951090182238252241838995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300726788158834827892663 4951090182238252241838995)
            ·
              refine ⟨7426635273357378362758493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4951090182238252241838995 7426635273357378362758493)
              ·
                refine ⟨2784988227509016886034435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7426635273357378362758493 2784988227509016886034435)
                ·
                  refine ⟨4177482341263525329051653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2784988227509016886034435 4177482341263525329051653)
                  ·
                    refine ⟨783277938986910999197185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4177482341263525329051653 783277938986910999197185)
                    ·
                      rfl

theorem cell23_4576285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_4576285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576285 prefixEnd_4576285 := by exact prefixLift 4576285
  have htrace : WordTrace (prefixWord ++ tailWord_4576285) baseStart_4576285 baseEnd_4576285 := by
    simpa [prefixWord, tailWord_4576285, baseEnd_4576285] using wordTrace_append hprefix tailTrace_4576285
  have hstable : (prefixWord ++ tailWord_4576285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576285).length < 2 ^ (prefixWord ++ tailWord_4576285).sum := by decide
  have hdescent : baseEnd_4576285 < baseStart_4576285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576308 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_4576308 : Nat := 118140960795 + 4576308 * 2 ^ 59
def prefixEnd_4576308 : Nat := 4983230072969 + 3 ^ 40 * 4576308 * 2
def baseEnd_4576308 : Nat := 2349845627015786407603949

theorem tailTrace_4576308 : CollatzResearch.WordTrace tailWord_4576308 prefixEnd_4576308 2349845627015786407603949 := by
  unfold tailWord_4576308
  simp only [CollatzResearch.WordTrace]
  refine ⟨83455832552412581013724789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111274443403216774684966385 83455832552412581013724789)
  ·
    refine ⟨7823984301788679470036699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83455832552412581013724789 7823984301788679470036699)
    ·
      refine ⟨11735976452683019205055049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7823984301788679470036699 11735976452683019205055049)
      ·
        refine ⟨8801982339512264403791287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11735976452683019205055049 8801982339512264403791287)
        ·
          refine ⟨13202973509268396605686931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8801982339512264403791287 13202973509268396605686931)
          ·
            refine ⟨19804460263902594908530397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13202973509268396605686931 19804460263902594908530397)
            ·
              refine ⟨7426672598963473090698899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19804460263902594908530397 7426672598963473090698899)
              ·
                refine ⟨11140008898445209636048349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7426672598963473090698899 11140008898445209636048349)
                ·
                  refine ⟨4177503336916953613518131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11140008898445209636048349 4177503336916953613518131)
                  ·
                    refine ⟨6266255005375430420277197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4177503336916953613518131 6266255005375430420277197)
                    ·
                      refine ⟨2349845627015786407603949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6266255005375430420277197 2349845627015786407603949)
                      ·
                        rfl

theorem cell23_4576308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_4576308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576308 prefixEnd_4576308 := by exact prefixLift 4576308
  have htrace : WordTrace (prefixWord ++ tailWord_4576308) baseStart_4576308 baseEnd_4576308 := by
    simpa [prefixWord, tailWord_4576308, baseEnd_4576308] using wordTrace_append hprefix tailTrace_4576308
  have hstable : (prefixWord ++ tailWord_4576308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576308).length < 2 ^ (prefixWord ++ tailWord_4576308).sum := by decide
  have hdescent : baseEnd_4576308 < baseStart_4576308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576327 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_4576327 : Nat := 118140960795 + 4576327 * 2 ^ 59
def prefixEnd_4576327 : Nat := 4983230072969 + 3 ^ 40 * 4576327 * 2
def baseEnd_4576327 : Nat := 2349855383148221833266361

theorem tailTrace_4576327 : CollatzResearch.WordTrace tailWord_4576327 prefixEnd_4576327 2349855383148221833266361 := by
  unfold tailWord_4576327
  simp only [CollatzResearch.WordTrace]
  refine ⟨166912358091756328272391235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111274905394504218848260823 166912358091756328272391235)
  ·
    refine ⟨250368537137634492408586853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166912358091756328272391235 250368537137634492408586853)
    ·
      refine ⟨46944100713306467326610035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 250368537137634492408586853 46944100713306467326610035)
      ·
        refine ⟨70416151069959700989915053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46944100713306467326610035 70416151069959700989915053)
        ·
          refine ⟨26406056651234887871218145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70416151069959700989915053 26406056651234887871218145)
          ·
            refine ⟨19804542488426165903413609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26406056651234887871218145 19804542488426165903413609)
            ·
              refine ⟨14853406866319624427560207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19804542488426165903413609 14853406866319624427560207)
              ·
                refine ⟨22280110299479436641340311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14853406866319624427560207 22280110299479436641340311)
                ·
                  refine ⟨33420165449219154962010467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22280110299479436641340311 33420165449219154962010467)
                  ·
                    refine ⟨50130248173828732443015701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33420165449219154962010467 50130248173828732443015701)
                    ·
                      refine ⟨2349855383148221833266361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50130248173828732443015701 2349855383148221833266361)
                      ·
                        rfl

theorem cell23_4576327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_4576327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576327 prefixEnd_4576327 := by exact prefixLift 4576327
  have htrace : WordTrace (prefixWord ++ tailWord_4576327) baseStart_4576327 baseEnd_4576327 := by
    simpa [prefixWord, tailWord_4576327, baseEnd_4576327] using wordTrace_append hprefix tailTrace_4576327
  have hstable : (prefixWord ++ tailWord_4576327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576327).length < 2 ^ (prefixWord ++ tailWord_4576327).sum := by decide
  have hdescent : baseEnd_4576327 < baseStart_4576327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576334 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_4576334 : Nat := 118140960795 + 4576334 * 2 ^ 59
def prefixEnd_4576334 : Nat := 4983230072969 + 3 ^ 40 * 4576334 * 2
def baseEnd_4576334 : Nat := 2349858977512803305878829

theorem tailTrace_4576334 : CollatzResearch.WordTrace tailWord_4576334 prefixEnd_4576334 2349858977512803305878829 := by
  unfold tailWord_4576334
  simp only [CollatzResearch.WordTrace]
  refine ⟨20864076675341371058487007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111275075601820645645264037 20864076675341371058487007)
  ·
    refine ⟨31296115013012056587730511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20864076675341371058487007 31296115013012056587730511)
    ·
      refine ⟨46944172519518084881595767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31296115013012056587730511 46944172519518084881595767)
      ·
        refine ⟨70416258779277127322393651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46944172519518084881595767 70416258779277127322393651)
        ·
          refine ⟨105624388168915690983590477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70416258779277127322393651 105624388168915690983590477)
          ·
            refine ⟨39609145563343384118846429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105624388168915690983590477 39609145563343384118846429)
            ·
              refine ⟨14853429586253769044567411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39609145563343384118846429 14853429586253769044567411)
              ·
                refine ⟨22280144379380653566851117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14853429586253769044567411 22280144379380653566851117)
                ·
                  refine ⟨8355054142267745087569169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22280144379380653566851117 8355054142267745087569169)
                  ·
                    refine ⟨6266290606700808815676877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8355054142267745087569169 6266290606700808815676877)
                    ·
                      refine ⟨2349858977512803305878829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6266290606700808815676877 2349858977512803305878829)
                      ·
                        rfl

theorem cell23_4576334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_4576334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576334 prefixEnd_4576334 := by exact prefixLift 4576334
  have htrace : WordTrace (prefixWord ++ tailWord_4576334) baseStart_4576334 baseEnd_4576334 := by
    simpa [prefixWord, tailWord_4576334, baseEnd_4576334] using wordTrace_append hprefix tailTrace_4576334
  have hstable : (prefixWord ++ tailWord_4576334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576334).length < 2 ^ (prefixWord ++ tailWord_4576334).sum := by decide
  have hdescent : baseEnd_4576334 < baseStart_4576334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576351 : List Nat := [1, 1, 2, 3, 1, 1, 7, 1, 1, 2, 3]
def baseStart_4576351 : Nat := 118140960795 + 4576351 * 2 ^ 59
def prefixEnd_4576351 : Nat := 4983230072969 + 3 ^ 40 * 4576351 * 2
def baseEnd_4576351 : Nat := 2349867706683929739366251

theorem tailTrace_4576351 : CollatzResearch.WordTrace tailWord_4576351 prefixEnd_4576351 2349867706683929739366251 := by
  unfold tailWord_4576351
  simp only [CollatzResearch.WordTrace]
  refine ⟨166913233443669380371264907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111275488962446253580843271 166913233443669380371264907)
  ·
    refine ⟨250369850165504070556897361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166913233443669380371264907 250369850165504070556897361)
    ·
      refine ⟨187777387624128052917673021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250369850165504070556897361 187777387624128052917673021)
      ·
        refine ⟨70416520359048019844127383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187777387624128052917673021 70416520359048019844127383)
        ·
          refine ⟨105624780538572029766191075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70416520359048019844127383 105624780538572029766191075)
          ·
            refine ⟨158437170807858044649286613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105624780538572029766191075 158437170807858044649286613)
            ·
              refine ⟨3713371190809172921467655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 158437170807858044649286613 3713371190809172921467655)
              ·
                refine ⟨5570056786213759382201483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3713371190809172921467655 5570056786213759382201483)
                ·
                  refine ⟨8355085179320639073302225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5570056786213759382201483 8355085179320639073302225)
                  ·
                    refine ⟨6266313884490479304976669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8355085179320639073302225 6266313884490479304976669)
                    ·
                      refine ⟨2349867706683929739366251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6266313884490479304976669 2349867706683929739366251)
                      ·
                        rfl

theorem cell23_4576351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_4576351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576351 prefixEnd_4576351 := by exact prefixLift 4576351
  have htrace : WordTrace (prefixWord ++ tailWord_4576351) baseStart_4576351 baseEnd_4576351 := by
    simpa [prefixWord, tailWord_4576351, baseEnd_4576351] using wordTrace_append hprefix tailTrace_4576351
  have hstable : (prefixWord ++ tailWord_4576351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576351).length < 2 ^ (prefixWord ++ tailWord_4576351).sum := by decide
  have hdescent : baseEnd_4576351 < baseStart_4576351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576365 : List Nat := [1, 5, 1, 1, 2, 3, 1, 4, 1, 2, 2]
def baseStart_4576365 : Nat := 118140960795 + 4576365 * 2 ^ 59
def prefixEnd_4576365 : Nat := 4983230072969 + 3 ^ 40 * 4576365 * 2
def baseEnd_4576365 : Nat := 2349874895413092684591187

theorem tailTrace_4576365 : CollatzResearch.WordTrace tailWord_4576365 prefixEnd_4576365 2349874895413092684591187 := by
  unfold tailWord_4576365
  simp only [CollatzResearch.WordTrace]
  refine ⟨166913744065618660762274549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111275829377079107174849699 166913744065618660762274549)
  ·
    refine ⟨15648163506151749446463239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166913744065618660762274549 15648163506151749446463239)
    ·
      refine ⟨23472245259227624169694859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15648163506151749446463239 23472245259227624169694859)
      ·
        refine ⟨35208367888841436254542289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23472245259227624169694859 35208367888841436254542289)
        ·
          refine ⟨26406275916631077190906717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35208367888841436254542289 26406275916631077190906717)
          ·
            refine ⟨9902353468736653946590019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26406275916631077190906717 9902353468736653946590019)
            ·
              refine ⟨14853530203104980919885029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9902353468736653946590019 14853530203104980919885029)
              ·
                refine ⟨2785036913082183922478443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14853530203104980919885029 2785036913082183922478443)
                ·
                  refine ⟨4177555369623275883717665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785036913082183922478443 4177555369623275883717665)
                  ·
                    refine ⟨3133166527217456912788249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4177555369623275883717665 3133166527217456912788249)
                    ·
                      refine ⟨2349874895413092684591187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3133166527217456912788249 2349874895413092684591187)
                      ·
                        rfl

theorem cell23_4576365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_4576365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576365 prefixEnd_4576365 := by exact prefixLift 4576365
  have htrace : WordTrace (prefixWord ++ tailWord_4576365) baseStart_4576365 baseEnd_4576365 := by
    simpa [prefixWord, tailWord_4576365, baseEnd_4576365] using wordTrace_append hprefix tailTrace_4576365
  have hstable : (prefixWord ++ tailWord_4576365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576365).length < 2 ^ (prefixWord ++ tailWord_4576365).sum := by decide
  have hdescent : baseEnd_4576365 < baseStart_4576365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576381 : List Nat := [1, 4, 1, 1, 3, 1, 1, 5, 2, 1, 3]
def baseStart_4576381 : Nat := 118140960795 + 4576381 * 2 ^ 59
def prefixEnd_4576381 : Nat := 4983230072969 + 3 ^ 40 * 4576381 * 2
def baseEnd_4576381 : Nat := 2349883111103564621991113

theorem tailTrace_4576381 : CollatzResearch.WordTrace tailWord_4576381 prefixEnd_4576381 2349883111103564621991113 := by
  unfold tailWord_4576381
  simp only [CollatzResearch.WordTrace]
  refine ⟨166914327633560695494856997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111276218422373796996571331 166914327633560695494856997)
  ·
    refine ⟨31296436431292630405285687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166914327633560695494856997 31296436431292630405285687)
    ·
      refine ⟨46944654646938945607928531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31296436431292630405285687 46944654646938945607928531)
      ·
        refine ⟨70416981970408418411892797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46944654646938945607928531 70416981970408418411892797)
        ·
          refine ⟨26406368238903156904459799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70416981970408418411892797 26406368238903156904459799)
          ·
            refine ⟨39609552358354735356689699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26406368238903156904459799 39609552358354735356689699)
            ·
              refine ⟨59414328537532103035034549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39609552358354735356689699 59414328537532103035034549)
              ·
                refine ⟨5570093300393634659534489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59414328537532103035034549 5570093300393634659534489)
                ·
                  refine ⟨4177569975295225994650867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5570093300393634659534489 4177569975295225994650867)
                  ·
                    refine ⟨6266354962942838991976301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4177569975295225994650867 6266354962942838991976301)
                    ·
                      refine ⟨2349883111103564621991113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6266354962942838991976301 2349883111103564621991113)
                      ·
                        rfl

theorem cell23_4576381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_4576381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576381 prefixEnd_4576381 := by exact prefixLift 4576381
  have htrace : WordTrace (prefixWord ++ tailWord_4576381) baseStart_4576381 baseEnd_4576381 := by
    simpa [prefixWord, tailWord_4576381, baseEnd_4576381] using wordTrace_append hprefix tailTrace_4576381
  have hstable : (prefixWord ++ tailWord_4576381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576381).length < 2 ^ (prefixWord ++ tailWord_4576381).sum := by decide
  have hdescent : baseEnd_4576381 < baseStart_4576381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576387 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 4]
def baseStart_4576387 : Nat := 118140960795 + 4576387 * 2 ^ 59
def prefixEnd_4576387 : Nat := 4983230072969 + 3 ^ 40 * 4576387 * 2
def baseEnd_4576387 : Nat := 2349886191987491598516085

theorem tailTrace_4576387 : CollatzResearch.WordTrace tailWord_4576387 prefixEnd_4576387 2349886191987491598516085 := by
  unfold tailWord_4576387
  simp only [CollatzResearch.WordTrace]
  refine ⟨166914546471538958519575415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111276364314359305679716943 166914546471538958519575415)
  ·
    refine ⟨250371819707308437779363123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166914546471538958519575415 250371819707308437779363123)
    ·
      refine ⟨375557729560962656669044685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250371819707308437779363123 375557729560962656669044685)
      ·
        refine ⟨140834148585360996250891757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 375557729560962656669044685 140834148585360996250891757)
        ·
          refine ⟨52812805719510373594084409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140834148585360996250891757 52812805719510373594084409)
          ·
            refine ⟨39609604289632780195563307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52812805719510373594084409 39609604289632780195563307)
            ·
              refine ⟨59414406434449170293344961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39609604289632780195563307 59414406434449170293344961)
              ·
                refine ⟨44560804825836877720008721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59414406434449170293344961 44560804825836877720008721)
                ·
                  refine ⟨33420603619377658290006541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44560804825836877720008721 33420603619377658290006541)
                  ·
                    refine ⟨12532726357266621858752453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33420603619377658290006541 12532726357266621858752453)
                    ·
                      refine ⟨2349886191987491598516085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12532726357266621858752453 2349886191987491598516085)
                      ·
                        rfl

theorem cell23_4576387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_4576387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576387 prefixEnd_4576387 := by exact prefixLift 4576387
  have htrace : WordTrace (prefixWord ++ tailWord_4576387) baseStart_4576387 baseEnd_4576387 := by
    simpa [prefixWord, tailWord_4576387, baseEnd_4576387] using wordTrace_append hprefix tailTrace_4576387
  have hstable : (prefixWord ++ tailWord_4576387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576387).length < 2 ^ (prefixWord ++ tailWord_4576387).sum := by decide
  have hdescent : baseEnd_4576387 < baseStart_4576387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576391 : List Nat := [1, 1, 4, 2, 1, 1, 1, 6, 1, 3, 2]
def baseStart_4576391 : Nat := 118140960795 + 4576391 * 2 ^ 59
def prefixEnd_4576391 : Nat := 4983230072969 + 3 ^ 40 * 4576391 * 2
def baseEnd_4576391 : Nat := 2349888245910109582866067

theorem tailTrace_4576391 : CollatzResearch.WordTrace tailWord_4576391 prefixEnd_4576391 2349888245910109582866067 := by
  unfold tailWord_4576391
  simp only [CollatzResearch.WordTrace]
  refine ⟨166914692363524467202721027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111276461575682978135147351 166914692363524467202721027)
  ·
    refine ⟨250372038545286700804081541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166914692363524467202721027 250372038545286700804081541)
    ·
      refine ⟨46944757227241256400765289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 250372038545286700804081541 46944757227241256400765289)
      ·
        refine ⟨35208567920430942300573967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46944757227241256400765289 35208567920430942300573967)
        ·
          refine ⟨52812851880646413450860951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35208567920430942300573967 52812851880646413450860951)
          ·
            refine ⟨79219277820969620176291427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52812851880646413450860951 79219277820969620176291427)
            ·
              refine ⟨118828916731454430264437141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79219277820969620176291427 118828916731454430264437141)
              ·
                refine ⟨5570105471786926418645491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118828916731454430264437141 5570105471786926418645491)
                ·
                  refine ⟨8355158207680389627968237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5570105471786926418645491 8355158207680389627968237)
                  ·
                    refine ⟨3133184327880146110488089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8355158207680389627968237 3133184327880146110488089)
                    ·
                      refine ⟨2349888245910109582866067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3133184327880146110488089 2349888245910109582866067)
                      ·
                        rfl

theorem cell23_4576391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_4576391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576391 prefixEnd_4576391 := by exact prefixLift 4576391
  have htrace : WordTrace (prefixWord ++ tailWord_4576391) baseStart_4576391 baseEnd_4576391 := by
    simpa [prefixWord, tailWord_4576391, baseEnd_4576391] using wordTrace_append hprefix tailTrace_4576391
  have hstable : (prefixWord ++ tailWord_4576391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576391).length < 2 ^ (prefixWord ++ tailWord_4576391).sum := by decide
  have hdescent : baseEnd_4576391 < baseStart_4576391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576408 : List Nat := [2, 1, 2, 4, 2, 2, 1, 3, 1, 3, 2]
def baseStart_4576408 : Nat := 118140960795 + 4576408 * 2 ^ 59
def prefixEnd_4576408 : Nat := 4983230072969 + 3 ^ 40 * 4576408 * 2
def baseEnd_4576408 : Nat := 2349896975081236016353489

theorem tailTrace_4576408 : CollatzResearch.WordTrace tailWord_4576408 prefixEnd_4576408 2349896975081236016353489 := by
  unfold tailWord_4576408
  simp only [CollatzResearch.WordTrace]
  refine ⟨83457656202231439553044939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111276874936308586070726585 83457656202231439553044939)
  ·
    refine ⟨125186484303347159329567409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83457656202231439553044939 125186484303347159329567409)
    ·
      refine ⟨93889863227510369497175557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125186484303347159329567409 93889863227510369497175557)
      ·
        refine ⟨17604349355158194280720417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93889863227510369497175557 17604349355158194280720417)
        ·
          refine ⟨13203262016368645710540313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17604349355158194280720417 13203262016368645710540313)
          ·
            refine ⟨9902446512276484282905235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13203262016368645710540313 9902446512276484282905235)
            ·
              refine ⟨14853669768414726424357853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9902446512276484282905235 14853669768414726424357853)
              ·
                refine ⟨5570126163155522409134195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14853669768414726424357853 5570126163155522409134195)
                ·
                  refine ⟨8355189244733283613701293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5570126163155522409134195 8355189244733283613701293)
                  ·
                    refine ⟨3133195966774981355137985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8355189244733283613701293 3133195966774981355137985)
                    ·
                      refine ⟨2349896975081236016353489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3133195966774981355137985 2349896975081236016353489)
                      ·
                        rfl

theorem cell23_4576408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_4576408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576408 prefixEnd_4576408 := by exact prefixLift 4576408
  have htrace : WordTrace (prefixWord ++ tailWord_4576408) baseStart_4576408 baseEnd_4576408 := by
    simpa [prefixWord, tailWord_4576408, baseEnd_4576408] using wordTrace_append hprefix tailTrace_4576408
  have hstable : (prefixWord ++ tailWord_4576408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576408).length < 2 ^ (prefixWord ++ tailWord_4576408).sum := by decide
  have hdescent : baseEnd_4576408 < baseStart_4576408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576415 : List Nat := [1, 1, 2, 6, 2, 2, 1, 2, 2, 1, 3]
def baseStart_4576415 : Nat := 118140960795 + 4576415 * 2 ^ 59
def prefixEnd_4576415 : Nat := 4983230072969 + 3 ^ 40 * 4576415 * 2
def baseEnd_4576415 : Nat := 2349900569445817488965957

theorem tailTrace_4576415 : CollatzResearch.WordTrace tailWord_4576415 prefixEnd_4576415 2349900569445817488965957 := by
  unfold tailWord_4576415
  simp only [CollatzResearch.WordTrace]
  refine ⟨166915567715437519301594699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111277045143625012867729799 166915567715437519301594699)
  ·
    refine ⟨250373351573156278952392049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166915567715437519301594699 250373351573156278952392049)
    ·
      refine ⟨187780013679867209214294037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250373351573156278952392049 187780013679867209214294037)
      ·
        refine ⟨8802188141243775431920033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 187780013679867209214294037 8802188141243775431920033)
        ·
          refine ⟨6601641105932831573940025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8802188141243775431920033 6601641105932831573940025)
          ·
            refine ⟨4951230829449623680455019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6601641105932831573940025 4951230829449623680455019)
            ·
              refine ⟨7426846244174435520682529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4951230829449623680455019 7426846244174435520682529)
              ·
                refine ⟨5570134683130826640511897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7426846244174435520682529 5570134683130826640511897)
                ·
                  refine ⟨4177601012348119980383923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5570134683130826640511897 4177601012348119980383923)
                  ·
                    refine ⟨6266401518522179970575885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4177601012348119980383923 6266401518522179970575885)
                    ·
                      refine ⟨2349900569445817488965957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6266401518522179970575885 2349900569445817488965957)
                      ·
                        rfl

theorem cell23_4576415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_4576415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576415 prefixEnd_4576415 := by exact prefixLift 4576415
  have htrace : WordTrace (prefixWord ++ tailWord_4576415) baseStart_4576415 baseEnd_4576415 := by
    simpa [prefixWord, tailWord_4576415, baseEnd_4576415] using wordTrace_append hprefix tailTrace_4576415
  have hstable : (prefixWord ++ tailWord_4576415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576415).length < 2 ^ (prefixWord ++ tailWord_4576415).sum := by decide
  have hdescent : baseEnd_4576415 < baseStart_4576415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576434 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_4576434 : Nat := 118140960795 + 4576434 * 2 ^ 59
def prefixEnd_4576434 : Nat := 4983230072969 + 3 ^ 40 * 4576434 * 2
def baseEnd_4576434 : Nat := 2349910325578252914628369

theorem tailTrace_4576434 : CollatzResearch.WordTrace tailWord_4576434 prefixEnd_4576434 2349910325578252914628369 := by
  unfold tailWord_4576434
  simp only [CollatzResearch.WordTrace]
  refine ⟨41729065175592171386634089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111277507134912457031024237 41729065175592171386634089)
  ·
    refine ⟨31296798881694128539975567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41729065175592171386634089 31296798881694128539975567)
    ·
      refine ⟨46945198322541192809963351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31296798881694128539975567 46945198322541192809963351)
      ·
        refine ⟨70417797483811789214945027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46945198322541192809963351 70417797483811789214945027)
        ·
          refine ⟨105626696225717683822417541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70417797483811789214945027 105626696225717683822417541)
          ·
            refine ⟨19805005542322065716703289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105626696225717683822417541 19805005542322065716703289)
            ·
              refine ⟨14853754156741549287527467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19805005542322065716703289 14853754156741549287527467)
              ·
                refine ⟨22280631235112323931291201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14853754156741549287527467 22280631235112323931291201)
                ·
                  refine ⟨16710473426334242948468401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22280631235112323931291201 16710473426334242948468401)
                  ·
                    refine ⟨12532855069750682211351301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16710473426334242948468401 12532855069750682211351301)
                    ·
                      refine ⟨2349910325578252914628369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12532855069750682211351301 2349910325578252914628369)
                      ·
                        rfl

theorem cell23_4576434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_4576434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576434 prefixEnd_4576434 := by exact prefixLift 4576434
  have htrace : WordTrace (prefixWord ++ tailWord_4576434) baseStart_4576434 baseEnd_4576434 := by
    simpa [prefixWord, tailWord_4576434, baseEnd_4576434] using wordTrace_append hprefix tailTrace_4576434
  have hstable : (prefixWord ++ tailWord_4576434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576434).length < 2 ^ (prefixWord ++ tailWord_4576434).sum := by decide
  have hdescent : baseEnd_4576434 < baseStart_4576434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576444 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 7]
def baseStart_4576444 : Nat := 118140960795 + 4576444 * 2 ^ 59
def prefixEnd_4576444 : Nat := 4983230072969 + 3 ^ 40 * 4576444 * 2
def baseEnd_4576444 : Nat := 261101717820533097278147

theorem tailTrace_4576444 : CollatzResearch.WordTrace tailWord_4576444 prefixEnd_4576444 261101717820533097278147 := by
  unfold tailWord_4576444
  simp only [CollatzResearch.WordTrace]
  refine ⟨83458312716166228627200193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111277750288221638169600257 83458312716166228627200193)
  ·
    refine ⟨62593734537124671470400145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83458312716166228627200193 62593734537124671470400145)
    ·
      refine ⟨46945300902843503602800109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62593734537124671470400145 46945300902843503602800109)
      ·
        refine ⟨17604487838566313851050041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46945300902843503602800109 17604487838566313851050041)
        ·
          refine ⟨13203365878924735388287531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17604487838566313851050041 13203365878924735388287531)
          ·
            refine ⟨19805048818387103082431297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13203365878924735388287531 19805048818387103082431297)
            ·
              refine ⟨14853786613790327311823473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19805048818387103082431297 14853786613790327311823473)
              ·
                refine ⟨11140339960342745483867605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14853786613790327311823473 11140339960342745483867605)
                ·
                  refine ⟨261101717820533097278147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11140339960342745483867605 261101717820533097278147)
                  ·
                    rfl

theorem cell23_4576444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_4576444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576444 prefixEnd_4576444 := by exact prefixLift 4576444
  have htrace : WordTrace (prefixWord ++ tailWord_4576444) baseStart_4576444 baseEnd_4576444 := by
    simpa [prefixWord, tailWord_4576444, baseEnd_4576444] using wordTrace_append hprefix tailTrace_4576444
  have hstable : (prefixWord ++ tailWord_4576444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576444).length < 2 ^ (prefixWord ++ tailWord_4576444).sum := by decide
  have hdescent : baseEnd_4576444 < baseStart_4576444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576467 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 5]
def baseStart_4576467 : Nat := 118140960795 + 4576467 * 2 ^ 59
def prefixEnd_4576467 : Nat := 4983230072969 + 3 ^ 40 * 4576467 * 2
def baseEnd_4576467 : Nat := 2349927270439851285515717

theorem tailTrace_4576467 : CollatzResearch.WordTrace tailWord_4576467 prefixEnd_4576467 2349927270439851285515717 := by
  unfold tailWord_4576467
  simp only [CollatzResearch.WordTrace]
  refine ⟨166917464311249132182487655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111278309540832754788325103 166917464311249132182487655)
  ·
    refine ⟨250376196466873698273731483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166917464311249132182487655 250376196466873698273731483)
    ·
      refine ⟨375564294700310547410597225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250376196466873698273731483 375564294700310547410597225)
      ·
        refine ⟨281673221025232910557947919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 375564294700310547410597225 281673221025232910557947919)
        ·
          refine ⟨422509831537849365836921879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281673221025232910557947919 422509831537849365836921879)
          ·
            refine ⟨633764747306774048755382819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422509831537849365836921879 633764747306774048755382819)
            ·
              refine ⟨950647120960161073133074229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633764747306774048755382819 950647120960161073133074229)
              ·
                refine ⟨89123167590015100606225709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 950647120960161073133074229 89123167590015100606225709)
                ·
                  refine ⟨33421187846255662727334641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89123167590015100606225709 33421187846255662727334641)
                  ·
                    refine ⟨25065890884691747045500981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33421187846255662727334641 25065890884691747045500981)
                    ·
                      refine ⟨2349927270439851285515717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25065890884691747045500981 2349927270439851285515717)
                      ·
                        rfl

theorem cell23_4576467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_4576467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576467 prefixEnd_4576467 := by exact prefixLift 4576467
  have htrace : WordTrace (prefixWord ++ tailWord_4576467) baseStart_4576467 baseEnd_4576467 := by
    simpa [prefixWord, tailWord_4576467, baseEnd_4576467] using wordTrace_append hprefix tailTrace_4576467
  have hstable : (prefixWord ++ tailWord_4576467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576467).length < 2 ^ (prefixWord ++ tailWord_4576467).sum := by decide
  have hdescent : baseEnd_4576467 < baseStart_4576467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576494 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_4576494 : Nat := 118140960795 + 4576494 * 2 ^ 59
def prefixEnd_4576494 : Nat := 4983230072969 + 3 ^ 40 * 4576494 * 2
def baseEnd_4576494 : Nat := 2349941134417522679878093

theorem tailTrace_4576494 : CollatzResearch.WordTrace tailWord_4576494 prefixEnd_4576494 2349941134417522679878093 := by
  unfold tailWord_4576494
  simp only [CollatzResearch.WordTrace]
  refine ⟨20864806135268914474215067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111278966054767543862480357 20864806135268914474215067)
  ·
    refine ⟨31297209202903371711322601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20864806135268914474215067 31297209202903371711322601)
    ·
      refine ⟨23472906902177528783491951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31297209202903371711322601 23472906902177528783491951)
      ·
        refine ⟨35209360353266293175237927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23472906902177528783491951 35209360353266293175237927)
        ·
          refine ⟨52814040529899439762856891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35209360353266293175237927 52814040529899439762856891)
          ·
            refine ⟨79221060794849159644285337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52814040529899439762856891 79221060794849159644285337)
            ·
              refine ⟨59415795596136869733214003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79221060794849159644285337 59415795596136869733214003)
              ·
                refine ⟨89123693394205304599821005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59415795596136869733214003 89123693394205304599821005)
                ·
                  refine ⟨33421385022826989224932877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89123693394205304599821005 33421385022826989224932877)
                  ·
                    refine ⟨12533019383560120959349829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33421385022826989224932877 12533019383560120959349829)
                    ·
                      refine ⟨2349941134417522679878093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12533019383560120959349829 2349941134417522679878093)
                      ·
                        rfl

theorem cell23_4576494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_4576494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576494 prefixEnd_4576494 := by exact prefixLift 4576494
  have htrace : WordTrace (prefixWord ++ tailWord_4576494) baseStart_4576494 baseEnd_4576494 := by
    simpa [prefixWord, tailWord_4576494, baseEnd_4576494] using wordTrace_append hprefix tailTrace_4576494
  have hstable : (prefixWord ++ tailWord_4576494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576494).length < 2 ^ (prefixWord ++ tailWord_4576494).sum := by decide
  have hdescent : baseEnd_4576494 < baseStart_4576494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576511 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 4]
def baseStart_4576511 : Nat := 118140960795 + 4576511 * 2 ^ 59
def prefixEnd_4576511 : Nat := 4983230072969 + 3 ^ 40 * 4576511 * 2
def baseEnd_4576511 : Nat := 2349949863588649113365515

theorem tailTrace_4576511 : CollatzResearch.WordTrace tailWord_4576511 prefixEnd_4576511 2349949863588649113365515 := by
  unfold tailWord_4576511
  simp only [CollatzResearch.WordTrace]
  refine ⟨166919069123089727697089387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111279379415393151798059591 166919069123089727697089387)
  ·
    refine ⟨250378603684634591545634081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166919069123089727697089387 250378603684634591545634081)
    ·
      refine ⟨187783952763475943659225561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250378603684634591545634081 187783952763475943659225561)
      ·
        refine ⟨140837964572606957744419171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187783952763475943659225561 140837964572606957744419171)
        ·
          refine ⟨211256946858910436616628757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140837964572606957744419171 211256946858910436616628757)
          ·
            refine ⟨9902669384011426716404473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 211256946858910436616628757 9902669384011426716404473)
            ·
              refine ⟨7427002038008570037303355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9902669384011426716404473 7427002038008570037303355)
              ·
                refine ⟨11140503057012855055955033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7427002038008570037303355 11140503057012855055955033)
                ·
                  refine ⟨8355377292759641291966275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11140503057012855055955033 8355377292759641291966275)
                  ·
                    refine ⟨12533065939139461937949413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8355377292759641291966275 12533065939139461937949413)
                    ·
                      refine ⟨2349949863588649113365515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12533065939139461937949413 2349949863588649113365515)
                      ·
                        rfl

theorem cell23_4576511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_4576511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576511 prefixEnd_4576511 := by exact prefixLift 4576511
  have htrace : WordTrace (prefixWord ++ tailWord_4576511) baseStart_4576511 baseEnd_4576511 := by
    simpa [prefixWord, tailWord_4576511, baseEnd_4576511] using wordTrace_append hprefix tailTrace_4576511
  have hstable : (prefixWord ++ tailWord_4576511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576511).length < 2 ^ (prefixWord ++ tailWord_4576511).sum := by decide
  have hdescent : baseEnd_4576511 < baseStart_4576511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576611 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 1, 6]
def baseStart_4576611 : Nat := 118140960795 + 4576611 * 2 ^ 59
def prefixEnd_4576611 : Nat := 4983230072969 + 3 ^ 40 * 4576611 * 2
def baseEnd_4576611 : Nat := 783333737218032907371685

theorem tailTrace_4576611 : CollatzResearch.WordTrace tailWord_4576611 prefixEnd_4576611 783333737218032907371685 := by
  unfold tailWord_4576611
  simp only [CollatzResearch.WordTrace]
  refine ⟨166922716422727444775729687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111281810948484963183819791 166922716422727444775729687)
  ·
    refine ⟨250384074634091167163594531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166922716422727444775729687 250384074634091167163594531)
    ·
      refine ⟨375576111951136750745391797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250384074634091167163594531 375576111951136750745391797)
      ·
        refine ⟨35210260495419070382380481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 375576111951136750745391797 35210260495419070382380481)
        ·
          refine ⟨26407695371564302786785361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35210260495419070382380481 26407695371564302786785361)
          ·
            refine ⟨19805771528673227090089021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26407695371564302786785361 19805771528673227090089021)
            ·
              refine ⟨7427164323252460158783383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19805771528673227090089021 7427164323252460158783383)
              ·
                refine ⟨11140746484878690238175075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7427164323252460158783383 11140746484878690238175075)
                ·
                  refine ⟨16711119727318035357262613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11140746484878690238175075 16711119727318035357262613)
                  ·
                    refine ⟨783333737218032907371685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16711119727318035357262613 783333737218032907371685)
                    ·
                      rfl

theorem cell23_4576611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 6].length) (baseStart_4576611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576611 prefixEnd_4576611 := by exact prefixLift 4576611
  have htrace : WordTrace (prefixWord ++ tailWord_4576611) baseStart_4576611 baseEnd_4576611 := by
    simpa [prefixWord, tailWord_4576611, baseEnd_4576611] using wordTrace_append hprefix tailTrace_4576611
  have hstable : (prefixWord ++ tailWord_4576611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576611).length < 2 ^ (prefixWord ++ tailWord_4576611).sum := by decide
  have hdescent : baseEnd_4576611 < baseStart_4576611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576624 : List Nat := [2, 1, 1, 1, 4, 2, 3, 9]
def baseStart_4576624 : Nat := 118140960795 + 4576624 * 2 ^ 59
def prefixEnd_4576624 : Nat := 4983230072969 + 3 ^ 40 * 4576624 * 2
def baseEnd_4576624 : Nat := 87037329144541006342685

theorem tailTrace_4576624 : CollatzResearch.WordTrace tailWord_4576624 prefixEnd_4576624 87037329144541006342685 := by
  unfold tailWord_4576624
  simp only [CollatzResearch.WordTrace]
  refine ⟨83461595285840173997976463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111282127047786898663968617 83461595285840173997976463)
  ·
    refine ⟨125192392928760260996964695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83461595285840173997976463 125192392928760260996964695)
    ·
      refine ⟨187788589393140391495447043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125192392928760260996964695 187788589393140391495447043)
      ·
        refine ⟨281682884089710587243170565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187788589393140391495447043 281682884089710587243170565)
        ·
          refine ⟨52815540766820735108094481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 281682884089710587243170565 52815540766820735108094481)
          ·
            refine ⟨39611655575115551331070861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52815540766820735108094481 39611655575115551331070861)
            ·
              refine ⟨14854370840668331749151573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39611655575115551331070861 14854370840668331749151573)
              ·
                refine ⟨87037329144541006342685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14854370840668331749151573 87037329144541006342685)
                ·
                  rfl

theorem cell23_4576624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 9].length) (baseStart_4576624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576624 prefixEnd_4576624 := by exact prefixLift 4576624
  have htrace : WordTrace (prefixWord ++ tailWord_4576624) baseStart_4576624 baseEnd_4576624 := by
    simpa [prefixWord, tailWord_4576624, baseEnd_4576624] using wordTrace_append hprefix tailTrace_4576624
  have hstable : (prefixWord ++ tailWord_4576624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576624).length < 2 ^ (prefixWord ++ tailWord_4576624).sum := by decide
  have hdescent : baseEnd_4576624 < baseStart_4576624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576629 : List Nat := [1, 3, 4, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_4576629 : Nat := 118140960795 + 4576629 * 2 ^ 59
def prefixEnd_4576629 : Nat := 4983230072969 + 3 ^ 40 * 4576629 * 2
def baseEnd_4576629 : Nat := 2350010454305879651689973

theorem tailTrace_4576629 : CollatzResearch.WordTrace tailWord_4576629 prefixEnd_4576629 2350010454305879651689973 := by
  unfold tailWord_4576629
  simp only [CollatzResearch.WordTrace]
  refine ⟨166923372936662233849884941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111282248624441489233256627 166923372936662233849884941)
  ·
    refine ⟨62596264851248337693706853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166923372936662233849884941 62596264851248337693706853)
    ·
      refine ⟨11736799659609063317570035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62596264851248337693706853 11736799659609063317570035)
      ·
        refine ⟨17605199489413594976355053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11736799659609063317570035 17605199489413594976355053)
        ·
          refine ⟨6601949808530098116133145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17605199489413594976355053 6601949808530098116133145)
          ·
            refine ⟨4951462356397573587099859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6601949808530098116133145 4951462356397573587099859)
            ·
              refine ⟨7427193534596360380649789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4951462356397573587099859 7427193534596360380649789)
              ·
                refine ⟨2785197575473635142743671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7427193534596360380649789 2785197575473635142743671)
                ·
                  refine ⟨4177796363210452714115507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785197575473635142743671 4177796363210452714115507)
                  ·
                    refine ⟨6266694544815679071173261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4177796363210452714115507 6266694544815679071173261)
                    ·
                      refine ⟨2350010454305879651689973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6266694544815679071173261 2350010454305879651689973)
                      ·
                        rfl

theorem cell23_4576629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_4576629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576629 prefixEnd_4576629 := by exact prefixLift 4576629
  have htrace : WordTrace (prefixWord ++ tailWord_4576629) baseStart_4576629 baseEnd_4576629 := by
    simpa [prefixWord, tailWord_4576629, baseEnd_4576629] using wordTrace_append hprefix tailTrace_4576629
  have hstable : (prefixWord ++ tailWord_4576629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576629).length < 2 ^ (prefixWord ++ tailWord_4576629).sum := by decide
  have hdescent : baseEnd_4576629 < baseStart_4576629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576685 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_4576685 : Nat := 118140960795 + 4576685 * 2 ^ 59
def prefixEnd_4576685 : Nat := 4983230072969 + 3 ^ 40 * 4576685 * 2
def baseEnd_4576685 : Nat := 2350039209222531432589715

theorem tailTrace_4576685 : CollatzResearch.WordTrace tailWord_4576685 prefixEnd_4576685 2350039209222531432589715 := by
  unfold tailWord_4576685
  simp only [CollatzResearch.WordTrace]
  refine ⟨166925415424459355413923509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111283610282972903609282339 166925415424459355413923509)
  ·
    refine ⟨15649257696043064570055329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 166925415424459355413923509 15649257696043064570055329)
    ·
      refine ⟨11736943272032298427541497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15649257696043064570055329 11736943272032298427541497)
      ·
        refine ⟨8802707454024223820656123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11736943272032298427541497 8802707454024223820656123)
        ·
          refine ⟨13204061181036335730984185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8802707454024223820656123 13204061181036335730984185)
          ·
            refine ⟨9903045885777251798238139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13204061181036335730984185 9903045885777251798238139)
            ·
              refine ⟨14854568828665877697357209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9903045885777251798238139 14854568828665877697357209)
              ·
                refine ⟨11140926621499408273017907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14854568828665877697357209 11140926621499408273017907)
                ·
                  refine ⟨16711389932249112409526861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11140926621499408273017907 16711389932249112409526861)
                  ·
                    refine ⟨6266771224593417153572573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16711389932249112409526861 6266771224593417153572573)
                    ·
                      refine ⟨2350039209222531432589715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6266771224593417153572573 2350039209222531432589715)
                      ·
                        rfl

theorem cell23_4576685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_4576685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576685 prefixEnd_4576685 := by exact prefixLift 4576685
  have htrace : WordTrace (prefixWord ++ tailWord_4576685) baseStart_4576685 baseEnd_4576685 := by
    simpa [prefixWord, tailWord_4576685, baseEnd_4576685] using wordTrace_append hprefix tailTrace_4576685
  have hstable : (prefixWord ++ tailWord_4576685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576685).length < 2 ^ (prefixWord ++ tailWord_4576685).sum := by decide
  have hdescent : baseEnd_4576685 < baseStart_4576685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576701 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_4576701 : Nat := 118140960795 + 4576701 * 2 ^ 59
def prefixEnd_4576701 : Nat := 4983230072969 + 3 ^ 40 * 4576701 * 2
def baseEnd_4576701 : Nat := 783349141637667789996547

theorem tailTrace_4576701 : CollatzResearch.WordTrace tailWord_4576701 prefixEnd_4576701 783349141637667789996547 := by
  unfold tailWord_4576701
  simp only [CollatzResearch.WordTrace]
  refine ⟨166925998992401390146505957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111283999328267593431003971 166925998992401390146505957)
  ·
    refine ⟨31298624811075260652469867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 166925998992401390146505957 31298624811075260652469867)
    ·
      refine ⟨46947937216612890978704801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31298624811075260652469867 46947937216612890978704801)
      ·
        refine ⟨35210952912459668234028601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46947937216612890978704801 35210952912459668234028601)
        ·
          refine ⟨26408214684344751175521451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35210952912459668234028601 26408214684344751175521451)
          ·
            refine ⟨39612322026517126763282177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26408214684344751175521451 39612322026517126763282177)
            ·
              refine ⟨29709241519887845072461633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39612322026517126763282177 29709241519887845072461633)
              ·
                refine ⟨22281931139915883804346225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29709241519887845072461633 22281931139915883804346225)
                ·
                  refine ⟨16711448354936912853259669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22281931139915883804346225 16711448354936912853259669)
                  ·
                    refine ⟨783349141637667789996547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16711448354936912853259669 783349141637667789996547)
                    ·
                      rfl

theorem cell23_4576701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_4576701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576701 prefixEnd_4576701 := by exact prefixLift 4576701
  have htrace : WordTrace (prefixWord ++ tailWord_4576701) baseStart_4576701 baseEnd_4576701 := by
    simpa [prefixWord, tailWord_4576701, baseEnd_4576701] using wordTrace_append hprefix tailTrace_4576701
  have hstable : (prefixWord ++ tailWord_4576701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576701).length < 2 ^ (prefixWord ++ tailWord_4576701).sum := by decide
  have hdescent : baseEnd_4576701 < baseStart_4576701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576708 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_4576708 : Nat := 118140960795 + 4576708 * 2 ^ 59
def prefixEnd_4576708 : Nat := 4983230072969 + 3 ^ 40 * 4576708 * 2
def baseEnd_4576708 : Nat := 2350051019277584842602109

theorem tailTrace_4576708 : CollatzResearch.WordTrace tailWord_4576708 prefixEnd_4576708 2350051019277584842602109 := by
  unfold tailWord_4576708
  simp only [CollatzResearch.WordTrace]
  refine ⟨83463127151688015171005389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111284169535584020228007185 83463127151688015171005389)
  ·
    refine ⟨31298672681883005689127021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83463127151688015171005389 31298672681883005689127021)
    ·
      refine ⟨11737002255706127133422633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31298672681883005689127021 11737002255706127133422633)
      ·
        refine ⟨8802751691779595350066975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11737002255706127133422633 8802751691779595350066975)
        ·
          refine ⟨13204127537669393025100463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8802751691779595350066975 13204127537669393025100463)
          ·
            refine ⟨19806191306504089537650695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13204127537669393025100463 19806191306504089537650695)
            ·
              refine ⟨29709286959756134306476043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19806191306504089537650695 29709286959756134306476043)
              ·
                refine ⟨44563930439634201459714065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29709286959756134306476043 44563930439634201459714065)
                ·
                  refine ⟨33422947829725651094785549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44563930439634201459714065 33422947829725651094785549)
                  ·
                    refine ⟨12533605436147119160544581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33422947829725651094785549 12533605436147119160544581)
                    ·
                      refine ⟨2350051019277584842602109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12533605436147119160544581 2350051019277584842602109)
                      ·
                        rfl

theorem cell23_4576708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_4576708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576708 prefixEnd_4576708 := by exact prefixLift 4576708
  have htrace : WordTrace (prefixWord ++ tailWord_4576708) baseStart_4576708 baseEnd_4576708 := by
    simpa [prefixWord, tailWord_4576708, baseEnd_4576708] using wordTrace_append hprefix tailTrace_4576708
  have hstable : (prefixWord ++ tailWord_4576708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576708).length < 2 ^ (prefixWord ++ tailWord_4576708).sum := by decide
  have hdescent : baseEnd_4576708 < baseStart_4576708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576711 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_4576711 : Nat := 118140960795 + 4576711 * 2 ^ 59
def prefixEnd_4576711 : Nat := 4983230072969 + 3 ^ 40 * 4576711 * 2
def baseEnd_4576711 : Nat := 2350052559719548330864595

theorem tailTrace_4576711 : CollatzResearch.WordTrace tailWord_4576711 prefixEnd_4576711 2350052559719548330864595 := by
  unfold tailWord_4576711
  simp only [CollatzResearch.WordTrace]
  refine ⟨166926363722365161854369987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111284242481576774569579991 166926363722365161854369987)
  ·
    refine ⟨250389545583547742781554981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166926363722365161854369987 250389545583547742781554981)
    ·
      refine ⟨46948039796915201771541559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 250389545583547742781554981 46948039796915201771541559)
      ·
        refine ⟨70422059695372802657312339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46948039796915201771541559 70422059695372802657312339)
        ·
          refine ⟨105633089543059203985968509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70422059695372802657312339 105633089543059203985968509)
          ·
            refine ⟨39612408578647201494738191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105633089543059203985968509 39612408578647201494738191)
            ·
              refine ⟨59418612867970802242107287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39612408578647201494738191 59418612867970802242107287)
              ·
                refine ⟨89127919301956203363160931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59418612867970802242107287 89127919301956203363160931)
                ·
                  refine ⟨133691878952934305044741397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89127919301956203363160931 133691878952934305044741397)
                  ·
                    refine ⟨6266806825918795548972253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 133691878952934305044741397 6266806825918795548972253)
                    ·
                      refine ⟨2350052559719548330864595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6266806825918795548972253 2350052559719548330864595)
                      ·
                        rfl

theorem cell23_4576711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_4576711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576711 prefixEnd_4576711 := by exact prefixLift 4576711
  have htrace : WordTrace (prefixWord ++ tailWord_4576711) baseStart_4576711 baseEnd_4576711 := by
    simpa [prefixWord, tailWord_4576711, baseEnd_4576711] using wordTrace_append hprefix tailTrace_4576711
  have hstable : (prefixWord ++ tailWord_4576711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576711).length < 2 ^ (prefixWord ++ tailWord_4576711).sum := by decide
  have hdescent : baseEnd_4576711 < baseStart_4576711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576725 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 1, 4, 2]
def baseStart_4576725 : Nat := 118140960795 + 4576725 * 2 ^ 59
def prefixEnd_4576725 : Nat := 4983230072969 + 3 ^ 40 * 4576725 * 2
def baseEnd_4576725 : Nat := 2350059748448711276089531

theorem tailTrace_4576725 : CollatzResearch.WordTrace tailWord_4576725 prefixEnd_4576725 2350059748448711276089531 := by
  unfold tailWord_4576725
  simp only [CollatzResearch.WordTrace]
  refine ⟨166926874344314442245379629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111284582896209628163586419 166926874344314442245379629)
  ·
    refine ⟨62597577879117915842017361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166926874344314442245379629 62597577879117915842017361)
    ·
      refine ⟨46948183409338436881513021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62597577879117915842017361 46948183409338436881513021)
      ·
        refine ⟨17605568778501913830567383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46948183409338436881513021 17605568778501913830567383)
        ·
          refine ⟨26408353167752870745851075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17605568778501913830567383 26408353167752870745851075)
          ·
            refine ⟨39612529751629306118776613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26408353167752870745851075 39612529751629306118776613)
            ·
              refine ⟨7427349328430494897270615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39612529751629306118776613 7427349328430494897270615)
              ·
                refine ⟨11141023992645742345905923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7427349328430494897270615 11141023992645742345905923)
                ·
                  refine ⟨16711535988968613518858885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11141023992645742345905923 16711535988968613518858885)
                  ·
                    refine ⟨3133412997931615034786041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16711535988968613518858885 3133412997931615034786041)
                    ·
                      refine ⟨2350059748448711276089531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3133412997931615034786041 2350059748448711276089531)
                      ·
                        rfl

theorem cell23_4576725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_4576725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576725 prefixEnd_4576725 := by exact prefixLift 4576725
  have htrace : WordTrace (prefixWord ++ tailWord_4576725) baseStart_4576725 baseEnd_4576725 := by
    simpa [prefixWord, tailWord_4576725, baseEnd_4576725] using wordTrace_append hprefix tailTrace_4576725
  have hstable : (prefixWord ++ tailWord_4576725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576725).length < 2 ^ (prefixWord ++ tailWord_4576725).sum := by decide
  have hdescent : baseEnd_4576725 < baseStart_4576725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576746 : List Nat := [3, 1, 3, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_4576746 : Nat := 118140960795 + 4576746 * 2 ^ 59
def prefixEnd_4576746 : Nat := 4983230072969 + 3 ^ 40 * 4576746 * 2
def baseEnd_4576746 : Nat := 2350070531542455693926935

theorem tailTrace_4576746 : CollatzResearch.WordTrace tailWord_4576746 prefixEnd_4576746 2350070531542455693926935 := by
  unfold tailWord_4576746
  simp only [CollatzResearch.WordTrace]
  refine ⟨41731910069309590707973523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111285093518158908554596061 41731910069309590707973523)
  ·
    refine ⟨62597865103964386061960285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41731910069309590707973523 62597865103964386061960285)
    ·
      refine ⟨23474199413986644773235107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62597865103964386061960285 23474199413986644773235107)
      ·
        refine ⟨35211299120979967159852661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23474199413986644773235107 35211299120979967159852661)
        ·
          refine ⟨3301059292591871921236187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35211299120979967159852661 3301059292591871921236187)
          ·
            refine ⟨4951588938887807881854281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3301059292591871921236187 4951588938887807881854281)
            ·
              refine ⟨3713691704165855911390711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4951588938887807881854281 3713691704165855911390711)
              ·
                refine ⟨5570537556248783867086067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3713691704165855911390711 5570537556248783867086067)
                ·
                  refine ⟨8355806334373175800629101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5570537556248783867086067 8355806334373175800629101)
                  ·
                    refine ⟨3133427375389940925235913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8355806334373175800629101 3133427375389940925235913)
                    ·
                      refine ⟨2350070531542455693926935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3133427375389940925235913 2350070531542455693926935)
                      ·
                        rfl

theorem cell23_4576746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_4576746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576746 prefixEnd_4576746 := by exact prefixLift 4576746
  have htrace : WordTrace (prefixWord ++ tailWord_4576746) baseStart_4576746 baseEnd_4576746 := by
    simpa [prefixWord, tailWord_4576746, baseEnd_4576746] using wordTrace_append hprefix tailTrace_4576746
  have hstable : (prefixWord ++ tailWord_4576746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576746).length < 2 ^ (prefixWord ++ tailWord_4576746).sum := by decide
  have hdescent : baseEnd_4576746 < baseStart_4576746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576761 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 4, 5]
def baseStart_4576761 : Nat := 118140960795 + 4576761 * 2 ^ 59
def prefixEnd_4576761 : Nat := 4983230072969 + 3 ^ 40 * 4576761 * 2
def baseEnd_4576761 : Nat := 783359411250757711746455

theorem tailTrace_4576761 : CollatzResearch.WordTrace tailWord_4576761 prefixEnd_4576761 783359411250757711746455 := by
  unfold tailWord_4576761
  simp only [CollatzResearch.WordTrace]
  refine ⟨166928187372184020393690137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111285458248122680262460091 166928187372184020393690137)
  ·
    refine ⟨125196140529138015295267603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166928187372184020393690137 125196140529138015295267603)
    ·
      refine ⟨187794210793707022942901405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125196140529138015295267603 187794210793707022942901405)
      ·
        refine ⟨70422829047640133603588027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187794210793707022942901405 70422829047640133603588027)
        ·
          refine ⟨105634243571460200405382041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70422829047640133603588027 105634243571460200405382041)
          ·
            refine ⟨79225682678595150304036531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105634243571460200405382041 79225682678595150304036531)
            ·
              refine ⟨118838524017892725456054797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79225682678595150304036531 118838524017892725456054797)
              ·
                refine ⟨44564446506709772046020549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118838524017892725456054797 44564446506709772046020549)
                ·
                  refine ⟨8355833720008082258628853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44564446506709772046020549 8355833720008082258628853)
                  ·
                    refine ⟨783359411250757711746455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8355833720008082258628853 783359411250757711746455)
                    ·
                      rfl

theorem cell23_4576761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 5].length) (baseStart_4576761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576761 prefixEnd_4576761 := by exact prefixLift 4576761
  have htrace : WordTrace (prefixWord ++ tailWord_4576761) baseStart_4576761 baseEnd_4576761 := by
    simpa [prefixWord, tailWord_4576761, baseEnd_4576761] using wordTrace_append hprefix tailTrace_4576761
  have hstable : (prefixWord ++ tailWord_4576761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576761).length < 2 ^ (prefixWord ++ tailWord_4576761).sum := by decide
  have hdescent : baseEnd_4576761 < baseStart_4576761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576825 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 3, 4]
def baseStart_4576825 : Nat := 118140960795 + 4576825 * 2 ^ 59
def prefixEnd_4576825 : Nat := 4983230072969 + 3 ^ 40 * 4576825 * 2
def baseEnd_4576825 : Nat := 783370365504720294946357

theorem tailTrace_4576825 : CollatzResearch.WordTrace tailWord_4576825 prefixEnd_4576825 783370365504720294946357 := by
  unfold tailWord_4576825
  simp only [CollatzResearch.WordTrace]
  refine ⟨166930521643952159324019929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111287014429301439549346619 166930521643952159324019929)
  ·
    refine ⟨125197891232964119493014947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166930521643952159324019929 125197891232964119493014947)
    ·
      refine ⟨187796836849446179239522421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125197891232964119493014947 187796836849446179239522421)
      ·
        refine ⟨17605953454635579303705227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 187796836849446179239522421 17605953454635579303705227)
        ·
          refine ⟨26408930181953368955557841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17605953454635579303705227 26408930181953368955557841)
          ·
            refine ⟨19806697636465026716668381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26408930181953368955557841 19806697636465026716668381)
            ·
              refine ⟨7427511613674385018750643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19806697636465026716668381 7427511613674385018750643)
              ·
                refine ⟨11141267420511577528125965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7427511613674385018750643 11141267420511577528125965)
                ·
                  refine ⟨4177975282691841573047237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11141267420511577528125965 4177975282691841573047237)
                  ·
                    refine ⟨783370365504720294946357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4177975282691841573047237 783370365504720294946357)
                    ·
                      rfl

theorem cell23_4576825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 4].length) (baseStart_4576825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576825 prefixEnd_4576825 := by exact prefixLift 4576825
  have htrace : WordTrace (prefixWord ++ tailWord_4576825) baseStart_4576825 baseEnd_4576825 := by
    simpa [prefixWord, tailWord_4576825, baseEnd_4576825] using wordTrace_append hprefix tailTrace_4576825
  have hstable : (prefixWord ++ tailWord_4576825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576825).length < 2 ^ (prefixWord ++ tailWord_4576825).sum := by decide
  have hdescent : baseEnd_4576825 < baseStart_4576825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576841 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 6]
def baseStart_4576841 : Nat := 118140960795 + 4576841 * 2 ^ 59
def prefixEnd_4576841 : Nat := 4983230072969 + 3 ^ 40 * 4576841 * 2
def baseEnd_4576841 : Nat := 2350119312204632822238997

theorem tailTrace_4576841 : CollatzResearch.WordTrace tailWord_4576841 prefixEnd_4576841 2350119312204632822238997 := by
  unfold tailWord_4576841
  simp only [CollatzResearch.WordTrace]
  refine ⟨166931105211894194056602377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111287403474596129371068251 166931105211894194056602377)
  ·
    refine ⟨125198328908920645542451783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166931105211894194056602377 125198328908920645542451783)
    ·
      refine ⟨187797493363380968313677675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125198328908920645542451783 187797493363380968313677675)
      ·
        refine ⟨281696240045071452470516513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187797493363380968313677675 281696240045071452470516513)
        ·
          refine ⟨211272180033803589352887385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281696240045071452470516513 211272180033803589352887385)
          ·
            refine ⟨158454135025352692014665539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211272180033803589352887385 158454135025352692014665539)
            ·
              refine ⟨237681202538029038021998309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158454135025352692014665539 237681202538029038021998309)
              ·
                refine ⟨44565225475880444629124683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 237681202538029038021998309 44565225475880444629124683)
                ·
                  refine ⟨66847838213820666943687025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44565225475880444629124683 66847838213820666943687025)
                  ·
                    refine ⟨50135878660365500207765269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66847838213820666943687025 50135878660365500207765269)
                    ·
                      refine ⟨2350119312204632822238997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50135878660365500207765269 2350119312204632822238997)
                      ·
                        rfl

theorem cell23_4576841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_4576841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576841 prefixEnd_4576841 := by exact prefixLift 4576841
  have htrace : WordTrace (prefixWord ++ tailWord_4576841) baseStart_4576841 baseEnd_4576841 := by
    simpa [prefixWord, tailWord_4576841, baseEnd_4576841] using wordTrace_append hprefix tailTrace_4576841
  have hstable : (prefixWord ++ tailWord_4576841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576841).length < 2 ^ (prefixWord ++ tailWord_4576841).sum := by decide
  have hdescent : baseEnd_4576841 < baseStart_4576841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576885 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 3, 5]
def baseStart_4576885 : Nat := 118140960795 + 4576885 * 2 ^ 59
def prefixEnd_4576885 : Nat := 4983230072969 + 3 ^ 40 * 4576885 * 2
def baseEnd_4576885 : Nat := 783380635117810216696265

theorem tailTrace_4576885 : CollatzResearch.WordTrace tailWord_4576885 prefixEnd_4576885 783380635117810216696265 := by
  unfold tailWord_4576885
  simp only [CollatzResearch.WordTrace]
  refine ⟨166932710023734789571204109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111288473349156526380802739 166932710023734789571204109)
  ·
    refine ⟨62599766258900546089201541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166932710023734789571204109 62599766258900546089201541)
    ·
      refine ⟨11737456173543852391725289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62599766258900546089201541 11737456173543852391725289)
      ·
        refine ⟨8803092130157889293793967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11737456173543852391725289 8803092130157889293793967)
        ·
          refine ⟨13204638195236833940690951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8803092130157889293793967 13204638195236833940690951)
          ·
            refine ⟨19806957292855250911036427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13204638195236833940690951 19806957292855250911036427)
            ·
              refine ⟨29710435939282876366554641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19806957292855250911036427 29710435939282876366554641)
              ·
                refine ⟨22282826954462157274915981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29710435939282876366554641 22282826954462157274915981)
                ·
                  refine ⟨8356060107923308978093493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22282826954462157274915981 8356060107923308978093493)
                  ·
                    refine ⟨783380635117810216696265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8356060107923308978093493 783380635117810216696265)
                    ·
                      rfl

theorem cell23_4576885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_4576885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576885 prefixEnd_4576885 := by exact prefixLift 4576885
  have htrace : WordTrace (prefixWord ++ tailWord_4576885) baseStart_4576885 baseEnd_4576885 := by
    simpa [prefixWord, tailWord_4576885, baseEnd_4576885] using wordTrace_append hprefix tailTrace_4576885
  have hstable : (prefixWord ++ tailWord_4576885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576885).length < 2 ^ (prefixWord ++ tailWord_4576885).sum := by decide
  have hdescent : baseEnd_4576885 < baseStart_4576885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576928 : List Nat := [2, 1, 1, 4, 3, 2, 10]
def baseStart_4576928 : Nat := 118140960795 + 4576928 * 2 ^ 59
def prefixEnd_4576928 : Nat := 4983230072969 + 3 ^ 40 * 4576928 * 2
def baseEnd_4576928 : Nat := 29014370185451530640137

theorem tailTrace_4576928 : CollatzResearch.WordTrace tailWord_4576928 prefixEnd_4576928 29014370185451530640137 := by
  unfold tailWord_4576928
  simp only [CollatzResearch.WordTrace]
  refine ⟨83467139181289503957509719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111289518908386005276679625 83467139181289503957509719)
  ·
    refine ⟨125200708771934255936264579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83467139181289503957509719 125200708771934255936264579)
    ·
      refine ⟨187801063157901383904396869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125200708771934255936264579 187801063157901383904396869)
      ·
        refine ⟨35212699342106509482074413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187801063157901383904396869 35212699342106509482074413)
        ·
          refine ⟨13204762253289941055777905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35212699342106509482074413 13204762253289941055777905)
          ·
            refine ⟨9903571689967455791833429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13204762253289941055777905 9903571689967455791833429)
            ·
              refine ⟨29014370185451530640137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9903571689967455791833429 29014370185451530640137)
              ·
                rfl

theorem cell23_4576928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 10].length) (baseStart_4576928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576928 prefixEnd_4576928 := by exact prefixLift 4576928
  have htrace : WordTrace (prefixWord ++ tailWord_4576928) baseStart_4576928 baseEnd_4576928 := by
    simpa [prefixWord, tailWord_4576928, baseEnd_4576928] using wordTrace_append hprefix tailTrace_4576928
  have hstable : (prefixWord ++ tailWord_4576928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576928).length < 2 ^ (prefixWord ++ tailWord_4576928).sum := by decide
  have hdescent : baseEnd_4576928 < baseStart_4576928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576932 : List Nat := [2, 3, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_4576932 : Nat := 118140960795 + 4576932 * 2 ^ 59
def prefixEnd_4576932 : Nat := 4983230072969 + 3 ^ 40 * 4576932 * 2
def baseEnd_4576932 : Nat := 783388679648063988733693

theorem tailTrace_4576932 : CollatzResearch.WordTrace tailWord_4576932 prefixEnd_4576932 783388679648063988733693 := by
  unfold tailWord_4576932
  simp only [CollatzResearch.WordTrace]
  refine ⟨83467212127282258299082525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111289616169709677732110033 83467212127282258299082525)
  ·
    refine ⟨31300204547730846862155947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83467212127282258299082525 31300204547730846862155947)
    ·
      refine ⟨46950306821596270293233921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31300204547730846862155947 46950306821596270293233921)
      ·
        refine ⟨35212730116197202719925441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46950306821596270293233921 35212730116197202719925441)
        ·
          refine ⟨26409547587147902039944081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35212730116197202719925441 26409547587147902039944081)
          ·
            refine ⟨19807160690360926529958061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26409547587147902039944081 19807160690360926529958061)
            ·
              refine ⟨7427685258885347448734273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19807160690360926529958061 7427685258885347448734273)
              ·
                refine ⟨5570763944164010586550705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7427685258885347448734273 5570763944164010586550705)
                ·
                  refine ⟨4178072958123007939913029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5570763944164010586550705 4178072958123007939913029)
                  ·
                    refine ⟨783388679648063988733693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4178072958123007939913029 783388679648063988733693)
                    ·
                      rfl

theorem cell23_4576932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_4576932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576932 prefixEnd_4576932 := by exact prefixLift 4576932
  have htrace : WordTrace (prefixWord ++ tailWord_4576932) baseStart_4576932 baseEnd_4576932 := by
    simpa [prefixWord, tailWord_4576932, baseEnd_4576932] using wordTrace_append hprefix tailTrace_4576932
  have hstable : (prefixWord ++ tailWord_4576932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576932).length < 2 ^ (prefixWord ++ tailWord_4576932).sum := by decide
  have hdescent : baseEnd_4576932 < baseStart_4576932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576949 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 1, 6]
def baseStart_4576949 : Nat := 118140960795 + 4576949 * 2 ^ 59
def prefixEnd_4576949 : Nat := 4983230072969 + 3 ^ 40 * 4576949 * 2
def baseEnd_4576949 : Nat := 783391589371772799896167

theorem tailTrace_4576949 : CollatzResearch.WordTrace tailWord_4576949 prefixEnd_4576949 783391589371772799896167 := by
  unfold tailWord_4576949
  simp only [CollatzResearch.WordTrace]
  refine ⟨166935044295502928501533901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111290029530335285667689267 166935044295502928501533901)
  ·
    refine ⟨62600641610813598188075213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 166935044295502928501533901 62600641610813598188075213)
    ·
      refine ⟨23475240604055099320528205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62600641610813598188075213 23475240604055099320528205)
      ·
        refine ⟨8803215226520662245198077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23475240604055099320528205 8803215226520662245198077)
        ·
          refine ⟨3301205709945248341949279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8803215226520662245198077 3301205709945248341949279)
          ·
            refine ⟨4951808564917872512923919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3301205709945248341949279 4951808564917872512923919)
            ·
              refine ⟨7427712847376808769385879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4951808564917872512923919 7427712847376808769385879)
              ·
                refine ⟨11141569271065213154078819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7427712847376808769385879 11141569271065213154078819)
                ·
                  refine ⟨16712353906597819731118229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11141569271065213154078819 16712353906597819731118229)
                  ·
                    refine ⟨783391589371772799896167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16712353906597819731118229 783391589371772799896167)
                    ·
                      rfl

theorem cell23_4576949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_4576949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576949 prefixEnd_4576949 := by exact prefixLift 4576949
  have htrace : WordTrace (prefixWord ++ tailWord_4576949) baseStart_4576949 baseEnd_4576949 := by
    simpa [prefixWord, tailWord_4576949, baseEnd_4576949] using wordTrace_append hprefix tailTrace_4576949
  have hstable : (prefixWord ++ tailWord_4576949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576949).length < 2 ^ (prefixWord ++ tailWord_4576949).sum := by decide
  have hdescent : baseEnd_4576949 < baseStart_4576949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4576968 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_4576968 : Nat := 118140960795 + 4576968 * 2 ^ 59
def prefixEnd_4576968 : Nat := 4983230072969 + 3 ^ 40 * 4576968 * 2
def baseEnd_4576968 : Nat := 2350184524247753825350913

theorem tailTrace_4576968 : CollatzResearch.WordTrace tailWord_4576968 prefixEnd_4576968 2350184524247753825350913 := by
  unfold tailWord_4576968
  simp only [CollatzResearch.WordTrace]
  refine ⟨83467868641217047373237779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111290491521622729830983705 83467868641217047373237779)
  ·
    refine ⟨125201802961825571059856669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83467868641217047373237779 125201802961825571059856669)
    ·
      refine ⟨46950676110684589147446251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125201802961825571059856669 46950676110684589147446251)
      ·
        refine ⟨70426014166026883721169377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46950676110684589147446251 70426014166026883721169377)
        ·
          refine ⟨52819510624520162790877033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70426014166026883721169377 52819510624520162790877033)
          ·
            refine ⟨39614632968390122093157775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52819510624520162790877033 39614632968390122093157775)
            ·
              refine ⟨59421949452585183139736663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39614632968390122093157775 59421949452585183139736663)
              ·
                refine ⟨89132924178877774709604995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59421949452585183139736663 89132924178877774709604995)
                ·
                  refine ⟨133699386268316662064407493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89132924178877774709604995 133699386268316662064407493)
                  ·
                    refine ⟨25068634925309374137076405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 133699386268316662064407493 25068634925309374137076405)
                    ·
                      refine ⟨2350184524247753825350913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25068634925309374137076405 2350184524247753825350913)
                      ·
                        rfl

theorem cell23_4576968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_4576968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4576968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4576968 prefixEnd_4576968 := by exact prefixLift 4576968
  have htrace : WordTrace (prefixWord ++ tailWord_4576968) baseStart_4576968 baseEnd_4576968 := by
    simpa [prefixWord, tailWord_4576968, baseEnd_4576968] using wordTrace_append hprefix tailTrace_4576968
  have hstable : (prefixWord ++ tailWord_4576968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4576968).length < 2 ^ (prefixWord ++ tailWord_4576968).sum := by decide
  have hdescent : baseEnd_4576968 < baseStart_4576968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4576968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577018 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 9]
def baseStart_4577018 : Nat := 118140960795 + 4577018 * 2 ^ 59
def prefixEnd_4577018 : Nat := 4983230072969 + 3 ^ 40 * 4577018 * 2
def baseEnd_4577018 : Nat := 261134466475608736636187

theorem tailTrace_4577018 : CollatzResearch.WordTrace tailWord_4577018 prefixEnd_4577018 261134466475608736636187 := by
  unfold tailWord_4577018
  simp only [CollatzResearch.WordTrace]
  refine ⟨41734390233063238321448927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111291707288168635523863805 41734390233063238321448927)
  ·
    refine ⟨62601585349594857482173391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41734390233063238321448927 62601585349594857482173391)
    ·
      refine ⟨93902378024392286223260087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62601585349594857482173391 93902378024392286223260087)
      ·
        refine ⟨140853567036588429334890131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93902378024392286223260087 140853567036588429334890131)
        ·
          refine ⟨211280350554882644002335197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140853567036588429334890131 211280350554882644002335197)
          ·
            refine ⟨79230131458080991500875699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211280350554882644002335197 79230131458080991500875699)
            ·
              refine ⟨118845197187121487251313549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79230131458080991500875699 118845197187121487251313549)
              ·
                refine ⟨44566948945170557719242581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118845197187121487251313549 44566948945170557719242581)
                ·
                  refine ⟨261134466475608736636187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44566948945170557719242581 261134466475608736636187)
                  ·
                    rfl

theorem cell23_4577018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_4577018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577018 prefixEnd_4577018 := by exact prefixLift 4577018
  have htrace : WordTrace (prefixWord ++ tailWord_4577018) baseStart_4577018 baseEnd_4577018 := by
    simpa [prefixWord, tailWord_4577018, baseEnd_4577018] using wordTrace_append hprefix tailTrace_4577018
  have hstable : (prefixWord ++ tailWord_4577018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577018).length < 2 ^ (prefixWord ++ tailWord_4577018).sum := by decide
  have hdescent : baseEnd_4577018 < baseStart_4577018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577052 : List Nat := [2, 2, 3, 1, 1, 2, 3, 4, 5]
def baseStart_4577052 : Nat := 118140960795 + 4577052 * 2 ^ 59
def prefixEnd_4577052 : Nat := 4983230072969 + 3 ^ 40 * 4577052 * 2
def baseEnd_4577052 : Nat := 261136406291414610744503

theorem tailTrace_4577052 : CollatzResearch.WordTrace tailWord_4577052 prefixEnd_4577052 261136406291414610744503 := by
  unfold tailWord_4577052
  simp only [CollatzResearch.WordTrace]
  refine ⟨83469400507064888546266705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111292534009419851395022273 83469400507064888546266705)
  ·
    refine ⟨62602050380298666409700029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83469400507064888546266705 62602050380298666409700029)
    ·
      refine ⟨23475768892611999903637511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62602050380298666409700029 23475768892611999903637511)
      ·
        refine ⟨35213653338917999855456267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23475768892611999903637511 35213653338917999855456267)
        ·
          refine ⟨52820480008376999783184401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35213653338917999855456267 52820480008376999783184401)
          ·
            refine ⟨39615360006282749837388301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52820480008376999783184401 39615360006282749837388301)
            ·
              refine ⟨14855760002356031189020613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39615360006282749837388301 14855760002356031189020613)
              ·
                refine ⟨2785455000441755847941365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14855760002356031189020613 2785455000441755847941365)
                ·
                  refine ⟨261136406291414610744503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2785455000441755847941365 261136406291414610744503)
                  ·
                    rfl

theorem cell23_4577052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 5].length) (baseStart_4577052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577052 prefixEnd_4577052 := by exact prefixLift 4577052
  have htrace : WordTrace (prefixWord ++ tailWord_4577052) baseStart_4577052 baseEnd_4577052 := by
    simpa [prefixWord, tailWord_4577052, baseEnd_4577052] using wordTrace_append hprefix tailTrace_4577052
  have hstable : (prefixWord ++ tailWord_4577052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577052).length < 2 ^ (prefixWord ++ tailWord_4577052).sum := by decide
  have hdescent : baseEnd_4577052 < baseStart_4577052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577082 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 2, 5]
def baseStart_4577082 : Nat := 118140960795 + 4577082 * 2 ^ 59
def prefixEnd_4577082 : Nat := 4983230072969 + 3 ^ 40 * 4577082 * 2
def baseEnd_4577082 : Nat := 783414353680788793108463

theorem tailTrace_4577082 : CollatzResearch.WordTrace tailWord_4577082 prefixEnd_4577082 783414353680788793108463 := by
  unfold tailWord_4577082
  simp only [CollatzResearch.WordTrace]
  refine ⟨41734973801005273054031375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111293263469347394810750333 41734973801005273054031375)
  ·
    refine ⟨62602460701507909581047063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41734973801005273054031375 62602460701507909581047063)
    ·
      refine ⟨93903691052261864371570595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62602460701507909581047063 93903691052261864371570595)
      ·
        refine ⟨140855536578392796557355893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93903691052261864371570595 140855536578392796557355893)
        ·
          refine ⟨13205206554224324677252115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140855536578392796557355893 13205206554224324677252115)
          ·
            refine ⟨19807809831336487015878173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13205206554224324677252115 19807809831336487015878173)
            ·
              refine ⟨7427928686751182630954315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19807809831336487015878173 7427928686751182630954315)
              ·
                refine ⟨11141893030126773946431473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7427928686751182630954315 11141893030126773946431473)
                ·
                  refine ⟨8356419772595080459823605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11141893030126773946431473 8356419772595080459823605)
                  ·
                    refine ⟨783414353680788793108463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8356419772595080459823605 783414353680788793108463)
                    ·
                      rfl

theorem cell23_4577082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_4577082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577082 prefixEnd_4577082 := by exact prefixLift 4577082
  have htrace : WordTrace (prefixWord ++ tailWord_4577082) baseStart_4577082 baseEnd_4577082 := by
    simpa [prefixWord, tailWord_4577082, baseEnd_4577082] using wordTrace_append hprefix tailTrace_4577082
  have hstable : (prefixWord ++ tailWord_4577082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577082).length < 2 ^ (prefixWord ++ tailWord_4577082).sum := by decide
  have hdescent : baseEnd_4577082 < baseStart_4577082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577169 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 3, 1, 3]
def baseStart_4577169 : Nat := 118140960795 + 4577169 * 2 ^ 59
def prefixEnd_4577169 : Nat := 4983230072969 + 3 ^ 40 * 4577169 * 2
def baseEnd_4577169 : Nat := 2350287733859307538937489

theorem tailTrace_4577169 : CollatzResearch.WordTrace tailWord_4577169 prefixEnd_4577169 2350287733859307538937489 := by
  unfold tailWord_4577169
  simp only [CollatzResearch.WordTrace]
  refine ⟨166943068354705906074542561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111295378903137270716361707 166943068354705906074542561)
  ·
    refine ⟨125207301266029429555906921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166943068354705906074542561 125207301266029429555906921)
    ·
      refine ⟨93905475949522072166930191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125207301266029429555906921 93905475949522072166930191)
      ·
        refine ⟨140858213924283108250395287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93905475949522072166930191 140858213924283108250395287)
        ·
          refine ⟨211287320886424662375592931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140858213924283108250395287 211287320886424662375592931)
          ·
            refine ⟨316930981329636993563389397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211287320886424662375592931 316930981329636993563389397)
            ·
              refine ⟨7428069874913367036641939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 316930981329636993563389397 7428069874913367036641939)
              ·
                refine ⟨11142104812370050554962909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7428069874913367036641939 11142104812370050554962909)
                ·
                  refine ⟨4178289304638768958111091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11142104812370050554962909 4178289304638768958111091)
                  ·
                    refine ⟨6267433956958153437166637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4178289304638768958111091 6267433956958153437166637)
                    ·
                      refine ⟨2350287733859307538937489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6267433956958153437166637 2350287733859307538937489)
                      ·
                        rfl

theorem cell23_4577169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_4577169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577169 prefixEnd_4577169 := by exact prefixLift 4577169
  have htrace : WordTrace (prefixWord ++ tailWord_4577169) baseStart_4577169 baseEnd_4577169 := by
    simpa [prefixWord, tailWord_4577169, baseEnd_4577169] using wordTrace_append hprefix tailTrace_4577169
  have hstable : (prefixWord ++ tailWord_4577169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577169).length < 2 ^ (prefixWord ++ tailWord_4577169).sum := by decide
  have hdescent : baseEnd_4577169 < baseStart_4577169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577202 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_4577202 : Nat := 118140960795 + 4577202 * 2 ^ 59
def prefixEnd_4577202 : Nat := 4983230072969 + 3 ^ 40 * 4577202 * 2
def baseEnd_4577202 : Nat := 783434892906968636608279

theorem tailTrace_4577202 : CollatzResearch.WordTrace tailWord_4577202 prefixEnd_4577202 783434892906968636608279 := by
  unfold tailWord_4577202
  simp only [CollatzResearch.WordTrace]
  refine ⟨41736067990896588177623465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111296181309057568473662573 41736067990896588177623465)
  ·
    refine ⟨31302050993172441133217599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41736067990896588177623465 31302050993172441133217599)
    ·
      refine ⟨46953076489758661699826399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31302050993172441133217599 46953076489758661699826399)
      ·
        refine ⟨70429614734637992549739599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46953076489758661699826399 70429614734637992549739599)
        ·
          refine ⟨105644422101956988824609399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70429614734637992549739599 105644422101956988824609399)
          ·
            refine ⟨158466633152935483236914099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105644422101956988824609399 158466633152935483236914099)
            ·
              refine ⟨237699949729403224855371149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158466633152935483236914099 237699949729403224855371149)
              ·
                refine ⟨89137481148526209320764181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237699949729403224855371149 89137481148526209320764181)
                ·
                  refine ⟨4178319428837166061910821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89137481148526209320764181 4178319428837166061910821)
                  ·
                    refine ⟨783434892906968636608279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4178319428837166061910821 783434892906968636608279)
                    ·
                      rfl

theorem cell23_4577202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_4577202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577202 prefixEnd_4577202 := by exact prefixLift 4577202
  have htrace : WordTrace (prefixWord ++ tailWord_4577202) baseStart_4577202 baseEnd_4577202 := by
    simpa [prefixWord, tailWord_4577202, baseEnd_4577202] using wordTrace_append hprefix tailTrace_4577202
  have hstable : (prefixWord ++ tailWord_4577202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577202).length < 2 ^ (prefixWord ++ tailWord_4577202).sum := by decide
  have hdescent : baseEnd_4577202 < baseStart_4577202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577270 : List Nat := [5, 1, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_4577270 : Nat := 118140960795 + 4577270 * 2 ^ 59
def prefixEnd_4577270 : Nat := 4983230072969 + 3 ^ 40 * 4577270 * 2
def baseEnd_4577270 : Nat := 783446531801803881258175

theorem tailTrace_4577270 : CollatzResearch.WordTrace tailWord_4577270 prefixEnd_4577270 783446531801803881258175 := by
  unfold tailWord_4577270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10434172007958750020248079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111297834751560000215979509 10434172007958750020248079)
  ·
    refine ⟨15651258011938125030372119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10434172007958750020248079 15651258011938125030372119)
    ·
      refine ⟨23476887017907187545558179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15651258011938125030372119 23476887017907187545558179)
      ·
        refine ⟨35215330526860781318337269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23476887017907187545558179 35215330526860781318337269)
        ·
          refine ⟨3301437236893198248594119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35215330526860781318337269 3301437236893198248594119)
          ·
            refine ⟨4952155855339797372891179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3301437236893198248594119 4952155855339797372891179)
            ·
              refine ⟨7428233783009696059336769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4952155855339797372891179 7428233783009696059336769)
              ·
                refine ⟨5571175337257272044502577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7428233783009696059336769 5571175337257272044502577)
                ·
                  refine ⟨4178381502942954033376933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5571175337257272044502577 4178381502942954033376933)
                  ·
                    refine ⟨783446531801803881258175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4178381502942954033376933 783446531801803881258175)
                    ·
                      rfl

theorem cell23_4577270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_4577270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577270 prefixEnd_4577270 := by exact prefixLift 4577270
  have htrace : WordTrace (prefixWord ++ tailWord_4577270) baseStart_4577270 baseEnd_4577270 := by
    simpa [prefixWord, tailWord_4577270, baseEnd_4577270] using wordTrace_append hprefix tailTrace_4577270
  have hstable : (prefixWord ++ tailWord_4577270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577270).length < 2 ^ (prefixWord ++ tailWord_4577270).sum := by decide
  have hdescent : baseEnd_4577270 < baseStart_4577270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577292 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 2, 6]
def baseStart_4577292 : Nat := 118140960795 + 4577292 * 2 ^ 59
def prefixEnd_4577292 : Nat := 4983230072969 + 3 ^ 40 * 4577292 * 2
def baseEnd_4577292 : Nat := 783450297326603519233141

theorem tailTrace_4577292 : CollatzResearch.WordTrace tailWord_4577292 prefixEnd_4577292 783450297326603519233141 := by
  unfold tailWord_4577292
  simp only [CollatzResearch.WordTrace]
  refine ⟨83473777266630149040635065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111298369688840198720846753 83473777266630149040635065)
  ·
    refine ⟨62605332949972611780476299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83473777266630149040635065 62605332949972611780476299)
    ·
      refine ⟨93907999424958917670714449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62605332949972611780476299 93907999424958917670714449)
      ·
        refine ⟨70430999568719188253035837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93907999424958917670714449 70430999568719188253035837)
        ·
          refine ⟨26411624838269695594888439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70430999568719188253035837 26411624838269695594888439)
          ·
            refine ⟨39617437257404543392332659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26411624838269695594888439 39617437257404543392332659)
            ·
              refine ⟨59426155886106815088498989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39617437257404543392332659 59426155886106815088498989)
              ·
                refine ⟨22284808457290055658187121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59426155886106815088498989 22284808457290055658187121)
                ·
                  refine ⟨16713606342967541743640341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22284808457290055658187121 16713606342967541743640341)
                  ·
                    refine ⟨783450297326603519233141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16713606342967541743640341 783450297326603519233141)
                    ·
                      rfl

theorem cell23_4577292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_4577292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577292 prefixEnd_4577292 := by exact prefixLift 4577292
  have htrace : WordTrace (prefixWord ++ tailWord_4577292) baseStart_4577292 baseEnd_4577292 := by
    simpa [prefixWord, tailWord_4577292, baseEnd_4577292] using wordTrace_append hprefix tailTrace_4577292
  have hstable : (prefixWord ++ tailWord_4577292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577292).length < 2 ^ (prefixWord ++ tailWord_4577292).sum := by decide
  have hdescent : baseEnd_4577292 < baseStart_4577292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577300 : List Nat := [2, 4, 3, 2, 2, 1, 2, 7]
def baseStart_4577300 : Nat := 118140960795 + 4577300 * 2 ^ 59
def prefixEnd_4577300 : Nat := 4983230072969 + 3 ^ 40 * 4577300 * 2
def baseEnd_4577300 : Nat := 87050185178705426903681

theorem tailTrace_4577300 : CollatzResearch.WordTrace tailWord_4577300 prefixEnd_4577300 87050185178705426903681 := by
  unfold tailWord_4577300
  simp only [CollatzResearch.WordTrace]
  refine ⟨83473923158615657723780677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111298564211487543631707569 83473923158615657723780677)
  ·
    refine ⟨15651360592240435823208877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83473923158615657723780677 15651360592240435823208877)
    ·
      refine ⟨5869260222090163433703329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15651360592240435823208877 5869260222090163433703329)
      ·
        refine ⟨4401945166567622575277497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5869260222090163433703329 4401945166567622575277497)
        ·
          refine ⟨3301458874925716931458123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4401945166567622575277497 3301458874925716931458123)
          ·
            refine ⟨4952188312388575397187185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3301458874925716931458123 4952188312388575397187185)
            ·
              refine ⟨3714141234291431547890389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4952188312388575397187185 3714141234291431547890389)
              ·
                refine ⟨87050185178705426903681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3714141234291431547890389 87050185178705426903681)
                ·
                  rfl

theorem cell23_4577300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 7].length) (baseStart_4577300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577300 prefixEnd_4577300 := by exact prefixLift 4577300
  have htrace : WordTrace (prefixWord ++ tailWord_4577300) baseStart_4577300 baseEnd_4577300 := by
    simpa [prefixWord, tailWord_4577300, baseEnd_4577300] using wordTrace_append hprefix tailTrace_4577300
  have hstable : (prefixWord ++ tailWord_4577300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577300).length < 2 ^ (prefixWord ++ tailWord_4577300).sum := by decide
  have hdescent : baseEnd_4577300 < baseStart_4577300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577352 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 1, 7]
def baseStart_4577352 : Nat := 118140960795 + 4577352 * 2 ^ 59
def prefixEnd_4577352 : Nat := 4983230072969 + 3 ^ 40 * 4577352 * 2
def baseEnd_4577352 : Nat := 783460566939693440983049

theorem tailTrace_4577352 : CollatzResearch.WordTrace tailWord_4577352 prefixEnd_4577352 783460566939693440983049 := by
  unfold tailWord_4577352
  simp only [CollatzResearch.WordTrace]
  refine ⟨83474871456521464164227155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111299828608695285552302873 83474871456521464164227155)
  ·
    refine ⟨125212307184782196246340733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83474871456521464164227155 125212307184782196246340733)
    ·
      refine ⟨46954615194293323592377775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125212307184782196246340733 46954615194293323592377775)
      ·
        refine ⟨70431922791439985388566663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46954615194293323592377775 70431922791439985388566663)
        ·
          refine ⟨105647884187159978082849995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70431922791439985388566663 105647884187159978082849995)
          ·
            refine ⟨158471826280739967124274993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105647884187159978082849995 158471826280739967124274993)
            ·
              refine ⟨118853869710554975343206245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158471826280739967124274993 118853869710554975343206245)
              ·
                refine ⟨22285100570729057876851171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118853869710554975343206245 22285100570729057876851171)
                ·
                  refine ⟨33427650856093586815276757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22285100570729057876851171 33427650856093586815276757)
                  ·
                    refine ⟨783460566939693440983049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33427650856093586815276757 783460566939693440983049)
                    ·
                      rfl

theorem cell23_4577352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_4577352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577352 prefixEnd_4577352 := by exact prefixLift 4577352
  have htrace : WordTrace (prefixWord ++ tailWord_4577352) baseStart_4577352 baseEnd_4577352 := by
    simpa [prefixWord, tailWord_4577352, baseEnd_4577352] using wordTrace_append hprefix tailTrace_4577352
  have hstable : (prefixWord ++ tailWord_4577352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577352).length < 2 ^ (prefixWord ++ tailWord_4577352).sum := by decide
  have hdescent : baseEnd_4577352 < baseStart_4577352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577359 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 2, 5, 2]
def baseStart_4577359 : Nat := 118140960795 + 4577359 * 2 ^ 59
def prefixEnd_4577359 : Nat := 4983230072969 + 3 ^ 40 * 4577359 * 2
def baseEnd_4577359 : Nat := 2350385295183661795561615

theorem tailTrace_4577359 : CollatzResearch.WordTrace tailWord_4577359 prefixEnd_4577359 2350385295183661795561615 := by
  unfold tailWord_4577359
  simp only [CollatzResearch.WordTrace]
  refine ⟨166949998224017568523959131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111299998816011712349306087 166949998224017568523959131)
  ·
    refine ⟨250424997336026352785938697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 166949998224017568523959131 250424997336026352785938697)
    ·
      refine ⟨187818748002019764589454023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250424997336026352785938697 187818748002019764589454023)
      ·
        refine ⟨281728122003029646884181035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187818748002019764589454023 281728122003029646884181035)
        ·
          refine ⟨422592183004544470326271553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281728122003029646884181035 422592183004544470326271553)
          ·
            refine ⟨316944137253408352744703665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422592183004544470326271553 316944137253408352744703665)
            ·
              refine ⟨237708102940056264558527749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316944137253408352744703665 237708102940056264558527749)
              ·
                refine ⟨44570269301260549604723953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 237708102940056264558527749 44570269301260549604723953)
                ·
                  refine ⟨33427701975945412203542965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44570269301260549604723953 33427701975945412203542965)
                  ·
                    refine ⟨3133847060244882394082153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33427701975945412203542965 3133847060244882394082153)
                    ·
                      refine ⟨2350385295183661795561615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3133847060244882394082153 2350385295183661795561615)
                      ·
                        rfl

theorem cell23_4577359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 5, 2].length) (baseStart_4577359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577359 prefixEnd_4577359 := by exact prefixLift 4577359
  have htrace : WordTrace (prefixWord ++ tailWord_4577359) baseStart_4577359 baseEnd_4577359 := by
    simpa [prefixWord, tailWord_4577359, baseEnd_4577359] using wordTrace_append hprefix tailTrace_4577359
  have hstable : (prefixWord ++ tailWord_4577359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577359).length < 2 ^ (prefixWord ++ tailWord_4577359).sum := by decide
  have hdescent : baseEnd_4577359 < baseStart_4577359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577369 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 2, 5]
def baseStart_4577369 : Nat := 118140960795 + 4577369 * 2 ^ 59
def prefixEnd_4577369 : Nat := 4983230072969 + 3 ^ 40 * 4577369 * 2
def baseEnd_4577369 : Nat := 783463476663402252145523

theorem tailTrace_4577369 : CollatzResearch.WordTrace tailWord_4577369 prefixEnd_4577369 783463476663402252145523 := by
  unfold tailWord_4577369
  simp only [CollatzResearch.WordTrace]
  refine ⟨166950362953981340231823161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111300241969320893487882107 166950362953981340231823161)
  ·
    refine ⟨125212772215486005173867371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166950362953981340231823161 125212772215486005173867371)
    ·
      refine ⟨187819158323229007760801057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125212772215486005173867371 187819158323229007760801057)
      ·
        refine ⟨140864368742421755820600793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187819158323229007760801057 140864368742421755820600793)
        ·
          refine ⟨105648276556816316865450595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140864368742421755820600793 105648276556816316865450595)
          ·
            refine ⟨158472414835224475298175893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105648276556816316865450595 158472414835224475298175893)
            ·
              refine ⟨7428394445401147279601995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 158472414835224475298175893 7428394445401147279601995)
              ·
                refine ⟨11142591668101720919402993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7428394445401147279601995 11142591668101720919402993)
                ·
                  refine ⟨8356943751076290689552245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11142591668101720919402993 8356943751076290689552245)
                  ·
                    refine ⟨783463476663402252145523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8356943751076290689552245 783463476663402252145523)
                    ·
                      rfl

theorem cell23_4577369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 5].length) (baseStart_4577369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577369 prefixEnd_4577369 := by exact prefixLift 4577369
  have htrace : WordTrace (prefixWord ++ tailWord_4577369) baseStart_4577369 baseEnd_4577369 := by
    simpa [prefixWord, tailWord_4577369, baseEnd_4577369] using wordTrace_append hprefix tailTrace_4577369
  have hstable : (prefixWord ++ tailWord_4577369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577369).length < 2 ^ (prefixWord ++ tailWord_4577369).sum := by decide
  have hdescent : baseEnd_4577369 < baseStart_4577369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577416 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 5, 4]
def baseStart_4577416 : Nat := 118140960795 + 4577416 * 2 ^ 59
def prefixEnd_4577416 : Nat := 4983230072969 + 3 ^ 40 * 4577416 * 2
def baseEnd_4577416 : Nat := 783471521193656024182951

theorem tailTrace_4577416 : CollatzResearch.WordTrace tailWord_4577416 prefixEnd_4577416 783471521193656024182951 := by
  unfold tailWord_4577416
  simp only [CollatzResearch.WordTrace]
  refine ⟨83476038592405533629392051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111301384789874044839189401 83476038592405533629392051)
  ·
    refine ⟨125214057888608300444088077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83476038592405533629392051 125214057888608300444088077)
    ·
      refine ⟨46955271708228112666533029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125214057888608300444088077 46955271708228112666533029)
      ·
        refine ⟨8804113445292771124974943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46955271708228112666533029 8804113445292771124974943)
        ·
          refine ⟨13206170167939156687462415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8804113445292771124974943 13206170167939156687462415)
          ·
            refine ⟨19809255251908735031193623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13206170167939156687462415 19809255251908735031193623)
            ·
              refine ⟨29713882877863102546790435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19809255251908735031193623 29713882877863102546790435)
              ·
                refine ⟨44570824316794653820185653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29713882877863102546790435 44570824316794653820185653)
                ·
                  refine ⟨4178514779699498795642405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44570824316794653820185653 4178514779699498795642405)
                  ·
                    refine ⟨783471521193656024182951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4178514779699498795642405 783471521193656024182951)
                    ·
                      rfl

theorem cell23_4577416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_4577416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577416 prefixEnd_4577416 := by exact prefixLift 4577416
  have htrace : WordTrace (prefixWord ++ tailWord_4577416) baseStart_4577416 baseEnd_4577416 := by
    simpa [prefixWord, tailWord_4577416, baseEnd_4577416] using wordTrace_append hprefix tailTrace_4577416
  have hstable : (prefixWord ++ tailWord_4577416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577416).length < 2 ^ (prefixWord ++ tailWord_4577416).sum := by decide
  have hdescent : baseEnd_4577416 < baseStart_4577416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577426 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_4577426 : Nat := 118140960795 + 4577426 * 2 ^ 59
def prefixEnd_4577426 : Nat := 4983230072969 + 3 ^ 40 * 4577426 * 2
def baseEnd_4577426 : Nat := 2350419698387513033423807

theorem tailTrace_4577426 : CollatzResearch.WordTrace tailWord_4577426 prefixEnd_4577426 2350419698387513033423807 := by
  unfold tailWord_4577426
  simp only [CollatzResearch.WordTrace]
  refine ⟨41738110478693709741662033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111301627943183225977765421 41738110478693709741662033)
  ·
    refine ⟨31303582859020282306246525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41738110478693709741662033 31303582859020282306246525)
    ·
      refine ⟨11738843572132605864842447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31303582859020282306246525 11738843572132605864842447)
      ·
        refine ⟨17608265358198908797263671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11738843572132605864842447 17608265358198908797263671)
        ·
          refine ⟨26412398037298363195895507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17608265358198908797263671 26412398037298363195895507)
          ·
            refine ⟨39618597055947544793843261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26412398037298363195895507 39618597055947544793843261)
            ·
              refine ⟨14856973895980329297691223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39618597055947544793843261 14856973895980329297691223)
              ·
                refine ⟨22285460843970493946536835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14856973895980329297691223 22285460843970493946536835)
                ·
                  refine ⟨33428191265955740919805253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22285460843970493946536835 33428191265955740919805253)
                  ·
                    refine ⟨6267785862366701422463485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33428191265955740919805253 6267785862366701422463485)
                    ·
                      refine ⟨2350419698387513033423807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6267785862366701422463485 2350419698387513033423807)
                      ·
                        rfl

theorem cell23_4577426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_4577426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577426 prefixEnd_4577426 := by exact prefixLift 4577426
  have htrace : WordTrace (prefixWord ++ tailWord_4577426) baseStart_4577426 baseEnd_4577426 := by
    simpa [prefixWord, tailWord_4577426, baseEnd_4577426] using wordTrace_append hprefix tailTrace_4577426
  have hstable : (prefixWord ++ tailWord_4577426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577426).length < 2 ^ (prefixWord ++ tailWord_4577426).sum := by decide
  have hdescent : baseEnd_4577426 < baseStart_4577426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577450 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 3, 4]
def baseStart_4577450 : Nat := 118140960795 + 4577450 * 2 ^ 59
def prefixEnd_4577450 : Nat := 4983230072969 + 3 ^ 40 * 4577450 * 2
def baseEnd_4577450 : Nat := 783477340641073646507899

theorem tailTrace_4577450 : CollatzResearch.WordTrace tailWord_4577450 prefixEnd_4577450 783477340641073646507899 := by
  unfold tailWord_4577450
  simp only [CollatzResearch.WordTrace]
  refine ⟨41738329316671972766380451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111302211511125260710347869 41738329316671972766380451)
  ·
    refine ⟨62607493975007959149570677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41738329316671972766380451 62607493975007959149570677)
    ·
      refine ⟨5869452560156996170272251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62607493975007959149570677 5869452560156996170272251)
      ·
        refine ⟨8804178840235494255408377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5869452560156996170272251 8804178840235494255408377)
        ·
          refine ⟨6603134130176620691556283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8804178840235494255408377 6603134130176620691556283)
          ·
            refine ⟨9904701195264931037334425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6603134130176620691556283 9904701195264931037334425)
            ·
              refine ⟨7428525896448698278000819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9904701195264931037334425 7428525896448698278000819)
              ·
                refine ⟨11142788844673047417001229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7428525896448698278000819 11142788844673047417001229)
                ·
                  refine ⟨4178545816752392781375461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11142788844673047417001229 4178545816752392781375461)
                  ·
                    refine ⟨783477340641073646507899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4178545816752392781375461 783477340641073646507899)
                    ·
                      rfl

theorem cell23_4577450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_4577450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577450 prefixEnd_4577450 := by exact prefixLift 4577450
  have htrace : WordTrace (prefixWord ++ tailWord_4577450) baseStart_4577450 baseEnd_4577450 := by
    simpa [prefixWord, tailWord_4577450, baseEnd_4577450] using wordTrace_append hprefix tailTrace_4577450
  have hstable : (prefixWord ++ tailWord_4577450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577450).length < 2 ^ (prefixWord ++ tailWord_4577450).sum := by decide
  have hdescent : baseEnd_4577450 < baseStart_4577450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577466 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2]
def baseStart_4577466 : Nat := 118140960795 + 4577466 * 2 ^ 59
def prefixEnd_4577466 : Nat := 4983230072969 + 3 ^ 40 * 4577466 * 2
def baseEnd_4577466 : Nat := 2350440237613692876923623

theorem tailTrace_4577466 : CollatzResearch.WordTrace tailWord_4577466 prefixEnd_4577466 2350440237613692876923623 := by
  unfold tailWord_4577466
  simp only [CollatzResearch.WordTrace]
  refine ⟨41738475208657481449526063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111302600556419950532069501 41738475208657481449526063)
  ·
    refine ⟨62607712812986222174289095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41738475208657481449526063 62607712812986222174289095)
    ·
      refine ⟨93911569219479333261433643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62607712812986222174289095 93911569219479333261433643)
      ·
        refine ⟨140867353829218999892150465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93911569219479333261433643 140867353829218999892150465)
        ·
          refine ⟨105650515371914249919112849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140867353829218999892150465 105650515371914249919112849)
          ·
            refine ⟨79237886528935687439334637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105650515371914249919112849 79237886528935687439334637)
            ·
              refine ⟨29714207448350882789750489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79237886528935687439334637 29714207448350882789750489)
              ·
                refine ⟨22285655586263162092312867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29714207448350882789750489 22285655586263162092312867)
                ·
                  refine ⟨33428483379394743138469301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22285655586263162092312867 33428483379394743138469301)
                  ·
                    refine ⟨3133920316818257169231497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33428483379394743138469301 3133920316818257169231497)
                    ·
                      refine ⟨2350440237613692876923623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3133920316818257169231497 2350440237613692876923623)
                      ·
                        rfl

theorem cell23_4577466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2].length) (baseStart_4577466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577466 prefixEnd_4577466 := by exact prefixLift 4577466
  have htrace : WordTrace (prefixWord ++ tailWord_4577466) baseStart_4577466 baseEnd_4577466 := by
    simpa [prefixWord, tailWord_4577466, baseEnd_4577466] using wordTrace_append hprefix tailTrace_4577466
  have hstable : (prefixWord ++ tailWord_4577466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577466).length < 2 ^ (prefixWord ++ tailWord_4577466).sum := by decide
  have hdescent : baseEnd_4577466 < baseStart_4577466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4577484 : List Nat := [2, 2, 1, 6, 2, 1, 1, 3, 1, 4]
def baseStart_4577484 : Nat := 118140960795 + 4577484 * 2 ^ 59
def prefixEnd_4577484 : Nat := 4983230072969 + 3 ^ 40 * 4577484 * 2
def baseEnd_4577484 : Nat := 783483160088491268832847

theorem tailTrace_4577484 : CollatzResearch.WordTrace tailWord_4577484 prefixEnd_4577484 783483160088491268832847 := by
  unfold tailWord_4577484
  simp only [CollatzResearch.WordTrace]
  refine ⟨83477278674282357436129753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111303038232376476581506337 83477278674282357436129753)
  ·
    refine ⟨62607959005711768077097315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83477278674282357436129753 62607959005711768077097315)
    ·
      refine ⟨93911938508567652115645973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62607959005711768077097315 93911938508567652115645973)
      ·
        refine ⟨4402122117589108692920905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93911938508567652115645973 4402122117589108692920905)
        ·
          refine ⟨3301591588191831519690679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4402122117589108692920905 3301591588191831519690679)
          ·
            refine ⟨4952387382287747279536019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3301591588191831519690679 4952387382287747279536019)
            ·
              refine ⟨7428581073431620919304029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4952387382287747279536019 7428581073431620919304029)
              ·
                refine ⟨2785717902536857844739011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7428581073431620919304029 2785717902536857844739011)
                ·
                  refine ⟨4178576853805286767108517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785717902536857844739011 4178576853805286767108517)
                  ·
                    refine ⟨783483160088491268832847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4178576853805286767108517 783483160088491268832847)
                    ·
                      rfl

theorem cell23_4577484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_4577484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4577484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4577484 prefixEnd_4577484 := by exact prefixLift 4577484
  have htrace : WordTrace (prefixWord ++ tailWord_4577484) baseStart_4577484 baseEnd_4577484 := by
    simpa [prefixWord, tailWord_4577484, baseEnd_4577484] using wordTrace_append hprefix tailTrace_4577484
  have hstable : (prefixWord ++ tailWord_4577484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4577484).length < 2 ^ (prefixWord ++ tailWord_4577484).sum := by decide
  have hdescent : baseEnd_4577484 < baseStart_4577484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4577484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
