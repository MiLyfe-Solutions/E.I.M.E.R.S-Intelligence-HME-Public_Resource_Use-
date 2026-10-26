import V185TrunkScan22Chunk469

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4189207 : List Nat := [1, 1, 3, 5, 1, 1, 2, 8]
def baseStart_4189207 : Nat := 118140960795 + 4189207 * 2 ^ 59
def prefixEnd_4189207 : Nat := 4983230072969 + 3 ^ 40 * 4189207 * 2
def baseEnd_4189207 : Nat := 159339018679977514225681

theorem tailTrace_4189207 : CollatzResearch.WordTrace tailWord_4189207 prefixEnd_4189207 159339018679977514225681 := by
  unfold tailWord_4189207
  simp only [CollatzResearch.WordTrace]
  refine ⟨152792931734225973440061875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101861954489483982293374583 152792931734225973440061875)
  ·
    refine ⟨229189397601338960160092813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152792931734225973440061875 229189397601338960160092813)
    ·
      refine ⟨85946024100502110060034805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229189397601338960160092813 85946024100502110060034805)
      ·
        refine ⟨8057439759422072818128263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85946024100502110060034805 8057439759422072818128263)
        ·
          refine ⟨12086159639133109227192395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057439759422072818128263 12086159639133109227192395)
          ·
            refine ⟨18129239458699663840788593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12086159639133109227192395 18129239458699663840788593)
            ·
              refine ⟨13596929594024747880591445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18129239458699663840788593 13596929594024747880591445)
              ·
                refine ⟨159339018679977514225681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13596929594024747880591445 159339018679977514225681)
                ·
                  rfl

theorem cell22_4189207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 8].length) (baseStart_4189207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189207 prefixEnd_4189207 := by exact prefixLift 4189207
  have htrace : WordTrace (prefixWord ++ tailWord_4189207) baseStart_4189207 baseEnd_4189207 := by
    simpa [prefixWord, tailWord_4189207, baseEnd_4189207] using wordTrace_append hprefix tailTrace_4189207
  have hstable : (prefixWord ++ tailWord_4189207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189207).length < 2 ^ (prefixWord ++ tailWord_4189207).sum := by decide
  have hdescent : baseEnd_4189207 < baseStart_4189207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189316 : List Nat := [2, 3, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_4189316 : Nat := 118140960795 + 4189316 * 2 ^ 59
def prefixEnd_4189316 : Nat := 4983230072969 + 3 ^ 40 * 4189316 * 2
def baseEnd_4189316 : Nat := 1434088481047357677055795

theorem tailTrace_4189316 : CollatzResearch.WordTrace tailWord_4189316 prefixEnd_4189316 1434088481047357677055795 := by
  unfold tailWord_4189316
  simp only [CollatzResearch.WordTrace]
  refine ⟨76398453645415542527889901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101864604860554056703853201 76398453645415542527889901)
  ·
    refine ⟨28649420117030828447958713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76398453645415542527889901 28649420117030828447958713)
    ·
      refine ⟨21487065087773121335969035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28649420117030828447958713 21487065087773121335969035)
      ·
        refine ⟨32230597631659682003953553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21487065087773121335969035 32230597631659682003953553)
        ·
          refine ⟨24172948223744761502965165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32230597631659682003953553 24172948223744761502965165)
          ·
            refine ⟨9064855583904285563611937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24172948223744761502965165 9064855583904285563611937)
            ·
              refine ⟨6798641687928214172708953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9064855583904285563611937 6798641687928214172708953)
              ·
                refine ⟨5098981265946160629531715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6798641687928214172708953 5098981265946160629531715)
                ·
                  refine ⟨7648471898919240944297573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098981265946160629531715 7648471898919240944297573)
                  ·
                    refine ⟨1434088481047357677055795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7648471898919240944297573 1434088481047357677055795)
                    ·
                      rfl

theorem cell22_4189316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_4189316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189316 prefixEnd_4189316 := by exact prefixLift 4189316
  have htrace : WordTrace (prefixWord ++ tailWord_4189316) baseStart_4189316 baseEnd_4189316 := by
    simpa [prefixWord, tailWord_4189316, baseEnd_4189316] using wordTrace_append hprefix tailTrace_4189316
  have hstable : (prefixWord ++ tailWord_4189316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189316).length < 2 ^ (prefixWord ++ tailWord_4189316).sum := by decide
  have hdescent : baseEnd_4189316 < baseStart_4189316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189344 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 2, 4]
def baseStart_4189344 : Nat := 118140960795 + 4189344 * 2 ^ 59
def prefixEnd_4189344 : Nat := 4983230072969 + 3 ^ 40 * 4189344 * 2
def baseEnd_4189344 : Nat := 1434098066019574937355709

theorem tailTrace_4189344 : CollatzResearch.WordTrace tailWord_4189344 prefixEnd_4189344 1434098066019574937355709 := by
  unfold tailWord_4189344
  simp only [CollatzResearch.WordTrace]
  refine ⟨76398964267364822918899543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101865285689819763891866057 76398964267364822918899543)
  ·
    refine ⟨114598446401047234378349315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76398964267364822918899543 114598446401047234378349315)
    ·
      refine ⟨171897669601570851567523973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114598446401047234378349315 171897669601570851567523973)
      ·
        refine ⟨32230813050294534668910745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171897669601570851567523973 32230813050294534668910745)
        ·
          refine ⟨24173109787720901001683059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32230813050294534668910745 24173109787720901001683059)
          ·
            refine ⟨36259664681581351502524589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24173109787720901001683059 36259664681581351502524589)
            ·
              refine ⟨13597374255593006813446721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36259664681581351502524589 13597374255593006813446721)
              ·
                refine ⟨10198030691694755110085041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13597374255593006813446721 10198030691694755110085041)
                ·
                  refine ⟨7648523018771066332563781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10198030691694755110085041 7648523018771066332563781)
                  ·
                    refine ⟨1434098066019574937355709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7648523018771066332563781 1434098066019574937355709)
                    ·
                      rfl

theorem cell22_4189344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_4189344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189344 prefixEnd_4189344 := by exact prefixLift 4189344
  have htrace : WordTrace (prefixWord ++ tailWord_4189344) baseStart_4189344 baseEnd_4189344 := by
    simpa [prefixWord, tailWord_4189344, baseEnd_4189344] using wordTrace_append hprefix tailTrace_4189344
  have hstable : (prefixWord ++ tailWord_4189344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189344).length < 2 ^ (prefixWord ++ tailWord_4189344).sum := by decide
  have hdescent : baseEnd_4189344 < baseStart_4189344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189348 : List Nat := [2, 3, 1, 2, 3, 2, 3, 2, 4]
def baseStart_4189348 : Nat := 118140960795 + 4189348 * 2 ^ 59
def prefixEnd_4189348 : Nat := 4983230072969 + 3 ^ 40 * 4189348 * 2
def baseEnd_4189348 : Nat := 478033145100440086751899

theorem tailTrace_4189348 : CollatzResearch.WordTrace tailWord_4189348 prefixEnd_4189348 478033145100440086751899 := by
  unfold tailWord_4189348
  simp only [CollatzResearch.WordTrace]
  refine ⟨76399037213357577260472349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101865382951143436347296465 76399037213357577260472349)
  ·
    refine ⟨28649638955009091472677131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76399037213357577260472349 28649638955009091472677131)
    ·
      refine ⟨42974458432513637209015697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28649638955009091472677131 42974458432513637209015697)
      ·
        refine ⟨32230843824385227906761773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42974458432513637209015697 32230843824385227906761773)
        ·
          refine ⟨12086566434144460465035665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32230843824385227906761773 12086566434144460465035665)
          ·
            refine ⟨9064924825608345348776749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12086566434144460465035665 9064924825608345348776749)
            ·
              refine ⟨3399346809603129505791281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9064924825608345348776749 3399346809603129505791281)
              ·
                refine ⟨2549510107202347129343461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3399346809603129505791281 2549510107202347129343461)
                ·
                  refine ⟨478033145100440086751899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2549510107202347129343461 478033145100440086751899)
                  ·
                    rfl

theorem cell22_4189348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_4189348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189348 prefixEnd_4189348 := by exact prefixLift 4189348
  have htrace : WordTrace (prefixWord ++ tailWord_4189348) baseStart_4189348 baseEnd_4189348 := by
    simpa [prefixWord, tailWord_4189348, baseEnd_4189348] using wordTrace_append hprefix tailTrace_4189348
  have hstable : (prefixWord ++ tailWord_4189348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189348).length < 2 ^ (prefixWord ++ tailWord_4189348).sum := by decide
  have hdescent : baseEnd_4189348 < baseStart_4189348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189387 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 7]
def baseStart_4189387 : Nat := 118140960795 + 4189387 * 2 ^ 59
def prefixEnd_4189387 : Nat := 4983230072969 + 3 ^ 40 * 4189387 * 2
def baseEnd_4189387 : Nat := 478037595266112386176859

theorem tailTrace_4189387 : CollatzResearch.WordTrace tailWord_4189387 prefixEnd_4189387 478037595266112386176859 := by
  unfold tailWord_4189387
  simp only [CollatzResearch.WordTrace]
  refine ⟨152799496873573864181614415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101866331249049242787742943 152799496873573864181614415)
  ·
    refine ⟨229199245310360796272421623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152799496873573864181614415 229199245310360796272421623)
    ·
      refine ⟨343798867965541194408632435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229199245310360796272421623 343798867965541194408632435)
      ·
        refine ⟨515698301948311791612948653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343798867965541194408632435 515698301948311791612948653)
        ·
          refine ⟨193386863230616921854855745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515698301948311791612948653 193386863230616921854855745)
          ·
            refine ⟨145040147422962691391141809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193386863230616921854855745 145040147422962691391141809)
            ·
              refine ⟨108780110567222018543356357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145040147422962691391141809 108780110567222018543356357)
              ·
                refine ⟨20396270731354128476879317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108780110567222018543356357 20396270731354128476879317)
                ·
                  refine ⟨478037595266112386176859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20396270731354128476879317 478037595266112386176859)
                  ·
                    rfl

theorem cell22_4189387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 7].length) (baseStart_4189387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189387 prefixEnd_4189387 := by exact prefixLift 4189387
  have htrace : WordTrace (prefixWord ++ tailWord_4189387) baseStart_4189387 baseEnd_4189387 := by
    simpa [prefixWord, tailWord_4189387, baseEnd_4189387] using wordTrace_append hprefix tailTrace_4189387
  have hstable : (prefixWord ++ tailWord_4189387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189387).length < 2 ^ (prefixWord ++ tailWord_4189387).sum := by decide
  have hdescent : baseEnd_4189387 < baseStart_4189387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189408 : List Nat := [2, 1, 1, 3, 1, 5, 1, 4, 1, 3]
def baseStart_4189408 : Nat := 118140960795 + 4189408 * 2 ^ 59
def prefixEnd_4189408 : Nat := 4983230072969 + 3 ^ 40 * 4189408 * 2
def baseEnd_4189408 : Nat := 1434119974527500103755513

theorem tailTrace_4189408 : CollatzResearch.WordTrace tailWord_4189408 prefixEnd_4189408 1434119974527500103755513 := by
  unfold tailWord_4189408
  simp only [CollatzResearch.WordTrace]
  refine ⟨76400131403248892384064439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101866841870998523178752585 76400131403248892384064439)
  ·
    refine ⟨114600197104873338576096659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76400131403248892384064439 114600197104873338576096659)
    ·
      refine ⟨171900295657310007864144989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114600197104873338576096659 171900295657310007864144989)
      ·
        refine ⟨64462610871491252949054371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171900295657310007864144989 64462610871491252949054371)
        ·
          refine ⟨96693916307236879423581557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64462610871491252949054371 96693916307236879423581557)
          ·
            refine ⟨9065054653803457445960771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96693916307236879423581557 9065054653803457445960771)
            ·
              refine ⟨13597581980705186168941157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9065054653803457445960771 13597581980705186168941157)
              ·
                refine ⟨2549546621382222406676467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13597581980705186168941157 2549546621382222406676467)
                ·
                  refine ⟨3824319932073333610014701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549546621382222406676467 3824319932073333610014701)
                  ·
                    refine ⟨1434119974527500103755513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3824319932073333610014701 1434119974527500103755513)
                    ·
                      rfl

theorem cell22_4189408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4, 1, 3].length) (baseStart_4189408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189408 prefixEnd_4189408 := by exact prefixLift 4189408
  have htrace : WordTrace (prefixWord ++ tailWord_4189408) baseStart_4189408 baseEnd_4189408 := by
    simpa [prefixWord, tailWord_4189408, baseEnd_4189408] using wordTrace_append hprefix tailTrace_4189408
  have hstable : (prefixWord ++ tailWord_4189408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189408).length < 2 ^ (prefixWord ++ tailWord_4189408).sum := by decide
  have hdescent : baseEnd_4189408 < baseStart_4189408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189417 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 1, 10]
def baseStart_4189417 : Nat := 118140960795 + 4189417 * 2 ^ 59
def prefixEnd_4189417 : Nat := 4983230072969 + 3 ^ 40 * 4189417 * 2
def baseEnd_4189417 : Nat := 1434123055411427080280485

theorem tailTrace_4189417 : CollatzResearch.WordTrace tailWord_4189417 prefixEnd_4189417 1434123055411427080280485 := by
  unfold tailWord_4189417
  simp only [CollatzResearch.WordTrace]
  refine ⟨152800591063465179305206505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101867060708976786203471003 152800591063465179305206505)
  ·
    refine ⟨114600443297598884478904879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152800591063465179305206505 114600443297598884478904879)
    ·
      refine ⟨171900664946398326718357319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114600443297598884478904879 171900664946398326718357319)
      ·
        refine ⟨257850997419597490077535979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171900664946398326718357319 257850997419597490077535979)
        ·
          refine ⟨386776496129396235116303969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257850997419597490077535979 386776496129396235116303969)
          ·
            refine ⟨290082372097047176337227977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386776496129396235116303969 290082372097047176337227977)
            ·
              refine ⟨217561779072785382252920983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290082372097047176337227977 217561779072785382252920983)
              ·
                refine ⟨326342668609178073379381475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217561779072785382252920983 326342668609178073379381475)
                ·
                  refine ⟨489514002913767110069072213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326342668609178073379381475 489514002913767110069072213)
                  ·
                    refine ⟨1434123055411427080280485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 489514002913767110069072213 1434123055411427080280485)
                    ·
                      rfl

theorem cell22_4189417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_4189417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189417 prefixEnd_4189417 := by exact prefixLift 4189417
  have htrace : WordTrace (prefixWord ++ tailWord_4189417) baseStart_4189417 baseEnd_4189417 := by
    simpa [prefixWord, tailWord_4189417, baseEnd_4189417] using wordTrace_append hprefix tailTrace_4189417
  have hstable : (prefixWord ++ tailWord_4189417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189417).length < 2 ^ (prefixWord ++ tailWord_4189417).sum := by decide
  have hdescent : baseEnd_4189417 < baseStart_4189417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189419 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 2, 5]
def baseStart_4189419 : Nat := 118140960795 + 4189419 * 2 ^ 59
def prefixEnd_4189419 : Nat := 4983230072969 + 3 ^ 40 * 4189419 * 2
def baseEnd_4189419 : Nat := 1434123740052299741730479

theorem tailTrace_4189419 : CollatzResearch.WordTrace tailWord_4189419 prefixEnd_4189419 1434123740052299741730479 := by
  unfold tailWord_4189419
  simp only [CollatzResearch.WordTrace]
  refine ⟨152800664009457933646779311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101867109339638622431186207 152800664009457933646779311)
  ·
    refine ⟨229200996014186900470168967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152800664009457933646779311 229200996014186900470168967)
    ·
      refine ⟨343801494021280350705253451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229200996014186900470168967 343801494021280350705253451)
      ·
        refine ⟨515702241031920526057880177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343801494021280350705253451 515702241031920526057880177)
        ·
          refine ⟨386776680773940394543410133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515702241031920526057880177 386776680773940394543410133)
          ·
            refine ⟨9065078455639227997111175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 386776680773940394543410133 9065078455639227997111175)
            ·
              refine ⟨13597617683458841995666763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9065078455639227997111175 13597617683458841995666763)
              ·
                refine ⟨20396426525188262993500145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13597617683458841995666763 20396426525188262993500145)
                ·
                  refine ⟨15297319893891197245125109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20396426525188262993500145 15297319893891197245125109)
                  ·
                    refine ⟨1434123740052299741730479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15297319893891197245125109 1434123740052299741730479)
                    ·
                      rfl

theorem cell22_4189419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 5].length) (baseStart_4189419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189419 prefixEnd_4189419 := by exact prefixLift 4189419
  have htrace : WordTrace (prefixWord ++ tailWord_4189419) baseStart_4189419 baseEnd_4189419 := by
    simpa [prefixWord, tailWord_4189419, baseEnd_4189419] using wordTrace_append hprefix tailTrace_4189419
  have hstable : (prefixWord ++ tailWord_4189419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189419).length < 2 ^ (prefixWord ++ tailWord_4189419).sum := by decide
  have hdescent : baseEnd_4189419 < baseStart_4189419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189421 : List Nat := [1, 5, 1, 2, 2, 1, 2, 3, 5]
def baseStart_4189421 : Nat := 118140960795 + 4189421 * 2 ^ 59
def prefixEnd_4189421 : Nat := 4983230072969 + 3 ^ 40 * 4189421 * 2
def baseEnd_4189421 : Nat := 478041474897724134393491

theorem tailTrace_4189421 : CollatzResearch.WordTrace tailWord_4189421 prefixEnd_4189421 478041474897724134393491 := by
  unfold tailWord_4189421
  simp only [CollatzResearch.WordTrace]
  refine ⟨152800736955450687988352117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101867157970300458658901411 152800736955450687988352117)
  ·
    refine ⟨14325069089573501998908011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152800736955450687988352117 14325069089573501998908011)
    ·
      refine ⟨21487603634360252998362017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14325069089573501998908011 21487603634360252998362017)
      ·
        refine ⟨16115702725770189748771513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21487603634360252998362017 16115702725770189748771513)
        ·
          refine ⟨12086777044327642311578635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16115702725770189748771513 12086777044327642311578635)
          ·
            refine ⟨18130165566491463467367953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12086777044327642311578635 18130165566491463467367953)
            ·
              refine ⟨13597624174868597600525965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18130165566491463467367953 13597624174868597600525965)
              ·
                refine ⟨5099109065575724100197237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13597624174868597600525965 5099109065575724100197237)
                ·
                  refine ⟨478041474897724134393491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5099109065575724100197237 478041474897724134393491)
                  ·
                    rfl

theorem cell22_4189421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_4189421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189421 prefixEnd_4189421 := by exact prefixLift 4189421
  have htrace : WordTrace (prefixWord ++ tailWord_4189421) baseStart_4189421 baseEnd_4189421 := by
    simpa [prefixWord, tailWord_4189421, baseEnd_4189421] using wordTrace_append hprefix tailTrace_4189421
  have hstable : (prefixWord ++ tailWord_4189421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189421).length < 2 ^ (prefixWord ++ tailWord_4189421).sum := by decide
  have hdescent : baseEnd_4189421 < baseStart_4189421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189434 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_4189434 : Nat := 118140960795 + 4189434 * 2 ^ 59
def prefixEnd_4189434 : Nat := 4983230072969 + 3 ^ 40 * 4189434 * 2
def baseEnd_4189434 : Nat := 1434128874858844702605433

theorem tailTrace_4189434 : CollatzResearch.WordTrace tailWord_4189434 prefixEnd_4189434 1434128874858844702605433 := by
  unfold tailWord_4189434
  simp only [CollatzResearch.WordTrace]
  refine ⟨38200302776100897802143839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101867474069602394139050237 38200302776100897802143839)
  ·
    refine ⟨57300454164151346703215759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38200302776100897802143839 57300454164151346703215759)
    ·
      refine ⟨85950681246227020054823639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57300454164151346703215759 85950681246227020054823639)
      ·
        refine ⟨128926021869340530082235459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85950681246227020054823639 128926021869340530082235459)
        ·
          refine ⟨193389032804010795123353189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128926021869340530082235459 193389032804010795123353189)
          ·
            refine ⟨36260443650752024085628723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193389032804010795123353189 36260443650752024085628723)
            ·
              refine ⟨54390665476128036128443085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36260443650752024085628723 54390665476128036128443085)
              ·
                refine ⟨20396499553548013548166157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54390665476128036128443085 20396499553548013548166157)
                ·
                  refine ⟨7648687332580505080562309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20396499553548013548166157 7648687332580505080562309)
                  ·
                    refine ⟨1434128874858844702605433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7648687332580505080562309 1434128874858844702605433)
                    ·
                      rfl

theorem cell22_4189434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_4189434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189434 prefixEnd_4189434 := by exact prefixLift 4189434
  have htrace : WordTrace (prefixWord ++ tailWord_4189434) baseStart_4189434 baseEnd_4189434 := by
    simpa [prefixWord, tailWord_4189434, baseEnd_4189434] using wordTrace_append hprefix tailTrace_4189434
  have hstable : (prefixWord ++ tailWord_4189434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189434).length < 2 ^ (prefixWord ++ tailWord_4189434).sum := by decide
  have hdescent : baseEnd_4189434 < baseStart_4189434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189442 : List Nat := [3, 4, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_4189442 : Nat := 118140960795 + 4189442 * 2 ^ 59
def prefixEnd_4189442 : Nat := 4983230072969 + 3 ^ 40 * 4189442 * 2
def baseEnd_4189442 : Nat := 1434131613422335348405409

theorem tailTrace_4189442 : CollatzResearch.WordTrace tailWord_4189442 prefixEnd_4189442 1434131613422335348405409 := by
  unfold tailWord_4189442
  simp only [CollatzResearch.WordTrace]
  refine ⟨38200375722093652143716645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101867668592249739049911053 38200375722093652143716645)
  ·
    refine ⟨7162570447892559776946871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38200375722093652143716645 7162570447892559776946871)
    ·
      refine ⟨10743855671838839665420307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7162570447892559776946871 10743855671838839665420307)
      ·
        refine ⟨16115783507758259498130461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10743855671838839665420307 16115783507758259498130461)
        ·
          refine ⟨6043418815409347311798923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16115783507758259498130461 6043418815409347311798923)
          ·
            refine ⟨9065128223114020967698385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6043418815409347311798923 9065128223114020967698385)
            ·
              refine ⟨6798846167335515725773789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9065128223114020967698385 6798846167335515725773789)
              ·
                refine ⟨2549567312750818397165171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6798846167335515725773789 2549567312750818397165171)
                ·
                  refine ⟨3824350969126227595747757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549567312750818397165171 3824350969126227595747757)
                  ·
                    refine ⟨1434131613422335348405409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3824350969126227595747757 1434131613422335348405409)
                    ·
                      rfl

theorem cell22_4189442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_4189442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189442 prefixEnd_4189442 := by exact prefixLift 4189442
  have htrace : WordTrace (prefixWord ++ tailWord_4189442) baseStart_4189442 baseEnd_4189442 := by
    simpa [prefixWord, tailWord_4189442, baseEnd_4189442] using wordTrace_append hprefix tailTrace_4189442
  have hstable : (prefixWord ++ tailWord_4189442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189442).length < 2 ^ (prefixWord ++ tailWord_4189442).sum := by decide
  have hdescent : baseEnd_4189442 < baseStart_4189442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189451 : List Nat := [1, 1, 1, 1, 5, 4, 1, 3, 1, 4]
def baseStart_4189451 : Nat := 118140960795 + 4189451 * 2 ^ 59
def prefixEnd_4189451 : Nat := 4983230072969 + 3 ^ 40 * 4189451 * 2
def baseEnd_4189451 : Nat := 1434134694306262324930381

theorem tailTrace_4189451 : CollatzResearch.WordTrace tailWord_4189451 prefixEnd_4189451 1434134694306262324930381 := by
  unfold tailWord_4189451
  simp only [CollatzResearch.WordTrace]
  refine ⟨152801831145342003111944207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101867887430228002074629471 152801831145342003111944207)
  ·
    refine ⟨229202746718013004667916311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152801831145342003111944207 229202746718013004667916311)
    ·
      refine ⟨343804120077019507001874467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229202746718013004667916311 343804120077019507001874467)
      ·
        refine ⟨515706180115529260502811701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343804120077019507001874467 515706180115529260502811701)
        ·
          refine ⟨48347454385830868172138597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 515706180115529260502811701 48347454385830868172138597)
          ·
            refine ⟨9065147697343287782275987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48347454385830868172138597 9065147697343287782275987)
            ·
              refine ⟨13597721546014931673413981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9065147697343287782275987 13597721546014931673413981)
              ·
                refine ⟨5099145579755599377530243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13597721546014931673413981 5099145579755599377530243)
                ·
                  refine ⟨7648718369633399066295365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5099145579755599377530243 7648718369633399066295365)
                  ·
                    refine ⟨1434134694306262324930381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7648718369633399066295365 1434134694306262324930381)
                    ·
                      rfl

theorem cell22_4189451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 4].length) (baseStart_4189451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189451 prefixEnd_4189451 := by exact prefixLift 4189451
  have htrace : WordTrace (prefixWord ++ tailWord_4189451) baseStart_4189451 baseEnd_4189451 := by
    simpa [prefixWord, tailWord_4189451, baseEnd_4189451] using wordTrace_append hprefix tailTrace_4189451
  have hstable : (prefixWord ++ tailWord_4189451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189451).length < 2 ^ (prefixWord ++ tailWord_4189451).sum := by decide
  have hdescent : baseEnd_4189451 < baseStart_4189451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189466 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 6]
def baseStart_4189466 : Nat := 118140960795 + 4189466 * 2 ^ 59
def prefixEnd_4189466 : Nat := 4983230072969 + 3 ^ 40 * 4189466 * 2
def baseEnd_4189466 : Nat := 478046609704269095268445

theorem tailTrace_4189466 : CollatzResearch.WordTrace tailWord_4189466 prefixEnd_4189466 478046609704269095268445 := by
  unfold tailWord_4189466
  simp only [CollatzResearch.WordTrace]
  refine ⟨38200594560071915168435063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101868252160191773782493501 38200594560071915168435063)
  ·
    refine ⟨57300891840107872752652595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38200594560071915168435063 57300891840107872752652595)
    ·
      refine ⟨85951337760161809128978893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57300891840107872752652595 85951337760161809128978893)
      ·
        refine ⟨32231751660060678423367085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85951337760161809128978893 32231751660060678423367085)
        ·
          refine ⟨12086906872522754408762657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32231751660060678423367085 12086906872522754408762657)
          ·
            refine ⟨9065180154392065806571993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12086906872522754408762657 9065180154392065806571993)
            ·
              refine ⟨6798885115794049354928995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9065180154392065806571993 6798885115794049354928995)
              ·
                refine ⟨10198327673691074032393493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6798885115794049354928995 10198327673691074032393493)
                ·
                  refine ⟨478046609704269095268445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10198327673691074032393493 478046609704269095268445)
                  ·
                    rfl

theorem cell22_4189466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_4189466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189466 prefixEnd_4189466 := by exact prefixLift 4189466
  have htrace : WordTrace (prefixWord ++ tailWord_4189466) baseStart_4189466 baseEnd_4189466 := by
    simpa [prefixWord, tailWord_4189466, baseEnd_4189466] using wordTrace_append hprefix tailTrace_4189466
  have hstable : (prefixWord ++ tailWord_4189466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189466).length < 2 ^ (prefixWord ++ tailWord_4189466).sum := by decide
  have hdescent : baseEnd_4189466 < baseStart_4189466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189485 : List Nat := [1, 5, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_4189485 : Nat := 118140960795 + 4189485 * 2 ^ 59
def prefixEnd_4189485 : Nat := 4983230072969 + 3 ^ 40 * 4189485 * 2
def baseEnd_4189485 : Nat := 1434146333201097569580277

theorem tailTrace_4189485 : CollatzResearch.WordTrace tailWord_4189485 prefixEnd_4189485 1434146333201097569580277 := by
  unfold tailWord_4189485
  simp only [CollatzResearch.WordTrace]
  refine ⟨152803071227218826918681909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101868714151479217945787939 152803071227218826918681909)
  ·
    refine ⟨14325287927551765023626429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152803071227218826918681909 14325287927551765023626429)
    ·
      refine ⟨5371982972831911883859911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14325287927551765023626429 5371982972831911883859911)
      ·
        refine ⟨8057974459247867825789867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5371982972831911883859911 8057974459247867825789867)
        ·
          refine ⟨12086961688871801738684801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057974459247867825789867 12086961688871801738684801)
          ·
            refine ⟨9065221266653851304013601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12086961688871801738684801 9065221266653851304013601)
            ·
              refine ⟨6798915949990388478010201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9065221266653851304013601 6798915949990388478010201)
              ·
                refine ⟨5099186962492791358507651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6798915949990388478010201 5099186962492791358507651)
                ·
                  refine ⟨7648780443739187037761477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5099186962492791358507651 7648780443739187037761477)
                  ·
                    refine ⟨1434146333201097569580277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7648780443739187037761477 1434146333201097569580277)
                    ·
                      rfl

theorem cell22_4189485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_4189485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189485 prefixEnd_4189485 := by exact prefixLift 4189485
  have htrace : WordTrace (prefixWord ++ tailWord_4189485) baseStart_4189485 baseEnd_4189485 := by
    simpa [prefixWord, tailWord_4189485, baseEnd_4189485] using wordTrace_append hprefix tailTrace_4189485
  have hstable : (prefixWord ++ tailWord_4189485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189485).length < 2 ^ (prefixWord ++ tailWord_4189485).sum := by decide
  have hdescent : baseEnd_4189485 < baseStart_4189485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189517 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 6]
def baseStart_4189517 : Nat := 118140960795 + 4189517 * 2 ^ 59
def prefixEnd_4189517 : Nat := 4983230072969 + 3 ^ 40 * 4189517 * 2
def baseEnd_4189517 : Nat := 478052429151686717593393

theorem tailTrace_4189517 : CollatzResearch.WordTrace tailWord_4189517 prefixEnd_4189517 478052429151686717593393 := by
  unfold tailWord_4189517
  simp only [CollatzResearch.WordTrace]
  refine ⟨152804238363102896383846805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101869492242068597589231203 152804238363102896383846805)
  ·
    refine ⟨7162698673270448267992819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152804238363102896383846805 7162698673270448267992819)
    ·
      refine ⟨10744048009905672401989229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7162698673270448267992819 10744048009905672401989229)
      ·
        refine ⟨4029018003714627150745961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10744048009905672401989229 4029018003714627150745961)
        ·
          refine ⟨3021763502785970363059471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4029018003714627150745961 3021763502785970363059471)
          ·
            refine ⟨4532645254178955544589207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021763502785970363059471 4532645254178955544589207)
            ·
              refine ⟨6798967881268433316883811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4532645254178955544589207 6798967881268433316883811)
              ·
                refine ⟨10198451821902649975325717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6798967881268433316883811 10198451821902649975325717)
                ·
                  refine ⟨478052429151686717593393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10198451821902649975325717 478052429151686717593393)
                  ·
                    rfl

theorem cell22_4189517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_4189517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189517 prefixEnd_4189517 := by exact prefixLift 4189517
  have htrace : WordTrace (prefixWord ++ tailWord_4189517) baseStart_4189517 baseEnd_4189517 := by
    simpa [prefixWord, tailWord_4189517, baseEnd_4189517] using wordTrace_append hprefix tailTrace_4189517
  have hstable : (prefixWord ++ tailWord_4189517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189517).length < 2 ^ (prefixWord ++ tailWord_4189517).sum := by decide
  have hdescent : baseEnd_4189517 < baseStart_4189517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189588 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_4189588 : Nat := 118140960795 + 4189588 * 2 ^ 59
def prefixEnd_4189588 : Nat := 4983230072969 + 3 ^ 40 * 4189588 * 2
def baseEnd_4189588 : Nat := 1434181592206039634254961

theorem tailTrace_4189588 : CollatzResearch.WordTrace tailWord_4189588 prefixEnd_4189588 1434181592206039634254961 := by
  unfold tailWord_4189588
  simp only [CollatzResearch.WordTrace]
  refine ⟨76403413972922837754840709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101871218630563783673120945 76403413972922837754840709)
  ·
    refine ⟨14325640119923032079032633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76403413972922837754840709 14325640119923032079032633)
    ·
      refine ⟨10744230089942274059274475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14325640119923032079032633 10744230089942274059274475)
      ·
        refine ⟨16116345134913411088911713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10744230089942274059274475 16116345134913411088911713)
        ·
          refine ⟨12087258851185058316683785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16116345134913411088911713 12087258851185058316683785)
          ·
            refine ⟨9065444138388793737512839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12087258851185058316683785 9065444138388793737512839)
            ·
              refine ⟨13598166207583190606269259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9065444138388793737512839 13598166207583190606269259)
              ·
                refine ⟨20397249311374785909403889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13598166207583190606269259 20397249311374785909403889)
                ·
                  refine ⟨15297936983531089432052917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20397249311374785909403889 15297936983531089432052917)
                  ·
                    refine ⟨1434181592206039634254961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15297936983531089432052917 1434181592206039634254961)
                    ·
                      rfl

theorem cell22_4189588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_4189588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189588 prefixEnd_4189588 := by exact prefixLift 4189588
  have htrace : WordTrace (prefixWord ++ tailWord_4189588) baseStart_4189588 baseEnd_4189588 := by
    simpa [prefixWord, tailWord_4189588, baseEnd_4189588] using wordTrace_append hprefix tailTrace_4189588
  have hstable : (prefixWord ++ tailWord_4189588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189588).length < 2 ^ (prefixWord ++ tailWord_4189588).sum := by decide
  have hdescent : baseEnd_4189588 < baseStart_4189588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189631 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 2, 4]
def baseStart_4189631 : Nat := 118140960795 + 4189631 * 2 ^ 59
def prefixEnd_4189631 : Nat := 4983230072969 + 3 ^ 40 * 4189631 * 2
def baseEnd_4189631 : Nat := 1434196311984801855429829

theorem tailTrace_4189631 : CollatzResearch.WordTrace tailWord_4189631 prefixEnd_4189631 1434196311984801855429829 := by
  unfold tailWord_4189631
  simp only [CollatzResearch.WordTrace]
  refine ⟨152808396284689893853496747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101872264189793262568997831 152808396284689893853496747)
  ·
    refine ⟨229212594427034840780245121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152808396284689893853496747 229212594427034840780245121)
    ·
      refine ⟨171909445820276130585183841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229212594427034840780245121 171909445820276130585183841)
      ·
        refine ⟨128932084365207097938887881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171909445820276130585183841 128932084365207097938887881)
        ·
          refine ⟨96699063273905323454165911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128932084365207097938887881 96699063273905323454165911)
          ·
            refine ⟨145048594910857985181248867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96699063273905323454165911 145048594910857985181248867)
            ·
              refine ⟨217572892366286977771873301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145048594910857985181248867 217572892366286977771873301)
              ·
                refine ⟨10198729329669702083056561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 217572892366286977771873301 10198729329669702083056561)
                ·
                  refine ⟨7649046997252276562292421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10198729329669702083056561 7649046997252276562292421)
                  ·
                    refine ⟨1434196311984801855429829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7649046997252276562292421 1434196311984801855429829)
                    ·
                      rfl

theorem cell22_4189631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_4189631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189631 prefixEnd_4189631 := by exact prefixLift 4189631
  have htrace : WordTrace (prefixWord ++ tailWord_4189631) baseStart_4189631 baseEnd_4189631 := by
    simpa [prefixWord, tailWord_4189631, baseEnd_4189631] using wordTrace_append hprefix tailTrace_4189631
  have hstable : (prefixWord ++ tailWord_4189631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189631).length < 2 ^ (prefixWord ++ tailWord_4189631).sum := by decide
  have hdescent : baseEnd_4189631 < baseStart_4189631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189768 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 8, 3]
def baseStart_4189768 : Nat := 118140960795 + 4189768 * 2 ^ 59
def prefixEnd_4189768 : Nat := 4983230072969 + 3 ^ 40 * 4189768 * 2
def baseEnd_4189768 : Nat := 1434243209884579164754409

theorem tailTrace_4189768 : CollatzResearch.WordTrace tailWord_4189768 prefixEnd_4189768 1434243209884579164754409 := by
  unfold tailWord_4189768
  simp only [CollatzResearch.WordTrace]
  refine ⟨76406696542596783125616979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101875595390129044167489305 76406696542596783125616979)
  ·
    refine ⟨114610044813895174688425469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76406696542596783125616979 114610044813895174688425469)
    ·
      refine ⟨42978766805210690508159551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114610044813895174688425469 42978766805210690508159551)
      ·
        refine ⟨64468150207816035762239327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42978766805210690508159551 64468150207816035762239327)
        ·
          refine ⟨96702225311724053643358991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64468150207816035762239327 96702225311724053643358991)
          ·
            refine ⟨145053337967586080465038487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96702225311724053643358991 145053337967586080465038487)
            ·
              refine ⟨217580006951379120697557731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145053337967586080465038487 217580006951379120697557731)
              ·
                refine ⟨326370010427068681046336597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217580006951379120697557731 326370010427068681046336597)
                ·
                  refine ⟨3824648559692211106011757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 326370010427068681046336597 3824648559692211106011757)
                  ·
                    refine ⟨1434243209884579164754409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3824648559692211106011757 1434243209884579164754409)
                    ·
                      rfl

theorem cell22_4189768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_4189768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189768 prefixEnd_4189768 := by exact prefixLift 4189768
  have htrace : WordTrace (prefixWord ++ tailWord_4189768) baseStart_4189768 baseEnd_4189768 := by
    simpa [prefixWord, tailWord_4189768, baseEnd_4189768] using wordTrace_append hprefix tailTrace_4189768
  have hstable : (prefixWord ++ tailWord_4189768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189768).length < 2 ^ (prefixWord ++ tailWord_4189768).sum := by decide
  have hdescent : baseEnd_4189768 < baseStart_4189768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189783 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 1, 6]
def baseStart_4189783 : Nat := 118140960795 + 4189783 * 2 ^ 59
def prefixEnd_4189783 : Nat := 4983230072969 + 3 ^ 40 * 4189783 * 2
def baseEnd_4189783 : Nat := 1434248344691124125629363

theorem tailTrace_4189783 : CollatzResearch.WordTrace tailWord_4189783 prefixEnd_4189783 1434248344691124125629363 := by
  unfold tailWord_4189783
  simp only [CollatzResearch.WordTrace]
  refine ⟨152813940180139223813030003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101875960120092815875353335 152813940180139223813030003)
  ·
    refine ⟨229220910270208835719545005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152813940180139223813030003 229220910270208835719545005)
    ·
      refine ⟨85957841351328313394829377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229220910270208835719545005 85957841351328313394829377)
      ·
        refine ⟨64468381013496235046122033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85957841351328313394829377 64468381013496235046122033)
        ·
          refine ⟨48351285760122176284591525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64468381013496235046122033 48351285760122176284591525)
          ·
            refine ⟨9065866080022908053360911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48351285760122176284591525 9065866080022908053360911)
            ·
              refine ⟨13598799120034362080041367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9065866080022908053360911 13598799120034362080041367)
              ·
                refine ⟨20398198680051543120062051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13598799120034362080041367 20398198680051543120062051)
                ·
                  refine ⟨30597298020077314680093077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20398198680051543120062051 30597298020077314680093077)
                  ·
                    refine ⟨1434248344691124125629363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30597298020077314680093077 1434248344691124125629363)
                    ·
                      rfl

theorem cell22_4189783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_4189783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189783 prefixEnd_4189783 := by exact prefixLift 4189783
  have htrace : WordTrace (prefixWord ++ tailWord_4189783) baseStart_4189783 baseEnd_4189783 := by
    simpa [prefixWord, tailWord_4189783, baseEnd_4189783] using wordTrace_append hprefix tailTrace_4189783
  have hstable : (prefixWord ++ tailWord_4189783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189783).length < 2 ^ (prefixWord ++ tailWord_4189783).sum := by decide
  have hdescent : baseEnd_4189783 < baseStart_4189783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189789 : List Nat := [1, 4, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_4189789 : Nat := 118140960795 + 4189789 * 2 ^ 59
def prefixEnd_4189789 : Nat := 4983230072969 + 3 ^ 40 * 4189789 * 2
def baseEnd_4189789 : Nat := 1434250398613742109979345

theorem tailTrace_4189789 : CollatzResearch.WordTrace tailWord_4189789 prefixEnd_4189789 1434250398613742109979345 := by
  unfold tailWord_4189789
  simp only [CollatzResearch.WordTrace]
  refine ⟨152814159018117486837748421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101876106012078324558498947 152814159018117486837748421)
  ·
    refine ⟨28652654815897028782077829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152814159018117486837748421 28652654815897028782077829)
    ·
      refine ⟨5372372777980692896639593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28652654815897028782077829 5372372777980692896639593)
      ·
        refine ⟨4029279583485519672479695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5372372777980692896639593 4029279583485519672479695)
        ·
          refine ⟨6043919375228279508719543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4029279583485519672479695 6043919375228279508719543)
          ·
            refine ⟨9065879062842419263079315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6043919375228279508719543 9065879062842419263079315)
            ·
              refine ⟨13598818594263628894618973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9065879062842419263079315 13598818594263628894618973)
              ·
                refine ⟨5099556972848860835482115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13598818594263628894618973 5099556972848860835482115)
                ·
                  refine ⟨7649335459273291253223173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5099556972848860835482115 7649335459273291253223173)
                  ·
                    refine ⟨1434250398613742109979345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7649335459273291253223173 1434250398613742109979345)
                    ·
                      rfl

theorem cell22_4189789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_4189789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189789 prefixEnd_4189789 := by exact prefixLift 4189789
  have htrace : WordTrace (prefixWord ++ tailWord_4189789) baseStart_4189789 baseEnd_4189789 := by
    simpa [prefixWord, tailWord_4189789, baseEnd_4189789] using wordTrace_append hprefix tailTrace_4189789
  have hstable : (prefixWord ++ tailWord_4189789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189789).length < 2 ^ (prefixWord ++ tailWord_4189789).sum := by decide
  have hdescent : baseEnd_4189789 < baseStart_4189789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189802 : List Nat := [3, 1, 3, 2, 1, 2, 3, 2, 2, 3]
def baseStart_4189802 : Nat := 118140960795 + 4189802 * 2 ^ 59
def prefixEnd_4189802 : Nat := 4983230072969 + 3 ^ 40 * 4189802 * 2
def baseEnd_4189802 : Nat := 1434254848779414409404305

theorem tailTrace_4189802 : CollatzResearch.WordTrace tailWord_4189802 prefixEnd_4189802 1434254848779414409404305 := by
  unfold tailWord_4189802
  simp only [CollatzResearch.WordTrace]
  refine ⟨38203658291767597514492915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101876422111380260038647773 38203658291767597514492915)
  ·
    refine ⟨57305487437651396271739373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38203658291767597514492915 57305487437651396271739373)
    ·
      refine ⟨21489557789119273601902265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57305487437651396271739373 21489557789119273601902265)
      ·
        refine ⟨16117168341839455201426699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21489557789119273601902265 16117168341839455201426699)
        ·
          refine ⟨24175752512759182802140049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16117168341839455201426699 24175752512759182802140049)
          ·
            refine ⟨18131814384569387101605037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24175752512759182802140049 18131814384569387101605037)
            ·
              refine ⟨6799430394213520163101889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18131814384569387101605037 6799430394213520163101889)
              ·
                refine ⟨5099572795660140122326417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799430394213520163101889 5099572795660140122326417)
                ·
                  refine ⟨3824679596745105091744813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5099572795660140122326417 3824679596745105091744813)
                  ·
                    refine ⟨1434254848779414409404305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3824679596745105091744813 1434254848779414409404305)
                    ·
                      rfl

theorem cell22_4189802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_4189802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189802 prefixEnd_4189802 := by exact prefixLift 4189802
  have htrace : WordTrace (prefixWord ++ tailWord_4189802) baseStart_4189802 baseEnd_4189802 := by
    simpa [prefixWord, tailWord_4189802, baseEnd_4189802] using wordTrace_append hprefix tailTrace_4189802
  have hstable : (prefixWord ++ tailWord_4189802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189802).length < 2 ^ (prefixWord ++ tailWord_4189802).sum := by decide
  have hdescent : baseEnd_4189802 < baseStart_4189802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189877 : List Nat := [1, 3, 3, 3, 2, 1, 1, 3, 5]
def baseStart_4189877 : Nat := 118140960795 + 4189877 * 2 ^ 59
def prefixEnd_4189877 : Nat := 4983230072969 + 3 ^ 40 * 4189877 * 2
def baseEnd_4189877 : Nat := 478093507604046404593025

theorem tailTrace_4189877 : CollatzResearch.WordTrace tailWord_4189877 prefixEnd_4189877 478093507604046404593025 := by
  unfold tailWord_4189877
  simp only [CollatzResearch.WordTrace]
  refine ⟨152817368641798677866951885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101878245761199118577967923 152817368641798677866951885)
  ·
    refine ⟨57306513240674504200106957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152817368641798677866951885 57306513240674504200106957)
    ·
      refine ⟨21489942465252939075040109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57306513240674504200106957 21489942465252939075040109)
      ·
        refine ⟨8058728424469852153140041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21489942465252939075040109 8058728424469852153140041)
        ·
          refine ⟨6044046318352389114855031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8058728424469852153140041 6044046318352389114855031)
          ·
            refine ⟨9066069477528583672282547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6044046318352389114855031 9066069477528583672282547)
            ·
              refine ⟨13599104216292875508423821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9066069477528583672282547 13599104216292875508423821)
              ·
                refine ⟨5099664081109828315658933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13599104216292875508423821 5099664081109828315658933)
                ·
                  refine ⟨478093507604046404593025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5099664081109828315658933 478093507604046404593025)
                  ·
                    rfl

theorem cell22_4189877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_4189877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189877 prefixEnd_4189877 := by exact prefixLift 4189877
  have htrace : WordTrace (prefixWord ++ tailWord_4189877) baseStart_4189877 baseEnd_4189877 := by
    simpa [prefixWord, tailWord_4189877, baseEnd_4189877] using wordTrace_append hprefix tailTrace_4189877
  have hstable : (prefixWord ++ tailWord_4189877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189877).length < 2 ^ (prefixWord ++ tailWord_4189877).sum := by decide
  have hdescent : baseEnd_4189877 < baseStart_4189877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189888 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 8]
def baseStart_4189888 : Nat := 118140960795 + 4189888 * 2 ^ 59
def prefixEnd_4189888 : Nat := 4983230072969 + 3 ^ 40 * 4189888 * 2
def baseEnd_4189888 : Nat := 478094762778979617251347

theorem tailTrace_4189888 : CollatzResearch.WordTrace tailWord_4189888 prefixEnd_4189888 478094762778979617251347 := by
  unfold tailWord_4189888
  simp only [CollatzResearch.WordTrace]
  refine ⟨76408884922379413372801159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101878513229839217830401545 76408884922379413372801159)
  ·
    refine ⟨114613327383569120059201739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76408884922379413372801159 114613327383569120059201739)
    ·
      refine ⟨171919991075353680088802609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114613327383569120059201739 171919991075353680088802609)
      ·
        refine ⟨128939993306515260066601957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171919991075353680088802609 128939993306515260066601957)
        ·
          refine ⟨24176248744971611262487867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128939993306515260066601957 24176248744971611262487867)
          ·
            refine ⟨36264373117457416893731801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24176248744971611262487867 36264373117457416893731801)
            ·
              refine ⟨27198279838093062670298851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36264373117457416893731801 27198279838093062670298851)
              ·
                refine ⟨40797419757139594005448277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27198279838093062670298851 40797419757139594005448277)
                ·
                  refine ⟨478094762778979617251347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40797419757139594005448277 478094762778979617251347)
                  ·
                    rfl

theorem cell22_4189888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_4189888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189888 prefixEnd_4189888 := by exact prefixLift 4189888
  have htrace : WordTrace (prefixWord ++ tailWord_4189888) baseStart_4189888 baseEnd_4189888 := by
    simpa [prefixWord, tailWord_4189888, baseEnd_4189888] using wordTrace_append hprefix tailTrace_4189888
  have hstable : (prefixWord ++ tailWord_4189888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189888).length < 2 ^ (prefixWord ++ tailWord_4189888).sum := by decide
  have hdescent : baseEnd_4189888 < baseStart_4189888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189920 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 4, 3]
def baseStart_4189920 : Nat := 118140960795 + 4189920 * 2 ^ 59
def prefixEnd_4189920 : Nat := 4983230072969 + 3 ^ 40 * 4189920 * 2
def baseEnd_4189920 : Nat := 1434295242590901434953943

theorem tailTrace_4189920 : CollatzResearch.WordTrace tailWord_4189920 prefixEnd_4189920 1434295242590901434953943 := by
  unfold tailWord_4189920
  simp only [CollatzResearch.WordTrace]
  refine ⟨76409468490321448105383607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101879291320428597473844809 76409468490321448105383607)
  ·
    refine ⟨114614202735482172158075411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76409468490321448105383607 114614202735482172158075411)
    ·
      refine ⟨171921304103223258237113117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114614202735482172158075411 171921304103223258237113117)
      ·
        refine ⟨64470489038708721838917419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171921304103223258237113117 64470489038708721838917419)
        ·
          refine ⟨96705733558063082758376129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64470489038708721838917419 96705733558063082758376129)
          ·
            refine ⟨72529300168547312068782097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96705733558063082758376129 72529300168547312068782097)
            ·
              refine ⟨54396975126410484051586573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72529300168547312068782097 54396975126410484051586573)
              ·
                refine ⟨20398865672403931519344965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54396975126410484051586573 20398865672403931519344965)
                ·
                  refine ⟨3824787313575737159877181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20398865672403931519344965 3824787313575737159877181)
                  ·
                    refine ⟨1434295242590901434953943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3824787313575737159877181 1434295242590901434953943)
                    ·
                      rfl

theorem cell22_4189920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 4, 3].length) (baseStart_4189920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189920 prefixEnd_4189920 := by exact prefixLift 4189920
  have htrace : WordTrace (prefixWord ++ tailWord_4189920) baseStart_4189920 baseEnd_4189920 := by
    simpa [prefixWord, tailWord_4189920, baseEnd_4189920] using wordTrace_append hprefix tailTrace_4189920
  have hstable : (prefixWord ++ tailWord_4189920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189920).length < 2 ^ (prefixWord ++ tailWord_4189920).sum := by decide
  have hdescent : baseEnd_4189920 < baseStart_4189920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189937 : List Nat := [1, 2, 2, 2, 2, 3, 2, 3, 2, 3]
def baseStart_4189937 : Nat := 118140960795 + 4189937 * 2 ^ 59
def prefixEnd_4189937 : Nat := 4983230072969 + 3 ^ 40 * 4189937 * 2
def baseEnd_4189937 : Nat := 1434301062038319057278891

theorem tailTrace_4189937 : CollatzResearch.WordTrace tailWord_4189937 prefixEnd_4189937 1434301062038319057278891 := by
  unfold tailWord_4189937
  simp only [CollatzResearch.WordTrace]
  refine ⟨152819557021581308114136065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101879704681054205409424043 152819557021581308114136065)
  ·
    refine ⟨114614667766185981085602049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152819557021581308114136065 114614667766185981085602049)
    ·
      refine ⟨85961000824639485814201537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114614667766185981085602049 85961000824639485814201537)
      ·
        refine ⟨64470750618479614360651153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85961000824639485814201537 64470750618479614360651153)
        ·
          refine ⟨48353062963859710770488365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64470750618479614360651153 48353062963859710770488365)
          ·
            refine ⟨18132398611447391538933137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48353062963859710770488365 18132398611447391538933137)
            ·
              refine ⟨13599298958585543654199853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18132398611447391538933137 13599298958585543654199853)
              ·
                refine ⟨5099737109469578870324945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13599298958585543654199853 5099737109469578870324945)
                ·
                  refine ⟨3824802832102184152743709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5099737109469578870324945 3824802832102184152743709)
                  ·
                    refine ⟨1434301062038319057278891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3824802832102184152743709 1434301062038319057278891)
                    ·
                      rfl

theorem cell22_4189937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_4189937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189937 prefixEnd_4189937 := by exact prefixLift 4189937
  have htrace : WordTrace (prefixWord ++ tailWord_4189937) baseStart_4189937 baseEnd_4189937 := by
    simpa [prefixWord, tailWord_4189937, baseEnd_4189937] using wordTrace_append hprefix tailTrace_4189937
  have hstable : (prefixWord ++ tailWord_4189937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189937).length < 2 ^ (prefixWord ++ tailWord_4189937).sum := by decide
  have hdescent : baseEnd_4189937 < baseStart_4189937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190089 : List Nat := [1, 2, 1, 1, 5, 1, 4, 2, 2, 3]
def baseStart_4190089 : Nat := 118140960795 + 4190089 * 2 ^ 59
def prefixEnd_4190089 : Nat := 4983230072969 + 3 ^ 40 * 4190089 * 2
def baseEnd_4190089 : Nat := 1434353094744641327478425

theorem tailTrace_4190089 : CollatzResearch.WordTrace tailWord_4190089 prefixEnd_4190089 1434353094744641327478425 := by
  unfold tailWord_4190089
  simp only [CollatzResearch.WordTrace]
  refine ⟨152825100917030638073669321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101883400611353758715779547 152825100917030638073669321)
  ·
    refine ⟨114618825687772978555251991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152825100917030638073669321 114618825687772978555251991)
    ·
      refine ⟨171928238531659467832877987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114618825687772978555251991 171928238531659467832877987)
      ·
        refine ⟨257892357797489201749316981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171928238531659467832877987 257892357797489201749316981)
        ·
          refine ⟨24177408543514612663998467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257892357797489201749316981 24177408543514612663998467)
          ·
            refine ⟨36266112815271918995997701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24177408543514612663998467 36266112815271918995997701)
            ·
              refine ⟨6799896152863484811749569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36266112815271918995997701 6799896152863484811749569)
              ·
                refine ⟨5099922114647613608812177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799896152863484811749569 5099922114647613608812177)
                ·
                  refine ⟨3824941585985710206609133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5099922114647613608812177 3824941585985710206609133)
                  ·
                    refine ⟨1434353094744641327478425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3824941585985710206609133 1434353094744641327478425)
                    ·
                      rfl

theorem cell22_4190089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 2, 3].length) (baseStart_4190089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190089 prefixEnd_4190089 := by exact prefixLift 4190089
  have htrace : WordTrace (prefixWord ++ tailWord_4190089) baseStart_4190089 baseEnd_4190089 := by
    simpa [prefixWord, tailWord_4190089, baseEnd_4190089] using wordTrace_append hprefix tailTrace_4190089
  have hstable : (prefixWord ++ tailWord_4190089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190089).length < 2 ^ (prefixWord ++ tailWord_4190089).sum := by decide
  have hdescent : baseEnd_4190089 < baseStart_4190089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190115 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 4, 6]
def baseStart_4190115 : Nat := 118140960795 + 4190115 * 2 ^ 59
def prefixEnd_4190115 : Nat := 4983230072969 + 3 ^ 40 * 4190115 * 2
def baseEnd_4190115 : Nat := 1434361995075985926328345

theorem tailTrace_4190115 : CollatzResearch.WordTrace tailWord_4190115 prefixEnd_4190115 1434361995075985926328345 := by
  unfold tailWord_4190115
  simp only [CollatzResearch.WordTrace]
  refine ⟨152826049214936444514115799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101884032809957629676077199 152826049214936444514115799)
  ·
    refine ⟨229239073822404666771173699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152826049214936444514115799 229239073822404666771173699)
    ·
      refine ⟨343858610733607000156760549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229239073822404666771173699 343858610733607000156760549)
      ·
        refine ⟨64473489512551312529392603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343858610733607000156760549 64473489512551312529392603)
        ·
          refine ⟨96710234268826968794088905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64473489512551312529392603 96710234268826968794088905)
          ·
            refine ⟨72532675701620226595566679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96710234268826968794088905 72532675701620226595566679)
            ·
              refine ⟨108799013552430339893350019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72532675701620226595566679 108799013552430339893350019)
              ·
                refine ⟨163198520328645509840025029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108799013552430339893350019 163198520328645509840025029)
                ·
                  refine ⟨30599722561621033095004693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163198520328645509840025029 30599722561621033095004693)
                  ·
                    refine ⟨1434361995075985926328345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30599722561621033095004693 1434361995075985926328345)
                    ·
                      rfl

theorem cell22_4190115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 6].length) (baseStart_4190115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190115 prefixEnd_4190115 := by exact prefixLift 4190115
  have htrace : WordTrace (prefixWord ++ tailWord_4190115) baseStart_4190115 baseEnd_4190115 := by
    simpa [prefixWord, tailWord_4190115, baseEnd_4190115] using wordTrace_append hprefix tailTrace_4190115
  have hstable : (prefixWord ++ tailWord_4190115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190115).length < 2 ^ (prefixWord ++ tailWord_4190115).sum := by decide
  have hdescent : baseEnd_4190115 < baseStart_4190115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190119 : List Nat := [1, 1, 6, 1, 2, 2, 3, 6]
def baseStart_4190119 : Nat := 118140960795 + 4190119 * 2 ^ 59
def prefixEnd_4190119 : Nat := 4983230072969 + 3 ^ 40 * 4190119 * 2
def baseEnd_4190119 : Nat := 159373707150859027692037

theorem tailTrace_4190119 : CollatzResearch.WordTrace tailWord_4190119 prefixEnd_4190119 159373707150859027692037 := by
  unfold tailWord_4190119
  simp only [CollatzResearch.WordTrace]
  refine ⟨152826195106921953197261411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101884130071281302131507607 152826195106921953197261411)
  ·
    refine ⟨229239292660382929795892117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152826195106921953197261411 229239292660382929795892117)
    ·
      refine ⟨10745591843455449834182443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 229239292660382929795892117 10745591843455449834182443)
      ·
        refine ⟨16118387765183174751273665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10745591843455449834182443 16118387765183174751273665)
        ·
          refine ⟨12088790823887381063455249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16118387765183174751273665 12088790823887381063455249)
          ·
            refine ⟨9066593117915535797591437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12088790823887381063455249 9066593117915535797591437)
            ·
              refine ⟨3399972419218325924096789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9066593117915535797591437 3399972419218325924096789)
              ·
                refine ⟨159373707150859027692037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3399972419218325924096789 159373707150859027692037)
                ·
                  rfl

theorem cell22_4190119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 6].length) (baseStart_4190119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190119 prefixEnd_4190119 := by exact prefixLift 4190119
  have htrace : WordTrace (prefixWord ++ tailWord_4190119) baseStart_4190119 baseEnd_4190119 := by
    simpa [prefixWord, tailWord_4190119, baseEnd_4190119] using wordTrace_append hprefix tailTrace_4190119
  have hstable : (prefixWord ++ tailWord_4190119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190119).length < 2 ^ (prefixWord ++ tailWord_4190119).sum := by decide
  have hdescent : baseEnd_4190119 < baseStart_4190119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190140 : List Nat := [2, 2, 2, 5, 2, 1, 1, 2, 2, 3]
def baseStart_4190140 : Nat := 118140960795 + 4190140 * 2 ^ 59
def prefixEnd_4190140 : Nat := 4983230072969 + 3 ^ 40 * 4190140 * 2
def baseEnd_4190140 : Nat := 1434370553086894194453269

theorem tailTrace_4190140 : CollatzResearch.WordTrace tailWord_4190140 prefixEnd_4190140 1434370553086894194453269 := by
  unfold tailWord_4190140
  simp only [CollatzResearch.WordTrace]
  refine ⟨76413480519922936891887937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101884640693230582522517249 76413480519922936891887937)
  ·
    refine ⟨57310110389942202668915953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76413480519922936891887937 57310110389942202668915953)
    ·
      refine ⟨42982582792456652001686965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57310110389942202668915953 42982582792456652001686965)
      ·
        refine ⟨4029617136792811125158153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42982582792456652001686965 4029617136792811125158153)
        ·
          refine ⟨3022212852594608343868615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4029617136792811125158153 3022212852594608343868615)
          ·
            refine ⟨4533319278891912515802923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022212852594608343868615 4533319278891912515802923)
            ·
              refine ⟨6799978918337868773704385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4533319278891912515802923 6799978918337868773704385)
              ·
                refine ⟨5099984188753401580278289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6799978918337868773704385 5099984188753401580278289)
                ·
                  refine ⟨3824988141565051185208717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5099984188753401580278289 3824988141565051185208717)
                  ·
                    refine ⟨1434370553086894194453269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3824988141565051185208717 1434370553086894194453269)
                    ·
                      rfl

theorem cell22_4190140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_4190140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190140 prefixEnd_4190140 := by exact prefixLift 4190140
  have htrace : WordTrace (prefixWord ++ tailWord_4190140) baseStart_4190140 baseEnd_4190140 := by
    simpa [prefixWord, tailWord_4190140, baseEnd_4190140] using wordTrace_append hprefix tailTrace_4190140
  have hstable : (prefixWord ++ tailWord_4190140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190140).length < 2 ^ (prefixWord ++ tailWord_4190140).sum := by decide
  have hdescent : baseEnd_4190140 < baseStart_4190140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190177 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 3, 4]
def baseStart_4190177 : Nat := 118140960795 + 4190177 * 2 ^ 59
def prefixEnd_4190177 : Nat := 4983230072969 + 3 ^ 40 * 4190177 * 2
def baseEnd_4190177 : Nat := 1434383218943038431278155

theorem tailTrace_4190177 : CollatzResearch.WordTrace tailWord_4190177 prefixEnd_4190177 1434383218943038431278155 := by
  unfold tailWord_4190177
  simp only [CollatzResearch.WordTrace]
  refine ⟨152828310540711829102872785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101885540360474552735248523 152828310540711829102872785)
  ·
    refine ⟨114621232905533871827154589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152828310540711829102872785 114621232905533871827154589)
    ·
      refine ⟨42982962339575201935182971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114621232905533871827154589 42982962339575201935182971)
      ·
        refine ⟨64474443509362802902774457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42982962339575201935182971 64474443509362802902774457)
        ·
          refine ⟨48355832632022102177080843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64474443509362802902774457 48355832632022102177080843)
          ·
            refine ⟨72533748948033153265621265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48355832632022102177080843 72533748948033153265621265)
            ·
              refine ⟨54400311711024864949215949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72533748948033153265621265 54400311711024864949215949)
              ·
                refine ⟨20400116891634324355955981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54400311711024864949215949 20400116891634324355955981)
                ·
                  refine ⟨7650043834362871633483493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20400116891634324355955981 7650043834362871633483493)
                  ·
                    refine ⟨1434383218943038431278155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7650043834362871633483493 1434383218943038431278155)
                    ·
                      rfl

theorem cell22_4190177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_4190177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190177 prefixEnd_4190177 := by exact prefixLift 4190177
  have htrace : WordTrace (prefixWord ++ tailWord_4190177) baseStart_4190177 baseEnd_4190177 := by
    simpa [prefixWord, tailWord_4190177, baseEnd_4190177] using wordTrace_append hprefix tailTrace_4190177
  have hstable : (prefixWord ++ tailWord_4190177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190177).length < 2 ^ (prefixWord ++ tailWord_4190177).sum := by decide
  have hdescent : baseEnd_4190177 < baseStart_4190177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190224 : List Nat := [2, 1, 1, 1, 1, 1, 1, 9, 2, 3]
def baseStart_4190224 : Nat := 118140960795 + 4190224 * 2 ^ 59
def prefixEnd_4190224 : Nat := 4983230072969 + 3 ^ 40 * 4190224 * 2
def baseEnd_4190224 : Nat := 1434399308003545975353011

theorem tailTrace_4190224 : CollatzResearch.WordTrace tailWord_4190224 prefixEnd_4190224 1434399308003545975353011 := by
  unfold tailWord_4190224
  simp only [CollatzResearch.WordTrace]
  refine ⟨76415012385770778064916863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101886683181027704086555817 76415012385770778064916863)
  ·
    refine ⟨114622518578656167097375295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76415012385770778064916863 114622518578656167097375295)
    ·
      refine ⟨171933777867984250646062943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114622518578656167097375295 171933777867984250646062943)
      ·
        refine ⟨257900666801976375969094415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171933777867984250646062943 257900666801976375969094415)
        ·
          refine ⟨386851000202964563953641623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257900666801976375969094415 386851000202964563953641623)
          ·
            refine ⟨580276500304446845930462435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386851000202964563953641623 580276500304446845930462435)
            ·
              refine ⟨870414750456670268895693653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580276500304446845930462435 870414750456670268895693653)
              ·
                refine ⟨5100086428457052356810705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 870414750456670268895693653 5100086428457052356810705)
                ·
                  refine ⟨3825064821342789267608029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5100086428457052356810705 3825064821342789267608029)
                  ·
                    refine ⟨1434399308003545975353011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3825064821342789267608029 1434399308003545975353011)
                    ·
                      rfl

theorem cell22_4190224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 2, 3].length) (baseStart_4190224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190224 prefixEnd_4190224 := by exact prefixLift 4190224
  have htrace : WordTrace (prefixWord ++ tailWord_4190224) baseStart_4190224 baseEnd_4190224 := by
    simpa [prefixWord, tailWord_4190224, baseEnd_4190224] using wordTrace_append hprefix tailTrace_4190224
  have hstable : (prefixWord ++ tailWord_4190224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190224).length < 2 ^ (prefixWord ++ tailWord_4190224).sum := by decide
  have hdescent : baseEnd_4190224 < baseStart_4190224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190228 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_4190228 : Nat := 118140960795 + 4190228 * 2 ^ 59
def prefixEnd_4190228 : Nat := 4983230072969 + 3 ^ 40 * 4190228 * 2
def baseEnd_4190228 : Nat := 1434400677285291298252999

theorem tailTrace_4190228 : CollatzResearch.WordTrace tailWord_4190228 prefixEnd_4190228 1434400677285291298252999 := by
  unfold tailWord_4190228
  simp only [CollatzResearch.WordTrace]
  refine ⟨76415085331763532406489669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101886780442351376541986225 76415085331763532406489669)
  ·
    refine ⟨14327828499705662326216813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76415085331763532406489669 14327828499705662326216813)
    ·
      refine ⟨5372935687389623372331305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14327828499705662326216813 5372935687389623372331305)
      ·
        refine ⟨4029701765542217529248479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5372935687389623372331305 4029701765542217529248479)
        ·
          refine ⟨6044552648313326293872719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4029701765542217529248479 6044552648313326293872719)
          ·
            refine ⟨9066828972469989440809079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6044552648313326293872719 9066828972469989440809079)
            ·
              refine ⟨13600243458704984161213619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9066828972469989440809079 13600243458704984161213619)
              ·
                refine ⟨20400365188057476241820429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13600243458704984161213619 20400365188057476241820429)
                ·
                  refine ⟨7650136945521553590682661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20400365188057476241820429 7650136945521553590682661)
                  ·
                    refine ⟨1434400677285291298252999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7650136945521553590682661 1434400677285291298252999)
                    ·
                      rfl

theorem cell22_4190228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_4190228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190228 prefixEnd_4190228 := by exact prefixLift 4190228
  have htrace : WordTrace (prefixWord ++ tailWord_4190228) baseStart_4190228 baseEnd_4190228 := by
    simpa [prefixWord, tailWord_4190228, baseEnd_4190228] using wordTrace_append hprefix tailTrace_4190228
  have hstable : (prefixWord ++ tailWord_4190228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190228).length < 2 ^ (prefixWord ++ tailWord_4190228).sum := by decide
  have hdescent : baseEnd_4190228 < baseStart_4190228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190239 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 2, 4]
def baseStart_4190239 : Nat := 118140960795 + 4190239 * 2 ^ 59
def prefixEnd_4190239 : Nat := 4983230072969 + 3 ^ 40 * 4190239 * 2
def baseEnd_4190239 : Nat := 1434404442810090936227965

theorem tailTrace_4190239 : CollatzResearch.WordTrace tailWord_4190239 prefixEnd_4190239 1434404442810090936227965 := by
  unfold tailWord_4190239
  simp only [CollatzResearch.WordTrace]
  refine ⟨152830571866487213691629771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101887047910991475794419847 152830571866487213691629771)
  ·
    refine ⟨229245857799730820537444657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152830571866487213691629771 229245857799730820537444657)
    ·
      refine ⟨171934393349798115403083493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229245857799730820537444657 171934393349798115403083493)
      ·
        refine ⟨32237698753087146638078155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171934393349798115403083493 32237698753087146638078155)
        ·
          refine ⟨48356548129630719957117233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32237698753087146638078155 48356548129630719957117233)
          ·
            refine ⟨36267411097223039967837925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48356548129630719957117233 36267411097223039967837925)
            ·
              refine ⟨6800139580729319993969611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36267411097223039967837925 6800139580729319993969611)
              ·
                refine ⟨10200209371093979990954417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6800139580729319993969611 10200209371093979990954417)
                ·
                  refine ⟨7650157028320484993215813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10200209371093979990954417 7650157028320484993215813)
                  ·
                    refine ⟨1434404442810090936227965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7650157028320484993215813 1434404442810090936227965)
                    ·
                      rfl

theorem cell22_4190239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_4190239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190239 prefixEnd_4190239 := by exact prefixLift 4190239
  have htrace : WordTrace (prefixWord ++ tailWord_4190239) baseStart_4190239 baseEnd_4190239 := by
    simpa [prefixWord, tailWord_4190239, baseEnd_4190239] using wordTrace_append hprefix tailTrace_4190239
  have hstable : (prefixWord ++ tailWord_4190239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190239).length < 2 ^ (prefixWord ++ tailWord_4190239).sum := by decide
  have hdescent : baseEnd_4190239 < baseStart_4190239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190282 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 9]
def baseStart_4190282 : Nat := 118140960795 + 4190282 * 2 ^ 59
def prefixEnd_4190282 : Nat := 4983230072969 + 3 ^ 40 * 4190282 * 2
def baseEnd_4190282 : Nat := 478139720862951052467611

theorem tailTrace_4190282 : CollatzResearch.WordTrace tailWord_4190282 prefixEnd_4190282 478139720862951052467611 := by
  unfold tailWord_4190282
  simp only [CollatzResearch.WordTrace]
  refine ⟨38208035051332858008861275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101888093470220954690296733 38208035051332858008861275)
  ·
    refine ⟨57312052576999287013291913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38208035051332858008861275 57312052576999287013291913)
    ·
      refine ⟨42984039432749465259968935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57312052576999287013291913 42984039432749465259968935)
      ·
        refine ⟨64476059149124197889953403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42984039432749465259968935 64476059149124197889953403)
        ·
          refine ⟨96714088723686296834930105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64476059149124197889953403 96714088723686296834930105)
          ·
            refine ⟨72535566542764722626197579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96714088723686296834930105 72535566542764722626197579)
            ·
              refine ⟨108803349814147083939296369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72535566542764722626197579 108803349814147083939296369)
              ·
                refine ⟨81602512360610312954472277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108803349814147083939296369 81602512360610312954472277)
                ·
                  refine ⟨478139720862951052467611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81602512360610312954472277 478139720862951052467611)
                  ·
                    rfl

theorem cell22_4190282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_4190282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190282 prefixEnd_4190282 := by exact prefixLift 4190282
  have htrace : WordTrace (prefixWord ++ tailWord_4190282) baseStart_4190282 baseEnd_4190282 := by
    simpa [prefixWord, tailWord_4190282, baseEnd_4190282] using wordTrace_append hprefix tailTrace_4190282
  have hstable : (prefixWord ++ tailWord_4190282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190282).length < 2 ^ (prefixWord ++ tailWord_4190282).sum := by decide
  have hdescent : baseEnd_4190282 < baseStart_4190282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190286 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_4190286 : Nat := 118140960795 + 4190286 * 2 ^ 59
def prefixEnd_4190286 : Nat := 4983230072969 + 3 ^ 40 * 4190286 * 2
def baseEnd_4190286 : Nat := 1434420531870598480302821

theorem tailTrace_4190286 : CollatzResearch.WordTrace tailWord_4190286 prefixEnd_4190286 1434420531870598480302821 := by
  unfold tailWord_4190286
  simp only [CollatzResearch.WordTrace]
  refine ⟨19104035762164617589823839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101888190731544627145727141 19104035762164617589823839)
  ·
    refine ⟨28656053643246926384735759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19104035762164617589823839 28656053643246926384735759)
    ·
      refine ⟨42984080464870389577103639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28656053643246926384735759 42984080464870389577103639)
      ·
        refine ⟨64476120697305584365655459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42984080464870389577103639 64476120697305584365655459)
        ·
          refine ⟨96714181045958376548483189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64476120697305584365655459 96714181045958376548483189)
          ·
            refine ⟨9066954473058597801420299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96714181045958376548483189 9066954473058597801420299)
            ·
              refine ⟨13600431709587896702130449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9066954473058597801420299 13600431709587896702130449)
              ·
                refine ⟨10200323782190922526597837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13600431709587896702130449 10200323782190922526597837)
                ·
                  refine ⟨3825121418321595947474189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10200323782190922526597837 3825121418321595947474189)
                  ·
                    refine ⟨1434420531870598480302821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3825121418321595947474189 1434420531870598480302821)
                    ·
                      rfl

theorem cell22_4190286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_4190286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190286 prefixEnd_4190286 := by exact prefixLift 4190286
  have htrace : WordTrace (prefixWord ++ tailWord_4190286) baseStart_4190286 baseEnd_4190286 := by
    simpa [prefixWord, tailWord_4190286, baseEnd_4190286] using wordTrace_append hprefix tailTrace_4190286
  have hstable : (prefixWord ++ tailWord_4190286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190286).length < 2 ^ (prefixWord ++ tailWord_4190286).sum := by decide
  have hdescent : baseEnd_4190286 < baseStart_4190286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190297 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 1, 7]
def baseStart_4190297 : Nat := 118140960795 + 4190297 * 2 ^ 59
def prefixEnd_4190297 : Nat := 4983230072969 + 3 ^ 40 * 4190297 * 2
def baseEnd_4190297 : Nat := 1434424297395398118277787

theorem tailTrace_4190297 : CollatzResearch.WordTrace tailWord_4190297 prefixEnd_4190297 1434424297395398118277787 := by
  unfold tailWord_4190297
  simp only [CollatzResearch.WordTrace]
  refine ⟨152832687300277089597241145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101888458200184726398160763 152832687300277089597241145)
  ·
    refine ⟨114624515475207817197930859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152832687300277089597241145 114624515475207817197930859)
    ·
      refine ⟨171936773212811725796896289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114624515475207817197930859 171936773212811725796896289)
      ·
        refine ⟨128952579909608794347672217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171936773212811725796896289 128952579909608794347672217)
        ·
          refine ⟨96714434932206595760754163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128952579909608794347672217 96714434932206595760754163)
          ·
            refine ⟨145071652398309893641131245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96714434932206595760754163 145071652398309893641131245)
            ·
              refine ⟨54401869649366210115424217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145071652398309893641131245 54401869649366210115424217)
              ·
                refine ⟨40801402237024657586568163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54401869649366210115424217 40801402237024657586568163)
                ·
                  refine ⟨61202103355536986379852245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40801402237024657586568163 61202103355536986379852245)
                  ·
                    refine ⟨1434424297395398118277787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61202103355536986379852245 1434424297395398118277787)
                    ·
                      rfl

theorem cell22_4190297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_4190297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190297 prefixEnd_4190297 := by exact prefixLift 4190297
  have htrace : WordTrace (prefixWord ++ tailWord_4190297) baseStart_4190297 baseEnd_4190297 := by
    simpa [prefixWord, tailWord_4190297, baseEnd_4190297] using wordTrace_append hprefix tailTrace_4190297
  have hstable : (prefixWord ++ tailWord_4190297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190297).length < 2 ^ (prefixWord ++ tailWord_4190297).sum := by decide
  have hdescent : baseEnd_4190297 < baseStart_4190297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190316 : List Nat := [2, 2, 1, 1, 3, 5, 1, 2, 5]
def baseStart_4190316 : Nat := 118140960795 + 4190316 * 2 ^ 59
def prefixEnd_4190316 : Nat := 4983230072969 + 3 ^ 40 * 4190316 * 2
def baseEnd_4190316 : Nat := 478143600494562800684243

theorem tailTrace_4190316 : CollatzResearch.WordTrace tailWord_4190316 prefixEnd_4190316 478143600494562800684243 := by
  unfold tailWord_4190316
  simp only [CollatzResearch.WordTrace]
  refine ⟨76416690143604127921091401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101888920191472170561455201 76416690143604127921091401)
  ·
    refine ⟨57312517607703095940818551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76416690143604127921091401 57312517607703095940818551)
    ·
      refine ⟨85968776411554643911227827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57312517607703095940818551 85968776411554643911227827)
      ·
        refine ⟨128953164617331965866841741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85968776411554643911227827 128953164617331965866841741)
        ·
          refine ⟨48357436731499487200065653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128953164617331965866841741 48357436731499487200065653)
          ·
            refine ⟨4533509693578076925006155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48357436731499487200065653 4533509693578076925006155)
            ·
              refine ⟨6800264540367115387509233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4533509693578076925006155 6800264540367115387509233)
              ·
                refine ⟨5100198405275336540631925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6800264540367115387509233 5100198405275336540631925)
                ·
                  refine ⟨478143600494562800684243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5100198405275336540631925 478143600494562800684243)
                  ·
                    rfl

theorem cell22_4190316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_4190316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190316 prefixEnd_4190316 := by exact prefixLift 4190316
  have htrace : WordTrace (prefixWord ++ tailWord_4190316) baseStart_4190316 baseEnd_4190316 := by
    simpa [prefixWord, tailWord_4190316, baseEnd_4190316] using wordTrace_append hprefix tailTrace_4190316
  have hstable : (prefixWord ++ tailWord_4190316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190316).length < 2 ^ (prefixWord ++ tailWord_4190316).sum := by decide
  have hdescent : baseEnd_4190316 < baseStart_4190316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190346 : List Nat := [3, 1, 2, 3, 1, 2, 1, 4, 1, 4]
def baseStart_4190346 : Nat := 118140960795 + 4190346 * 2 ^ 59
def prefixEnd_4190346 : Nat := 4983230072969 + 3 ^ 40 * 4190346 * 2
def baseEnd_4190346 : Nat := 1434441071096778323802637

theorem tailTrace_4190346 : CollatzResearch.WordTrace tailWord_4190346 prefixEnd_4190346 1434441071096778323802637 := by
  unfold tailWord_4190346
  simp only [CollatzResearch.WordTrace]
  refine ⟨38208618619274892741443723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101889649651399713977183261 38208618619274892741443723)
  ·
    refine ⟨57312927928912339112165585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38208618619274892741443723 57312927928912339112165585)
    ·
      refine ⟨42984695946684254334124189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57312927928912339112165585 42984695946684254334124189)
      ·
        refine ⟨16119260980006595375296571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42984695946684254334124189 16119260980006595375296571)
        ·
          refine ⟨24178891470009893062944857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16119260980006595375296571 24178891470009893062944857)
          ·
            refine ⟨18134168602507419797208643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24178891470009893062944857 18134168602507419797208643)
            ·
              refine ⟨27201252903761129695812965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18134168602507419797208643 27201252903761129695812965)
              ·
                refine ⟨5100234919455211817964931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27201252903761129695812965 5100234919455211817964931)
                ·
                  refine ⟨7650352379182817726947397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100234919455211817964931 7650352379182817726947397)
                  ·
                    refine ⟨1434441071096778323802637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7650352379182817726947397 1434441071096778323802637)
                    ·
                      rfl

theorem cell22_4190346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_4190346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190346 prefixEnd_4190346 := by exact prefixLift 4190346
  have htrace : WordTrace (prefixWord ++ tailWord_4190346) baseStart_4190346 baseEnd_4190346 := by
    simpa [prefixWord, tailWord_4190346, baseEnd_4190346] using wordTrace_append hprefix tailTrace_4190346
  have hstable : (prefixWord ++ tailWord_4190346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190346).length < 2 ^ (prefixWord ++ tailWord_4190346).sum := by decide
  have hdescent : baseEnd_4190346 < baseStart_4190346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190449 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 1, 7]
def baseStart_4190449 : Nat := 118140960795 + 4190449 * 2 ^ 59
def prefixEnd_4190449 : Nat := 4983230072969 + 3 ^ 40 * 4190449 * 2
def baseEnd_4190449 : Nat := 1434476330101720388477321

theorem tailTrace_4190449 : CollatzResearch.WordTrace tailWord_4190449 prefixEnd_4190449 1434476330101720388477321 := by
  unfold tailWord_4190449
  simp only [CollatzResearch.WordTrace]
  refine ⟨152838231195726419556774401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101892154130484279704516267 152838231195726419556774401)
  ·
    refine ⟨114628673396794814667580801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152838231195726419556774401 114628673396794814667580801)
    ·
      refine ⟨85971505047596111000685601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114628673396794814667580801 85971505047596111000685601)
      ·
        refine ⟨64478628785697083250514201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85971505047596111000685601 64478628785697083250514201)
        ·
          refine ⟨48358971589272812437885651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64478628785697083250514201 48358971589272812437885651)
          ·
            refine ⟨72538457383909218656828477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48358971589272812437885651 72538457383909218656828477)
            ·
              refine ⟨27201921518965956996310679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72538457383909218656828477 27201921518965956996310679)
              ·
                refine ⟨40802882278448935494466019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27201921518965956996310679 40802882278448935494466019)
                ·
                  refine ⟨61204323417673403241699029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40802882278448935494466019 61204323417673403241699029)
                  ·
                    refine ⟨1434476330101720388477321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61204323417673403241699029 1434476330101720388477321)
                    ·
                      rfl

theorem cell22_4190449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_4190449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190449 prefixEnd_4190449 := by exact prefixLift 4190449
  have htrace : WordTrace (prefixWord ++ tailWord_4190449) baseStart_4190449 baseEnd_4190449 := by
    simpa [prefixWord, tailWord_4190449, baseEnd_4190449] using wordTrace_append hprefix tailTrace_4190449
  have hstable : (prefixWord ++ tailWord_4190449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190449).length < 2 ^ (prefixWord ++ tailWord_4190449).sum := by decide
  have hdescent : baseEnd_4190449 < baseStart_4190449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190496 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 6]
def baseStart_4190496 : Nat := 118140960795 + 4190496 * 2 ^ 59
def prefixEnd_4190496 : Nat := 4983230072969 + 3 ^ 40 * 4190496 * 2
def baseEnd_4190496 : Nat := 478164139720742644184059

theorem tailTrace_4190496 : CollatzResearch.WordTrace tailWord_4190496 prefixEnd_4190496 478164139720742644184059 := by
  unfold tailWord_4190496
  simp only [CollatzResearch.WordTrace]
  refine ⟨76419972713278073291867671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101893296951037431055823561 76419972713278073291867671)
  ·
    refine ⟨114629959069917109937801507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76419972713278073291867671 114629959069917109937801507)
    ·
      refine ⟨171944938604875664906702261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114629959069917109937801507 171944938604875664906702261)
      ·
        refine ⟨16119837994207093585003337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171944938604875664906702261 16119837994207093585003337)
        ·
          refine ⟨12089878495655320188752503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16119837994207093585003337 12089878495655320188752503)
          ·
            refine ⟨18134817743482980283128755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12089878495655320188752503 18134817743482980283128755)
            ·
              refine ⟨27202226615224470424693133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18134817743482980283128755 27202226615224470424693133)
              ·
                refine ⟨10200834980709176409259925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27202226615224470424693133 10200834980709176409259925)
                ·
                  refine ⟨478164139720742644184059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10200834980709176409259925 478164139720742644184059)
                  ·
                    rfl

theorem cell22_4190496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 6].length) (baseStart_4190496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190496 prefixEnd_4190496 := by exact prefixLift 4190496
  have htrace : WordTrace (prefixWord ++ tailWord_4190496) baseStart_4190496 baseEnd_4190496 := by
    simpa [prefixWord, tailWord_4190496, baseEnd_4190496] using wordTrace_append hprefix tailTrace_4190496
  have hstable : (prefixWord ++ tailWord_4190496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190496).length < 2 ^ (prefixWord ++ tailWord_4190496).sum := by decide
  have hdescent : baseEnd_4190496 < baseStart_4190496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190511 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 1, 5]
def baseStart_4190511 : Nat := 118140960795 + 4190511 * 2 ^ 59
def prefixEnd_4190511 : Nat := 4983230072969 + 3 ^ 40 * 4190511 * 2
def baseEnd_4190511 : Nat := 1434497553968772893427131

theorem tailTrace_4190511 : CollatzResearch.WordTrace tailWord_4190511 prefixEnd_4190511 1434497553968772893427131 := by
  unfold tailWord_4190511
  simp only [CollatzResearch.WordTrace]
  refine ⟨152840492521501804145531387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101893661681001202763687591 152840492521501804145531387)
  ·
    refine ⟨229260738782252706218297081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152840492521501804145531387 229260738782252706218297081)
    ·
      refine ⟨171945554086689529663722811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229260738782252706218297081 171945554086689529663722811)
      ·
        refine ⟨257918331130034294495584217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171945554086689529663722811 257918331130034294495584217)
        ·
          refine ⟨193438748347525720871688163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257918331130034294495584217 193438748347525720871688163)
          ·
            refine ⟨290158122521288581307532245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193438748347525720871688163 290158122521288581307532245)
            ·
              refine ⟨6800580996592701124395287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 290158122521288581307532245 6800580996592701124395287)
              ·
                refine ⟨10200871494889051686592931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6800580996592701124395287 10200871494889051686592931)
                ·
                  refine ⟨15301307242333577529889397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10200871494889051686592931 15301307242333577529889397)
                  ·
                    refine ⟨1434497553968772893427131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15301307242333577529889397 1434497553968772893427131)
                    ·
                      rfl

theorem cell22_4190511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_4190511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190511 prefixEnd_4190511 := by exact prefixLift 4190511
  have htrace : WordTrace (prefixWord ++ tailWord_4190511) baseStart_4190511 baseEnd_4190511 := by
    simpa [prefixWord, tailWord_4190511, baseEnd_4190511] using wordTrace_append hprefix tailTrace_4190511
  have hstable : (prefixWord ++ tailWord_4190511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190511).length < 2 ^ (prefixWord ++ tailWord_4190511).sum := by decide
  have hdescent : baseEnd_4190511 < baseStart_4190511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190562 : List Nat := [3, 3, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_4190562 : Nat := 118140960795 + 4190562 * 2 ^ 59
def prefixEnd_4190562 : Nat := 4983230072969 + 3 ^ 40 * 4190562 * 2
def baseEnd_4190562 : Nat := 1434515012311025760401975

theorem tailTrace_4190562 : CollatzResearch.WordTrace tailWord_4190562 prefixEnd_4190562 1434515012311025760401975 := by
  unfold tailWord_4190562
  simp only [CollatzResearch.WordTrace]
  refine ⟨38210588161079259963909485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101894901762878026570425293 38210588161079259963909485)
  ·
    refine ⟨14328970560404722486466057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38210588161079259963909485 14328970560404722486466057)
    ·
      refine ⟨10746727920303541864849543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14328970560404722486466057 10746727920303541864849543)
      ·
        refine ⟨16120091880455312797274315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10746727920303541864849543 16120091880455312797274315)
        ·
          refine ⟨24180137820682969195911473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16120091880455312797274315 24180137820682969195911473)
          ·
            refine ⟨18135103365512226896933605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24180137820682969195911473 18135103365512226896933605)
            ·
              refine ⟨3400331881033542543175051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18135103365512226896933605 3400331881033542543175051)
              ·
                refine ⟨5100497821550313814762577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400331881033542543175051 5100497821550313814762577)
                ·
                  refine ⟨3825373366162735361071933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5100497821550313814762577 3825373366162735361071933)
                  ·
                    refine ⟨1434515012311025760401975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3825373366162735361071933 1434515012311025760401975)
                    ·
                      rfl

theorem cell22_4190562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_4190562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190562 prefixEnd_4190562 := by exact prefixLift 4190562
  have htrace : WordTrace (prefixWord ++ tailWord_4190562) baseStart_4190562 baseEnd_4190562 := by
    simpa [prefixWord, tailWord_4190562, baseEnd_4190562] using wordTrace_append hprefix tailTrace_4190562
  have hstable : (prefixWord ++ tailWord_4190562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190562).length < 2 ^ (prefixWord ++ tailWord_4190562).sum := by decide
  have hdescent : baseEnd_4190562 < baseStart_4190562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190573 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_4190573 : Nat := 118140960795 + 4190573 * 2 ^ 59
def prefixEnd_4190573 : Nat := 4983230072969 + 3 ^ 40 * 4190573 * 2
def baseEnd_4190573 : Nat := 1434518777835825398376941

theorem tailTrace_4190573 : CollatzResearch.WordTrace tailWord_4190573 prefixEnd_4190573 1434518777835825398376941 := by
  unfold tailWord_4190573
  simp only [CollatzResearch.WordTrace]
  refine ⟨152842753847277188734288373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101895169231518125822858915 152842753847277188734288373)
  ·
    refine ⟨14329008173182236443839535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152842753847277188734288373 14329008173182236443839535)
    ·
      refine ⟨21493512259773354665759303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14329008173182236443839535 21493512259773354665759303)
      ·
        refine ⟨32240268389660031998638955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21493512259773354665759303 32240268389660031998638955)
        ·
          refine ⟨48360402584490047997958433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32240268389660031998638955 48360402584490047997958433)
          ·
            refine ⟨36270301938367535998468825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48360402584490047997958433 36270301938367535998468825)
            ·
              refine ⟨27202726453775651998851619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36270301938367535998468825 27202726453775651998851619)
              ·
                refine ⟨40804089680663477998277429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27202726453775651998851619 40804089680663477998277429)
                ·
                  refine ⟨3825383407562201062338509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40804089680663477998277429 3825383407562201062338509)
                  ·
                    refine ⟨1434518777835825398376941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3825383407562201062338509 1434518777835825398376941)
                    ·
                      rfl

theorem cell22_4190573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_4190573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190573 prefixEnd_4190573 := by exact prefixLift 4190573
  have htrace : WordTrace (prefixWord ++ tailWord_4190573) baseStart_4190573 baseEnd_4190573 := by
    simpa [prefixWord, tailWord_4190573, baseEnd_4190573] using wordTrace_append hprefix tailTrace_4190573
  have hstable : (prefixWord ++ tailWord_4190573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190573).length < 2 ^ (prefixWord ++ tailWord_4190573).sum := by decide
  have hdescent : baseEnd_4190573 < baseStart_4190573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190603 : List Nat := [1, 1, 1, 1, 4, 5, 2, 2, 5]
def baseStart_4190603 : Nat := 118140960795 + 4190603 * 2 ^ 59
def prefixEnd_4190603 : Nat := 4983230072969 + 3 ^ 40 * 4190603 * 2
def baseEnd_4190603 : Nat := 478176349149638440042283

theorem tailTrace_4190603 : CollatzResearch.WordTrace tailWord_4190603 prefixEnd_4190603 478176349149638440042283 := by
  unfold tailWord_4190603
  simp only [CollatzResearch.WordTrace]
  refine ⟨152843848037168503857880463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101895898691445669238586975 152843848037168503857880463)
  ·
    refine ⟨229265772055752755786820695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152843848037168503857880463 229265772055752755786820695)
    ·
      refine ⟨343898658083629133680231043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229265772055752755786820695 343898658083629133680231043)
      ·
        refine ⟨515847987125443700520346565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343898658083629133680231043 515847987125443700520346565)
        ·
          refine ⟨96721497586020693847564981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 515847987125443700520346565 96721497586020693847564981)
          ·
            refine ⟨9067640398689440048209217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96721497586020693847564981 9067640398689440048209217)
            ·
              refine ⟨6800730299017080036156913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9067640398689440048209217 6800730299017080036156913)
              ·
                refine ⟨5100547724262810027117685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6800730299017080036156913 5100547724262810027117685)
                ·
                  refine ⟨478176349149638440042283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5100547724262810027117685 478176349149638440042283)
                  ·
                    rfl

theorem cell22_4190603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 5].length) (baseStart_4190603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190603 prefixEnd_4190603 := by exact prefixLift 4190603
  have htrace : WordTrace (prefixWord ++ tailWord_4190603) baseStart_4190603 baseEnd_4190603 := by
    simpa [prefixWord, tailWord_4190603, baseEnd_4190603] using wordTrace_append hprefix tailTrace_4190603
  have hstable : (prefixWord ++ tailWord_4190603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190603).length < 2 ^ (prefixWord ++ tailWord_4190603).sum := by decide
  have hdescent : baseEnd_4190603 < baseStart_4190603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190618 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_4190618 : Nat := 118140960795 + 4190618 * 2 ^ 59
def prefixEnd_4190618 : Nat := 4983230072969 + 3 ^ 40 * 4190618 * 2
def baseEnd_4190618 : Nat := 1434534182255460281001803

theorem tailTrace_4190618 : CollatzResearch.WordTrace tailWord_4190618 prefixEnd_4190618 1434534182255460281001803 := by
  unfold tailWord_4190618
  simp only [CollatzResearch.WordTrace]
  refine ⟨38211098783028540354919127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101896263421409440946451005 38211098783028540354919127)
  ·
    refine ⟨57316648174542810532378691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38211098783028540354919127 57316648174542810532378691)
    ·
      refine ⟨85974972261814215798568037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57316648174542810532378691 85974972261814215798568037)
      ·
        refine ⟨16120307299090165462231507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85974972261814215798568037 16120307299090165462231507)
        ·
          refine ⟨24180460948635248193347261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16120307299090165462231507 24180460948635248193347261)
          ·
            refine ⟨9067672855738218072505223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24180460948635248193347261 9067672855738218072505223)
            ·
              refine ⟨13601509283607327108757835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9067672855738218072505223 13601509283607327108757835)
              ·
                refine ⟨20402263925410990663136753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13601509283607327108757835 20402263925410990663136753)
                ·
                  refine ⟨15301697944058242997352565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20402263925410990663136753 15301697944058242997352565)
                  ·
                    refine ⟨1434534182255460281001803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15301697944058242997352565 1434534182255460281001803)
                    ·
                      rfl

theorem cell22_4190618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_4190618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190618 prefixEnd_4190618 := by exact prefixLift 4190618
  have htrace : WordTrace (prefixWord ++ tailWord_4190618) baseStart_4190618 baseEnd_4190618 := by
    simpa [prefixWord, tailWord_4190618, baseEnd_4190618] using wordTrace_append hprefix tailTrace_4190618
  have hstable : (prefixWord ++ tailWord_4190618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190618).length < 2 ^ (prefixWord ++ tailWord_4190618).sum := by decide
  have hdescent : baseEnd_4190618 < baseStart_4190618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190725 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 3, 3]
def baseStart_4190725 : Nat := 118140960795 + 4190725 * 2 ^ 59
def prefixEnd_4190725 : Nat := 4983230072969 + 3 ^ 40 * 4190725 * 2
def baseEnd_4190725 : Nat := 1434570810542147668576475

theorem tailTrace_4190725 : CollatzResearch.WordTrace tailWord_4190725 prefixEnd_4190725 1434570810542147668576475 := by
  unfold tailWord_4190725
  simp only [CollatzResearch.WordTrace]
  refine ⟨152848297742726518693821629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101898865161817679129214419 152848297742726518693821629)
  ·
    refine ⟨57318111653522444510183111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152848297742726518693821629 57318111653522444510183111)
    ·
      refine ⟨85977167480283666765274667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57318111653522444510183111 85977167480283666765274667)
      ·
        refine ⟨128965751220425500147912001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85977167480283666765274667 128965751220425500147912001)
        ·
          refine ⟨96724313415319125110934001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128965751220425500147912001 96724313415319125110934001)
          ·
            refine ⟨72543235061489343833200501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96724313415319125110934001 72543235061489343833200501)
            ·
              refine ⟨6800928287014625984362547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72543235061489343833200501 6800928287014625984362547)
              ·
                refine ⟨10201392430521938976543821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6800928287014625984362547 10201392430521938976543821)
                ·
                  refine ⟨3825522161445727116203933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10201392430521938976543821 3825522161445727116203933)
                  ·
                    refine ⟨1434570810542147668576475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3825522161445727116203933 1434570810542147668576475)
                    ·
                      rfl

theorem cell22_4190725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_4190725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190725 prefixEnd_4190725 := by exact prefixLift 4190725
  have htrace : WordTrace (prefixWord ++ tailWord_4190725) baseStart_4190725 baseEnd_4190725 := by
    simpa [prefixWord, tailWord_4190725, baseEnd_4190725] using wordTrace_append hprefix tailTrace_4190725
  have hstable : (prefixWord ++ tailWord_4190725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190725).length < 2 ^ (prefixWord ++ tailWord_4190725).sum := by decide
  have hdescent : baseEnd_4190725 < baseStart_4190725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190783 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 6]
def baseStart_4190783 : Nat := 118140960795 + 4190783 * 2 ^ 59
def prefixEnd_4190783 : Nat := 4983230072969 + 3 ^ 40 * 4190783 * 2
def baseEnd_4190783 : Nat := 478196888375818283542099

theorem tailTrace_4190783 : CollatzResearch.WordTrace tailWord_4190783 prefixEnd_4190783 478196888375818283542099 := by
  unfold tailWord_4190783
  simp only [CollatzResearch.WordTrace]
  refine ⟨152850413176516394599433003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101900275451010929732955335 152850413176516394599433003)
  ·
    refine ⟨229275619764774591899149505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152850413176516394599433003 229275619764774591899149505)
    ·
      refine ⟨171956714823580943924362129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229275619764774591899149505 171956714823580943924362129)
      ·
        refine ⟨128967536117685707943271597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171956714823580943924362129 128967536117685707943271597)
        ·
          refine ⟨48362826044132140478726849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128967536117685707943271597 48362826044132140478726849)
          ·
            refine ⟨36272119533099105359045137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48362826044132140478726849 36272119533099105359045137)
            ·
              refine ⟨27204089649824329019283853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36272119533099105359045137 27204089649824329019283853)
              ·
                refine ⟨10201533618684123382231445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27204089649824329019283853 10201533618684123382231445)
                ·
                  refine ⟨478196888375818283542099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10201533618684123382231445 478196888375818283542099)
                  ·
                    rfl

theorem cell22_4190783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 6].length) (baseStart_4190783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190783 prefixEnd_4190783 := by exact prefixLift 4190783
  have htrace : WordTrace (prefixWord ++ tailWord_4190783) baseStart_4190783 baseEnd_4190783 := by
    simpa [prefixWord, tailWord_4190783, baseEnd_4190783] using wordTrace_append hprefix tailTrace_4190783
  have hstable : (prefixWord ++ tailWord_4190783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190783).length < 2 ^ (prefixWord ++ tailWord_4190783).sum := by decide
  have hdescent : baseEnd_4190783 < baseStart_4190783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190785 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 3, 4]
def baseStart_4190785 : Nat := 118140960795 + 4190785 * 2 ^ 59
def prefixEnd_4190785 : Nat := 4983230072969 + 3 ^ 40 * 4190785 * 2
def baseEnd_4190785 : Nat := 1434591349768327512076291

theorem tailTrace_4190785 : CollatzResearch.WordTrace tailWord_4190785 prefixEnd_4190785 1434591349768327512076291 := by
  unfold tailWord_4190785
  simp only [CollatzResearch.WordTrace]
  refine ⟨152850486122509148941005809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101900324081672765960670539 152850486122509148941005809)
  ·
    refine ⟨114637864591881861705754357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152850486122509148941005809 114637864591881861705754357)
    ·
      refine ⟨10747299805488924534914471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114637864591881861705754357 10747299805488924534914471)
      ·
        refine ⟨16120949708233386802371707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10747299805488924534914471 16120949708233386802371707)
        ·
          refine ⟨24181424562350080203557561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16120949708233386802371707 24181424562350080203557561)
          ·
            refine ⟨18136068421762560152668171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24181424562350080203557561 18136068421762560152668171)
            ·
              refine ⟨27204102632643840229002257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18136068421762560152668171 27204102632643840229002257)
              ·
                refine ⟨20403076974482880171751693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27204102632643840229002257 20403076974482880171751693)
                ·
                  refine ⟨7651153865431080064406885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20403076974482880171751693 7651153865431080064406885)
                  ·
                    refine ⟨1434591349768327512076291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7651153865431080064406885 1434591349768327512076291)
                    ·
                      rfl

theorem cell22_4190785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_4190785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190785 prefixEnd_4190785 := by exact prefixLift 4190785
  have htrace : WordTrace (prefixWord ++ tailWord_4190785) baseStart_4190785 baseEnd_4190785 := by
    simpa [prefixWord, tailWord_4190785, baseEnd_4190785] using wordTrace_append hprefix tailTrace_4190785
  have hstable : (prefixWord ++ tailWord_4190785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190785).length < 2 ^ (prefixWord ++ tailWord_4190785).sum := by decide
  have hdescent : baseEnd_4190785 < baseStart_4190785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190817 : List Nat := [1, 2, 3, 1, 1, 5, 2, 3, 4]
def baseStart_4190817 : Nat := 118140960795 + 4190817 * 2 ^ 59
def prefixEnd_4190817 : Nat := 4983230072969 + 3 ^ 40 * 4190817 * 2
def baseEnd_4190817 : Nat := 478200768007430031758731

theorem tailTrace_4190817 : CollatzResearch.WordTrace tailWord_4190817 prefixEnd_4190817 478200768007430031758731 := by
  unfold tailWord_4190817
  simp only [CollatzResearch.WordTrace]
  refine ⟨152851653258393218406170705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101901102172262145604113803 152851653258393218406170705)
  ·
    refine ⟨114638739943794913804628029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152851653258393218406170705 114638739943794913804628029)
    ·
      refine ⟨42989527478923092676735511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114638739943794913804628029 42989527478923092676735511)
      ·
        refine ⟨64484291218384639015103267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42989527478923092676735511 64484291218384639015103267)
        ·
          refine ⟨96726436827576958522654901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64484291218384639015103267 96726436827576958522654901)
          ·
            refine ⟨9068103452585339861498897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96726436827576958522654901 9068103452585339861498897)
            ·
              refine ⟨6801077589439004896124173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9068103452585339861498897 6801077589439004896124173)
              ·
                refine ⟨2550404096039626836046565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6801077589439004896124173 2550404096039626836046565)
                ·
                  refine ⟨478200768007430031758731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2550404096039626836046565 478200768007430031758731)
                  ·
                    rfl

theorem cell22_4190817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 4].length) (baseStart_4190817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190817 prefixEnd_4190817 := by exact prefixLift 4190817
  have htrace : WordTrace (prefixWord ++ tailWord_4190817) baseStart_4190817 baseEnd_4190817 := by
    simpa [prefixWord, tailWord_4190817, baseEnd_4190817] using wordTrace_append hprefix tailTrace_4190817
  have hstable : (prefixWord ++ tailWord_4190817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190817).length < 2 ^ (prefixWord ++ tailWord_4190817).sum := by decide
  have hdescent : baseEnd_4190817 < baseStart_4190817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190832 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 4, 3]
def baseStart_4190832 : Nat := 118140960795 + 4190832 * 2 ^ 59
def prefixEnd_4190832 : Nat := 4983230072969 + 3 ^ 40 * 4190832 * 2
def baseEnd_4190832 : Nat := 1434607438828835056151147

theorem tailTrace_4190832 : CollatzResearch.WordTrace tailWord_4190832 prefixEnd_4190832 1434607438828835056151147 := by
  unfold tailWord_4190832
  simp only [CollatzResearch.WordTrace]
  refine ⟨76426100176669437983983375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101901466902225917311977833 76426100176669437983983375)
  ·
    refine ⟨114639150265004156975975063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76426100176669437983983375 114639150265004156975975063)
    ·
      refine ⟨171958725397506235463962595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114639150265004156975975063 171958725397506235463962595)
      ·
        refine ⟨257938088096259353195943893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171958725397506235463962595 257938088096259353195943893)
        ·
          refine ⟨6045423939756078590529935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 257938088096259353195943893 6045423939756078590529935)
          ·
            refine ⟨9068135909634117885794903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6045423939756078590529935 9068135909634117885794903)
            ·
              refine ⟨13602203864451176828692355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9068135909634117885794903 13602203864451176828692355)
              ·
                refine ⟨20403305796676765243038533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13602203864451176828692355 20403305796676765243038533)
                ·
                  refine ⟨3825619836876893483069725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20403305796676765243038533 3825619836876893483069725)
                  ·
                    refine ⟨1434607438828835056151147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3825619836876893483069725 1434607438828835056151147)
                    ·
                      rfl

theorem cell22_4190832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 4, 3].length) (baseStart_4190832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190832 prefixEnd_4190832 := by exact prefixLift 4190832
  have htrace : WordTrace (prefixWord ++ tailWord_4190832) baseStart_4190832 baseEnd_4190832 := by
    simpa [prefixWord, tailWord_4190832, baseEnd_4190832] using wordTrace_append hprefix tailTrace_4190832
  have hstable : (prefixWord ++ tailWord_4190832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190832).length < 2 ^ (prefixWord ++ tailWord_4190832).sum := by decide
  have hdescent : baseEnd_4190832 < baseStart_4190832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190849 : List Nat := [1, 2, 4, 2, 1, 1, 5, 1, 2, 3]
def baseStart_4190849 : Nat := 118140960795 + 4190849 * 2 ^ 59
def prefixEnd_4190849 : Nat := 4983230072969 + 3 ^ 40 * 4190849 * 2
def baseEnd_4190849 : Nat := 1434613258276252678476095

theorem tailTrace_4190849 : CollatzResearch.WordTrace tailWord_4190849 prefixEnd_4190849 1434613258276252678476095 := by
  unfold tailWord_4190849
  simp only [CollatzResearch.WordTrace]
  refine ⟨152852820394277287871335601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101901880262851525247557067 152852820394277287871335601)
  ·
    refine ⟨114639615295707965903501701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152852820394277287871335601 114639615295707965903501701)
    ·
      refine ⟨21494927867945243606906569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114639615295707965903501701 21494927867945243606906569)
      ·
        refine ⟨16121195900958932705179927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21494927867945243606906569 16121195900958932705179927)
        ·
          refine ⟨24181793851438399057769891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16121195900958932705179927 24181793851438399057769891)
          ·
            refine ⟨36272690777157598586654837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24181793851438399057769891 36272690777157598586654837)
            ·
              refine ⟨3400564760358524867498891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36272690777157598586654837 3400564760358524867498891)
              ·
                refine ⟨5100847140537787301248337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400564760358524867498891 5100847140537787301248337)
                ·
                  refine ⟨3825635355403340475936253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5100847140537787301248337 3825635355403340475936253)
                  ·
                    refine ⟨1434613258276252678476095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3825635355403340475936253 1434613258276252678476095)
                    ·
                      rfl

theorem cell22_4190849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_4190849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190849 prefixEnd_4190849 := by exact prefixLift 4190849
  have htrace : WordTrace (prefixWord ++ tailWord_4190849) baseStart_4190849 baseEnd_4190849 := by
    simpa [prefixWord, tailWord_4190849, baseEnd_4190849] using wordTrace_append hprefix tailTrace_4190849
  have hstable : (prefixWord ++ tailWord_4190849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190849).length < 2 ^ (prefixWord ++ tailWord_4190849).sum := by decide
  have hdescent : baseEnd_4190849 < baseStart_4190849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190860 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 5, 3]
def baseStart_4190860 : Nat := 118140960795 + 4190860 * 2 ^ 59
def prefixEnd_4190860 : Nat := 4983230072969 + 3 ^ 40 * 4190860 * 2
def baseEnd_4190860 : Nat := 1434617023801052316451061

theorem tailTrace_4190860 : CollatzResearch.WordTrace tailWord_4190860 prefixEnd_4190860 1434617023801052316451061 := by
  unfold tailWord_4190860
  simp only [CollatzResearch.WordTrace]
  refine ⟨76426610798618718374993017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101902147731491624499990689 76426610798618718374993017)
  ·
    refine ⟨57319958098964038781244763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76426610798618718374993017 57319958098964038781244763)
    ·
      refine ⟨85979937148446058171867145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57319958098964038781244763 85979937148446058171867145)
      ·
        refine ⟨64484952861334543628900359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85979937148446058171867145 64484952861334543628900359)
        ·
          refine ⟨96727429292001815443350539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64484952861334543628900359 96727429292001815443350539)
          ·
            refine ⟨145091143938002723165025809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96727429292001815443350539 145091143938002723165025809)
            ·
              refine ⟨108818357953502042373769357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145091143938002723165025809 108818357953502042373769357)
              ·
                refine ⟨40806884232563265890163509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108818357953502042373769357 40806884232563265890163509)
                ·
                  refine ⟨3825645396802806177202829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40806884232563265890163509 3825645396802806177202829)
                  ·
                    refine ⟨1434617023801052316451061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3825645396802806177202829 1434617023801052316451061)
                    ·
                      rfl

theorem cell22_4190860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_4190860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190860 prefixEnd_4190860 := by exact prefixLift 4190860
  have htrace : WordTrace (prefixWord ++ tailWord_4190860) baseStart_4190860 baseEnd_4190860 := by
    simpa [prefixWord, tailWord_4190860, baseEnd_4190860] using wordTrace_append hprefix tailTrace_4190860
  have hstable : (prefixWord ++ tailWord_4190860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190860).length < 2 ^ (prefixWord ++ tailWord_4190860).sum := by decide
  have hdescent : baseEnd_4190860 < baseStart_4190860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190873 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 9]
def baseStart_4190873 : Nat := 118140960795 + 4190873 * 2 ^ 59
def prefixEnd_4190873 : Nat := 4983230072969 + 3 ^ 40 * 4190873 * 2
def baseEnd_4190873 : Nat := 478207157988908205292007

theorem tailTrace_4190873 : CollatzResearch.WordTrace tailWord_4190873 prefixEnd_4190873 478207157988908205292007 := by
  unfold tailWord_4190873
  simp only [CollatzResearch.WordTrace]
  refine ⟨152853695746190339970209273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101902463830793559980139515 152853695746190339970209273)
  ·
    refine ⟨114640271809642754977656955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152853695746190339970209273 114640271809642754977656955)
    ·
      refine ⟨171960407714464132466485433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114640271809642754977656955 171960407714464132466485433)
      ·
        refine ⟨128970305785848099349864075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171960407714464132466485433 128970305785848099349864075)
        ·
          refine ⟨193455458678772149024796113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128970305785848099349864075 193455458678772149024796113)
          ·
            refine ⟨145091594009079111768597085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193455458678772149024796113 145091594009079111768597085)
            ·
              refine ⟨54409347753404666913223907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145091594009079111768597085 54409347753404666913223907)
              ·
                refine ⟨81614021630107000369835861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54409347753404666913223907 81614021630107000369835861)
                ·
                  refine ⟨478207157988908205292007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81614021630107000369835861 478207157988908205292007)
                  ·
                    rfl

theorem cell22_4190873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_4190873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4190873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4190873 prefixEnd_4190873 := by exact prefixLift 4190873
  have htrace : WordTrace (prefixWord ++ tailWord_4190873) baseStart_4190873 baseEnd_4190873 := by
    simpa [prefixWord, tailWord_4190873, baseEnd_4190873] using wordTrace_append hprefix tailTrace_4190873
  have hstable : (prefixWord ++ tailWord_4190873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190873).length < 2 ^ (prefixWord ++ tailWord_4190873).sum := by decide
  have hdescent : baseEnd_4190873 < baseStart_4190873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191018 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 1, 5]
def baseStart_4191018 : Nat := 118140960795 + 4191018 * 2 ^ 59
def prefixEnd_4191018 : Nat := 4983230072969 + 3 ^ 40 * 4191018 * 2
def baseEnd_4191018 : Nat := 1434671110429992571000577

theorem tailTrace_4191018 : CollatzResearch.WordTrace tailWord_4191018 prefixEnd_4191018 1434671110429992571000577 := by
  unfold tailWord_4191018
  simp only [CollatzResearch.WordTrace]
  refine ⟨38214746082666257433559427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101905989553776686489491805 38214746082666257433559427)
  ·
    refine ⟨57322119123999386150339141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38214746082666257433559427 57322119123999386150339141)
    ·
      refine ⟨10747897335749884903188589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57322119123999386150339141 10747897335749884903188589)
      ·
        refine ⟨4030461500906206838695721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10747897335749884903188589 4030461500906206838695721)
        ·
          refine ⟨3022846125679655129021791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4030461500906206838695721 3022846125679655129021791)
          ·
            refine ⟨4534269188519482693532687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022846125679655129021791 4534269188519482693532687)
            ·
              refine ⟨6801403782779224040299031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4534269188519482693532687 6801403782779224040299031)
              ·
                refine ⟨10202105674168836060448547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6801403782779224040299031 10202105674168836060448547)
                ·
                  refine ⟨15303158511253254090672821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10202105674168836060448547 15303158511253254090672821)
                  ·
                    refine ⟨1434671110429992571000577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15303158511253254090672821 1434671110429992571000577)
                    ·
                      rfl

theorem cell22_4191018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_4191018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191018 prefixEnd_4191018 := by exact prefixLift 4191018
  have htrace : WordTrace (prefixWord ++ tailWord_4191018) baseStart_4191018 baseEnd_4191018 := by
    simpa [prefixWord, tailWord_4191018, baseEnd_4191018] using wordTrace_append hprefix tailTrace_4191018
  have hstable : (prefixWord ++ tailWord_4191018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191018).length < 2 ^ (prefixWord ++ tailWord_4191018).sum := by decide
  have hdescent : baseEnd_4191018 < baseStart_4191018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191029 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 3, 3]
def baseStart_4191029 : Nat := 118140960795 + 4191029 * 2 ^ 59
def prefixEnd_4191029 : Nat := 4983230072969 + 3 ^ 40 * 4191029 * 2
def baseEnd_4191029 : Nat := 1434674875954792208975543

theorem tailTrace_4191029 : CollatzResearch.WordTrace tailWord_4191029 prefixEnd_4191029 1434674875954792208975543 := by
  unfold tailWord_4191029
  simp only [CollatzResearch.WordTrace]
  refine ⟨152859385533625178612888141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101906257022416785741925427 152859385533625178612888141)
  ·
    refine ⟨57322269575109441979833053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152859385533625178612888141 57322269575109441979833053)
    ·
      refine ⟨21495851090666040742437395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57322269575109441979833053 21495851090666040742437395)
      ·
        refine ⟨32243776635999061113656093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21495851090666040742437395 32243776635999061113656093)
        ·
          refine ⟨12091416238499647917621035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32243776635999061113656093 12091416238499647917621035)
          ·
            refine ⟨18137124357749471876431553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12091416238499647917621035 18137124357749471876431553)
            ·
              refine ⟨13602843268312103907323665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18137124357749471876431553 13602843268312103907323665)
              ·
                refine ⟨10202132451234077930492749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13602843268312103907323665 10202132451234077930492749)
                ·
                  refine ⟨3825799669212779223934781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10202132451234077930492749 3825799669212779223934781)
                  ·
                    refine ⟨1434674875954792208975543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3825799669212779223934781 1434674875954792208975543)
                    ·
                      rfl

theorem cell22_4191029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_4191029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191029 prefixEnd_4191029 := by exact prefixLift 4191029
  have htrace : WordTrace (prefixWord ++ tailWord_4191029) baseStart_4191029 baseEnd_4191029 := by
    simpa [prefixWord, tailWord_4191029, baseEnd_4191029] using wordTrace_append hprefix tailTrace_4191029
  have hstable : (prefixWord ++ tailWord_4191029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191029).length < 2 ^ (prefixWord ++ tailWord_4191029).sum := by decide
  have hdescent : baseEnd_4191029 < baseStart_4191029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191040 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 1, 7]
def baseStart_4191040 : Nat := 118140960795 + 4191040 * 2 ^ 59
def prefixEnd_4191040 : Nat := 4983230072969 + 3 ^ 40 * 4191040 * 2
def baseEnd_4191040 : Nat := 1434678641479591846950509

theorem tailTrace_4191040 : CollatzResearch.WordTrace tailWord_4191040 prefixEnd_4191040 1434678641479591846950509 := by
  unfold tailWord_4191040
  simp only [CollatzResearch.WordTrace]
  refine ⟨76429893368292663745769287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101906524491056884994359049 76429893368292663745769287)
  ·
    refine ⟨114644840052438995618653931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76429893368292663745769287 114644840052438995618653931)
    ·
      refine ⟨171967260078658493427980897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114644840052438995618653931 171967260078658493427980897)
      ·
        refine ⟨128975445058993870070985673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171967260078658493427980897 128975445058993870070985673)
        ·
          refine ⟨96731583794245402553239255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128975445058993870070985673 96731583794245402553239255)
          ·
            refine ⟨145097375691368103829858883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96731583794245402553239255 145097375691368103829858883)
            ·
              refine ⟨217646063537052155744788325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145097375691368103829858883 217646063537052155744788325)
              ·
                refine ⟨40808636913197279202147811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217646063537052155744788325 40808636913197279202147811)
                ·
                  refine ⟨61212955369795918803221717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40808636913197279202147811 61212955369795918803221717)
                  ·
                    refine ⟨1434678641479591846950509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61212955369795918803221717 1434678641479591846950509)
                    ·
                      rfl

theorem cell22_4191040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_4191040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191040 prefixEnd_4191040 := by exact prefixLift 4191040
  have htrace : WordTrace (prefixWord ++ tailWord_4191040) baseStart_4191040 baseEnd_4191040 := by
    simpa [prefixWord, tailWord_4191040, baseEnd_4191040] using wordTrace_append hprefix tailTrace_4191040
  have hstable : (prefixWord ++ tailWord_4191040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191040).length < 2 ^ (prefixWord ++ tailWord_4191040).sum := by decide
  have hdescent : baseEnd_4191040 < baseStart_4191040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191063 : List Nat := [1, 1, 3, 2, 4, 2, 3, 2, 1, 3]
def baseStart_4191063 : Nat := 118140960795 + 4191063 * 2 ^ 59
def prefixEnd_4191063 : Nat := 4983230072969 + 3 ^ 40 * 4191063 * 2
def baseEnd_4191063 : Nat := 1434686514849627453625439

theorem tailTrace_4191063 : CollatzResearch.WordTrace tailWord_4191063 prefixEnd_4191063 1434686514849627453625439 := by
  unfold tailWord_4191063
  simp only [CollatzResearch.WordTrace]
  refine ⟨152860625615502002419625843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101907083743668001613083895 152860625615502002419625843)
  ·
    refine ⟨229290938423253003629438765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152860625615502002419625843 229290938423253003629438765)
    ·
      refine ⟨85984101908719876361039537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229290938423253003629438765 85984101908719876361039537)
      ·
        refine ⟨64488076431539907270779653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85984101908719876361039537 64488076431539907270779653)
        ·
          refine ⟨12091514330913732613271185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64488076431539907270779653 12091514330913732613271185)
          ·
            refine ⟨9068635748185299459953389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12091514330913732613271185 9068635748185299459953389)
            ·
              refine ⟨3400738405569487297482521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9068635748185299459953389 3400738405569487297482521)
              ·
                refine ⟨2550553804177115473111891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400738405569487297482521 2550553804177115473111891)
                ·
                  refine ⟨3825830706265673209667837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550553804177115473111891 3825830706265673209667837)
                  ·
                    refine ⟨1434686514849627453625439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3825830706265673209667837 1434686514849627453625439)
                    ·
                      rfl

theorem cell22_4191063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_4191063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191063 prefixEnd_4191063 := by exact prefixLift 4191063
  have htrace : WordTrace (prefixWord ++ tailWord_4191063) baseStart_4191063 baseEnd_4191063 := by
    simpa [prefixWord, tailWord_4191063, baseEnd_4191063] using wordTrace_append hprefix tailTrace_4191063
  have hstable : (prefixWord ++ tailWord_4191063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191063).length < 2 ^ (prefixWord ++ tailWord_4191063).sum := by decide
  have hdescent : baseEnd_4191063 < baseStart_4191063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191072 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 3, 4]
def baseStart_4191072 : Nat := 118140960795 + 4191072 * 2 ^ 59
def prefixEnd_4191072 : Nat := 4983230072969 + 3 ^ 40 * 4191072 * 2
def baseEnd_4191072 : Nat := 1434689595733554430150411

theorem tailTrace_4191072 : CollatzResearch.WordTrace tailWord_4191072 prefixEnd_4191072 1434689595733554430150411 := by
  unfold tailWord_4191072
  simp only [CollatzResearch.WordTrace]
  refine ⟨76430476936234698478351735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101907302581646264637802313 76430476936234698478351735)
  ·
    refine ⟨114645715404352047717527603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76430476936234698478351735 114645715404352047717527603)
    ·
      refine ⟨171968573106528071576291405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114645715404352047717527603 171968573106528071576291405)
      ·
        refine ⟨64488214914948026841109277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171968573106528071576291405 64488214914948026841109277)
        ·
          refine ⟨24183080593105510065415979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64488214914948026841109277 24183080593105510065415979)
          ·
            refine ⟨36274620889658265098123969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24183080593105510065415979 36274620889658265098123969)
            ·
              refine ⟨27205965667243698823592977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36274620889658265098123969 27205965667243698823592977)
              ·
                refine ⟨20404474250432774117694733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27205965667243698823592977 20404474250432774117694733)
                ·
                  refine ⟨7651677843912290294135525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20404474250432774117694733 7651677843912290294135525)
                  ·
                    refine ⟨1434689595733554430150411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7651677843912290294135525 1434689595733554430150411)
                    ·
                      rfl

theorem cell22_4191072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_4191072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191072 prefixEnd_4191072 := by exact prefixLift 4191072
  have htrace : WordTrace (prefixWord ++ tailWord_4191072) baseStart_4191072 baseEnd_4191072 := by
    simpa [prefixWord, tailWord_4191072, baseEnd_4191072] using wordTrace_append hprefix tailTrace_4191072
  have hstable : (prefixWord ++ tailWord_4191072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191072).length < 2 ^ (prefixWord ++ tailWord_4191072).sum := by decide
  have hdescent : baseEnd_4191072 < baseStart_4191072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191076 : List Nat := [2, 3, 1, 1, 4, 3, 2, 1, 5]
def baseStart_4191076 : Nat := 118140960795 + 4191076 * 2 ^ 59
def prefixEnd_4191076 : Nat := 4983230072969 + 3 ^ 40 * 4191076 * 2
def baseEnd_4191076 : Nat := 478230321671766584350133

theorem tailTrace_4191076 : CollatzResearch.WordTrace tailWord_4191076 prefixEnd_4191076 478230321671766584350133 := by
  unfold tailWord_4191076
  simp only [CollatzResearch.WordTrace]
  refine ⟨76430549882227452819924541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101907399842969937093232721 76430549882227452819924541)
  ·
    refine ⟨28661456205835294807471703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76430549882227452819924541 28661456205835294807471703)
    ·
      refine ⟨42992184308752942211207555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28661456205835294807471703 42992184308752942211207555)
      ·
        refine ⟨64488276463129413316811333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42992184308752942211207555 64488276463129413316811333)
        ·
          refine ⟨12091551836836764996902125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64488276463129413316811333 12091551836836764996902125)
          ·
            refine ⟨4534331938813786873838297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12091551836836764996902125 4534331938813786873838297)
            ·
              refine ⟨3400748954110340155378723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4534331938813786873838297 3400748954110340155378723)
              ·
                refine ⟨5101123431165510233068085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400748954110340155378723 5101123431165510233068085)
                ·
                  refine ⟨478230321671766584350133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5101123431165510233068085 478230321671766584350133)
                  ·
                    rfl

theorem cell22_4191076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_4191076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191076 prefixEnd_4191076 := by exact prefixLift 4191076
  have htrace : WordTrace (prefixWord ++ tailWord_4191076) baseStart_4191076 baseEnd_4191076 := by
    simpa [prefixWord, tailWord_4191076, baseEnd_4191076] using wordTrace_append hprefix tailTrace_4191076
  have hstable : (prefixWord ++ tailWord_4191076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191076).length < 2 ^ (prefixWord ++ tailWord_4191076).sum := by decide
  have hdescent : baseEnd_4191076 < baseStart_4191076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191089 : List Nat := [1, 2, 2, 2, 1, 4, 3, 2, 1, 4]
def baseStart_4191089 : Nat := 118140960795 + 4191089 * 2 ^ 59
def prefixEnd_4191089 : Nat := 4983230072969 + 3 ^ 40 * 4191089 * 2
def baseEnd_4191089 : Nat := 1434695415180972052475359

theorem tailTrace_4191089 : CollatzResearch.WordTrace tailWord_4191089 prefixEnd_4191089 1434695415180972052475359 := by
  unfold tailWord_4191089
  simp only [CollatzResearch.WordTrace]
  refine ⟨152861573913407808860072321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101907715942271872573381547 152861573913407808860072321)
  ·
    refine ⟨114646180435055856645054241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152861573913407808860072321 114646180435055856645054241)
    ·
      refine ⟨85984635326291892483790681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114646180435055856645054241 85984635326291892483790681)
      ·
        refine ⟨64488476494718919362843011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85984635326291892483790681 64488476494718919362843011)
        ·
          refine ⟨96732714742078379044264517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64488476494718919362843011 96732714742078379044264517)
          ·
            refine ⟨18137384014139696070799597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96732714742078379044264517 18137384014139696070799597)
            ·
              refine ⟨6801519005302386026549849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18137384014139696070799597 6801519005302386026549849)
              ·
                refine ⟨5101139253976789519912387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6801519005302386026549849 5101139253976789519912387)
                ·
                  refine ⟨7651708880965184279868581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5101139253976789519912387 7651708880965184279868581)
                  ·
                    refine ⟨1434695415180972052475359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7651708880965184279868581 1434695415180972052475359)
                    ·
                      rfl

theorem cell22_4191089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_4191089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191089 prefixEnd_4191089 := by exact prefixLift 4191089
  have htrace : WordTrace (prefixWord ++ tailWord_4191089) baseStart_4191089 baseEnd_4191089 := by
    simpa [prefixWord, tailWord_4191089, baseEnd_4191089] using wordTrace_append hprefix tailTrace_4191089
  have hstable : (prefixWord ++ tailWord_4191089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191089).length < 2 ^ (prefixWord ++ tailWord_4191089).sum := by decide
  have hdescent : baseEnd_4191089 < baseStart_4191089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191271 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 3, 5]
def baseStart_4191271 : Nat := 118140960795 + 4191271 * 2 ^ 59
def prefixEnd_4191271 : Nat := 4983230072969 + 3 ^ 40 * 4191271 * 2
def baseEnd_4191271 : Nat := 1434757717500384244424801

theorem tailTrace_4191271 : CollatzResearch.WordTrace tailWord_4191271 prefixEnd_4191271 1434757717500384244424801 := by
  unfold tailWord_4191271
  simp only [CollatzResearch.WordTrace]
  refine ⟨152868211998748453943197667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101912141332498969295465111 152868211998748453943197667)
  ·
    refine ⟨229302317998122680914796501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152868211998748453943197667 229302317998122680914796501)
    ·
      refine ⟨5374273078081000333940543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 229302317998122680914796501 5374273078081000333940543)
      ·
        refine ⟨8061409617121500500910815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5374273078081000333940543 8061409617121500500910815)
        ·
          refine ⟨12092114425682250751366223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8061409617121500500910815 12092114425682250751366223)
          ·
            refine ⟨18138171638523376127049335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12092114425682250751366223 18138171638523376127049335)
            ·
              refine ⟨27207257457785064190574003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18138171638523376127049335 27207257457785064190574003)
              ·
                refine ⟨40810886186677596285861005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27207257457785064190574003 40810886186677596285861005)
                ·
                  refine ⟨15304082320004098607197877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40810886186677596285861005 15304082320004098607197877)
                  ·
                    refine ⟨1434757717500384244424801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15304082320004098607197877 1434757717500384244424801)
                    ·
                      rfl

theorem cell22_4191271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_4191271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191271 prefixEnd_4191271 := by exact prefixLift 4191271
  have htrace : WordTrace (prefixWord ++ tailWord_4191271) baseStart_4191271 baseEnd_4191271 := by
    simpa [prefixWord, tailWord_4191271, baseEnd_4191271] using wordTrace_append hprefix tailTrace_4191271
  have hstable : (prefixWord ++ tailWord_4191271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191271).length < 2 ^ (prefixWord ++ tailWord_4191271).sum := by decide
  have hdescent : baseEnd_4191271 < baseStart_4191271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191288 : List Nat := [2, 1, 2, 1, 5, 2, 2, 2, 2, 3]
def baseStart_4191288 : Nat := 118140960795 + 4191288 * 2 ^ 59
def prefixEnd_4191288 : Nat := 4983230072969 + 3 ^ 40 * 4191288 * 2
def baseEnd_4191288 : Nat := 1434763536947801866749749

theorem tailTrace_4191288 : CollatzResearch.WordTrace tailWord_4191288 prefixEnd_4191288 1434763536947801866749749 := by
  unfold tailWord_4191288
  simp only [CollatzResearch.WordTrace]
  refine ⟨76434416019843432923283259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101912554693124577231044345 76434416019843432923283259)
  ·
    refine ⟨114651624029765149384924889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76434416019843432923283259 114651624029765149384924889)
    ·
      refine ⟨85988718022323862038693667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114651624029765149384924889 85988718022323862038693667)
      ·
        refine ⟨128983077033485793058040501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85988718022323862038693667 128983077033485793058040501)
        ·
          refine ⟨12092163471889293099191297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128983077033485793058040501 12092163471889293099191297)
          ·
            refine ⟨9069122603916969824393473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12092163471889293099191297 9069122603916969824393473)
            ·
              refine ⟨6801841952937727368295105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9069122603916969824393473 6801841952937727368295105)
              ·
                refine ⟨5101381464703295526221329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6801841952937727368295105 5101381464703295526221329)
                ·
                  refine ⟨3826036098527471644665997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5101381464703295526221329 3826036098527471644665997)
                  ·
                    refine ⟨1434763536947801866749749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3826036098527471644665997 1434763536947801866749749)
                    ·
                      rfl

theorem cell22_4191288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_4191288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191288 prefixEnd_4191288 := by exact prefixLift 4191288
  have htrace : WordTrace (prefixWord ++ tailWord_4191288) baseStart_4191288 baseEnd_4191288 := by
    simpa [prefixWord, tailWord_4191288, baseEnd_4191288] using wordTrace_append hprefix tailTrace_4191288
  have hstable : (prefixWord ++ tailWord_4191288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191288).length < 2 ^ (prefixWord ++ tailWord_4191288).sum := by decide
  have hdescent : baseEnd_4191288 < baseStart_4191288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191316 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_4191316 : Nat := 118140960795 + 4191316 * 2 ^ 59
def prefixEnd_4191316 : Nat := 4983230072969 + 3 ^ 40 * 4191316 * 2
def baseEnd_4191316 : Nat := 1434773121920019127049663

theorem tailTrace_4191316 : CollatzResearch.WordTrace tailWord_4191316 prefixEnd_4191316 1434773121920019127049663 := by
  unfold tailWord_4191316
  simp only [CollatzResearch.WordTrace]
  refine ⟨76434926641792713314292901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101913235522390284419057201 76434926641792713314292901)
  ·
    refine ⟨14331548745336133746429919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76434926641792713314292901 14331548745336133746429919)
    ·
      refine ⟨21497323118004200619644879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14331548745336133746429919 21497323118004200619644879)
      ·
        refine ⟨32245984677006300929467319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21497323118004200619644879 32245984677006300929467319)
        ·
          refine ⟨48368977015509451394200979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32245984677006300929467319 48368977015509451394200979)
          ·
            refine ⟨72553465523264177091301469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48368977015509451394200979 72553465523264177091301469)
            ·
              refine ⟨27207549571224066409238051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72553465523264177091301469 27207549571224066409238051)
              ·
                refine ⟨40811324356836099613857077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27207549571224066409238051 40811324356836099613857077)
                ·
                  refine ⟨3826061658453384338799101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40811324356836099613857077 3826061658453384338799101)
                  ·
                    refine ⟨1434773121920019127049663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3826061658453384338799101 1434773121920019127049663)
                    ·
                      rfl

theorem cell22_4191316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_4191316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191316 prefixEnd_4191316 := by exact prefixLift 4191316
  have htrace : WordTrace (prefixWord ++ tailWord_4191316) baseStart_4191316 baseEnd_4191316 := by
    simpa [prefixWord, tailWord_4191316, baseEnd_4191316] using wordTrace_append hprefix tailTrace_4191316
  have hstable : (prefixWord ++ tailWord_4191316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191316).length < 2 ^ (prefixWord ++ tailWord_4191316).sum := by decide
  have hdescent : baseEnd_4191316 < baseStart_4191316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191344 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 4, 5]
def baseStart_4191344 : Nat := 118140960795 + 4191344 * 2 ^ 59
def prefixEnd_4191344 : Nat := 4983230072969 + 3 ^ 40 * 4191344 * 2
def baseEnd_4191344 : Nat := 1434782706892236387349577

theorem tailTrace_4191344 : CollatzResearch.WordTrace tailWord_4191344 prefixEnd_4191344 1434782706892236387349577 := by
  unfold tailWord_4191344
  simp only [CollatzResearch.WordTrace]
  refine ⟨76435437263741993705302543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101913916351655991607070057 76435437263741993705302543)
  ·
    refine ⟨114653155895612990557953815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76435437263741993705302543 114653155895612990557953815)
    ·
      refine ⟨171979733843419485836930723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114653155895612990557953815 171979733843419485836930723)
      ·
        refine ⟨257969600765129228755396085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171979733843419485836930723 257969600765129228755396085)
        ·
          refine ⟨24184650071730865195818383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257969600765129228755396085 24184650071730865195818383)
          ·
            refine ⟨36276975107596297793727575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24184650071730865195818383 36276975107596297793727575)
            ·
              refine ⟨54415462661394446690591363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36276975107596297793727575 54415462661394446690591363)
              ·
                refine ⟨81623193992091670035887045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54415462661394446690591363 81623193992091670035887045)
                ·
                  refine ⟨15304348873517188131728821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81623193992091670035887045 15304348873517188131728821)
                  ·
                    refine ⟨1434782706892236387349577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15304348873517188131728821 1434782706892236387349577)
                    ·
                      rfl

theorem cell22_4191344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_4191344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191344 prefixEnd_4191344 := by exact prefixLift 4191344
  have htrace : WordTrace (prefixWord ++ tailWord_4191344) baseStart_4191344 baseEnd_4191344 := by
    simpa [prefixWord, tailWord_4191344, baseEnd_4191344] using wordTrace_append hprefix tailTrace_4191344
  have hstable : (prefixWord ++ tailWord_4191344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191344).length < 2 ^ (prefixWord ++ tailWord_4191344).sum := by decide
  have hdescent : baseEnd_4191344 < baseStart_4191344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191350 : List Nat := [5, 1, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_4191350 : Nat := 118140960795 + 4191350 * 2 ^ 59
def prefixEnd_4191350 : Nat := 4983230072969 + 3 ^ 40 * 4191350 * 2
def baseEnd_4191350 : Nat := 1434784760814854371699559

theorem tailTrace_4191350 : CollatzResearch.WordTrace tailWord_4191350 prefixEnd_4191350 1434784760814854371699559 := by
  unfold tailWord_4191350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9554443335341390652207719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101914062243641500290215669 9554443335341390652207719)
  ·
    refine ⟨14331665003012085978311579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9554443335341390652207719 14331665003012085978311579)
    ·
      refine ⟨21497497504518128967467369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14331665003012085978311579 21497497504518128967467369)
      ·
        refine ⟨16123123128388596725600527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21497497504518128967467369 16123123128388596725600527)
        ·
          refine ⟨24184684692582895088400791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16123123128388596725600527 24184684692582895088400791)
          ·
            refine ⟨36277027038874342632601187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24184684692582895088400791 36277027038874342632601187)
            ·
              refine ⟨54415540558311513948901781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36277027038874342632601187 54415540558311513948901781)
              ·
                refine ⟨2550728463670852216354771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54415540558311513948901781 2550728463670852216354771)
                ·
                  refine ⟨3826092695506278324532157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550728463670852216354771 3826092695506278324532157)
                  ·
                    refine ⟨1434784760814854371699559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3826092695506278324532157 1434784760814854371699559)
                    ·
                      rfl

theorem cell22_4191350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_4191350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191350 prefixEnd_4191350 := by exact prefixLift 4191350
  have htrace : WordTrace (prefixWord ++ tailWord_4191350) baseStart_4191350 baseEnd_4191350 := by
    simpa [prefixWord, tailWord_4191350, baseEnd_4191350] using wordTrace_append hprefix tailTrace_4191350
  have hstable : (prefixWord ++ tailWord_4191350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191350).length < 2 ^ (prefixWord ++ tailWord_4191350).sum := by decide
  have hdescent : baseEnd_4191350 < baseStart_4191350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191361 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 2, 5]
def baseStart_4191361 : Nat := 118140960795 + 4191361 * 2 ^ 59
def prefixEnd_4191361 : Nat := 4983230072969 + 3 ^ 40 * 4191361 * 2
def baseEnd_4191361 : Nat := 1434788526339654009674525

theorem tailTrace_4191361 : CollatzResearch.WordTrace tailWord_4191361 prefixEnd_4191361 1434788526339654009674525 := by
  unfold tailWord_4191361
  simp only [CollatzResearch.WordTrace]
  refine ⟨152871494568422399313973937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101914329712281599542649291 152871494568422399313973937)
  ·
    refine ⟨114653620926316799485480453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152871494568422399313973937 114653620926316799485480453)
    ·
      refine ⟨21497553923684399903527585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114653620926316799485480453 21497553923684399903527585)
      ·
        refine ⟨16123165442763299927645689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21497553923684399903527585 16123165442763299927645689)
        ·
          refine ⟨12092374082072474945734267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16123165442763299927645689 12092374082072474945734267)
          ·
            refine ⟨18138561123108712418601401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12092374082072474945734267 18138561123108712418601401)
            ·
              refine ⟨13603920842331534313951051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18138561123108712418601401 13603920842331534313951051)
              ·
                refine ⟨20405881263497301470926577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13603920842331534313951051 20405881263497301470926577)
                ·
                  refine ⟨15304410947622976103194933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20405881263497301470926577 15304410947622976103194933)
                  ·
                    refine ⟨1434788526339654009674525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15304410947622976103194933 1434788526339654009674525)
                    ·
                      rfl

theorem cell22_4191361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_4191361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191361 prefixEnd_4191361 := by exact prefixLift 4191361
  have htrace : WordTrace (prefixWord ++ tailWord_4191361) baseStart_4191361 baseEnd_4191361 := by
    simpa [prefixWord, tailWord_4191361, baseEnd_4191361] using wordTrace_append hprefix tailTrace_4191361
  have hstable : (prefixWord ++ tailWord_4191361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191361).length < 2 ^ (prefixWord ++ tailWord_4191361).sum := by decide
  have hdescent : baseEnd_4191361 < baseStart_4191361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191404 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_4191404 : Nat := 118140960795 + 4191404 * 2 ^ 59
def prefixEnd_4191404 : Nat := 4983230072969 + 3 ^ 40 * 4191404 * 2
def baseEnd_4191404 : Nat := 1434803246118416230849393

theorem tailTrace_4191404 : CollatzResearch.WordTrace tailWord_4191404 prefixEnd_4191404 1434803246118416230849393 := by
  unfold tailWord_4191404
  simp only [CollatzResearch.WordTrace]
  refine ⟨76436531453633308828894633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101915375271511078438526177 76436531453633308828894633)
  ·
    refine ⟨57327398590224981621670975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76436531453633308828894633 57327398590224981621670975)
    ·
      refine ⟨85991097885337472432506463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57327398590224981621670975 85991097885337472432506463)
      ·
        refine ⟨128986646828006208648759695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85991097885337472432506463 128986646828006208648759695)
        ·
          refine ⟨193479970242009312973139543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128986646828006208648759695 193479970242009312973139543)
          ·
            refine ⟨290219955363013969459709315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193479970242009312973139543 290219955363013969459709315)
            ·
              refine ⟨435329933044520954189563973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290219955363013969459709315 435329933044520954189563973)
              ·
                refine ⟨81624362445847678910543245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 435329933044520954189563973 81624362445847678910543245)
                ·
                  refine ⟨30609135917192879591453717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81624362445847678910543245 30609135917192879591453717)
                  ·
                    refine ⟨1434803246118416230849393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30609135917192879591453717 1434803246118416230849393)
                    ·
                      rfl

theorem cell22_4191404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_4191404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191404 prefixEnd_4191404 := by exact prefixLift 4191404
  have htrace : WordTrace (prefixWord ++ tailWord_4191404) baseStart_4191404 baseEnd_4191404 := by
    simpa [prefixWord, tailWord_4191404, baseEnd_4191404] using wordTrace_append hprefix tailTrace_4191404
  have hstable : (prefixWord ++ tailWord_4191404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191404).length < 2 ^ (prefixWord ++ tailWord_4191404).sum := by decide
  have hdescent : baseEnd_4191404 < baseStart_4191404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191414 : List Nat := [5, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_4191414 : Nat := 118140960795 + 4191414 * 2 ^ 59
def prefixEnd_4191414 : Nat := 4983230072969 + 3 ^ 40 * 4191414 * 2
def baseEnd_4191414 : Nat := 478268889774259846033121

theorem tailTrace_4191414 : CollatzResearch.WordTrace tailWord_4191414 prefixEnd_4191414 478268889774259846033121 := by
  unfold tailWord_4191414
  simp only [CollatzResearch.WordTrace]
  refine ⟨9554589227326899335353331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101915618424820259577102197 9554589227326899335353331)
  ·
    refine ⟨14331883840990349003029997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9554589227326899335353331 14331883840990349003029997)
    ·
      refine ⟨5374456440371380876136249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14331883840990349003029997 5374456440371380876136249)
      ·
        refine ⟨4030842330278535657102187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5374456440371380876136249 4030842330278535657102187)
        ·
          refine ⟨6046263495417803485653281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4030842330278535657102187 6046263495417803485653281)
          ·
            refine ⟨4534697621563352614239961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6046263495417803485653281 4534697621563352614239961)
            ·
              refine ⟨3401023216172514460679971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4534697621563352614239961 3401023216172514460679971)
              ·
                refine ⟨5101534824258771691019957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3401023216172514460679971 5101534824258771691019957)
                ·
                  refine ⟨478268889774259846033121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5101534824258771691019957 478268889774259846033121)
                  ·
                    rfl

theorem cell22_4191414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_4191414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191414 prefixEnd_4191414 := by exact prefixLift 4191414
  have htrace : WordTrace (prefixWord ++ tailWord_4191414) baseStart_4191414 baseEnd_4191414 := by
    simpa [prefixWord, tailWord_4191414, baseEnd_4191414] using wordTrace_append hprefix tailTrace_4191414
  have hstable : (prefixWord ++ tailWord_4191414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191414).length < 2 ^ (prefixWord ++ tailWord_4191414).sum := by decide
  have hdescent : baseEnd_4191414 < baseStart_4191414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191453 : List Nat := [1, 4, 3, 2, 3, 9]
def baseStart_4191453 : Nat := 118140960795 + 4191453 * 2 ^ 59
def prefixEnd_4191453 : Nat := 4983230072969 + 3 ^ 40 * 4191453 * 2
def baseEnd_4191453 : Nat := 17713827405182672054003

theorem tailTrace_4191453 : CollatzResearch.WordTrace tailWord_4191453 prefixEnd_4191453 17713827405182672054003 := by
  unfold tailWord_4191453
  simp only [CollatzResearch.WordTrace]
  refine ⟨152874850084089099026323013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101916566722726066017548675 152874850084089099026323013)
  ·
    refine ⟨28664034390766706067435565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152874850084089099026323013 28664034390766706067435565)
    ·
      refine ⟨10749012896537514775288337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28664034390766706067435565 10749012896537514775288337)
      ·
        refine ⟨8061759672403136081466253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10749012896537514775288337 8061759672403136081466253)
        ·
          refine ⟨3023159877151176030549845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8061759672403136081466253 3023159877151176030549845)
          ·
            refine ⟨17713827405182672054003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 3023159877151176030549845 17713827405182672054003)
            ·
              rfl

theorem cell22_4191453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 9].length) (baseStart_4191453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191453 prefixEnd_4191453 := by exact prefixLift 4191453
  have htrace : WordTrace (prefixWord ++ tailWord_4191453) baseStart_4191453 baseEnd_4191453 := by
    simpa [prefixWord, tailWord_4191453, baseEnd_4191453] using wordTrace_append hprefix tailTrace_4191453
  have hstable : (prefixWord ++ tailWord_4191453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191453).length < 2 ^ (prefixWord ++ tailWord_4191453).sum := by decide
  have hdescent : baseEnd_4191453 < baseStart_4191453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191466 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_4191466 : Nat := 118140960795 + 4191466 * 2 ^ 59
def prefixEnd_4191466 : Nat := 4983230072969 + 3 ^ 40 * 4191466 * 2
def baseEnd_4191466 : Nat := 1434824469985468735799203

theorem tailTrace_4191466 : CollatzResearch.WordTrace tailWord_4191466 prefixEnd_4191466 1434824469985468735799203 := by
  unfold tailWord_4191466
  simp only [CollatzResearch.WordTrace]
  refine ⟨38218831058260500561636563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101916882822028001497697501 38218831058260500561636563)
  ·
    refine ⟨57328246587390750842454845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38218831058260500561636563 57328246587390750842454845)
    ·
      refine ⟨21498092470271531565920567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57328246587390750842454845 21498092470271531565920567)
      ·
        refine ⟨32247138705407297348880851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21498092470271531565920567 32247138705407297348880851)
        ·
          refine ⟨48370708058110946023321277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32247138705407297348880851 48370708058110946023321277)
          ·
            refine ⟨18139015521791604758745479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48370708058110946023321277 18139015521791604758745479)
            ·
              refine ⟨27208523282687407138118219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18139015521791604758745479 27208523282687407138118219)
              ·
                refine ⟨40812784924031110707177329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27208523282687407138118219 40812784924031110707177329)
                ·
                  refine ⟨30609588693023333030382997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40812784924031110707177329 30609588693023333030382997)
                  ·
                    refine ⟨1434824469985468735799203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30609588693023333030382997 1434824469985468735799203)
                    ·
                      rfl

theorem cell22_4191466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_4191466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191466 prefixEnd_4191466 := by exact prefixLift 4191466
  have htrace : WordTrace (prefixWord ++ tailWord_4191466) baseStart_4191466 baseEnd_4191466 := by
    simpa [prefixWord, tailWord_4191466, baseEnd_4191466] using wordTrace_append hprefix tailTrace_4191466
  have hstable : (prefixWord ++ tailWord_4191466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191466).length < 2 ^ (prefixWord ++ tailWord_4191466).sum := by decide
  have hdescent : baseEnd_4191466 < baseStart_4191466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191481 : List Nat := [1, 2, 1, 3, 1, 1, 3, 5, 5]
def baseStart_4191481 : Nat := 118140960795 + 4191481 * 2 ^ 59
def prefixEnd_4191481 : Nat := 4983230072969 + 3 ^ 40 * 4191481 * 2
def baseEnd_4191481 : Nat := 478276534930671232224719

theorem tailTrace_4191481 : CollatzResearch.WordTrace tailWord_4191481 prefixEnd_4191481 478276534930671232224719 := by
  unfold tailWord_4191481
  simp only [CollatzResearch.WordTrace]
  refine ⟨152875871327987659808342297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101917247551991773205561531 152875871327987659808342297)
  ·
    refine ⟨114656903495990744856256723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152875871327987659808342297 114656903495990744856256723)
    ·
      refine ⟨171985355243986117284385085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114656903495990744856256723 171985355243986117284385085)
      ·
        refine ⟨64494508216494793981644407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171985355243986117284385085 64494508216494793981644407)
        ·
          refine ⟨96741762324742190972466611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64494508216494793981644407 96741762324742190972466611)
          ·
            refine ⟨145112643487113286458699917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96741762324742190972466611 145112643487113286458699917)
            ·
              refine ⟨54417241307667482422012469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145112643487113286458699917 54417241307667482422012469)
              ·
                refine ⟨5101616372593826477063669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54417241307667482422012469 5101616372593826477063669)
                ·
                  refine ⟨478276534930671232224719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5101616372593826477063669 478276534930671232224719)
                  ·
                    rfl

theorem cell22_4191481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 5].length) (baseStart_4191481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191481 prefixEnd_4191481 := by exact prefixLift 4191481
  have htrace : WordTrace (prefixWord ++ tailWord_4191481) baseStart_4191481 baseEnd_4191481 := by
    simpa [prefixWord, tailWord_4191481, baseEnd_4191481] using wordTrace_append hprefix tailTrace_4191481
  have hstable : (prefixWord ++ tailWord_4191481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191481).length < 2 ^ (prefixWord ++ tailWord_4191481).sum := by decide
  have hdescent : baseEnd_4191481 < baseStart_4191481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191502 : List Nat := [4, 1, 1, 2, 1, 4, 2, 3, 1, 3]
def baseStart_4191502 : Nat := 118140960795 + 4191502 * 2 ^ 59
def prefixEnd_4191502 : Nat := 4983230072969 + 3 ^ 40 * 4191502 * 2
def baseEnd_4191502 : Nat := 1434836793521176641899093

theorem tailTrace_4191502 : CollatzResearch.WordTrace tailWord_4191502 prefixEnd_4191502 1434836793521176641899093 := by
  unfold tailWord_4191502
  simp only [CollatzResearch.WordTrace]
  refine ⟨19109579657613947549357095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101917758173941053596571173 19109579657613947549357095)
  ·
    refine ⟨28664369486420921324035643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19109579657613947549357095 28664369486420921324035643)
    ·
      refine ⟨42996554229631381986053465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28664369486420921324035643 42996554229631381986053465)
      ·
        refine ⟨32247415672223536489540099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42996554229631381986053465 32247415672223536489540099)
        ·
          refine ⟨48371123508335304734310149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32247415672223536489540099 48371123508335304734310149)
          ·
            refine ⟨9069585657812869637683153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48371123508335304734310149 9069585657812869637683153)
            ·
              refine ⟨6802189243359652228262365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9069585657812869637683153 6802189243359652228262365)
              ·
                refine ⟨2550820966259869585598387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6802189243359652228262365 2550820966259869585598387)
                ·
                  refine ⟨3826231449389804378397581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550820966259869585598387 3826231449389804378397581)
                  ·
                    refine ⟨1434836793521176641899093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3826231449389804378397581 1434836793521176641899093)
                    ·
                      rfl

theorem cell22_4191502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_4191502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191502 prefixEnd_4191502 := by exact prefixLift 4191502
  have htrace : WordTrace (prefixWord ++ tailWord_4191502) baseStart_4191502 baseEnd_4191502 := by
    simpa [prefixWord, tailWord_4191502, baseEnd_4191502] using wordTrace_append hprefix tailTrace_4191502
  have hstable : (prefixWord ++ tailWord_4191502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191502).length < 2 ^ (prefixWord ++ tailWord_4191502).sum := by decide
  have hdescent : baseEnd_4191502 < baseStart_4191502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191573 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_4191573 : Nat := 118140960795 + 4191573 * 2 ^ 59
def prefixEnd_4191573 : Nat := 4983230072969 + 3 ^ 40 * 4191573 * 2
def baseEnd_4191573 : Nat := 1434861098272156123373875

theorem tailTrace_4191573 : CollatzResearch.WordTrace tailWord_4191573 prefixEnd_4191573 1434861098272156123373875 := by
  unfold tailWord_4191573
  simp only [CollatzResearch.WordTrace]
  refine ⟨152879226843654359520691373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101919484562436239680460915 152879226843654359520691373)
  ·
    refine ⟨57329710066370384820259265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152879226843654359520691373 57329710066370384820259265)
    ·
      refine ⟨42997282549777788615194449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57329710066370384820259265 42997282549777788615194449)
      ·
        refine ⟨32247961912333341461395837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42997282549777788615194449 32247961912333341461395837)
        ·
          refine ⟨12092985717125003048023439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32247961912333341461395837 12092985717125003048023439)
          ·
            refine ⟨18139478575687504572035159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12092985717125003048023439 18139478575687504572035159)
            ·
              refine ⟨27209217863531256858052739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18139478575687504572035159 27209217863531256858052739)
              ·
                refine ⟨40813826795296885287079109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27209217863531256858052739 40813826795296885287079109)
                ·
                  refine ⟨7652592524118165991327333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40813826795296885287079109 7652592524118165991327333)
                  ·
                    refine ⟨1434861098272156123373875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7652592524118165991327333 1434861098272156123373875)
                    ·
                      rfl

theorem cell22_4191573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_4191573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191573 prefixEnd_4191573 := by exact prefixLift 4191573
  have htrace : WordTrace (prefixWord ++ tailWord_4191573) baseStart_4191573 baseEnd_4191573 := by
    simpa [prefixWord, tailWord_4191573, baseEnd_4191573] using wordTrace_append hprefix tailTrace_4191573
  have hstable : (prefixWord ++ tailWord_4191573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191573).length < 2 ^ (prefixWord ++ tailWord_4191573).sum := by decide
  have hdescent : baseEnd_4191573 < baseStart_4191573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191588 : List Nat := [2, 3, 1, 1, 3, 3, 2, 7]
def baseStart_4191588 : Nat := 118140960795 + 4191588 * 2 ^ 59
def prefixEnd_4191588 : Nat := 4983230072969 + 3 ^ 40 * 4191588 * 2
def baseEnd_4191588 : Nat := 159429581453189009360981

theorem tailTrace_4191588 : CollatzResearch.WordTrace tailWord_4191588 prefixEnd_4191588 159429581453189009360981 := by
  unfold tailWord_4191588
  simp only [CollatzResearch.WordTrace]
  refine ⟨76439886969300008541243709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101919849292400011388324945 76439886969300008541243709)
  ·
    refine ⟨28664957613487503202966391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76439886969300008541243709 28664957613487503202966391)
    ·
      refine ⟨42997436420231254804449587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28664957613487503202966391 42997436420231254804449587)
      ·
        refine ⟨64496154630346882206674381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42997436420231254804449587 64496154630346882206674381)
        ·
          refine ⟨24186057986380080827502893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64496154630346882206674381 24186057986380080827502893)
          ·
            refine ⟨9069771744892530310313585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24186057986380080827502893 9069771744892530310313585)
            ·
              refine ⟨6802328808669397732735189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9069771744892530310313585 6802328808669397732735189)
              ·
                refine ⟨159429581453189009360981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6802328808669397732735189 159429581453189009360981)
                ·
                  rfl

theorem cell22_4191588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 7].length) (baseStart_4191588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191588 prefixEnd_4191588 := by exact prefixLift 4191588
  have htrace : WordTrace (prefixWord ++ tailWord_4191588) baseStart_4191588 baseEnd_4191588 := by
    simpa [prefixWord, tailWord_4191588, baseEnd_4191588] using wordTrace_append hprefix tailTrace_4191588
  have hstable : (prefixWord ++ tailWord_4191588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191588).length < 2 ^ (prefixWord ++ tailWord_4191588).sum := by decide
  have hdescent : baseEnd_4191588 < baseStart_4191588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191592 : List Nat := [2, 1, 4, 2, 3, 1, 1, 3, 2, 3]
def baseStart_4191592 : Nat := 118140960795 + 4191592 * 2 ^ 59
def prefixEnd_4191592 : Nat := 4983230072969 + 3 ^ 40 * 4191592 * 2
def baseEnd_4191592 : Nat := 1434867602360446407148817

theorem tailTrace_4191592 : CollatzResearch.WordTrace tailWord_4191592 prefixEnd_4191592 1434867602360446407148817 := by
  unfold tailWord_4191592
  simp only [CollatzResearch.WordTrace]
  refine ⟨76439959915292762882816515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101919946553723683843755353 76439959915292762882816515)
  ·
    refine ⟨114659939872939144324224773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76439959915292762882816515 114659939872939144324224773)
    ·
      refine ⟨21498738726176089560792145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114659939872939144324224773 21498738726176089560792145)
      ·
        refine ⟨16124054044632067170594109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21498738726176089560792145 16124054044632067170594109)
        ·
          refine ⟨6046520266737025188972791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16124054044632067170594109 6046520266737025188972791)
          ·
            refine ⟨9069780400105537783459187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6046520266737025188972791 9069780400105537783459187)
            ·
              refine ⟨13604670600158306675188781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9069780400105537783459187 13604670600158306675188781)
              ·
                refine ⟨5101751475059365003195793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13604670600158306675188781 5101751475059365003195793)
                ·
                  refine ⟨3826313606294523752396845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5101751475059365003195793 3826313606294523752396845)
                  ·
                    refine ⟨1434867602360446407148817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3826313606294523752396845 1434867602360446407148817)
                    ·
                      rfl

theorem cell22_4191592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_4191592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191592 prefixEnd_4191592 := by exact prefixLift 4191592
  have htrace : WordTrace (prefixWord ++ tailWord_4191592) baseStart_4191592 baseEnd_4191592 := by
    simpa [prefixWord, tailWord_4191592, baseEnd_4191592] using wordTrace_append hprefix tailTrace_4191592
  have hstable : (prefixWord ++ tailWord_4191592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191592).length < 2 ^ (prefixWord ++ tailWord_4191592).sum := by decide
  have hdescent : baseEnd_4191592 < baseStart_4191592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191616 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 9]
def baseStart_4191616 : Nat := 118140960795 + 4191616 * 2 ^ 59
def prefixEnd_4191616 : Nat := 4983230072969 + 3 ^ 40 * 4191616 * 2
def baseEnd_4191616 : Nat := 478291939350306114849581

theorem tailTrace_4191616 : CollatzResearch.WordTrace tailWord_4191616 prefixEnd_4191616 478291939350306114849581 := by
  unfold tailWord_4191616
  simp only [CollatzResearch.WordTrace]
  refine ⟨76440397591249288932253351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101920530121665718576337801 76440397591249288932253351)
  ·
    refine ⟨114660596386873933398380027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76440397591249288932253351 114660596386873933398380027)
    ·
      refine ⟨171990894580310900097570041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114660596386873933398380027 171990894580310900097570041)
      ·
        refine ⟨128993170935233175073177531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171990894580310900097570041 128993170935233175073177531)
        ·
          refine ⟨193489756402849762609766297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128993170935233175073177531 193489756402849762609766297)
          ·
            refine ⟨145117317302137321957324723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193489756402849762609766297 145117317302137321957324723)
            ·
              refine ⟨217675975953205982935987085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145117317302137321957324723 217675975953205982935987085)
              ·
                refine ⟨81628490982452243600995157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217675975953205982935987085 81628490982452243600995157)
                ·
                  refine ⟨478291939350306114849581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81628490982452243600995157 478291939350306114849581)
                  ·
                    rfl

theorem cell22_4191616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_4191616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191616 prefixEnd_4191616 := by exact prefixLift 4191616
  have htrace : WordTrace (prefixWord ++ tailWord_4191616) baseStart_4191616 baseEnd_4191616 := by
    simpa [prefixWord, tailWord_4191616, baseEnd_4191616] using wordTrace_append hprefix tailTrace_4191616
  have hstable : (prefixWord ++ tailWord_4191616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191616).length < 2 ^ (prefixWord ++ tailWord_4191616).sum := by decide
  have hdescent : baseEnd_4191616 < baseStart_4191616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191648 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 2, 5]
def baseStart_4191648 : Nat := 118140960795 + 4191648 * 2 ^ 59
def prefixEnd_4191648 : Nat := 4983230072969 + 3 ^ 40 * 4191648 * 2
def baseEnd_4191648 : Nat := 1434886772304880927748645

theorem tailTrace_4191648 : CollatzResearch.WordTrace tailWord_4191648 prefixEnd_4191648 1434886772304880927748645 := by
  unfold tailWord_4191648
  simp only [CollatzResearch.WordTrace]
  refine ⟨76440981159191323664835799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101921308212255098219781065 76440981159191323664835799)
  ·
    refine ⟨114661471738786985497253699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76440981159191323664835799 114661471738786985497253699)
    ·
      refine ⟨171992207608180478245880549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114661471738786985497253699 171992207608180478245880549)
      ·
        refine ⟨32248538926533839671102603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171992207608180478245880549 32248538926533839671102603)
        ·
          refine ⟨48372808389800759506653905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32248538926533839671102603 48372808389800759506653905)
          ·
            refine ⟨36279606292350569629990429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48372808389800759506653905 36279606292350569629990429)
            ·
              refine ⟨13604852359631463611246411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36279606292350569629990429 13604852359631463611246411)
              ·
                refine ⟨20407278539447195416869617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13604852359631463611246411 20407278539447195416869617)
                ·
                  refine ⟨15305458904585396562652213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20407278539447195416869617 15305458904585396562652213)
                  ·
                    refine ⟨1434886772304880927748645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15305458904585396562652213 1434886772304880927748645)
                    ·
                      rfl

theorem cell22_4191648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_4191648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191648 prefixEnd_4191648 := by exact prefixLift 4191648
  have htrace : WordTrace (prefixWord ++ tailWord_4191648) baseStart_4191648 baseEnd_4191648 := by
    simpa [prefixWord, tailWord_4191648, baseEnd_4191648] using wordTrace_append hprefix tailTrace_4191648
  have hstable : (prefixWord ++ tailWord_4191648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191648).length < 2 ^ (prefixWord ++ tailWord_4191648).sum := by decide
  have hdescent : baseEnd_4191648 < baseStart_4191648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191650 : List Nat := [3, 3, 1, 2, 1, 2, 2, 3, 5]
def baseStart_4191650 : Nat := 118140960795 + 4191650 * 2 ^ 59
def prefixEnd_4191650 : Nat := 4983230072969 + 3 ^ 40 * 4191650 * 2
def baseEnd_4191650 : Nat := 478295818981917863066213

theorem tailTrace_4191650 : CollatzResearch.WordTrace tailWord_4191650 prefixEnd_4191650 478295818981917863066213 := by
  unfold tailWord_4191650
  simp only [CollatzResearch.WordTrace]
  refine ⟨38220508816093850417811101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101921356842916934447496269 38220508816093850417811101)
  ·
    refine ⟨14332690806035193906679163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38220508816093850417811101 14332690806035193906679163)
    ·
      refine ⟨21499036209052790860018745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14332690806035193906679163 21499036209052790860018745)
      ·
        refine ⟨16124277156789593145014059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21499036209052790860018745 16124277156789593145014059)
        ·
          refine ⟨24186415735184389717521089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16124277156789593145014059 24186415735184389717521089)
          ·
            refine ⟨18139811801388292288140817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24186415735184389717521089 18139811801388292288140817)
            ·
              refine ⟨13604858851041219216105613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18139811801388292288140817 13604858851041219216105613)
              ·
                refine ⟨5101822069140457206039605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13604858851041219216105613 5101822069140457206039605)
                ·
                  refine ⟨478295818981917863066213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5101822069140457206039605 478295818981917863066213)
                  ·
                    rfl

theorem cell22_4191650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_4191650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191650 prefixEnd_4191650 := by exact prefixLift 4191650
  have htrace : WordTrace (prefixWord ++ tailWord_4191650) baseStart_4191650 baseEnd_4191650 := by
    simpa [prefixWord, tailWord_4191650, baseEnd_4191650] using wordTrace_append hprefix tailTrace_4191650
  have hstable : (prefixWord ++ tailWord_4191650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191650).length < 2 ^ (prefixWord ++ tailWord_4191650).sum := by decide
  have hdescent : baseEnd_4191650 < baseStart_4191650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191678 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_4191678 : Nat := 118140960795 + 4191678 * 2 ^ 59
def prefixEnd_4191678 : Nat := 4983230072969 + 3 ^ 40 * 4191678 * 2
def baseEnd_4191678 : Nat := 478299013972656949832851

theorem tailTrace_4191678 : CollatzResearch.WordTrace tailWord_4191678 prefixEnd_4191678 478299013972656949832851 := by
  unfold tailWord_4191678
  simp only [CollatzResearch.WordTrace]
  refine ⟨19110382063534245306657961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101922037672182641635509125 19110382063534245306657961)
  ·
    refine ⟨14332786547650683979993471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19110382063534245306657961 14332786547650683979993471)
    ·
      refine ⟨21499179821476025969990207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14332786547650683979993471 21499179821476025969990207)
      ·
        refine ⟨32248769732214038954985311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21499179821476025969990207 32248769732214038954985311)
        ·
          refine ⟨48373154598321058432477967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32248769732214038954985311 48373154598321058432477967)
          ·
            refine ⟨72559731897481587648716951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48373154598321058432477967 72559731897481587648716951)
            ·
              refine ⟨108839597846222381473075427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72559731897481587648716951 108839597846222381473075427)
              ·
                refine ⟨163259396769333572209613141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108839597846222381473075427 163259396769333572209613141)
                ·
                  refine ⟨478299013972656949832851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 163259396769333572209613141 478299013972656949832851)
                  ·
                    rfl

theorem cell22_4191678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_4191678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191678 prefixEnd_4191678 := by exact prefixLift 4191678
  have htrace : WordTrace (prefixWord ++ tailWord_4191678) baseStart_4191678 baseEnd_4191678 := by
    simpa [prefixWord, tailWord_4191678, baseEnd_4191678] using wordTrace_append hprefix tailTrace_4191678
  have hstable : (prefixWord ++ tailWord_4191678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191678).length < 2 ^ (prefixWord ++ tailWord_4191678).sum := by decide
  have hdescent : baseEnd_4191678 < baseStart_4191678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191695 : List Nat := [1, 1, 2, 1, 1, 4, 4, 4, 4]
def baseStart_4191695 : Nat := 118140960795 + 4191695 * 2 ^ 59
def prefixEnd_4191695 : Nat := 4983230072969 + 3 ^ 40 * 4191695 * 2
def baseEnd_4191695 : Nat := 478300953788462823941167

theorem tailTrace_4191695 : CollatzResearch.WordTrace tailWord_4191695 prefixEnd_4191695 478300953788462823941167 := by
  unfold tailWord_4191695
  simp only [CollatzResearch.WordTrace]
  refine ⟨152883676549212374356632539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101922451032808249571088359 152883676549212374356632539)
  ·
    refine ⟨229325514823818561534948809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152883676549212374356632539 229325514823818561534948809)
    ·
      refine ⟨171994136117863921151211607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229325514823818561534948809 171994136117863921151211607)
      ·
        refine ⟨257991204176795881726817411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171994136117863921151211607 257991204176795881726817411)
        ·
          refine ⟨386986806265193822590226117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257991204176795881726817411 386986806265193822590226117)
          ·
            refine ⟨72560026174723841735667397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386986806265193822590226117 72560026174723841735667397)
            ·
              refine ⟨13605004907760720325437637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72560026174723841735667397 13605004907760720325437637)
              ·
                refine ⟨2550938420205135061019557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13605004907760720325437637 2550938420205135061019557)
                ·
                  refine ⟨478300953788462823941167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2550938420205135061019557 478300953788462823941167)
                  ·
                    rfl

theorem cell22_4191695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 4].length) (baseStart_4191695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191695 prefixEnd_4191695 := by exact prefixLift 4191695
  have htrace : WordTrace (prefixWord ++ tailWord_4191695) baseStart_4191695 baseEnd_4191695 := by
    simpa [prefixWord, tailWord_4191695, baseEnd_4191695] using wordTrace_append hprefix tailTrace_4191695
  have hstable : (prefixWord ++ tailWord_4191695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191695).length < 2 ^ (prefixWord ++ tailWord_4191695).sum := by decide
  have hdescent : baseEnd_4191695 < baseStart_4191695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191746 : List Nat := [3, 4, 1, 2, 1, 2, 3, 2, 4]
def baseStart_4191746 : Nat := 118140960795 + 4191746 * 2 ^ 59
def prefixEnd_4191746 : Nat := 4983230072969 + 3 ^ 40 * 4191746 * 2
def baseEnd_4191746 : Nat := 478306773235880446266115

theorem tailTrace_4191746 : CollatzResearch.WordTrace tailWord_4191746 prefixEnd_4191746 478306773235880446266115 := by
  unfold tailWord_4191746
  simp only [CollatzResearch.WordTrace]
  refine ⟨38221384168006902516684773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101923691114685073377826061 38221384168006902516684773)
  ·
    refine ⟨7166509531501294221878395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38221384168006902516684773 7166509531501294221878395)
    ·
      refine ⟨10749764297251941332817593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7166509531501294221878395 10749764297251941332817593)
      ·
        refine ⟨8062323222938955999613195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10749764297251941332817593 8062323222938955999613195)
        ·
          refine ⟨12093484834408433999419793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8062323222938955999613195 12093484834408433999419793)
          ·
            refine ⟨9070113625806325499564845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12093484834408433999419793 9070113625806325499564845)
            ·
              refine ⟨3401292609677372062336817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9070113625806325499564845 3401292609677372062336817)
              ·
                refine ⟨2550969457258029046752613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3401292609677372062336817 2550969457258029046752613)
                ·
                  refine ⟨478306773235880446266115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2550969457258029046752613 478306773235880446266115)
                  ·
                    rfl

theorem cell22_4191746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_4191746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191746 prefixEnd_4191746 := by exact prefixLift 4191746
  have htrace : WordTrace (prefixWord ++ tailWord_4191746) baseStart_4191746 baseEnd_4191746 := by
    simpa [prefixWord, tailWord_4191746, baseEnd_4191746] using wordTrace_append hprefix tailTrace_4191746
  have hstable : (prefixWord ++ tailWord_4191746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191746).length < 2 ^ (prefixWord ++ tailWord_4191746).sum := by decide
  have hdescent : baseEnd_4191746 < baseStart_4191746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191753 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 2, 6]
def baseStart_4191753 : Nat := 118140960795 + 4191753 * 2 ^ 59
def prefixEnd_4191753 : Nat := 4983230072969 + 3 ^ 40 * 4191753 * 2
def baseEnd_4191753 : Nat := 1434922715950695653873323

theorem tailTrace_4191753 : CollatzResearch.WordTrace tailWord_4191753 prefixEnd_4191753 1434922715950695653873323 := by
  unfold tailWord_4191753
  simp only [CollatzResearch.WordTrace]
  refine ⟨152885791983002250262243913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101923861322001500174829275 152885791983002250262243913)
  ·
    refine ⟨114664343987251687696682935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152885791983002250262243913 114664343987251687696682935)
    ·
      refine ⟨171996515980877531545024403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114664343987251687696682935 171996515980877531545024403)
      ·
        refine ⟨257994773971316297317536605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171996515980877531545024403 257994773971316297317536605)
        ·
          refine ⟨96748040239243611494076227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257994773971316297317536605 96748040239243611494076227)
          ·
            refine ⟨145122060358865417241114341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96748040239243611494076227 145122060358865417241114341)
            ·
              refine ⟨27210386317287265732708939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145122060358865417241114341 27210386317287265732708939)
              ·
                refine ⟨40815579475930898599063409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27210386317287265732708939 40815579475930898599063409)
                ·
                  refine ⟨30611684606948173949297557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40815579475930898599063409 30611684606948173949297557)
                  ·
                    refine ⟨1434922715950695653873323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30611684606948173949297557 1434922715950695653873323)
                    ·
                      rfl

theorem cell22_4191753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_4191753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191753 prefixEnd_4191753 := by exact prefixLift 4191753
  have htrace : WordTrace (prefixWord ++ tailWord_4191753) baseStart_4191753 baseEnd_4191753 := by
    simpa [prefixWord, tailWord_4191753, baseEnd_4191753] using wordTrace_append hprefix tailTrace_4191753
  have hstable : (prefixWord ++ tailWord_4191753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191753).length < 2 ^ (prefixWord ++ tailWord_4191753).sum := by decide
  have hdescent : baseEnd_4191753 < baseStart_4191753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191847 : List Nat := [1, 1, 5, 1, 1, 1, 3, 5, 4]
def baseStart_4191847 : Nat := 118140960795 + 4191847 * 2 ^ 59
def prefixEnd_4191847 : Nat := 4983230072969 + 3 ^ 40 * 4191847 * 2
def baseEnd_4191847 : Nat := 478318298023903580674345

theorem tailTrace_4191847 : CollatzResearch.WordTrace tailWord_4191847 prefixEnd_4191847 478318298023903580674345 := by
  unfold tailWord_4191847
  simp only [CollatzResearch.WordTrace]
  refine ⟨152889220444661704316165795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101926146963107802877443863 152889220444661704316165795)
  ·
    refine ⟨229333830666992556474248693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152889220444661704316165795 229333830666992556474248693)
    ·
      refine ⟨21500046625030552169460815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 229333830666992556474248693 21500046625030552169460815)
      ·
        refine ⟨32250069937545828254191223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21500046625030552169460815 32250069937545828254191223)
        ·
          refine ⟨48375104906318742381286835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32250069937545828254191223 48375104906318742381286835)
          ·
            refine ⟨72562657359478113571930253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48375104906318742381286835 72562657359478113571930253)
            ·
              refine ⟨27210996509804292589473845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72562657359478113571930253 27210996509804292589473845)
              ·
                refine ⟨2551030922794152430263173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27210996509804292589473845 2551030922794152430263173)
                ·
                  refine ⟨478318298023903580674345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2551030922794152430263173 478318298023903580674345)
                  ·
                    rfl

theorem cell22_4191847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 4].length) (baseStart_4191847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191847 prefixEnd_4191847 := by exact prefixLift 4191847
  have htrace : WordTrace (prefixWord ++ tailWord_4191847) baseStart_4191847 baseEnd_4191847 := by
    simpa [prefixWord, tailWord_4191847, baseEnd_4191847] using wordTrace_append hprefix tailTrace_4191847
  have hstable : (prefixWord ++ tailWord_4191847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191847).length < 2 ^ (prefixWord ++ tailWord_4191847).sum := by decide
  have hdescent : baseEnd_4191847 < baseStart_4191847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191920 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 7]
def baseStart_4191920 : Nat := 118140960795 + 4191920 * 2 ^ 59
def prefixEnd_4191920 : Nat := 4983230072969 + 3 ^ 40 * 4191920 * 2
def baseEnd_4191920 : Nat := 478326627821187628315937

theorem tailTrace_4191920 : CollatzResearch.WordTrace tailWord_4191920 prefixEnd_4191920 478326627821187628315937 := by
  unfold tailWord_4191920
  simp only [CollatzResearch.WordTrace]
  refine ⟨76445941486698618891786607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101927921982264825189048809 76445941486698618891786607)
  ·
    refine ⟨114668912230047928337679911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76445941486698618891786607 114668912230047928337679911)
    ·
      refine ⟨172003368345071892506519867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114668912230047928337679911 172003368345071892506519867)
      ·
        refine ⟨258005052517607838759779801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172003368345071892506519867 258005052517607838759779801)
        ·
          refine ⟨193503789388205879069834851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258005052517607838759779801 193503789388205879069834851)
          ·
            refine ⟨290255684082308818604752277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193503789388205879069834851 290255684082308818604752277)
            ·
              refine ⟨13605735191358225872097763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 290255684082308818604752277 13605735191358225872097763)
              ·
                refine ⟨20408602787037338808146645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13605735191358225872097763 20408602787037338808146645)
                ·
                  refine ⟨478326627821187628315937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20408602787037338808146645 478326627821187628315937)
                  ·
                    rfl

theorem cell22_4191920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 7].length) (baseStart_4191920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191920 prefixEnd_4191920 := by exact prefixLift 4191920
  have htrace : WordTrace (prefixWord ++ tailWord_4191920) baseStart_4191920 baseEnd_4191920 := by
    simpa [prefixWord, tailWord_4191920, baseEnd_4191920] using wordTrace_append hprefix tailTrace_4191920
  have hstable : (prefixWord ++ tailWord_4191920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191920).length < 2 ^ (prefixWord ++ tailWord_4191920).sum := by decide
  have hdescent : baseEnd_4191920 < baseStart_4191920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191935 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 1, 7]
def baseStart_4191935 : Nat := 118140960795 + 4191935 * 2 ^ 59
def prefixEnd_4191935 : Nat := 4983230072969 + 3 ^ 40 * 4191935 * 2
def baseEnd_4191935 : Nat := 1434985018270107845822765

theorem tailTrace_4191935 : CollatzResearch.WordTrace tailWord_4191935 prefixEnd_4191935 1434985018270107845822765 := by
  unfold tailWord_4191935
  simp only [CollatzResearch.WordTrace]
  refine ⟨152892430068342895345369259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101928286712228596896912839 152892430068342895345369259)
  ·
    refine ⟨229338645102514343018053889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152892430068342895345369259 229338645102514343018053889)
    ·
      refine ⟨172003983826885757263540417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229338645102514343018053889 172003983826885757263540417)
      ·
        refine ⟨129002987870164317947655313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172003983826885757263540417 129002987870164317947655313)
        ·
          refine ⟨96752240902623238460741485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129002987870164317947655313 96752240902623238460741485)
          ·
            refine ⟨36282090338483714422778057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96752240902623238460741485 36282090338483714422778057)
            ·
              refine ⟨27211567753862785817083543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36282090338483714422778057 27211567753862785817083543)
              ·
                refine ⟨40817351630794178725625315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27211567753862785817083543 40817351630794178725625315)
                ·
                  refine ⟨61226027446191268088437973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40817351630794178725625315 61226027446191268088437973)
                  ·
                    refine ⟨1434985018270107845822765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61226027446191268088437973 1434985018270107845822765)
                    ·
                      rfl

theorem cell22_4191935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_4191935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191935 prefixEnd_4191935 := by exact prefixLift 4191935
  have htrace : WordTrace (prefixWord ++ tailWord_4191935) baseStart_4191935 baseEnd_4191935 := by
    simpa [prefixWord, tailWord_4191935, baseEnd_4191935] using wordTrace_append hprefix tailTrace_4191935
  have hstable : (prefixWord ++ tailWord_4191935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191935).length < 2 ^ (prefixWord ++ tailWord_4191935).sum := by decide
  have hdescent : baseEnd_4191935 < baseStart_4191935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191982 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_4191982 : Nat := 118140960795 + 4191982 * 2 ^ 59
def prefixEnd_4191982 : Nat := 4983230072969 + 3 ^ 40 * 4191982 * 2
def baseEnd_4191982 : Nat := 478333702443538463299207

theorem tailTrace_4191982 : CollatzResearch.WordTrace tailWord_4191982 prefixEnd_4191982 478333702443538463299207 := by
  unfold tailWord_4191982
  simp only [CollatzResearch.WordTrace]
  refine ⟨19111768037396577796541275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101929429532781748248220133 19111768037396577796541275)
  ·
    refine ⟨28667652056094866694811913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19111768037396577796541275 28667652056094866694811913)
    ·
      refine ⟨21500739042071150021108935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28667652056094866694811913 21500739042071150021108935)
      ·
        refine ⟨32251108563106725031663403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21500739042071150021108935 32251108563106725031663403)
        ·
          refine ⟨48376662844660087547495105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32251108563106725031663403 48376662844660087547495105)
          ·
            refine ⟨36282497133495065660621329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48376662844660087547495105 36282497133495065660621329)
            ·
              refine ⟨27211872850121299245465997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36282497133495065660621329 27211872850121299245465997)
              ·
                refine ⟨10204452318795487217049749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27211872850121299245465997 10204452318795487217049749)
                ·
                  refine ⟨478333702443538463299207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10204452318795487217049749 478333702443538463299207)
                  ·
                    rfl

theorem cell22_4191982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_4191982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4191982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4191982 prefixEnd_4191982 := by exact prefixLift 4191982
  have htrace : WordTrace (prefixWord ++ tailWord_4191982) baseStart_4191982 baseEnd_4191982 := by
    simpa [prefixWord, tailWord_4191982, baseEnd_4191982] using wordTrace_append hprefix tailTrace_4191982
  have hstable : (prefixWord ++ tailWord_4191982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191982).length < 2 ^ (prefixWord ++ tailWord_4191982).sum := by decide
  have hdescent : baseEnd_4191982 < baseStart_4191982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192018 : List Nat := [3, 2, 4, 1, 1, 1, 4, 1, 1, 4]
def baseStart_4192018 : Nat := 118140960795 + 4192018 * 2 ^ 59
def prefixEnd_4192018 : Nat := 4983230072969 + 3 ^ 40 * 4192018 * 2
def baseEnd_4192018 : Nat := 1435013430866323295997511

theorem tailTrace_4192018 : CollatzResearch.WordTrace tailWord_4192018 prefixEnd_4192018 1435013430866323295997511 := by
  unfold tailWord_4192018
  simp only [CollatzResearch.WordTrace]
  refine ⟨38223864331760550130160177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101930304884694800347093805 38223864331760550130160177)
  ·
    refine ⟨28667898248820412597620133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38223864331760550130160177 28667898248820412597620133)
    ·
      refine ⟨5375230921653827362053775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28667898248820412597620133 5375230921653827362053775)
      ·
        refine ⟨8062846382480741043080663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5375230921653827362053775 8062846382480741043080663)
        ·
          refine ⟨12094269573721111564620995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8062846382480741043080663 12094269573721111564620995)
          ·
            refine ⟨18141404360581667346931493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12094269573721111564620995 18141404360581667346931493)
            ·
              refine ⟨3401513317609062627549655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18141404360581667346931493 3401513317609062627549655)
              ·
                refine ⟨5102269976413593941324483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3401513317609062627549655 5102269976413593941324483)
                ·
                  refine ⟨7653404964620390911986725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5102269976413593941324483 7653404964620390911986725)
                  ·
                    refine ⟨1435013430866323295997511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7653404964620390911986725 1435013430866323295997511)
                    ·
                      rfl

theorem cell22_4192018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_4192018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192018 prefixEnd_4192018 := by exact prefixLift 4192018
  have htrace : WordTrace (prefixWord ++ tailWord_4192018) baseStart_4192018 baseEnd_4192018 := by
    simpa [prefixWord, tailWord_4192018, baseEnd_4192018] using wordTrace_append hprefix tailTrace_4192018
  have hstable : (prefixWord ++ tailWord_4192018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192018).length < 2 ^ (prefixWord ++ tailWord_4192018).sum := by decide
  have hdescent : baseEnd_4192018 < baseStart_4192018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192061 : List Nat := [1, 4, 1, 4, 1, 3, 2, 6]
def baseStart_4192061 : Nat := 118140960795 + 4192061 * 2 ^ 59
def prefixEnd_4192061 : Nat := 4983230072969 + 3 ^ 40 * 4192061 * 2
def baseEnd_4192061 : Nat := 159447572293898390796931

theorem tailTrace_4192061 : CollatzResearch.WordTrace tailWord_4192061 prefixEnd_4192061 159447572293898390796931 := by
  unfold tailWord_4192061
  simp only [CollatzResearch.WordTrace]
  refine ⟨152897025665886418864456037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101931350443924279242970691 152897025665886418864456037)
  ·
    refine ⟨28668192312353703537085507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152897025665886418864456037 28668192312353703537085507)
    ·
      refine ⟨43002288468530555305628261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28668192312353703537085507 43002288468530555305628261)
      ·
        refine ⟨8062929087849479119805299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43002288468530555305628261 8062929087849479119805299)
        ·
          refine ⟨12094393631774218679707949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8062929087849479119805299 12094393631774218679707949)
          ·
            refine ⟨4535397611915332004890481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12094393631774218679707949 4535397611915332004890481)
            ·
              refine ⟨3401548208936499003667861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4535397611915332004890481 3401548208936499003667861)
              ·
                refine ⟨159447572293898390796931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3401548208936499003667861 159447572293898390796931)
                ·
                  rfl

theorem cell22_4192061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 6].length) (baseStart_4192061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192061 prefixEnd_4192061 := by exact prefixLift 4192061
  have htrace : WordTrace (prefixWord ++ tailWord_4192061) baseStart_4192061 baseEnd_4192061 := by
    simpa [prefixWord, tailWord_4192061, baseEnd_4192061] using wordTrace_append hprefix tailTrace_4192061
  have hstable : (prefixWord ++ tailWord_4192061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192061).length < 2 ^ (prefixWord ++ tailWord_4192061).sum := by decide
  have hdescent : baseEnd_4192061 < baseStart_4192061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192072 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 7]
def baseStart_4192072 : Nat := 118140960795 + 4192072 * 2 ^ 59
def prefixEnd_4192072 : Nat := 4983230072969 + 3 ^ 40 * 4192072 * 2
def baseEnd_4192072 : Nat := 478343972056628385049115

theorem tailTrace_4192072 : CollatzResearch.WordTrace tailWord_4192072 prefixEnd_4192072 478343972056628385049115 := by
  unfold tailWord_4192072
  simp only [CollatzResearch.WordTrace]
  refine ⟨76448713434423283871553235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101931617912564378495404313 76448713434423283871553235)
  ·
    refine ⟨114673070151634925807329853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76448713434423283871553235 114673070151634925807329853)
    ·
      refine ⟨43002401306863097177748695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114673070151634925807329853 43002401306863097177748695)
      ·
        refine ⟨64503601960294645766623043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43002401306863097177748695 64503601960294645766623043)
        ·
          refine ⟨96755402940441968649934565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64503601960294645766623043 96755402940441968649934565)
          ·
            refine ⟨18141638051332869121862731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96755402940441968649934565 18141638051332869121862731)
            ·
              refine ⟨27212457076999303682794097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18141638051332869121862731 27212457076999303682794097)
              ·
                refine ⟨20409342807749477762095573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27212457076999303682794097 20409342807749477762095573)
                ·
                  refine ⟨478343972056628385049115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20409342807749477762095573 478343972056628385049115)
                  ·
                    rfl

theorem cell22_4192072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_4192072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192072 prefixEnd_4192072 := by exact prefixLift 4192072
  have htrace : WordTrace (prefixWord ++ tailWord_4192072) baseStart_4192072 baseEnd_4192072 := by
    simpa [prefixWord, tailWord_4192072, baseEnd_4192072] using wordTrace_append hprefix tailTrace_4192072
  have hstable : (prefixWord ++ tailWord_4192072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192072).length < 2 ^ (prefixWord ++ tailWord_4192072).sum := by decide
  have hdescent : baseEnd_4192072 < baseStart_4192072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192151 : List Nat := [1, 1, 3, 3, 1, 4, 1, 4, 4]
def baseStart_4192151 : Nat := 118140960795 + 4192151 * 2 ^ 59
def prefixEnd_4192151 : Nat := 4983230072969 + 3 ^ 40 * 4192151 * 2
def baseEnd_4192151 : Nat := 478352986494785094140701

theorem tailTrace_4192151 : CollatzResearch.WordTrace tailWord_4192151 prefixEnd_4192151 478352986494785094140701 := by
  unfold tailWord_4192151
  simp only [CollatzResearch.WordTrace]
  refine ⟨152900308235560364235232307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101933538823706909490154871 152900308235560364235232307)
  ·
    refine ⟨229350462353340546352848461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152900308235560364235232307 229350462353340546352848461)
    ·
      refine ⟨86006423382502704882318173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229350462353340546352848461 86006423382502704882318173)
      ·
        refine ⟨32252408768438514330869315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86006423382502704882318173 32252408768438514330869315)
        ·
          refine ⟨48378613152657771496303973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32252408768438514330869315 48378613152657771496303973)
          ·
            refine ⟨9070989966123332155556995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48378613152657771496303973 9070989966123332155556995)
            ·
              refine ⟨13606484949184998233335493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9070989966123332155556995 13606484949184998233335493)
              ·
                refine ⟨2551215927972187168750405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13606484949184998233335493 2551215927972187168750405)
                ·
                  refine ⟨478352986494785094140701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2551215927972187168750405 478352986494785094140701)
                  ·
                    rfl

theorem cell22_4192151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 4].length) (baseStart_4192151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192151 prefixEnd_4192151 := by exact prefixLift 4192151
  have htrace : WordTrace (prefixWord ++ tailWord_4192151) baseStart_4192151 baseEnd_4192151 := by
    simpa [prefixWord, tailWord_4192151, baseEnd_4192151] using wordTrace_append hprefix tailTrace_4192151
  have hstable : (prefixWord ++ tailWord_4192151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192151).length < 2 ^ (prefixWord ++ tailWord_4192151).sum := by decide
  have hdescent : baseEnd_4192151 < baseStart_4192151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192168 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 6]
def baseStart_4192168 : Nat := 118140960795 + 4192168 * 2 ^ 59
def prefixEnd_4192168 : Nat := 4983230072969 + 3 ^ 40 * 4192168 * 2
def baseEnd_4192168 : Nat := 478354926310590968249017

theorem tailTrace_4192168 : CollatzResearch.WordTrace tailWord_4192168 prefixEnd_4192168 478354926310590968249017 := by
  unfold tailWord_4192168
  simp only [CollatzResearch.WordTrace]
  refine ⟨76450464138249388069300579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101933952184332517425734105 76450464138249388069300579)
  ·
    refine ⟨114675696207374082103950869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76450464138249388069300579 114675696207374082103950869)
    ·
      refine ⟨5375423259720660098622697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 114675696207374082103950869 5375423259720660098622697)
      ·
        refine ⟨4031567444790495073967023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5375423259720660098622697 4031567444790495073967023)
        ·
          refine ⟨6047351167185742610950535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4031567444790495073967023 6047351167185742610950535)
          ·
            refine ⟨9071026750778613916425803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6047351167185742610950535 9071026750778613916425803)
            ·
              refine ⟨13606540126167920874638705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9071026750778613916425803 13606540126167920874638705)
              ·
                refine ⟨10204905094625940655979029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13606540126167920874638705 10204905094625940655979029)
                ·
                  refine ⟨478354926310590968249017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10204905094625940655979029 478354926310590968249017)
                  ·
                    rfl

theorem cell22_4192168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 6].length) (baseStart_4192168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192168 prefixEnd_4192168 := by exact prefixLift 4192168
  have htrace : WordTrace (prefixWord ++ tailWord_4192168) baseStart_4192168 baseEnd_4192168 := by
    simpa [prefixWord, tailWord_4192168, baseEnd_4192168] using wordTrace_append hprefix tailTrace_4192168
  have hstable : (prefixWord ++ tailWord_4192168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192168).length < 2 ^ (prefixWord ++ tailWord_4192168).sum := by decide
  have hdescent : baseEnd_4192168 < baseStart_4192168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192179 : List Nat := [1, 1, 1, 2, 3, 1, 7, 6]
def baseStart_4192179 : Nat := 118140960795 + 4192179 * 2 ^ 59
def prefixEnd_4192179 : Nat := 4983230072969 + 3 ^ 40 * 4192179 * 2
def baseEnd_4192179 : Nat := 159452060495174726969113

theorem tailTrace_4192179 : CollatzResearch.WordTrace tailWord_4192179 prefixEnd_4192179 159452060495174726969113 := by
  unfold tailWord_4192179
  simp only [CollatzResearch.WordTrace]
  refine ⟨152901329479458925017251591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101934219652972616678167727 152901329479458925017251591)
  ·
    refine ⟨229351994219188387525877387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152901329479458925017251591 229351994219188387525877387)
    ·
      refine ⟨344027991328782581288816081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229351994219188387525877387 344027991328782581288816081)
      ·
        refine ⟨258020993496586935966612061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344027991328782581288816081 258020993496586935966612061)
        ·
          refine ⟨96757872561220100987479523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258020993496586935966612061 96757872561220100987479523)
          ·
            refine ⟨145136808841830151481219285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96757872561220100987479523 145136808841830151481219285)
            ·
              refine ⟨3401643957230394175341077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 145136808841830151481219285 3401643957230394175341077)
              ·
                refine ⟨159452060495174726969113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3401643957230394175341077 159452060495174726969113)
                ·
                  rfl

theorem cell22_4192179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 6].length) (baseStart_4192179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192179 prefixEnd_4192179 := by exact prefixLift 4192179
  have htrace : WordTrace (prefixWord ++ tailWord_4192179) baseStart_4192179 baseEnd_4192179 := by
    simpa [prefixWord, tailWord_4192179, baseEnd_4192179] using wordTrace_append hprefix tailTrace_4192179
  have hstable : (prefixWord ++ tailWord_4192179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192179).length < 2 ^ (prefixWord ++ tailWord_4192179).sum := by decide
  have hdescent : baseEnd_4192179 < baseStart_4192179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192181 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 2, 4]
def baseStart_4192181 : Nat := 118140960795 + 4192181 * 2 ^ 59
def prefixEnd_4192181 : Nat := 4983230072969 + 3 ^ 40 * 4192181 * 2
def baseEnd_4192181 : Nat := 1435069229097445204172011

theorem tailTrace_4192181 : CollatzResearch.WordTrace tailWord_4192181 prefixEnd_4192181 1435069229097445204172011 := by
  unfold tailWord_4192181
  simp only [CollatzResearch.WordTrace]
  refine ⟨152901402425451679358824397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101934268283634452905882931 152901402425451679358824397)
  ·
    refine ⟨57338025909544379759559149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152901402425451679358824397 57338025909544379759559149)
    ·
      refine ⟨21501759716079142409834681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57338025909544379759559149 21501759716079142409834681)
      ·
        refine ⟨16126319787059356807376011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21501759716079142409834681 16126319787059356807376011)
        ·
          refine ⟨24189479680589035211064017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16126319787059356807376011 24189479680589035211064017)
          ·
            refine ⟨18142109760441776408298013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24189479680589035211064017 18142109760441776408298013)
            ·
              refine ⟨6803291160165666153111755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18142109760441776408298013 6803291160165666153111755)
              ·
                refine ⟨10204936740248499229667633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6803291160165666153111755 10204936740248499229667633)
                ·
                  refine ⟨7653702555186374422250725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10204936740248499229667633 7653702555186374422250725)
                  ·
                    refine ⟨1435069229097445204172011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7653702555186374422250725 1435069229097445204172011)
                    ·
                      rfl

theorem cell22_4192181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_4192181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192181 prefixEnd_4192181 := by exact prefixLift 4192181
  have htrace : WordTrace (prefixWord ++ tailWord_4192181) baseStart_4192181 baseEnd_4192181 := by
    simpa [prefixWord, tailWord_4192181, baseEnd_4192181] using wordTrace_append hprefix tailTrace_4192181
  have hstable : (prefixWord ++ tailWord_4192181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192181).length < 2 ^ (prefixWord ++ tailWord_4192181).sum := by decide
  have hdescent : baseEnd_4192181 < baseStart_4192181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192224 : List Nat := [2, 1, 1, 3, 1, 1, 1, 7, 5]
def baseStart_4192224 : Nat := 118140960795 + 4192224 * 2 ^ 59
def prefixEnd_4192224 : Nat := 4983230072969 + 3 ^ 40 * 4192224 * 2
def baseEnd_4192224 : Nat := 478361316292069141782293

theorem tailTrace_4192224 : CollatzResearch.WordTrace tailWord_4192224 prefixEnd_4192224 478361316292069141782293 := by
  unfold tailWord_4192224
  simp only [CollatzResearch.WordTrace]
  refine ⟨76451485382147948851319863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101935313842863931801759817 76451485382147948851319863)
  ·
    refine ⟨114677228073221923276979795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76451485382147948851319863 114677228073221923276979795)
    ·
      refine ⟨172015842109832884915469693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114677228073221923276979795 172015842109832884915469693)
      ·
        refine ⟨64505940791187331843301135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172015842109832884915469693 64505940791187331843301135)
        ·
          refine ⟨96758911186780997764951703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64505940791187331843301135 96758911186780997764951703)
          ·
            refine ⟨145138366780171496647427555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96758911186780997764951703 145138366780171496647427555)
            ·
              refine ⟨217707550170257244971141333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145138366780171496647427555 217707550170257244971141333)
              ·
                refine ⟨5102520707115404179011125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 217707550170257244971141333 5102520707115404179011125)
                ·
                  refine ⟨478361316292069141782293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5102520707115404179011125 478361316292069141782293)
                  ·
                    rfl

theorem cell22_4192224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 5].length) (baseStart_4192224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192224 prefixEnd_4192224 := by exact prefixLift 4192224
  have htrace : WordTrace (prefixWord ++ tailWord_4192224) baseStart_4192224 baseEnd_4192224 := by
    simpa [prefixWord, tailWord_4192224, baseEnd_4192224] using wordTrace_append hprefix tailTrace_4192224
  have hstable : (prefixWord ++ tailWord_4192224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192224).length < 2 ^ (prefixWord ++ tailWord_4192224).sum := by decide
  have hdescent : baseEnd_4192224 < baseStart_4192224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192316 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_4192316 : Nat := 118140960795 + 4192316 * 2 ^ 59
def prefixEnd_4192316 : Nat := 4983230072969 + 3 ^ 40 * 4192316 * 2
def baseEnd_4192316 : Nat := 1435115442356349852046597

theorem tailTrace_4192316 : CollatzResearch.WordTrace tailWord_4192316 prefixEnd_4192316 1435115442356349852046597 := by
  unfold tailWord_4192316
  simp only [CollatzResearch.WordTrace]
  refine ⟨76453163139981298707494401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101937550853308398276659201 76453163139981298707494401)
  ·
    refine ⟨57339872354985974030620801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76453163139981298707494401 57339872354985974030620801)
    ·
      refine ⟨43004904266239480522965601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57339872354985974030620801 43004904266239480522965601)
      ·
        refine ⟨32253678199679610392224201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43004904266239480522965601 32253678199679610392224201)
        ·
          refine ⟨24190258649759707794168151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32253678199679610392224201 24190258649759707794168151)
          ·
            refine ⟨36285387974639561691252227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24190258649759707794168151 36285387974639561691252227)
            ·
              refine ⟨54428081961959342536878341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36285387974639561691252227 54428081961959342536878341)
              ·
                refine ⟨10205265367867376725664689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54428081961959342536878341 10205265367867376725664689)
                ·
                  refine ⟨7653949025900532544248517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10205265367867376725664689 7653949025900532544248517)
                  ·
                    refine ⟨1435115442356349852046597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7653949025900532544248517 1435115442356349852046597)
                    ·
                      rfl

theorem cell22_4192316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_4192316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192316 prefixEnd_4192316 := by exact prefixLift 4192316
  have htrace : WordTrace (prefixWord ++ tailWord_4192316) baseStart_4192316 baseEnd_4192316 := by
    simpa [prefixWord, tailWord_4192316, baseEnd_4192316] using wordTrace_append hprefix tailTrace_4192316
  have hstable : (prefixWord ++ tailWord_4192316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192316).length < 2 ^ (prefixWord ++ tailWord_4192316).sum := by decide
  have hdescent : baseEnd_4192316 < baseStart_4192316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192320 : List Nat := [2, 1, 1, 2, 2, 6, 2, 2, 4]
def baseStart_4192320 : Nat := 118140960795 + 4192320 * 2 ^ 59
def prefixEnd_4192320 : Nat := 4983230072969 + 3 ^ 40 * 4192320 * 2
def baseEnd_4192320 : Nat := 478372270546031724982195

theorem tailTrace_4192320 : CollatzResearch.WordTrace tailWord_4192320 prefixEnd_4192320 478372270546031724982195 := by
  unfold tailWord_4192320
  simp only [CollatzResearch.WordTrace]
  refine ⟨76453236085974053049067207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101937648114632070732089609 76453236085974053049067207)
  ·
    refine ⟨114679854128961079573600811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76453236085974053049067207 114679854128961079573600811)
    ·
      refine ⟨172019781193441619360401217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114679854128961079573600811 172019781193441619360401217)
      ·
        refine ⟨129014835895081214520300913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172019781193441619360401217 129014835895081214520300913)
        ·
          refine ⟨96761126921310910890225685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129014835895081214520300913 96761126921310910890225685)
          ·
            refine ⟨4535677824436448947979329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96761126921310910890225685 4535677824436448947979329)
            ·
              refine ⟨3401758368327336710984497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4535677824436448947979329 3401758368327336710984497)
              ·
                refine ⟨2551318776245502533238373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3401758368327336710984497 2551318776245502533238373)
                ·
                  refine ⟨478372270546031724982195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2551318776245502533238373 478372270546031724982195)
                  ·
                    rfl

theorem cell22_4192320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 4].length) (baseStart_4192320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192320 prefixEnd_4192320 := by exact prefixLift 4192320
  have htrace : WordTrace (prefixWord ++ tailWord_4192320) baseStart_4192320 baseEnd_4192320 := by
    simpa [prefixWord, tailWord_4192320, baseEnd_4192320] using wordTrace_append hprefix tailTrace_4192320
  have hstable : (prefixWord ++ tailWord_4192320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192320).length < 2 ^ (prefixWord ++ tailWord_4192320).sum := by decide
  have hdescent : baseEnd_4192320 < baseStart_4192320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192348 : List Nat := [2, 2, 4, 1, 1, 3, 3, 6]
def baseStart_4192348 : Nat := 118140960795 + 4192348 * 2 ^ 59
def prefixEnd_4192348 : Nat := 4983230072969 + 3 ^ 40 * 4192348 * 2
def baseEnd_4192348 : Nat := 159458488512256937249611

theorem tailTrace_4192348 : CollatzResearch.WordTrace tailWord_4192348 prefixEnd_4192348 159458488512256937249611 := by
  unfold tailWord_4192348
  simp only [CollatzResearch.WordTrace]
  refine ⟨76453746707923333440076849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101938328943897777920102465 76453746707923333440076849)
  ·
    refine ⟨57340310030942500080057637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76453746707923333440076849 57340310030942500080057637)
    ·
      refine ⟨10751308130801718765010807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57340310030942500080057637 10751308130801718765010807)
      ·
        refine ⟨16126962196202578147516211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10751308130801718765010807 16126962196202578147516211)
        ·
          refine ⟨24190443294303867221274317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16126962196202578147516211 24190443294303867221274317)
          ·
            refine ⟨9071416235363950207977869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24190443294303867221274317 9071416235363950207977869)
            ·
              refine ⟨3401781088261481327991701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9071416235363950207977869 3401781088261481327991701)
              ·
                refine ⟨159458488512256937249611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3401781088261481327991701 159458488512256937249611)
                ·
                  rfl

theorem cell22_4192348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 6].length) (baseStart_4192348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192348 prefixEnd_4192348 := by exact prefixLift 4192348
  have htrace : WordTrace (prefixWord ++ tailWord_4192348) baseStart_4192348 baseEnd_4192348 := by
    simpa [prefixWord, tailWord_4192348, baseEnd_4192348] using wordTrace_append hprefix tailTrace_4192348
  have hstable : (prefixWord ++ tailWord_4192348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192348).length < 2 ^ (prefixWord ++ tailWord_4192348).sum := by decide
  have hdescent : baseEnd_4192348 < baseStart_4192348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192380 : List Nat := [2, 2, 2, 1, 1, 4, 2, 4, 1, 3]
def baseStart_4192380 : Nat := 118140960795 + 4192380 * 2 ^ 59
def prefixEnd_4192380 : Nat := 4983230072969 + 3 ^ 40 * 4192380 * 2
def baseEnd_4192380 : Nat := 1435137350864275018446401

theorem tailTrace_4192380 : CollatzResearch.WordTrace tailWord_4192380 prefixEnd_4192380 1435137350864275018446401 := by
  unfold tailWord_4192380
  simp only [CollatzResearch.WordTrace]
  refine ⟨76454330275865368172659297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101939107034487157563545729 76454330275865368172659297)
  ·
    refine ⟨57340747706899026129494473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76454330275865368172659297 57340747706899026129494473)
    ·
      refine ⟨43005560780174269597120855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57340747706899026129494473 43005560780174269597120855)
      ·
        refine ⟨64508341170261404395681283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43005560780174269597120855 64508341170261404395681283)
        ·
          refine ⟨96762511755392106593521925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64508341170261404395681283 96762511755392106593521925)
          ·
            refine ⟨18142970954136019986285361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96762511755392106593521925 18142970954136019986285361)
            ·
              refine ⟨13607228215602014989714021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18142970954136019986285361 13607228215602014989714021)
              ·
                refine ⟨2551355290425377810571379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13607228215602014989714021 2551355290425377810571379)
                ·
                  refine ⟨3827032935638066715857069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551355290425377810571379 3827032935638066715857069)
                  ·
                    refine ⟨1435137350864275018446401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3827032935638066715857069 1435137350864275018446401)
                    ·
                      rfl

theorem cell22_4192380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_4192380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192380 prefixEnd_4192380 := by exact prefixLift 4192380
  have htrace : WordTrace (prefixWord ++ tailWord_4192380) baseStart_4192380 baseEnd_4192380 := by
    simpa [prefixWord, tailWord_4192380, baseEnd_4192380] using wordTrace_append hprefix tailTrace_4192380
  have hstable : (prefixWord ++ tailWord_4192380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192380).length < 2 ^ (prefixWord ++ tailWord_4192380).sum := by decide
  have hdescent : baseEnd_4192380 < baseStart_4192380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192391 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 2, 5]
def baseStart_4192391 : Nat := 118140960795 + 4192391 * 2 ^ 59
def prefixEnd_4192391 : Nat := 4983230072969 + 3 ^ 40 * 4192391 * 2
def baseEnd_4192391 : Nat := 1435141116389074656421367

theorem tailTrace_4192391 : CollatzResearch.WordTrace tailWord_4192391 prefixEnd_4192391 1435141116389074656421367 := by
  unfold tailWord_4192391
  simp only [CollatzResearch.WordTrace]
  refine ⟨152909061754690885223969027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101939374503127256815979351 152909061754690885223969027)
  ·
    refine ⟨229363592632036327835953541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152909061754690885223969027 229363592632036327835953541)
    ·
      refine ⟨43005673618506811469241289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229363592632036327835953541 43005673618506811469241289)
      ·
        refine ⟨32254255213880108601930967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43005673618506811469241289 32254255213880108601930967)
        ·
          refine ⟨48381382820820162902896451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32254255213880108601930967 48381382820820162902896451)
          ·
            refine ⟨72572074231230244354344677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48381382820820162902896451 72572074231230244354344677)
            ·
              refine ⟨13607263918355670816439627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72572074231230244354344677 13607263918355670816439627)
              ·
                refine ⟨20410895877533506224659441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13607263918355670816439627 20410895877533506224659441)
                ·
                  refine ⟨15308171908150129668494581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20410895877533506224659441 15308171908150129668494581)
                  ·
                    refine ⟨1435141116389074656421367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15308171908150129668494581 1435141116389074656421367)
                    ·
                      rfl

theorem cell22_4192391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_4192391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192391 prefixEnd_4192391 := by exact prefixLift 4192391
  have htrace : WordTrace (prefixWord ++ tailWord_4192391) baseStart_4192391 baseEnd_4192391 := by
    simpa [prefixWord, tailWord_4192391, baseEnd_4192391] using wordTrace_append hprefix tailTrace_4192391
  have hstable : (prefixWord ++ tailWord_4192391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192391).length < 2 ^ (prefixWord ++ tailWord_4192391).sum := by decide
  have hdescent : baseEnd_4192391 < baseStart_4192391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192393 : List Nat := [1, 2, 1, 1, 4, 2, 5, 1, 5]
def baseStart_4192393 : Nat := 118140960795 + 4192393 * 2 ^ 59
def prefixEnd_4192393 : Nat := 4983230072969 + 3 ^ 40 * 4192393 * 2
def baseEnd_4192393 : Nat := 478380600343315772623787

theorem tailTrace_4192393 : CollatzResearch.WordTrace tailWord_4192393 prefixEnd_4192393 478380600343315772623787 := by
  unfold tailWord_4192393
  simp only [CollatzResearch.WordTrace]
  refine ⟨152909134700683639565541833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101939423133789093043694555 152909134700683639565541833)
  ·
    refine ⟨114681851025512729674156375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152909134700683639565541833 114681851025512729674156375)
    ·
      refine ⟨172022776538269094511234563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114681851025512729674156375 172022776538269094511234563)
      ·
        refine ⟨258034164807403641766851845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172022776538269094511234563 258034164807403641766851845)
        ·
          refine ⟨48381405901388182831284721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258034164807403641766851845 48381405901388182831284721)
          ·
            refine ⟨36286054426041137123463541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48381405901388182831284721 36286054426041137123463541)
            ·
              refine ⟨3401817602441356605324707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36286054426041137123463541 3401817602441356605324707)
              ·
                refine ⟨5102726403662034907987061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3401817602441356605324707 5102726403662034907987061)
                ·
                  refine ⟨478380600343315772623787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5102726403662034907987061 478380600343315772623787)
                  ·
                    rfl

theorem cell22_4192393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 5].length) (baseStart_4192393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192393 prefixEnd_4192393 := by exact prefixLift 4192393
  have htrace : WordTrace (prefixWord ++ tailWord_4192393) baseStart_4192393 baseEnd_4192393 := by
    simpa [prefixWord, tailWord_4192393, baseEnd_4192393] using wordTrace_append hprefix tailTrace_4192393
  have hstable : (prefixWord ++ tailWord_4192393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192393).length < 2 ^ (prefixWord ++ tailWord_4192393).sum := by decide
  have hdescent : baseEnd_4192393 < baseStart_4192393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192470 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_4192470 : Nat := 118140960795 + 4192470 * 2 ^ 59
def prefixEnd_4192470 : Nat := 4983230072969 + 3 ^ 40 * 4192470 * 2
def baseEnd_4192470 : Nat := 1435168159703544783696125

theorem tailTrace_4192470 : CollatzResearch.WordTrace tailWord_4192470 prefixEnd_4192470 1435168159703544783696125 := by
  unfold tailWord_4192470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9556996445087792607255929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101941295414269787810729909 9556996445087792607255929)
  ·
    refine ⟨7167747333815844455441947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9556996445087792607255929 7167747333815844455441947)
    ·
      refine ⟨10751621000723766683162921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7167747333815844455441947 10751621000723766683162921)
      ·
        refine ⟨8063715750542825012372191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10751621000723766683162921 8063715750542825012372191)
        ·
          refine ⟨12095573625814237518558287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8063715750542825012372191 12095573625814237518558287)
          ·
            refine ⟨18143360438721356277837431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12095573625814237518558287 18143360438721356277837431)
            ·
              refine ⟨27215040658082034416756147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18143360438721356277837431 27215040658082034416756147)
              ·
                refine ⟨40822560987123051625134221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27215040658082034416756147 40822560987123051625134221)
                ·
                  refine ⟨15308460370171144359425333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40822560987123051625134221 15308460370171144359425333)
                  ·
                    refine ⟨1435168159703544783696125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15308460370171144359425333 1435168159703544783696125)
                    ·
                      rfl

theorem cell22_4192470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_4192470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192470 prefixEnd_4192470 := by exact prefixLift 4192470
  have htrace : WordTrace (prefixWord ++ tailWord_4192470) baseStart_4192470 baseEnd_4192470 := by
    simpa [prefixWord, tailWord_4192470, baseEnd_4192470] using wordTrace_append hprefix tailTrace_4192470
  have hstable : (prefixWord ++ tailWord_4192470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192470).length < 2 ^ (prefixWord ++ tailWord_4192470).sum := by decide
  have hdescent : baseEnd_4192470 < baseStart_4192470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192483 : List Nat := [1, 1, 1, 8, 1, 10]
def baseStart_4192483 : Nat := 118140960795 + 4192483 * 2 ^ 59
def prefixEnd_4192483 : Nat := 4983230072969 + 3 ^ 40 * 4192483 * 2
def baseEnd_4192483 : Nat := 17718180368755766458285

theorem tailTrace_4192483 : CollatzResearch.WordTrace tailWord_4192483 prefixEnd_4192483 17718180368755766458285 := by
  unfold tailWord_4192483
  simp only [CollatzResearch.WordTrace]
  refine ⟨152912417270357584936318103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101941611513571723290878735 152912417270357584936318103)
  ·
    refine ⟨229368625905536377404477155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152912417270357584936318103 229368625905536377404477155)
    ·
      refine ⟨344052938858304566106715733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229368625905536377404477155 344052938858304566106715733)
      ·
        refine ⟨4031870377245756634063075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 344052938858304566106715733 4031870377245756634063075)
        ·
          refine ⟨6047805565868634951094613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4031870377245756634063075 6047805565868634951094613)
          ·
            refine ⟨17718180368755766458285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 6047805565868634951094613 17718180368755766458285)
            ·
              rfl

theorem cell22_4192483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 10].length) (baseStart_4192483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192483 prefixEnd_4192483 := by exact prefixLift 4192483
  have htrace : WordTrace (prefixWord ++ tailWord_4192483) baseStart_4192483 baseEnd_4192483 := by
    simpa [prefixWord, tailWord_4192483, baseEnd_4192483] using wordTrace_append hprefix tailTrace_4192483
  have hstable : (prefixWord ++ tailWord_4192483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192483).length < 2 ^ (prefixWord ++ tailWord_4192483).sum := by decide
  have hdescent : baseEnd_4192483 < baseStart_4192483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192487 : List Nat := [1, 1, 5, 3, 1, 2, 2, 2, 2, 3]
def baseStart_4192487 : Nat := 118140960795 + 4192487 * 2 ^ 59
def prefixEnd_4192487 : Nat := 4983230072969 + 3 ^ 40 * 4192487 * 2
def baseEnd_4192487 : Nat := 1435173979150962406021073

theorem tailTrace_4192487 : CollatzResearch.WordTrace tailWord_4192487 prefixEnd_4192487 1435173979150962406021073 := by
  unfold tailWord_4192487
  simp only [CollatzResearch.WordTrace]
  refine ⟨152912563162343093619463715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101941708774895395746309143 152912563162343093619463715)
  ·
    refine ⟨229368844743514640429195573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152912563162343093619463715 229368844743514640429195573)
    ·
      refine ⟨21503329194704497540237085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 229368844743514640429195573 21503329194704497540237085)
      ·
        refine ⟨8063748448014186577588907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21503329194704497540237085 8063748448014186577588907)
        ·
          refine ⟨12095622672021279866383361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8063748448014186577588907 12095622672021279866383361)
          ·
            refine ⟨9071717004015959899787521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12095622672021279866383361 9071717004015959899787521)
            ·
              refine ⟨6803787753011969924840641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9071717004015959899787521 6803787753011969924840641)
              ·
                refine ⟨5102840814758977443630481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6803787753011969924840641 5102840814758977443630481)
                ·
                  refine ⟨3827130611069233082722861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5102840814758977443630481 3827130611069233082722861)
                  ·
                    refine ⟨1435173979150962406021073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3827130611069233082722861 1435173979150962406021073)
                    ·
                      rfl

theorem cell22_4192487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_4192487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192487 prefixEnd_4192487 := by exact prefixLift 4192487
  have htrace : WordTrace (prefixWord ++ tailWord_4192487) baseStart_4192487 baseEnd_4192487 := by
    simpa [prefixWord, tailWord_4192487, baseEnd_4192487] using wordTrace_append hprefix tailTrace_4192487
  have hstable : (prefixWord ++ tailWord_4192487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192487).length < 2 ^ (prefixWord ++ tailWord_4192487).sum := by decide
  have hdescent : baseEnd_4192487 < baseStart_4192487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192519 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 2, 4]
def baseStart_4192519 : Nat := 118140960795 + 4192519 * 2 ^ 59
def prefixEnd_4192519 : Nat := 4983230072969 + 3 ^ 40 * 4192519 * 2
def baseEnd_4192519 : Nat := 1435184933404924989220975

theorem tailTrace_4192519 : CollatzResearch.WordTrace tailWord_4192519 prefixEnd_4192519 1435184933404924989220975 := by
  unfold tailWord_4192519
  simp only [CollatzResearch.WordTrace]
  refine ⟨152913730298227163084628611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101942486865484775389752407 152913730298227163084628611)
  ·
    refine ⟨229370595447340744626942917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152913730298227163084628611 229370595447340744626942917)
    ·
      refine ⟨43006986646376389617551797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229370595447340744626942917 43006986646376389617551797)
      ·
        refine ⟨4031904998097786526645481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43006986646376389617551797 4031904998097786526645481)
        ·
          refine ⟨3023928748573339894984111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4031904998097786526645481 3023928748573339894984111)
          ·
            refine ⟨4535893122860009842476167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3023928748573339894984111 4535893122860009842476167)
            ·
              refine ⟨6803839684290014763714251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535893122860009842476167 6803839684290014763714251)
              ·
                refine ⟨10205759526435022145571377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6803839684290014763714251 10205759526435022145571377)
                ·
                  refine ⟨7654319644826266609178533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10205759526435022145571377 7654319644826266609178533)
                  ·
                    refine ⟨1435184933404924989220975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7654319644826266609178533 1435184933404924989220975)
                    ·
                      rfl

theorem cell22_4192519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_4192519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192519 prefixEnd_4192519 := by exact prefixLift 4192519
  have htrace : WordTrace (prefixWord ++ tailWord_4192519) baseStart_4192519 baseEnd_4192519 := by
    simpa [prefixWord, tailWord_4192519, baseEnd_4192519] using wordTrace_append hprefix tailTrace_4192519
  have hstable : (prefixWord ++ tailWord_4192519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192519).length < 2 ^ (prefixWord ++ tailWord_4192519).sum := by decide
  have hdescent : baseEnd_4192519 < baseStart_4192519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192543 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 2, 5]
def baseStart_4192543 : Nat := 118140960795 + 4192543 * 2 ^ 59
def prefixEnd_4192543 : Nat := 4983230072969 + 3 ^ 40 * 4192543 * 2
def baseEnd_4192543 : Nat := 1435193149095396926620901

theorem tailTrace_4192543 : CollatzResearch.WordTrace tailWord_4192543 prefixEnd_4192543 1435193149095396926620901 := by
  unfold tailWord_4192543
  simp only [CollatzResearch.WordTrace]
  refine ⟨152914605650140215183502283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101943070433426810122334855 152914605650140215183502283)
  ·
    refine ⟨229371908475210322775253425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152914605650140215183502283 229371908475210322775253425)
    ·
      refine ⟨172028931356407742081440069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229371908475210322775253425 172028931356407742081440069)
      ·
        refine ⟨32255424629326451640270013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172028931356407742081440069 32255424629326451640270013)
        ·
          refine ⟨12095784235997419365101255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32255424629326451640270013 12095784235997419365101255)
          ·
            refine ⟨18143676353996129047651883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12095784235997419365101255 18143676353996129047651883)
            ·
              refine ⟨27215514530994193571477825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18143676353996129047651883 27215514530994193571477825)
              ·
                refine ⟨20411635898245645178608369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27215514530994193571477825 20411635898245645178608369)
                ·
                  refine ⟨15308726923684233883956277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20411635898245645178608369 15308726923684233883956277)
                  ·
                    refine ⟨1435193149095396926620901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15308726923684233883956277 1435193149095396926620901)
                    ·
                      rfl

theorem cell22_4192543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_4192543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192543 prefixEnd_4192543 := by exact prefixLift 4192543
  have htrace : WordTrace (prefixWord ++ tailWord_4192543) baseStart_4192543 baseEnd_4192543 := by
    simpa [prefixWord, tailWord_4192543, baseEnd_4192543] using wordTrace_append hprefix tailTrace_4192543
  have hstable : (prefixWord ++ tailWord_4192543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192543).length < 2 ^ (prefixWord ++ tailWord_4192543).sum := by decide
  have hdescent : baseEnd_4192543 < baseStart_4192543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192562 : List Nat := [3, 2, 1, 1, 5, 1, 3, 1, 5]
def baseStart_4192562 : Nat := 118140960795 + 4192562 * 2 ^ 59
def prefixEnd_4192562 : Nat := 4983230072969 + 3 ^ 40 * 4192562 * 2
def baseEnd_4192562 : Nat := 478399884394562403465281

theorem tailTrace_4192562 : CollatzResearch.WordTrace tailWord_4192562 prefixEnd_4192562 478399884394562403465281 := by
  unfold tailWord_4192562
  simp only [CollatzResearch.WordTrace]
  refine ⟨38228824659267845357110985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101943532424714254285629293 38228824659267845357110985)
  ·
    refine ⟨28671618494450884017833239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38228824659267845357110985 28671618494450884017833239)
    ·
      refine ⟨43007427741676326026749859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28671618494450884017833239 43007427741676326026749859)
      ·
        refine ⟨64511141612514489040124789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43007427741676326026749859 64511141612514489040124789)
        ·
          refine ⟨6047919526173233347511699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64511141612514489040124789 6047919526173233347511699)
          ·
            refine ⟨9071879289259850021267549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6047919526173233347511699 9071879289259850021267549)
            ·
              refine ⟨3401954733472443757975331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9071879289259850021267549 3401954733472443757975331)
              ·
                refine ⟨5102932100208665636962997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3401954733472443757975331 5102932100208665636962997)
                ·
                  refine ⟨478399884394562403465281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5102932100208665636962997 478399884394562403465281)
                  ·
                    rfl

theorem cell22_4192562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_4192562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192562 prefixEnd_4192562 := by exact prefixLift 4192562
  have htrace : WordTrace (prefixWord ++ tailWord_4192562) baseStart_4192562 baseEnd_4192562 := by
    simpa [prefixWord, tailWord_4192562, baseEnd_4192562] using wordTrace_append hprefix tailTrace_4192562
  have hstable : (prefixWord ++ tailWord_4192562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192562).length < 2 ^ (prefixWord ++ tailWord_4192562).sum := by decide
  have hdescent : baseEnd_4192562 < baseStart_4192562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192575 : List Nat := [1, 1, 2, 2, 4, 1, 4, 2, 1, 4]
def baseStart_4192575 : Nat := 118140960795 + 4192575 * 2 ^ 59
def prefixEnd_4192575 : Nat := 4983230072969 + 3 ^ 40 * 4192575 * 2
def baseEnd_4192575 : Nat := 1435204103349359509820803

theorem tailTrace_4192575 : CollatzResearch.WordTrace tailWord_4192575 prefixEnd_4192575 1435204103349359509820803 := by
  unfold tailWord_4192575
  simp only [CollatzResearch.WordTrace]
  refine ⟨152915772786024284648667179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101943848524016189765778119 152915772786024284648667179)
  ·
    refine ⟨229373659179036426973000769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152915772786024284648667179 229373659179036426973000769)
    ·
      refine ⟨172030244384277320229750577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229373659179036426973000769 172030244384277320229750577)
      ·
        refine ⟨129022683288207990172312933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172030244384277320229750577 129022683288207990172312933)
        ·
          refine ⟨24191753116538998157308675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129022683288207990172312933 24191753116538998157308675)
          ·
            refine ⟨36287629674808497235963013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24191753116538998157308675 36287629674808497235963013)
            ·
              refine ⟨6803930564026593231743065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36287629674808497235963013 6803930564026593231743065)
              ·
                refine ⟨5102947923019944923807299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6803930564026593231743065 5102947923019944923807299)
                ·
                  refine ⟨7654421884529917385710949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5102947923019944923807299 7654421884529917385710949)
                  ·
                    refine ⟨1435204103349359509820803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7654421884529917385710949 1435204103349359509820803)
                    ·
                      rfl

theorem cell22_4192575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_4192575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192575 prefixEnd_4192575 := by exact prefixLift 4192575
  have htrace : WordTrace (prefixWord ++ tailWord_4192575) baseStart_4192575 baseEnd_4192575 := by
    simpa [prefixWord, tailWord_4192575, baseEnd_4192575] using wordTrace_append hprefix tailTrace_4192575
  have hstable : (prefixWord ++ tailWord_4192575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192575).length < 2 ^ (prefixWord ++ tailWord_4192575).sum := by decide
  have hdescent : baseEnd_4192575 < baseStart_4192575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192588 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_4192588 : Nat := 118140960795 + 4192588 * 2 ^ 59
def prefixEnd_4192588 : Nat := 4983230072969 + 3 ^ 40 * 4192588 * 2
def baseEnd_4192588 : Nat := 1435208553515031809245763

theorem tailTrace_4192588 : CollatzResearch.WordTrace tailWord_4192588 prefixEnd_4192588 1435208553515031809245763 := by
  unfold tailWord_4192588
  simp only [CollatzResearch.WordTrace]
  refine ⟨76458123467488593934445209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101944164623318125245926945 76458123467488593934445209)
  ·
    refine ⟨57343592600616445450833907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76458123467488593934445209 57343592600616445450833907)
    ·
      refine ⟨86015388900924668176250861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57343592600616445450833907 86015388900924668176250861)
      ·
        refine ⟨32255770837846750566094073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86015388900924668176250861 32255770837846750566094073)
        ·
          refine ⟨24191828128385062924570555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32255770837846750566094073 24191828128385062924570555)
          ·
            refine ⟨36287742192577594386855833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24191828128385062924570555 36287742192577594386855833)
            ·
              refine ⟨27215806644433195790141875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36287742192577594386855833 27215806644433195790141875)
              ·
                refine ⟨40823709966649793685212813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27215806644433195790141875 40823709966649793685212813)
                ·
                  refine ⟨15308891237493672631954805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40823709966649793685212813 15308891237493672631954805)
                  ·
                    refine ⟨1435208553515031809245763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15308891237493672631954805 1435208553515031809245763)
                    ·
                      rfl

theorem cell22_4192588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_4192588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192588 prefixEnd_4192588 := by exact prefixLift 4192588
  have htrace : WordTrace (prefixWord ++ tailWord_4192588) baseStart_4192588 baseEnd_4192588 := by
    simpa [prefixWord, tailWord_4192588, baseEnd_4192588] using wordTrace_append hprefix tailTrace_4192588
  have hstable : (prefixWord ++ tailWord_4192588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192588).length < 2 ^ (prefixWord ++ tailWord_4192588).sum := by decide
  have hdescent : baseEnd_4192588 < baseStart_4192588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192590 : List Nat := [4, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_4192590 : Nat := 118140960795 + 4192590 * 2 ^ 59
def prefixEnd_4192590 : Nat := 4983230072969 + 3 ^ 40 * 4192590 * 2
def baseEnd_4192590 : Nat := 478403079385301490231919

theorem tailTrace_4192590 : CollatzResearch.WordTrace tailWord_4192590 prefixEnd_4192590 478403079385301490231919 := by
  unfold tailWord_4192590
  simp only [CollatzResearch.WordTrace]
  refine ⟨19114539985121242776307903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101944213253979961473642149 19114539985121242776307903)
  ·
    refine ⟨28671809977681864164461855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19114539985121242776307903 28671809977681864164461855)
    ·
      refine ⟨43007714966522796246692783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28671809977681864164461855 43007714966522796246692783)
      ·
        refine ⟨64511572449784194370039175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43007714966522796246692783 64511572449784194370039175)
        ·
          refine ⟨96767358674676291555058763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64511572449784194370039175 96767358674676291555058763)
          ·
            refine ⟨145151038012014437332588145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96767358674676291555058763 145151038012014437332588145)
            ·
              refine ⟨108863278509010827999441109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145151038012014437332588145 108863278509010827999441109)
              ·
                refine ⟨2551483090054941281236901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108863278509010827999441109 2551483090054941281236901)
                ·
                  refine ⟨478403079385301490231919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2551483090054941281236901 478403079385301490231919)
                  ·
                    rfl

theorem cell22_4192590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_4192590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192590 prefixEnd_4192590 := by exact prefixLift 4192590
  have htrace : WordTrace (prefixWord ++ tailWord_4192590) baseStart_4192590 baseEnd_4192590 := by
    simpa [prefixWord, tailWord_4192590, baseEnd_4192590] using wordTrace_append hprefix tailTrace_4192590
  have hstable : (prefixWord ++ tailWord_4192590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192590).length < 2 ^ (prefixWord ++ tailWord_4192590).sum := by decide
  have hdescent : baseEnd_4192590 < baseStart_4192590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192663 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 7]
def baseStart_4192663 : Nat := 118140960795 + 4192663 * 2 ^ 59
def prefixEnd_4192663 : Nat := 4983230072969 + 3 ^ 40 * 4192663 * 2
def baseEnd_4192663 : Nat := 478411409182585537873511

theorem tailTrace_4192663 : CollatzResearch.WordTrace tailWord_4192663 prefixEnd_4192663 478411409182585537873511 := by
  unfold tailWord_4192663
  simp only [CollatzResearch.WordTrace]
  refine ⟨152918982409705475677870643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101945988273136983785247095 152918982409705475677870643)
  ·
    refine ⟨229378473614558213516805965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152918982409705475677870643 229378473614558213516805965)
    ·
      refine ⟨86016927605459330068802237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229378473614558213516805965 86016927605459330068802237)
      ·
        refine ⟨32256347852047248775800839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86016927605459330068802237 32256347852047248775800839)
        ·
          refine ⟨48384521778070873163701259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32256347852047248775800839 48384521778070873163701259)
          ·
            refine ⟨72576782667106309745551889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48384521778070873163701259 72576782667106309745551889)
            ·
              refine ⟨54432587000329732309163917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72576782667106309745551889 54432587000329732309163917)
              ·
                refine ⟨20412220125123649615936469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54432587000329732309163917 20412220125123649615936469)
                ·
                  refine ⟨478411409182585537873511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20412220125123649615936469 478411409182585537873511)
                  ·
                    rfl

theorem cell22_4192663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 7].length) (baseStart_4192663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192663 prefixEnd_4192663 := by exact prefixLift 4192663
  have htrace : WordTrace (prefixWord ++ tailWord_4192663) baseStart_4192663 baseEnd_4192663 := by
    simpa [prefixWord, tailWord_4192663, baseEnd_4192663] using wordTrace_append hprefix tailTrace_4192663
  have hstable : (prefixWord ++ tailWord_4192663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192663).length < 2 ^ (prefixWord ++ tailWord_4192663).sum := by decide
  have hdescent : baseEnd_4192663 < baseStart_4192663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192725 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 6]
def baseStart_4192725 : Nat := 118140960795 + 4192725 * 2 ^ 59
def prefixEnd_4192725 : Nat := 4983230072969 + 3 ^ 40 * 4192725 * 2
def baseEnd_4192725 : Nat := 478418483804936372856781

theorem tailTrace_4192725 : CollatzResearch.WordTrace tailWord_4192725 prefixEnd_4192725 478418483804936372856781 := by
  unfold tailWord_4192725
  simp only [CollatzResearch.WordTrace]
  refine ⟨152921243735480860266627629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101947495823653906844418419 152921243735480860266627629)
  ·
    refine ⟨57345466400805322599985361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152921243735480860266627629 57345466400805322599985361)
    ·
      refine ⟨43009099800603991949989021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57345466400805322599985361 43009099800603991949989021)
      ·
        refine ⟨16128412425226496981245883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43009099800603991949989021 16128412425226496981245883)
        ·
          refine ⟨24192618637839745471868825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16128412425226496981245883 24192618637839745471868825)
          ·
            refine ⟨18144463978379809103901619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24192618637839745471868825 18144463978379809103901619)
            ·
              refine ⟨27216695967569713655852429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18144463978379809103901619 27216695967569713655852429)
              ·
                refine ⟨10206260987838642620944661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27216695967569713655852429 10206260987838642620944661)
                ·
                  refine ⟨478418483804936372856781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10206260987838642620944661 478418483804936372856781)
                  ·
                    rfl

theorem cell22_4192725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_4192725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192725 prefixEnd_4192725 := by exact prefixLift 4192725
  have htrace : WordTrace (prefixWord ++ tailWord_4192725) baseStart_4192725 baseEnd_4192725 := by
    simpa [prefixWord, tailWord_4192725, baseEnd_4192725] using wordTrace_append hprefix tailTrace_4192725
  have hstable : (prefixWord ++ tailWord_4192725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192725).length < 2 ^ (prefixWord ++ tailWord_4192725).sum := by decide
  have hdescent : baseEnd_4192725 < baseStart_4192725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192755 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 2, 4]
def baseStart_4192755 : Nat := 118140960795 + 4192755 * 2 ^ 59
def prefixEnd_4192755 : Nat := 4983230072969 + 3 ^ 40 * 4192755 * 2
def baseEnd_4192755 : Nat := 1435265721027899040320251

theorem tailTrace_4192755 : CollatzResearch.WordTrace tailWord_4192755 prefixEnd_4192755 1435265721027899040320251 := by
  unfold tailWord_4192755
  simp only [CollatzResearch.WordTrace]
  refine ⟨152922337925372175390219719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101948225283581450260146479 152922337925372175390219719)
  ·
    refine ⟨229383506888058263085329579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152922337925372175390219719 229383506888058263085329579)
    ·
      refine ⟨344075260332087394627994369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229383506888058263085329579 344075260332087394627994369)
      ·
        refine ⟨258056445249065545970995777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344075260332087394627994369 258056445249065545970995777)
        ·
          refine ⟨193542333936799159478246833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258056445249065545970995777 193542333936799159478246833)
          ·
            refine ⟨145156750452599369608685125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193542333936799159478246833 145156750452599369608685125)
            ·
              refine ⟨27216890709862381801628461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145156750452599369608685125 27216890709862381801628461)
              ·
                refine ⟨10206334016198393175610673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27216890709862381801628461 10206334016198393175610673)
                ·
                  refine ⟨7654750512148794881708005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10206334016198393175610673 7654750512148794881708005)
                  ·
                    refine ⟨1435265721027899040320251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7654750512148794881708005 1435265721027899040320251)
                    ·
                      rfl

theorem cell22_4192755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 4].length) (baseStart_4192755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192755 prefixEnd_4192755 := by exact prefixLift 4192755
  have htrace : WordTrace (prefixWord ++ tailWord_4192755) baseStart_4192755 baseEnd_4192755 := by
    simpa [prefixWord, tailWord_4192755, baseEnd_4192755] using wordTrace_append hprefix tailTrace_4192755
  have hstable : (prefixWord ++ tailWord_4192755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192755).length < 2 ^ (prefixWord ++ tailWord_4192755).sum := by decide
  have hdescent : baseEnd_4192755 < baseStart_4192755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192772 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_4192772 : Nat := 118140960795 + 4192772 * 2 ^ 59
def prefixEnd_4192772 : Nat := 4983230072969 + 3 ^ 40 * 4192772 * 2
def baseEnd_4192772 : Nat := 1435271540475316662645199

theorem tailTrace_4192772 : CollatzResearch.WordTrace tailWord_4192772 prefixEnd_4192772 1435271540475316662645199 := by
  unfold tailWord_4192772
  simp only [CollatzResearch.WordTrace]
  refine ⟨76461478983155293646794285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101948638644207058195725713 76461478983155293646794285)
  ·
    refine ⟨28673054618683235117547857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76461478983155293646794285 28673054618683235117547857)
    ·
      refine ⟨21504790964012426338160893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28673054618683235117547857 21504790964012426338160893)
      ·
        refine ⟨8064296611504659876810335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21504790964012426338160893 8064296611504659876810335)
        ·
          refine ⟨12096444917256989815215503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8064296611504659876810335 12096444917256989815215503)
          ·
            refine ⟨18144667375885484722823255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12096444917256989815215503 18144667375885484722823255)
            ·
              refine ⟨27217001063828227084234883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18144667375885484722823255 27217001063828227084234883)
              ·
                refine ⟨40825501595742340626352325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27217001063828227084234883 40825501595742340626352325)
                ·
                  refine ⟨7654781549201688867441061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40825501595742340626352325 7654781549201688867441061)
                  ·
                    refine ⟨1435271540475316662645199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7654781549201688867441061 1435271540475316662645199)
                    ·
                      rfl

theorem cell22_4192772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_4192772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192772 prefixEnd_4192772 := by exact prefixLift 4192772
  have htrace : WordTrace (prefixWord ++ tailWord_4192772) baseStart_4192772 baseEnd_4192772 := by
    simpa [prefixWord, tailWord_4192772, baseEnd_4192772] using wordTrace_append hprefix tailTrace_4192772
  have hstable : (prefixWord ++ tailWord_4192772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192772).length < 2 ^ (prefixWord ++ tailWord_4192772).sum := by decide
  have hdescent : baseEnd_4192772 < baseStart_4192772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192791 : List Nat := [1, 1, 3, 6, 1, 1, 1, 3, 2, 3]
def baseStart_4192791 : Nat := 118140960795 + 4192791 * 2 ^ 59
def prefixEnd_4192791 : Nat := 4983230072969 + 3 ^ 40 * 4192791 * 2
def baseEnd_4192791 : Nat := 1435278044563606946420141

theorem tailTrace_4192791 : CollatzResearch.WordTrace tailWord_4192791 prefixEnd_4192791 1435278044563606946420141 := by
  unfold tailWord_4192791
  simp only [CollatzResearch.WordTrace]
  refine ⟨152923650953241753538530227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101949100635494502359020151 152923650953241753538530227)
  ·
    refine ⟨229385476429862630307795341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152923650953241753538530227 229385476429862630307795341)
    ·
      refine ⟨86019553661198486365423253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229385476429862630307795341 86019553661198486365423253)
      ·
        refine ⟨4032166577868679048379215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86019553661198486365423253 4032166577868679048379215)
        ·
          refine ⟨6048249866803018572568823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4032166577868679048379215 6048249866803018572568823)
          ·
            refine ⟨9072374800204527858853235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6048249866803018572568823 9072374800204527858853235)
            ·
              refine ⟨13608562200306791788279853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9072374800204527858853235 13608562200306791788279853)
              ·
                refine ⟨5103210825115046920604945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13608562200306791788279853 5103210825115046920604945)
                ·
                  refine ⟨3827408118836285190453709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5103210825115046920604945 3827408118836285190453709)
                  ·
                    refine ⟨1435278044563606946420141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3827408118836285190453709 1435278044563606946420141)
                    ·
                      rfl

theorem cell22_4192791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_4192791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192791 prefixEnd_4192791 := by exact prefixLift 4192791
  have htrace : WordTrace (prefixWord ++ tailWord_4192791) baseStart_4192791 baseEnd_4192791 := by
    simpa [prefixWord, tailWord_4192791, baseEnd_4192791] using wordTrace_append hprefix tailTrace_4192791
  have hstable : (prefixWord ++ tailWord_4192791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192791).length < 2 ^ (prefixWord ++ tailWord_4192791).sum := by decide
  have hdescent : baseEnd_4192791 < baseStart_4192791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192802 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_4192802 : Nat := 118140960795 + 4192802 * 2 ^ 59
def prefixEnd_4192802 : Nat := 4983230072969 + 3 ^ 40 * 4192802 * 2
def baseEnd_4192802 : Nat := 1435281810088406584395107

theorem tailTrace_4192802 : CollatzResearch.WordTrace tailWord_4192802 prefixEnd_4192802 1435281810088406584395107 := by
  unfold tailWord_4192802
  simp only [CollatzResearch.WordTrace]
  refine ⟨38231013039050475604295165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101949368104134601611453773 38231013039050475604295165)
  ·
    refine ⟨14336629889643928351610687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38231013039050475604295165 14336629889643928351610687)
    ·
      refine ⟨21504944834465892527416031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14336629889643928351610687 21504944834465892527416031)
      ·
        refine ⟨32257417251698838791124047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21504944834465892527416031 32257417251698838791124047)
        ·
          refine ⟨48386125877548258186686071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32257417251698838791124047 48386125877548258186686071)
          ·
            refine ⟨72579188816322387280029107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48386125877548258186686071 72579188816322387280029107)
            ·
              refine ⟨108868783224483580920043661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72579188816322387280029107 108868783224483580920043661)
              ·
                refine ⟨40825793709181342845016373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108868783224483580920043661 40825793709181342845016373)
                ·
                  refine ⟨3827418160235750891720285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40825793709181342845016373 3827418160235750891720285)
                  ·
                    refine ⟨1435281810088406584395107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3827418160235750891720285 1435281810088406584395107)
                    ·
                      rfl

theorem cell22_4192802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_4192802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192802 prefixEnd_4192802 := by exact prefixLift 4192802
  have htrace : WordTrace (prefixWord ++ tailWord_4192802) baseStart_4192802 baseEnd_4192802 := by
    simpa [prefixWord, tailWord_4192802, baseEnd_4192802] using wordTrace_append hprefix tailTrace_4192802
  have hstable : (prefixWord ++ tailWord_4192802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192802).length < 2 ^ (prefixWord ++ tailWord_4192802).sum := by decide
  have hdescent : baseEnd_4192802 < baseStart_4192802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192819 : List Nat := [1, 1, 1, 2, 4, 2, 2, 5, 1, 3]
def baseStart_4192819 : Nat := 118140960795 + 4192819 * 2 ^ 59
def prefixEnd_4192819 : Nat := 4983230072969 + 3 ^ 40 * 4192819 * 2
def baseEnd_4192819 : Nat := 1435287629535824206720055

theorem tailTrace_4192819 : CollatzResearch.WordTrace tailWord_4192819 prefixEnd_4192819 1435287629535824206720055 := by
  unfold tailWord_4192819
  simp only [CollatzResearch.WordTrace]
  refine ⟨152924672197140314320549511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101949781464760209547033007 152924672197140314320549511)
  ·
    refine ⟨229387008295710471480824267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152924672197140314320549511 229387008295710471480824267)
    ·
      refine ⟨344080512443565707221236401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229387008295710471480824267 344080512443565707221236401)
      ·
        refine ⟨258060384332674280415927301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344080512443565707221236401 258060384332674280415927301)
        ·
          refine ⟨48386322062376427577986369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258060384332674280415927301 48386322062376427577986369)
          ·
            refine ⟨36289741546782320683489777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48386322062376427577986369 36289741546782320683489777)
            ·
              refine ⟨27217306160086740512617333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36289741546782320683489777 27217306160086740512617333)
              ·
                refine ⟨2551622452508131923057875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27217306160086740512617333 2551622452508131923057875)
                ·
                  refine ⟨3827433678762197884586813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551622452508131923057875 3827433678762197884586813)
                  ·
                    refine ⟨1435287629535824206720055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3827433678762197884586813 1435287629535824206720055)
                    ·
                      rfl

theorem cell22_4192819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 1, 3].length) (baseStart_4192819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192819 prefixEnd_4192819 := by exact prefixLift 4192819
  have htrace : WordTrace (prefixWord ++ tailWord_4192819) baseStart_4192819 baseEnd_4192819 := by
    simpa [prefixWord, tailWord_4192819, baseEnd_4192819] using wordTrace_append hprefix tailTrace_4192819
  have hstable : (prefixWord ++ tailWord_4192819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192819).length < 2 ^ (prefixWord ++ tailWord_4192819).sum := by decide
  have hdescent : baseEnd_4192819 < baseStart_4192819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192875 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 3, 5]
def baseStart_4192875 : Nat := 118140960795 + 4192875 * 2 ^ 59
def prefixEnd_4192875 : Nat := 4983230072969 + 3 ^ 40 * 4192875 * 2
def baseEnd_4192875 : Nat := 1435306799480258727319883

theorem tailTrace_4192875 : CollatzResearch.WordTrace tailWord_4192875 prefixEnd_4192875 1435306799480258727319883 := by
  unfold tailWord_4192875
  simp only [CollatzResearch.WordTrace]
  refine ⟨152926714684937435884588079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101951143123291623923058719 152926714684937435884588079)
  ·
    refine ⟨229390072027406153826882119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152926714684937435884588079 229390072027406153826882119)
    ·
      refine ⟨344085108041109230740323179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229390072027406153826882119 344085108041109230740323179)
      ·
        refine ⟨516127662061663846110484769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344085108041109230740323179 516127662061663846110484769)
        ·
          refine ⟨387095746546247884582863577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516127662061663846110484769 387095746546247884582863577)
          ·
            refine ⟨290321809909685913437147683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387095746546247884582863577 290321809909685913437147683)
            ·
              refine ⟨435482714864528870155721525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290321809909685913437147683 435482714864528870155721525)
              ·
                refine ⟨40826504518549581577098893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 435482714864528870155721525 40826504518549581577098893)
                ·
                  refine ⟨15309939194456093091412085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40826504518549581577098893 15309939194456093091412085)
                  ·
                    refine ⟨1435306799480258727319883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15309939194456093091412085 1435306799480258727319883)
                    ·
                      rfl

theorem cell22_4192875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 5].length) (baseStart_4192875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192875 prefixEnd_4192875 := by exact prefixLift 4192875
  have htrace : WordTrace (prefixWord ++ tailWord_4192875) baseStart_4192875 baseEnd_4192875 := by
    simpa [prefixWord, tailWord_4192875, baseEnd_4192875] using wordTrace_append hprefix tailTrace_4192875
  have hstable : (prefixWord ++ tailWord_4192875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192875).length < 2 ^ (prefixWord ++ tailWord_4192875).sum := by decide
  have hdescent : baseEnd_4192875 < baseStart_4192875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192879 : List Nat := [1, 1, 2, 1, 3, 2, 6, 1, 1, 4]
def baseStart_4192879 : Nat := 118140960795 + 4192879 * 2 ^ 59
def prefixEnd_4192879 : Nat := 4983230072969 + 3 ^ 40 * 4192879 * 2
def baseEnd_4192879 : Nat := 1435308168762004050219871

theorem tailTrace_4192879 : CollatzResearch.WordTrace tailWord_4192879 prefixEnd_4192879 1435308168762004050219871 := by
  unfold tailWord_4192879
  simp only [CollatzResearch.WordTrace]
  refine ⟨152926860576922944567733691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101951240384615296378489127 152926860576922944567733691)
  ·
    refine ⟨229390290865384416851600537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152926860576922944567733691 229390290865384416851600537)
    ·
      refine ⟨172042718149038312638700403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229390290865384416851600537 172042718149038312638700403)
      ·
        refine ⟨258064077223557468958050605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172042718149038312638700403 258064077223557468958050605)
        ·
          refine ⟨96774028958834050859268977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258064077223557468958050605 96774028958834050859268977)
          ·
            refine ⟨72580521719125538144451733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96774028958834050859268977 72580521719125538144451733)
            ·
              refine ⟨3402211955584009600521175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72580521719125538144451733 3402211955584009600521175)
              ·
                refine ⟨5103317933376014400781763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3402211955584009600521175 5103317933376014400781763)
                ·
                  refine ⟨7654976900064021601172645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5103317933376014400781763 7654976900064021601172645)
                  ·
                    refine ⟨1435308168762004050219871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7654976900064021601172645 1435308168762004050219871)
                    ·
                      rfl

theorem cell22_4192879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 1, 4].length) (baseStart_4192879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192879 prefixEnd_4192879 := by exact prefixLift 4192879
  have htrace : WordTrace (prefixWord ++ tailWord_4192879) baseStart_4192879 baseEnd_4192879 := by
    simpa [prefixWord, tailWord_4192879, baseEnd_4192879] using wordTrace_append hprefix tailTrace_4192879
  have hstable : (prefixWord ++ tailWord_4192879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192879).length < 2 ^ (prefixWord ++ tailWord_4192879).sum := by decide
  have hdescent : baseEnd_4192879 < baseStart_4192879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192905 : List Nat := [1, 2, 1, 1, 4, 1, 1, 11]
def baseStart_4192905 : Nat := 118140960795 + 4192905 * 2 ^ 59
def prefixEnd_4192905 : Nat := 4983230072969 + 3 ^ 40 * 4192905 * 2
def baseEnd_4192905 : Nat := 159479674343705405452199

theorem tailTrace_4192905 : CollatzResearch.WordTrace tailWord_4192905 prefixEnd_4192905 159479674343705405452199 := by
  unfold tailWord_4192905
  simp only [CollatzResearch.WordTrace]
  refine ⟨152927808874828751008180169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101951872583219167338786779 152927808874828751008180169)
  ·
    refine ⟨114695856656121563256135127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152927808874828751008180169 114695856656121563256135127)
    ·
      refine ⟨172043784984182344884202691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114695856656121563256135127 172043784984182344884202691)
      ·
        refine ⟨258065677476273517326304037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172043784984182344884202691 258065677476273517326304037)
        ·
          refine ⟨48387314526801284498682007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258065677476273517326304037 48387314526801284498682007)
          ·
            refine ⟨72580971790201926748023011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48387314526801284498682007 72580971790201926748023011)
            ·
              refine ⟨108871457685302890122034517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72580971790201926748023011 108871457685302890122034517)
              ·
                refine ⟨159479674343705405452199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 108871457685302890122034517 159479674343705405452199)
                ·
                  rfl

theorem cell22_4192905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 11].length) (baseStart_4192905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192905 prefixEnd_4192905 := by exact prefixLift 4192905
  have htrace : WordTrace (prefixWord ++ tailWord_4192905) baseStart_4192905 baseEnd_4192905 := by
    simpa [prefixWord, tailWord_4192905, baseEnd_4192905] using wordTrace_append hprefix tailTrace_4192905
  have hstable : (prefixWord ++ tailWord_4192905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192905).length < 2 ^ (prefixWord ++ tailWord_4192905).sum := by decide
  have hdescent : baseEnd_4192905 < baseStart_4192905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192928 : List Nat := [2, 1, 1, 4, 5, 1, 1, 3, 4]
def baseStart_4192928 : Nat := 118140960795 + 4192928 * 2 ^ 59
def prefixEnd_4192928 : Nat := 4983230072969 + 3 ^ 40 * 4192928 * 2
def baseEnd_4192928 : Nat := 478441647487794751914907

theorem tailTrace_4192928 : CollatzResearch.WordTrace tailWord_4192928 prefixEnd_4192928 478441647487794751914907 := by
  unfold tailWord_4192928
  simp only [CollatzResearch.WordTrace]
  refine ⟨76464323876872712968133719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101952431835830283957511625 76464323876872712968133719)
  ·
    refine ⟨114696485815309069452200579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76464323876872712968133719 114696485815309069452200579)
    ·
      refine ⟨172044728722963604178300869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114696485815309069452200579 172044728722963604178300869)
      ·
        refine ⟨32258386635555675783431413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172044728722963604178300869 32258386635555675783431413)
        ·
          refine ⟨3024223747083344604696695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32258386635555675783431413 3024223747083344604696695)
          ·
            refine ⟨4536335620625016907045043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024223747083344604696695 4536335620625016907045043)
            ·
              refine ⟨6804503430937525360567565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536335620625016907045043 6804503430937525360567565)
              ·
                refine ⟨2551688786601572010212837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6804503430937525360567565 2551688786601572010212837)
                ·
                  refine ⟨478441647487794751914907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2551688786601572010212837 478441647487794751914907)
                  ·
                    rfl

theorem cell22_4192928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 4].length) (baseStart_4192928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192928 prefixEnd_4192928 := by exact prefixLift 4192928
  have htrace : WordTrace (prefixWord ++ tailWord_4192928) baseStart_4192928 baseEnd_4192928 := by
    simpa [prefixWord, tailWord_4192928, baseEnd_4192928] using wordTrace_append hprefix tailTrace_4192928
  have hstable : (prefixWord ++ tailWord_4192928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192928).length < 2 ^ (prefixWord ++ tailWord_4192928).sum := by decide
  have hdescent : baseEnd_4192928 < baseStart_4192928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192937 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 7, 3]
def baseStart_4192937 : Nat := 118140960795 + 4192937 * 2 ^ 59
def prefixEnd_4192937 : Nat := 4983230072969 + 3 ^ 40 * 4192937 * 2
def baseEnd_4192937 : Nat := 1435328023347311232269693

theorem tailTrace_4192937 : CollatzResearch.WordTrace tailWord_4192937 prefixEnd_4192937 1435328023347311232269693 := by
  unfold tailWord_4192937
  simp only [CollatzResearch.WordTrace]
  refine ⟨152928976010712820473345065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101952650673808546982230043 152928976010712820473345065)
  ·
    refine ⟨114696732008034615355008799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152928976010712820473345065 114696732008034615355008799)
    ·
      refine ⟨172045098012051923032513199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114696732008034615355008799 172045098012051923032513199)
      ·
        refine ⟨258067647018077884548769799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172045098012051923032513199 258067647018077884548769799)
        ·
          refine ⟨387101470527116826823154699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258067647018077884548769799 387101470527116826823154699)
          ·
            refine ⟨580652205790675240234732049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387101470527116826823154699 580652205790675240234732049)
            ·
              refine ⟨435489154343006430176049037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580652205790675240234732049 435489154343006430176049037)
              ·
                refine ⟨163308432878627411316018389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435489154343006430176049037 163308432878627411316018389)
                ·
                  refine ⟨3827541395592829952719181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 163308432878627411316018389 3827541395592829952719181)
                  ·
                    refine ⟨1435328023347311232269693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3827541395592829952719181 1435328023347311232269693)
                    ·
                      rfl

theorem cell22_4192937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 3].length) (baseStart_4192937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4192937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4192937 prefixEnd_4192937 := by exact prefixLift 4192937
  have htrace : WordTrace (prefixWord ++ tailWord_4192937) baseStart_4192937 baseEnd_4192937 := by
    simpa [prefixWord, tailWord_4192937, baseEnd_4192937] using wordTrace_append hprefix tailTrace_4192937
  have hstable : (prefixWord ++ tailWord_4192937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192937).length < 2 ^ (prefixWord ++ tailWord_4192937).sum := by decide
  have hdescent : baseEnd_4192937 < baseStart_4192937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193014 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_4193014 : Nat := 118140960795 + 4193014 * 2 ^ 59
def prefixEnd_4193014 : Nat := 4983230072969 + 3 ^ 40 * 4193014 * 2
def baseEnd_4193014 : Nat := 1435354382020908698094457

theorem tailTrace_4193014 : CollatzResearch.WordTrace tailWord_4193014 prefixEnd_4193014 1435354382020908698094457 := by
  unfold tailWord_4193014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9558236526964616413993631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101954522954289241749265397 9558236526964616413993631)
  ·
    refine ⟨14337354790446924620990447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9558236526964616413993631 14337354790446924620990447)
    ·
      refine ⟨21506032185670386931485671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14337354790446924620990447 21506032185670386931485671)
      ·
        refine ⟨32259048278505580397228507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21506032185670386931485671 32259048278505580397228507)
        ·
          refine ⟨48388572417758370595842761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32259048278505580397228507 48388572417758370595842761)
          ·
            refine ⟨36291429313318777946882071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48388572417758370595842761 36291429313318777946882071)
            ·
              refine ⟨54437143969978166920323107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36291429313318777946882071 54437143969978166920323107)
              ·
                refine ⟨81655715954967250380484661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54437143969978166920323107 81655715954967250380484661)
                ·
                  refine ⟨7655223370778179723170437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81655715954967250380484661 7655223370778179723170437)
                  ·
                    refine ⟨1435354382020908698094457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7655223370778179723170437 1435354382020908698094457)
                    ·
                      rfl

theorem cell22_4193014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_4193014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193014 prefixEnd_4193014 := by exact prefixLift 4193014
  have htrace : WordTrace (prefixWord ++ tailWord_4193014) baseStart_4193014 baseEnd_4193014 := by
    simpa [prefixWord, tailWord_4193014, baseEnd_4193014] using wordTrace_append hprefix tailTrace_4193014
  have hstable : (prefixWord ++ tailWord_4193014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193014).length < 2 ^ (prefixWord ++ tailWord_4193014).sum := by decide
  have hdescent : baseEnd_4193014 < baseStart_4193014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193057 : List Nat := [1, 2, 3, 2, 1, 2, 11]
def baseStart_4193057 : Nat := 118140960795 + 4193057 * 2 ^ 59
def prefixEnd_4193057 : Nat := 4983230072969 + 3 ^ 40 * 4193057 * 2
def baseEnd_4193057 : Nat := 53161818585172997009975

theorem tailTrace_4193057 : CollatzResearch.WordTrace tailWord_4193057 prefixEnd_4193057 53161818585172997009975 := by
  unfold tailWord_4193057
  simp only [CollatzResearch.WordTrace]
  refine ⟨152933352770278080967713425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101955568513518720645142283 152933352770278080967713425)
  ·
    refine ⟨114700014577708560725785069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152933352770278080967713425 114700014577708560725785069)
    ·
      refine ⟨43012505466640710272169401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114700014577708560725785069 43012505466640710272169401)
      ·
        refine ⟨32259379099980532704127051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43012505466640710272169401 32259379099980532704127051)
        ·
          refine ⟨48389068649970799056190577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32259379099980532704127051 48389068649970799056190577)
          ·
            refine ⟨36291801487478099292142933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48389068649970799056190577 36291801487478099292142933)
            ·
              refine ⟨53161818585172997009975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 36291801487478099292142933 53161818585172997009975)
              ·
                rfl

theorem cell22_4193057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 11].length) (baseStart_4193057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193057 prefixEnd_4193057 := by exact prefixLift 4193057
  have htrace : WordTrace (prefixWord ++ tailWord_4193057) baseStart_4193057 baseEnd_4193057 := by
    simpa [prefixWord, tailWord_4193057, baseEnd_4193057] using wordTrace_append hprefix tailTrace_4193057
  have hstable : (prefixWord ++ tailWord_4193057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193057).length < 2 ^ (prefixWord ++ tailWord_4193057).sum := by decide
  have hdescent : baseEnd_4193057 < baseStart_4193057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193119 : List Nat := [1, 1, 2, 3, 1, 3, 2, 4, 5]
def baseStart_4193119 : Nat := 118140960795 + 4193119 * 2 ^ 59
def prefixEnd_4193119 : Nat := 4983230072969 + 3 ^ 40 * 4193119 * 2
def baseEnd_4193119 : Nat := 478463441888907808073045

theorem tailTrace_4193119 : CollatzResearch.WordTrace tailWord_4193119 prefixEnd_4193119 478463441888907808073045 := by
  unfold tailWord_4193119
  simp only [CollatzResearch.WordTrace]
  refine ⟨152935614096053465556470411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101957076064035643704313607 152935614096053465556470411)
  ·
    refine ⟨229403421144080198334705617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152935614096053465556470411 229403421144080198334705617)
    ·
      refine ⟨172052565858060148751029213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229403421144080198334705617 172052565858060148751029213)
      ·
        refine ⟨64519712196772555781635955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172052565858060148751029213 64519712196772555781635955)
        ·
          refine ⟨96779568295158833672453933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64519712196772555781635955 96779568295158833672453933)
          ·
            refine ⟨36292338110684562627170225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96779568295158833672453933 36292338110684562627170225)
            ·
              refine ⟨27219253583013421970377669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36292338110684562627170225 27219253583013421970377669)
              ·
                refine ⟨5103610046815016619445813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27219253583013421970377669 5103610046815016619445813)
                ·
                  refine ⟨478463441888907808073045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5103610046815016619445813 478463441888907808073045)
                  ·
                    rfl

theorem cell22_4193119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 5].length) (baseStart_4193119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193119 prefixEnd_4193119 := by exact prefixLift 4193119
  have htrace : WordTrace (prefixWord ++ tailWord_4193119) baseStart_4193119 baseEnd_4193119 := by
    simpa [prefixWord, tailWord_4193119, baseEnd_4193119] using wordTrace_append hprefix tailTrace_4193119
  have hstable : (prefixWord ++ tailWord_4193119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193119).length < 2 ^ (prefixWord ++ tailWord_4193119).sum := by decide
  have hdescent : baseEnd_4193119 < baseStart_4193119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193123 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 3, 3]
def baseStart_4193123 : Nat := 118140960795 + 4193123 * 2 ^ 59
def prefixEnd_4193123 : Nat := 4983230072969 + 3 ^ 40 * 4193123 * 2
def baseEnd_4193123 : Nat := 1435391694948468747119123

theorem tailTrace_4193123 : CollatzResearch.WordTrace tailWord_4193123 prefixEnd_4193123 1435391694948468747119123 := by
  unfold tailWord_4193123
  simp only [CollatzResearch.WordTrace]
  refine ⟨152935759988038974239616023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101957173325359316159744015 152935759988038974239616023)
  ·
    refine ⟨229403639982058461359424035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152935759988038974239616023 229403639982058461359424035)
    ·
      refine ⟨344105459973087692039136053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229403639982058461359424035 344105459973087692039136053)
      ·
        refine ⟨32259886872476971128669005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 344105459973087692039136053 32259886872476971128669005)
        ·
          refine ⟨12097457577178864173250877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32259886872476971128669005 12097457577178864173250877)
          ·
            refine ⟨4536546591442074064969079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12097457577178864173250877 4536546591442074064969079)
            ·
              refine ⟨6804819887163111097453619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536546591442074064969079 6804819887163111097453619)
              ·
                refine ⟨10207229830744666646180429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6804819887163111097453619 10207229830744666646180429)
                ·
                  refine ⟨3827711186529249992317661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10207229830744666646180429 3827711186529249992317661)
                  ·
                    refine ⟨1435391694948468747119123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3827711186529249992317661 1435391694948468747119123)
                    ·
                      rfl

theorem cell22_4193123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 3].length) (baseStart_4193123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193123 prefixEnd_4193123 := by exact prefixLift 4193123
  have htrace : WordTrace (prefixWord ++ tailWord_4193123) baseStart_4193123 baseEnd_4193123 := by
    simpa [prefixWord, tailWord_4193123, baseEnd_4193123] using wordTrace_append hprefix tailTrace_4193123
  have hstable : (prefixWord ++ tailWord_4193123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193123).length < 2 ^ (prefixWord ++ tailWord_4193123).sum := by decide
  have hdescent : baseEnd_4193123 < baseStart_4193123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193136 : List Nat := [2, 1, 1, 1, 4, 1, 6, 1, 5]
def baseStart_4193136 : Nat := 118140960795 + 4193136 * 2 ^ 59
def prefixEnd_4193136 : Nat := 4983230072969 + 3 ^ 40 * 4193136 * 2
def baseEnd_4193136 : Nat := 478465381704713682181361

theorem tailTrace_4193136 : CollatzResearch.WordTrace tailWord_4193136 prefixEnd_4193136 478465381704713682181361 := by
  unfold tailWord_4193136
  simp only [CollatzResearch.WordTrace]
  refine ⟨76468117068495938729919631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101957489424661251639892841 76468117068495938729919631)
  ·
    refine ⟨114702175602743908094879447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76468117068495938729919631 114702175602743908094879447)
    ·
      refine ⟨172053263404115862142319171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114702175602743908094879447 172053263404115862142319171)
      ·
        refine ⟨258079895106173793213478757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172053263404115862142319171 258079895106173793213478757)
        ·
          refine ⟨48389980332407586227527267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258079895106173793213478757 48389980332407586227527267)
          ·
            refine ⟨72584970498611379341290901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48389980332407586227527267 72584970498611379341290901)
            ·
              refine ⟨3402420492122408406623011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72584970498611379341290901 3402420492122408406623011)
              ·
                refine ⟨5103630738183612609934517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3402420492122408406623011 5103630738183612609934517)
                ·
                  refine ⟨478465381704713682181361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5103630738183612609934517 478465381704713682181361)
                  ·
                    rfl

theorem cell22_4193136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 5].length) (baseStart_4193136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193136 prefixEnd_4193136 := by exact prefixLift 4193136
  have htrace : WordTrace (prefixWord ++ tailWord_4193136) baseStart_4193136 baseEnd_4193136 := by
    simpa [prefixWord, tailWord_4193136, baseEnd_4193136] using wordTrace_append hprefix tailTrace_4193136
  have hstable : (prefixWord ++ tailWord_4193136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193136).length < 2 ^ (prefixWord ++ tailWord_4193136).sum := by decide
  have hdescent : baseEnd_4193136 < baseStart_4193136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193174 : List Nat := [5, 3, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_4193174 : Nat := 118140960795 + 4193174 * 2 ^ 59
def prefixEnd_4193174 : Nat := 4983230072969 + 3 ^ 40 * 4193174 * 2
def baseEnd_4193174 : Nat := 1435409153290721614093967

theorem tailTrace_4193174 : CollatzResearch.WordTrace tailWord_4193174 prefixEnd_4193174 1435409153290721614093967 := by
  unfold tailWord_4193174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9558601256928388121857661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101958413407236139966481717 9558601256928388121857661)
  ·
    refine ⟨3584475471348145545696623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9558601256928388121857661 3584475471348145545696623)
    ·
      refine ⟨5376713207022218318544935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3584475471348145545696623 5376713207022218318544935)
      ·
        refine ⟨8065069810533327477817403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5376713207022218318544935 8065069810533327477817403)
        ·
          refine ⟨12097604715799991216726105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8065069810533327477817403 12097604715799991216726105)
          ·
            refine ⟨9073203536849993412544579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12097604715799991216726105 9073203536849993412544579)
            ·
              refine ⟨13609805305274990118816869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9073203536849993412544579 13609805305274990118816869)
              ·
                refine ⟨2551838494739060647278163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13609805305274990118816869 2551838494739060647278163)
                ·
                  refine ⟨3827757742108590970917245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551838494739060647278163 3827757742108590970917245)
                  ·
                    refine ⟨1435409153290721614093967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3827757742108590970917245 1435409153290721614093967)
                    ·
                      rfl

theorem cell22_4193174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_4193174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193174 prefixEnd_4193174 := by exact prefixLift 4193174
  have htrace : WordTrace (prefixWord ++ tailWord_4193174) baseStart_4193174 baseEnd_4193174 := by
    simpa [prefixWord, tailWord_4193174, baseEnd_4193174] using wordTrace_append hprefix tailTrace_4193174
  have hstable : (prefixWord ++ tailWord_4193174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193174).length < 2 ^ (prefixWord ++ tailWord_4193174).sum := by decide
  have hdescent : baseEnd_4193174 < baseStart_4193174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193230 : List Nat := [4, 1, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_4193230 : Nat := 118140960795 + 4193230 * 2 ^ 59
def prefixEnd_4193230 : Nat := 4983230072969 + 3 ^ 40 * 4193230 * 2
def baseEnd_4193230 : Nat := 1435428323235156134693795

theorem tailTrace_4193230 : CollatzResearch.WordTrace tailWord_4193230 prefixEnd_4193230 1435428323235156134693795 := by
  unfold tailWord_4193230
  simp only [CollatzResearch.WordTrace]
  refine ⟨19117457824831416439220143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101959775065767554342507429 19117457824831416439220143)
  ·
    refine ⟨28676186737247124658830215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19117457824831416439220143 28676186737247124658830215)
    ·
      refine ⟨43014280105870686988245323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28676186737247124658830215 43014280105870686988245323)
      ·
        refine ⟨64521420158806030482367985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43014280105870686988245323 64521420158806030482367985)
        ·
          refine ⟨48391065119104522861775989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64521420158806030482367985 48391065119104522861775989)
          ·
            refine ⟨4536662354916049018291499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48391065119104522861775989 4536662354916049018291499)
            ·
              refine ⟨6804993532374073527437249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536662354916049018291499 6804993532374073527437249)
              ·
                refine ⟨5103745149280555145577937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6804993532374073527437249 5103745149280555145577937)
                ·
                  refine ⟨3827808861960416359183453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5103745149280555145577937 3827808861960416359183453)
                  ·
                    refine ⟨1435428323235156134693795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3827808861960416359183453 1435428323235156134693795)
                    ·
                      rfl

theorem cell22_4193230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_4193230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193230 prefixEnd_4193230 := by exact prefixLift 4193230
  have htrace : WordTrace (prefixWord ++ tailWord_4193230) baseStart_4193230 baseEnd_4193230 := by
    simpa [prefixWord, tailWord_4193230, baseEnd_4193230] using wordTrace_append hprefix tailTrace_4193230
  have hstable : (prefixWord ++ tailWord_4193230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193230).length < 2 ^ (prefixWord ++ tailWord_4193230).sum := by decide
  have hdescent : baseEnd_4193230 < baseStart_4193230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193239 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 2, 6]
def baseStart_4193239 : Nat := 118140960795 + 4193239 * 2 ^ 59
def prefixEnd_4193239 : Nat := 4983230072969 + 3 ^ 40 * 4193239 * 2
def baseEnd_4193239 : Nat := 1435431404119083111218767

theorem tailTrace_4193239 : CollatzResearch.WordTrace tailWord_4193239 prefixEnd_4193239 1435431404119083111218767 := by
  unfold tailWord_4193239
  simp only [CollatzResearch.WordTrace]
  refine ⟨152939990855618726050838771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101959993903745817367225847 152939990855618726050838771)
  ·
    refine ⟨229409986283428089076258157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152939990855618726050838771 229409986283428089076258157)
    ·
      refine ⟨86028744856285533403596809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229409986283428089076258157 86028744856285533403596809)
      ·
        refine ⟨64521558642214150052697607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86028744856285533403596809 64521558642214150052697607)
        ·
          refine ⟨96782337963321225079046411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64521558642214150052697607 96782337963321225079046411)
          ·
            refine ⟨145173506944981837618569617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96782337963321225079046411 145173506944981837618569617)
            ·
              refine ⟨108880130208736378213927213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145173506944981837618569617 108880130208736378213927213)
              ·
                refine ⟨40830048828276141830222705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108880130208736378213927213 40830048828276141830222705)
                ·
                  refine ⟨30622536621207106372667029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40830048828276141830222705 30622536621207106372667029)
                  ·
                    refine ⟨1435431404119083111218767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30622536621207106372667029 1435431404119083111218767)
                    ·
                      rfl

theorem cell22_4193239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_4193239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193239 prefixEnd_4193239 := by exact prefixLift 4193239
  have htrace : WordTrace (prefixWord ++ tailWord_4193239) baseStart_4193239 baseEnd_4193239 := by
    simpa [prefixWord, tailWord_4193239, baseEnd_4193239] using wordTrace_append hprefix tailTrace_4193239
  have hstable : (prefixWord ++ tailWord_4193239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193239).length < 2 ^ (prefixWord ++ tailWord_4193239).sum := by decide
  have hdescent : baseEnd_4193239 < baseStart_4193239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193258 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 3, 3]
def baseStart_4193258 : Nat := 118140960795 + 4193258 * 2 ^ 59
def prefixEnd_4193258 : Nat := 4983230072969 + 3 ^ 40 * 4193258 * 2
def baseEnd_4193258 : Nat := 1435437908207373394993709

theorem tailTrace_4193258 : CollatzResearch.WordTrace tailWord_4193258 prefixEnd_4193258 1435437908207373394993709 := by
  unfold tailWord_4193258
  simp only [CollatzResearch.WordTrace]
  refine ⟨38235170960637473073945107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101960455895033261530520285 38235170960637473073945107)
  ·
    refine ⟨57352756440956209610917661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38235170960637473073945107 57352756440956209610917661)
    ·
      refine ⟨21507283665358578604094123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57352756440956209610917661 21507283665358578604094123)
      ·
        refine ⟨32260925498037867906141185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21507283665358578604094123 32260925498037867906141185)
        ·
          refine ⟨24195694123528400929605889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32260925498037867906141185 24195694123528400929605889)
          ·
            refine ⟨18146770592646300697204417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24195694123528400929605889 18146770592646300697204417)
            ·
              refine ⟨13610077944484725522903313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18146770592646300697204417 13610077944484725522903313)
              ·
                refine ⟨10207558458363544142177485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13610077944484725522903313 10207558458363544142177485)
                ·
                  refine ⟨3827834421886329053316557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10207558458363544142177485 3827834421886329053316557)
                  ·
                    refine ⟨1435437908207373394993709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3827834421886329053316557 1435437908207373394993709)
                    ·
                      rfl

theorem cell22_4193258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_4193258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193258 prefixEnd_4193258 := by exact prefixLift 4193258
  have htrace : WordTrace (prefixWord ++ tailWord_4193258) baseStart_4193258 baseEnd_4193258 := by
    simpa [prefixWord, tailWord_4193258, baseEnd_4193258] using wordTrace_append hprefix tailTrace_4193258
  have hstable : (prefixWord ++ tailWord_4193258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193258).length < 2 ^ (prefixWord ++ tailWord_4193258).sum := by decide
  have hdescent : baseEnd_4193258 < baseStart_4193258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193292 : List Nat := [2, 2, 1, 2, 3, 3, 3, 2, 1, 3]
def baseStart_4193292 : Nat := 118140960795 + 4193292 * 2 ^ 59
def prefixEnd_4193292 : Nat := 4983230072969 + 3 ^ 40 * 4193292 * 2
def baseEnd_4193292 : Nat := 1435449547102208639643605

theorem tailTrace_4193292 : CollatzResearch.WordTrace tailWord_4193292 prefixEnd_4193292 1435449547102208639643605 := by
  unfold tailWord_4193292
  simp only [CollatzResearch.WordTrace]
  refine ⟨76470961962213358051259065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101961282616284477401678753 76470961962213358051259065)
  ·
    refine ⟨57353221471660018538444299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76470961962213358051259065 57353221471660018538444299)
    ·
      refine ⟨86029832207490027807666449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57353221471660018538444299 86029832207490027807666449)
      ·
        refine ⟨64522374155617520855749837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86029832207490027807666449 64522374155617520855749837)
        ·
          refine ⟨24195890308356570320906189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64522374155617520855749837 24195890308356570320906189)
          ·
            refine ⟨9073458865633713870339821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24195890308356570320906189 9073458865633713870339821)
            ·
              refine ⟨3402547074612642701377433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9073458865633713870339821 3402547074612642701377433)
              ·
                refine ⟨2551910305959482026033075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3402547074612642701377433 2551910305959482026033075)
                ·
                  refine ⟨3827865458939223039049613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551910305959482026033075 3827865458939223039049613)
                  ·
                    refine ⟨1435449547102208639643605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3827865458939223039049613 1435449547102208639643605)
                    ·
                      rfl

theorem cell22_4193292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_4193292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193292 prefixEnd_4193292 := by exact prefixLift 4193292
  have htrace : WordTrace (prefixWord ++ tailWord_4193292) baseStart_4193292 baseEnd_4193292 := by
    simpa [prefixWord, tailWord_4193292, baseEnd_4193292] using wordTrace_append hprefix tailTrace_4193292
  have hstable : (prefixWord ++ tailWord_4193292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193292).length < 2 ^ (prefixWord ++ tailWord_4193292).sum := by decide
  have hdescent : baseEnd_4193292 < baseStart_4193292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193298 : List Nat := [3, 2, 5, 1, 2, 1, 2, 1, 2, 3]
def baseStart_4193298 : Nat := 118140960795 + 4193298 * 2 ^ 59
def prefixEnd_4193298 : Nat := 4983230072969 + 3 ^ 40 * 4193298 * 2
def baseEnd_4193298 : Nat := 1435451601024826623993587

theorem tailTrace_4193298 : CollatzResearch.WordTrace tailWord_4193298 prefixEnd_4193298 1435451601024826623993587 := by
  unfold tailWord_4193298
  simp only [CollatzResearch.WordTrace]
  refine ⟨38235535690601244781809137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101961428508269986084824365 38235535690601244781809137)
  ·
    refine ⟨28676651767950933586356853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38235535690601244781809137 28676651767950933586356853)
    ·
      refine ⟨2688436103245400023720955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28676651767950933586356853 2688436103245400023720955)
      ·
        refine ⟨4032654154868100035581433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2688436103245400023720955 4032654154868100035581433)
        ·
          refine ⟨3024490616151075026686075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4032654154868100035581433 3024490616151075026686075)
          ·
            refine ⟨4536735924226612540029113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024490616151075026686075 4536735924226612540029113)
            ·
              refine ⟨3402551943169959405021835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4536735924226612540029113 3402551943169959405021835)
              ·
                refine ⟨5103827914754939107532753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3402551943169959405021835 5103827914754939107532753)
                ·
                  refine ⟨3827870936066204330649565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5103827914754939107532753 3827870936066204330649565)
                  ·
                    refine ⟨1435451601024826623993587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3827870936066204330649565 1435451601024826623993587)
                    ·
                      rfl

theorem cell22_4193298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_4193298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193298 prefixEnd_4193298 := by exact prefixLift 4193298
  have htrace : WordTrace (prefixWord ++ tailWord_4193298) baseStart_4193298 baseEnd_4193298 := by
    simpa [prefixWord, tailWord_4193298, baseEnd_4193298] using wordTrace_append hprefix tailTrace_4193298
  have hstable : (prefixWord ++ tailWord_4193298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193298).length < 2 ^ (prefixWord ++ tailWord_4193298).sum := by decide
  have hdescent : baseEnd_4193298 < baseStart_4193298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193333 : List Nat := [1, 3, 3, 1, 1, 1, 1, 7, 4]
def baseStart_4193333 : Nat := 118140960795 + 4193333 * 2 ^ 59
def prefixEnd_4193333 : Nat := 4983230072969 + 3 ^ 40 * 4193333 * 2
def baseEnd_4193333 : Nat := 478487860746699399789493

theorem tailTrace_4193333 : CollatzResearch.WordTrace tailWord_4193333 prefixEnd_4193333 478487860746699399789493 := by
  unfold tailWord_4193333
  simp only [CollatzResearch.WordTrace]
  refine ⟨152943419317278180104760653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101962279544852120069840435 152943419317278180104760653)
  ·
    refine ⟨57353782243979317539285245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152943419317278180104760653 57353782243979317539285245)
    ·
      refine ⟨21507668341492244077231967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57353782243979317539285245 21507668341492244077231967)
      ·
        refine ⟨32261502512238366115847951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21507668341492244077231967 32261502512238366115847951)
        ·
          refine ⟨48392253768357549173771927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32261502512238366115847951 48392253768357549173771927)
          ·
            refine ⟨72588380652536323760657891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48392253768357549173771927 72588380652536323760657891)
            ·
              refine ⟨108882570978804485640986837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72588380652536323760657891 108882570978804485640986837)
              ·
                refine ⟨2551935257315730132210629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108882570978804485640986837 2551935257315730132210629)
                ·
                  refine ⟨478487860746699399789493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2551935257315730132210629 478487860746699399789493)
                  ·
                    rfl

theorem cell22_4193333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_4193333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193333 prefixEnd_4193333 := by exact prefixLift 4193333
  have htrace : WordTrace (prefixWord ++ tailWord_4193333) baseStart_4193333 baseEnd_4193333 := by
    simpa [prefixWord, tailWord_4193333, baseEnd_4193333] using wordTrace_append hprefix tailTrace_4193333
  have hstable : (prefixWord ++ tailWord_4193333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193333).length < 2 ^ (prefixWord ++ tailWord_4193333).sum := by decide
  have hdescent : baseEnd_4193333 < baseStart_4193333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193361 : List Nat := [1, 2, 2, 1, 3, 1, 5, 7]
def baseStart_4193361 : Nat := 118140960795 + 4193361 * 2 ^ 59
def prefixEnd_4193361 : Nat := 4983230072969 + 3 ^ 40 * 4193361 * 2
def baseEnd_4193361 : Nat := 159497018579146162185377

theorem tailTrace_4193361 : CollatzResearch.WordTrace tailWord_4193361 prefixEnd_4193361 159497018579146162185377 := by
  unfold tailWord_4193361
  simp only [CollatzResearch.WordTrace]
  refine ⟨152944440561176740886779937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101962960374117827257853291 152944440561176740886779937)
  ·
    refine ⟨114708330420882555665084953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152944440561176740886779937 114708330420882555665084953)
    ·
      refine ⟨86031247815661916748813715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114708330420882555665084953 86031247815661916748813715)
      ·
        refine ⟨129046871723492875123220573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86031247815661916748813715 129046871723492875123220573)
        ·
          refine ⟨48392576896309828171207715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129046871723492875123220573 48392576896309828171207715)
          ·
            refine ⟨72588865344464742256811573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48392576896309828171207715 72588865344464742256811573)
            ·
              refine ⟨6805206126043569586576085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72588865344464742256811573 6805206126043569586576085)
              ·
                refine ⟨159497018579146162185377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6805206126043569586576085 159497018579146162185377)
                ·
                  rfl

theorem cell22_4193361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 7].length) (baseStart_4193361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193361 prefixEnd_4193361 := by exact prefixLift 4193361
  have htrace : WordTrace (prefixWord ++ tailWord_4193361) baseStart_4193361 baseEnd_4193361 := by
    simpa [prefixWord, tailWord_4193361, baseEnd_4193361] using wordTrace_append hprefix tailTrace_4193361
  have hstable : (prefixWord ++ tailWord_4193361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193361).length < 2 ^ (prefixWord ++ tailWord_4193361).sum := by decide
  have hdescent : baseEnd_4193361 < baseStart_4193361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193444 : List Nat := [2, 3, 1, 2, 3, 3, 1, 3, 1, 3]
def baseStart_4193444 : Nat := 118140960795 + 4193444 * 2 ^ 59
def prefixEnd_4193444 : Nat := 4983230072969 + 3 ^ 40 * 4193444 * 2
def baseEnd_4193444 : Nat := 1435501579808530909843139

theorem tailTrace_4193444 : CollatzResearch.WordTrace tailWord_4193444 prefixEnd_4193444 1435501579808530909843139 := by
  unfold tailWord_4193444
  simp only [CollatzResearch.WordTrace]
  refine ⟨76473733909938023031025693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101964978546584030708034257 76473733909938023031025693)
  ·
    refine ⟨28677650216226758636634635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76473733909938023031025693 28677650216226758636634635)
    ·
      refine ⟨43016475324340137954951953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28677650216226758636634635 43016475324340137954951953)
      ·
        refine ⟨32262356493255103466213965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43016475324340137954951953 32262356493255103466213965)
        ·
          refine ⟨12098383684970663799830237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32262356493255103466213965 12098383684970663799830237)
          ·
            refine ⟨4536893881863998924936339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12098383684970663799830237 4536893881863998924936339)
            ·
              refine ⟨6805340822795998387404509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536893881863998924936339 6805340822795998387404509)
              ·
                refine ⟨2552002808548499395276691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6805340822795998387404509 2552002808548499395276691)
                ·
                  refine ⟨3828004212822749092915037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552002808548499395276691 3828004212822749092915037)
                  ·
                    refine ⟨1435501579808530909843139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3828004212822749092915037 1435501579808530909843139)
                    ·
                      rfl

theorem cell22_4193444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_4193444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193444 prefixEnd_4193444 := by exact prefixLift 4193444
  have htrace : WordTrace (prefixWord ++ tailWord_4193444) baseStart_4193444 baseEnd_4193444 := by
    simpa [prefixWord, tailWord_4193444, baseEnd_4193444] using wordTrace_append hprefix tailTrace_4193444
  have hstable : (prefixWord ++ tailWord_4193444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193444).length < 2 ^ (prefixWord ++ tailWord_4193444).sum := by decide
  have hdescent : baseEnd_4193444 < baseStart_4193444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193474 : List Nat := [3, 5, 1, 1, 2, 1, 1, 3, 5]
def baseStart_4193474 : Nat := 118140960795 + 4193474 * 2 ^ 59
def prefixEnd_4193474 : Nat := 4983230072969 + 3 ^ 40 * 4193474 * 2
def baseEnd_4193474 : Nat := 478503949807206943864349

theorem tailTrace_4193474 : CollatzResearch.WordTrace tailWord_4193474 prefixEnd_4193474 478503949807206943864349 := by
  unfold tailWord_4193474
  simp only [CollatzResearch.WordTrace]
  refine ⟨38237140502441840296410869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101965708006511574123762317 38237140502441840296410869)
  ·
    refine ⟨3584731922103922527788519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38237140502441840296410869 3584731922103922527788519)
    ·
      refine ⟨5377097883155883791682779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3584731922103922527788519 5377097883155883791682779)
      ·
        refine ⟨8065646824733825687524169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5377097883155883791682779 8065646824733825687524169)
        ·
          refine ⟨6049235118550369265643127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8065646824733825687524169 6049235118550369265643127)
          ·
            refine ⟨9073852677825553898464691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6049235118550369265643127 9073852677825553898464691)
            ·
              refine ⟨13610779016738330847697037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9073852677825553898464691 13610779016738330847697037)
              ·
                refine ⟨5104042131276874067886389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13610779016738330847697037 5104042131276874067886389)
                ·
                  refine ⟨478503949807206943864349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5104042131276874067886389 478503949807206943864349)
                  ·
                    rfl

theorem cell22_4193474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_4193474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193474 prefixEnd_4193474 := by exact prefixLift 4193474
  have htrace : WordTrace (prefixWord ++ tailWord_4193474) baseStart_4193474 baseEnd_4193474 := by
    simpa [prefixWord, tailWord_4193474, baseEnd_4193474] using wordTrace_append hprefix tailTrace_4193474
  have hstable : (prefixWord ++ tailWord_4193474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193474).length < 2 ^ (prefixWord ++ tailWord_4193474).sum := by decide
  have hdescent : baseEnd_4193474 < baseStart_4193474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193483 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 6, 3]
def baseStart_4193483 : Nat := 118140960795 + 4193483 * 2 ^ 59
def prefixEnd_4193483 : Nat := 4983230072969 + 3 ^ 40 * 4193483 * 2
def baseEnd_4193483 : Nat := 1435514930305547808118019

theorem tailTrace_4193483 : CollatzResearch.WordTrace tailWord_4193483 prefixEnd_4193483 1435514930305547808118019 := by
  unfold tailWord_4193483
  simp only [CollatzResearch.WordTrace]
  refine ⟨152948890266734755722721103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101965926844489837148480735 152948890266734755722721103)
  ·
    refine ⟨229423335400102133584081655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152948890266734755722721103 229423335400102133584081655)
    ·
      refine ⟨344135003100153200376122483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229423335400102133584081655 344135003100153200376122483)
      ·
        refine ⟨516202504650229800564183725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344135003100153200376122483 516202504650229800564183725)
        ·
          refine ⟨193575939243836175211568897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 516202504650229800564183725 193575939243836175211568897)
          ·
            refine ⟨145181954432877131408676673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193575939243836175211568897 145181954432877131408676673)
            ·
              refine ⟨108886465824657848556507505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145181954432877131408676673 108886465824657848556507505)
              ·
                refine ⟨81664849368493386417380629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108886465824657848556507505 81664849368493386417380629)
                ·
                  refine ⟨3828039814148127488314717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81664849368493386417380629 3828039814148127488314717)
                  ·
                    refine ⟨1435514930305547808118019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3828039814148127488314717 1435514930305547808118019)
                    ·
                      rfl

theorem cell22_4193483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 3].length) (baseStart_4193483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193483 prefixEnd_4193483 := by exact prefixLift 4193483
  have htrace : WordTrace (prefixWord ++ tailWord_4193483) baseStart_4193483 baseEnd_4193483 := by
    simpa [prefixWord, tailWord_4193483, baseEnd_4193483] using wordTrace_append hprefix tailTrace_4193483
  have hstable : (prefixWord ++ tailWord_4193483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193483).length < 2 ^ (prefixWord ++ tailWord_4193483).sum := by decide
  have hdescent : baseEnd_4193483 < baseStart_4193483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193517 : List Nat := [1, 5, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_4193517 : Nat := 118140960795 + 4193517 * 2 ^ 59
def prefixEnd_4193517 : Nat := 4983230072969 + 3 ^ 40 * 4193517 * 2
def baseEnd_4193517 : Nat := 1435526569200383052767915

theorem tailTrace_4193517 : CollatzResearch.WordTrace tailWord_4193517 prefixEnd_4193517 1435526569200383052767915 := by
  unfold tailWord_4193517
  simp only [CollatzResearch.WordTrace]
  refine ⟨152950130348611579529458805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101966753565741053019639203 152950130348611579529458805)
  ·
    refine ⟨14339074720182335580886763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152950130348611579529458805 14339074720182335580886763)
    ·
      refine ⟨21508612080273503371330145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14339074720182335580886763 21508612080273503371330145)
      ·
        refine ⟨16131459060205127528497609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21508612080273503371330145 16131459060205127528497609)
        ·
          refine ⟨12098594295153845646373207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16131459060205127528497609 12098594295153845646373207)
          ·
            refine ⟨18147891442730768469559811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12098594295153845646373207 18147891442730768469559811)
            ·
              refine ⟨27221837164096152704339717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18147891442730768469559811 27221837164096152704339717)
              ·
                refine ⟨5104094468268028632063697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27221837164096152704339717 5104094468268028632063697)
                ·
                  refine ⟨3828070851201021474047773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5104094468268028632063697 3828070851201021474047773)
                  ·
                    refine ⟨1435526569200383052767915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3828070851201021474047773 1435526569200383052767915)
                    ·
                      rfl

theorem cell22_4193517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_4193517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193517 prefixEnd_4193517 := by exact prefixLift 4193517
  have htrace : WordTrace (prefixWord ++ tailWord_4193517) baseStart_4193517 baseEnd_4193517 := by
    simpa [prefixWord, tailWord_4193517, baseEnd_4193517] using wordTrace_append hprefix tailTrace_4193517
  have hstable : (prefixWord ++ tailWord_4193517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193517).length < 2 ^ (prefixWord ++ tailWord_4193517).sum := by decide
  have hdescent : baseEnd_4193517 < baseStart_4193517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193519 : List Nat := [1, 1, 2, 1, 7, 2, 2, 2, 4]
def baseStart_4193519 : Nat := 118140960795 + 4193519 * 2 ^ 59
def prefixEnd_4193519 : Nat := 4983230072969 + 3 ^ 40 * 4193519 * 2
def baseEnd_4193519 : Nat := 478509084613751904739303

theorem tailTrace_4193519 : CollatzResearch.WordTrace tailWord_4193519 prefixEnd_4193519 478509084613751904739303 := by
  unfold tailWord_4193519
  simp only [CollatzResearch.WordTrace]
  refine ⟨152950203294604333871031611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101966802196402889247354407 152950203294604333871031611)
  ·
    refine ⟨229425304941906500806547417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152950203294604333871031611 229425304941906500806547417)
    ·
      refine ⟨172068978706429875604910563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229425304941906500806547417 172068978706429875604910563)
      ·
        refine ⟨258103468059644813407365845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172068978706429875604910563 258103468059644813407365845)
        ·
          refine ⟨6049300032647925314235137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 258103468059644813407365845 6049300032647925314235137)
          ·
            refine ⟨4536975024485943985676353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6049300032647925314235137 4536975024485943985676353)
            ·
              refine ⟨3402731268364457989257265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4536975024485943985676353 3402731268364457989257265)
              ·
                refine ⟨2552048451273343491942949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3402731268364457989257265 2552048451273343491942949)
                ·
                  refine ⟨478509084613751904739303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2552048451273343491942949 478509084613751904739303)
                  ·
                    rfl

theorem cell22_4193519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 2, 4].length) (baseStart_4193519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193519 prefixEnd_4193519 := by exact prefixLift 4193519
  have htrace : WordTrace (prefixWord ++ tailWord_4193519) baseStart_4193519 baseEnd_4193519 := by
    simpa [prefixWord, tailWord_4193519, baseEnd_4193519] using wordTrace_append hprefix tailTrace_4193519
  have hstable : (prefixWord ++ tailWord_4193519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193519).length < 2 ^ (prefixWord ++ tailWord_4193519).sum := by decide
  have hdescent : baseEnd_4193519 < baseStart_4193519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193545 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 3, 3]
def baseStart_4193545 : Nat := 118140960795 + 4193545 * 2 ^ 59
def prefixEnd_4193545 : Nat := 4983230072969 + 3 ^ 40 * 4193545 * 2
def baseEnd_4193545 : Nat := 1435536154172600313067829

theorem tailTrace_4193545 : CollatzResearch.WordTrace tailWord_4193545 prefixEnd_4193545 1435536154172600313067829 := by
  unfold tailWord_4193545
  simp only [CollatzResearch.WordTrace]
  refine ⟨152951151592510140311478089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101967434395006760207652059 152951151592510140311478089)
  ·
    refine ⟨114713363694382605233608567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152951151592510140311478089 114713363694382605233608567)
    ·
      refine ⟨172070045541573907850412851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114713363694382605233608567 172070045541573907850412851)
      ·
        refine ⟨258105068312360861775619277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172070045541573907850412851 258105068312360861775619277)
        ·
          refine ⟨96789400617135323165857229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258105068312360861775619277 96789400617135323165857229)
          ·
            refine ⟨36296025231425746187196461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96789400617135323165857229 36296025231425746187196461)
            ·
              refine ⟨13611009461784654820198673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36296025231425746187196461 13611009461784654820198673)
              ·
                refine ⟨10208257096338491115149005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13611009461784654820198673 10208257096338491115149005)
                ·
                  refine ⟨3828096411126934168180877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10208257096338491115149005 3828096411126934168180877)
                  ·
                    refine ⟨1435536154172600313067829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3828096411126934168180877 1435536154172600313067829)
                    ·
                      rfl

theorem cell22_4193545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 3].length) (baseStart_4193545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193545 prefixEnd_4193545 := by exact prefixLift 4193545
  have htrace : WordTrace (prefixWord ++ tailWord_4193545) baseStart_4193545 baseEnd_4193545 := by
    simpa [prefixWord, tailWord_4193545, baseEnd_4193545] using wordTrace_append hprefix tailTrace_4193545
  have hstable : (prefixWord ++ tailWord_4193545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193545).length < 2 ^ (prefixWord ++ tailWord_4193545).sum := by decide
  have hdescent : baseEnd_4193545 < baseStart_4193545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193650 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_4193650 : Nat := 118140960795 + 4193650 * 2 ^ 59
def prefixEnd_4193650 : Nat := 4983230072969 + 3 ^ 40 * 4193650 * 2
def baseEnd_4193650 : Nat := 1435572097818415039192507

theorem tailTrace_4193650 : CollatzResearch.WordTrace tailWord_4193650 prefixEnd_4193650 1435572097818415039192507 := by
  unfold tailWord_4193650
  simp only [CollatzResearch.WordTrace]
  refine ⟨38238745314282435811012601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101969987504753162162700269 38238745314282435811012601)
  ·
    refine ⟨28679058985711826858259451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38238745314282435811012601 28679058985711826858259451)
    ·
      refine ⟨43018588478567740287389177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28679058985711826858259451 43018588478567740287389177)
      ·
        refine ⟨32263941358925805215541883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43018588478567740287389177 32263941358925805215541883)
        ·
          refine ⟨48395912038388707823312825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32263941358925805215541883 48395912038388707823312825)
          ·
            refine ⟨36296934028791530867484619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48395912038388707823312825 36296934028791530867484619)
            ·
              refine ⟨54445401043187296301226929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36296934028791530867484619 54445401043187296301226929)
              ·
                refine ⟨40834050782390472225920197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54445401043187296301226929 40834050782390472225920197)
                ·
                  refine ⟨7656384521698213542360037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40834050782390472225920197 7656384521698213542360037)
                  ·
                    refine ⟨1435572097818415039192507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7656384521698213542360037 1435572097818415039192507)
                    ·
                      rfl

theorem cell22_4193650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_4193650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193650 prefixEnd_4193650 := by exact prefixLift 4193650
  have htrace : WordTrace (prefixWord ++ tailWord_4193650) baseStart_4193650 baseEnd_4193650 := by
    simpa [prefixWord, tailWord_4193650, baseEnd_4193650] using wordTrace_append hprefix tailTrace_4193650
  have hstable : (prefixWord ++ tailWord_4193650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193650).length < 2 ^ (prefixWord ++ tailWord_4193650).sum := by decide
  have hdescent : baseEnd_4193650 < baseStart_4193650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193667 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 2, 4]
def baseStart_4193667 : Nat := 118140960795 + 4193667 * 2 ^ 59
def prefixEnd_4193667 : Nat := 4983230072969 + 3 ^ 40 * 4193667 * 2
def baseEnd_4193667 : Nat := 1435577917265832661517455

theorem tailTrace_4193667 : CollatzResearch.WordTrace tailWord_4193667 prefixEnd_4193667 1435577917265832661517455 := by
  unfold tailWord_4193667
  simp only [CollatzResearch.WordTrace]
  refine ⟨152955601298068155147419255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101970400865378770098279503 152955601298068155147419255)
  ·
    refine ⟨229433401947102232721128883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152955601298068155147419255 229433401947102232721128883)
    ·
      refine ⟨344150102920653349081693325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229433401947102232721128883 344150102920653349081693325)
      ·
        refine ⟨129056288595245005905634997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 344150102920653349081693325 129056288595245005905634997)
        ·
          refine ⟨12099027055804219303653281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129056288595245005905634997 12099027055804219303653281)
          ·
            refine ⟨9074270291853164477739961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12099027055804219303653281 9074270291853164477739961)
            ·
              refine ⟨6805702718889873358304971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9074270291853164477739961 6805702718889873358304971)
              ·
                refine ⟨10208554078334810037457457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6805702718889873358304971 10208554078334810037457457)
                ·
                  refine ⟨7656415558751107528093093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10208554078334810037457457 7656415558751107528093093)
                  ·
                    refine ⟨1435577917265832661517455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7656415558751107528093093 1435577917265832661517455)
                    ·
                      rfl

theorem cell22_4193667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 4].length) (baseStart_4193667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193667 prefixEnd_4193667 := by exact prefixLift 4193667
  have htrace : WordTrace (prefixWord ++ tailWord_4193667) baseStart_4193667 baseEnd_4193667 := by
    simpa [prefixWord, tailWord_4193667, baseEnd_4193667] using wordTrace_append hprefix tailTrace_4193667
  have hstable : (prefixWord ++ tailWord_4193667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193667).length < 2 ^ (prefixWord ++ tailWord_4193667).sum := by decide
  have hdescent : baseEnd_4193667 < baseStart_4193667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193682 : List Nat := [3, 2, 3, 3, 1, 10]
def baseStart_4193682 : Nat := 118140960795 + 4193682 * 2 ^ 59
def prefixEnd_4193682 : Nat := 4983230072969 + 3 ^ 40 * 4193682 * 2
def baseEnd_4193682 : Nat := 17723247556449106449289

theorem tailTrace_4193682 : CollatzResearch.WordTrace tailWord_4193682 prefixEnd_4193682 17723247556449106449289 := by
  unfold tailWord_4193682
  simp only [CollatzResearch.WordTrace]
  refine ⟨38239037098253453177303825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101970765595342541806143533 38239037098253453177303825)
  ·
    refine ⟨28679277823690089882977869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38239037098253453177303825 28679277823690089882977869)
    ·
      refine ⟨10754729183883783706116701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28679277823690089882977869 10754729183883783706116701)
      ·
        refine ⟨4033023443956418889793763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10754729183883783706116701 4033023443956418889793763)
        ·
          refine ⟨6049535165934628334690645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4033023443956418889793763 6049535165934628334690645)
          ·
            refine ⟨17723247556449106449289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 6049535165934628334690645 17723247556449106449289)
            ·
              rfl

theorem cell22_4193682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 10].length) (baseStart_4193682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193682 prefixEnd_4193682 := by exact prefixLift 4193682
  have htrace : WordTrace (prefixWord ++ tailWord_4193682) baseStart_4193682 baseEnd_4193682 := by
    simpa [prefixWord, tailWord_4193682, baseEnd_4193682] using wordTrace_append hprefix tailTrace_4193682
  have hstable : (prefixWord ++ tailWord_4193682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193682).length < 2 ^ (prefixWord ++ tailWord_4193682).sum := by decide
  have hdescent : baseEnd_4193682 < baseStart_4193682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193688 : List Nat := [2, 1, 2, 5, 3, 1, 2, 2, 4]
def baseStart_4193688 : Nat := 118140960795 + 4193688 * 2 ^ 59
def prefixEnd_4193688 : Nat := 4983230072969 + 3 ^ 40 * 4193688 * 2
def baseEnd_4193688 : Nat := 478528368664998535580797

theorem tailTrace_4193688 : CollatzResearch.WordTrace tailWord_4193688 prefixEnd_4193688 478528368664998535580797 := by
  unfold tailWord_4193688
  simp only [CollatzResearch.WordTrace]
  refine ⟨76478183615496037866966859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101970911487328050489289145 76478183615496037866966859)
  ·
    refine ⟨114717275423244056800450289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76478183615496037866966859 114717275423244056800450289)
    ·
      refine ⟨86037956567433042600337717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114717275423244056800450289 86037956567433042600337717)
      ·
        refine ⟨8066058428196847743781661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86037956567433042600337717 8066058428196847743781661)
        ·
          refine ⟨3024771910573817903918123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8066058428196847743781661 3024771910573817903918123)
          ·
            refine ⟨4537157865860726855877185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024771910573817903918123 4537157865860726855877185)
            ·
              refine ⟨3402868399395545141907889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4537157865860726855877185 3402868399395545141907889)
              ·
                refine ⟨2552151299546658856430917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3402868399395545141907889 2552151299546658856430917)
                ·
                  refine ⟨478528368664998535580797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2552151299546658856430917 478528368664998535580797)
                  ·
                    rfl

theorem cell22_4193688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 2, 4].length) (baseStart_4193688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193688 prefixEnd_4193688 := by exact prefixLift 4193688
  have htrace : WordTrace (prefixWord ++ tailWord_4193688) baseStart_4193688 baseEnd_4193688 := by
    simpa [prefixWord, tailWord_4193688, baseEnd_4193688] using wordTrace_append hprefix tailTrace_4193688
  have hstable : (prefixWord ++ tailWord_4193688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193688).length < 2 ^ (prefixWord ++ tailWord_4193688).sum := by decide
  have hdescent : baseEnd_4193688 < baseStart_4193688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193695 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 2, 6]
def baseStart_4193695 : Nat := 118140960795 + 4193695 * 2 ^ 59
def prefixEnd_4193695 : Nat := 4983230072969 + 3 ^ 40 * 4193695 * 2
def baseEnd_4193695 : Nat := 1435587502238049921817369

theorem tailTrace_4193695 : CollatzResearch.WordTrace tailWord_4193695 prefixEnd_4193695 1435587502238049921817369 := by
  unfold tailWord_4193695
  simp only [CollatzResearch.WordTrace]
  refine ⟨152956622541966715929438539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101971081694644477286292359 152956622541966715929438539)
  ·
    refine ⟨229434933812950073894157809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152956622541966715929438539 229434933812950073894157809)
    ·
      refine ⟨172076200359712555420618357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229434933812950073894157809 172076200359712555420618357)
      ·
        refine ⟨16132143783723052070682971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172076200359712555420618357 16132143783723052070682971)
        ·
          refine ⟨24198215675584578106024457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16132143783723052070682971 24198215675584578106024457)
          ·
            refine ⟨18148661756688433579518343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24198215675584578106024457 18148661756688433579518343)
            ·
              refine ⟨27222992635032650369277515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18148661756688433579518343 27222992635032650369277515)
              ·
                refine ⟨40834488952548975553916273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27222992635032650369277515 40834488952548975553916273)
                ·
                  refine ⟨30625866714411731665437205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40834488952548975553916273 30625866714411731665437205)
                  ·
                    refine ⟨1435587502238049921817369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30625866714411731665437205 1435587502238049921817369)
                    ·
                      rfl

theorem cell22_4193695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_4193695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193695 prefixEnd_4193695 := by exact prefixLift 4193695
  have htrace : WordTrace (prefixWord ++ tailWord_4193695) baseStart_4193695 baseEnd_4193695 := by
    simpa [prefixWord, tailWord_4193695, baseEnd_4193695] using wordTrace_append hprefix tailTrace_4193695
  have hstable : (prefixWord ++ tailWord_4193695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193695).length < 2 ^ (prefixWord ++ tailWord_4193695).sum := by decide
  have hdescent : baseEnd_4193695 < baseStart_4193695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193725 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_4193725 : Nat := 118140960795 + 4193725 * 2 ^ 59
def prefixEnd_4193725 : Nat := 4983230072969 + 3 ^ 40 * 4193725 * 2
def baseEnd_4193725 : Nat := 1435597771851139843567277

theorem tailTrace_4193725 : CollatzResearch.WordTrace tailWord_4193725 prefixEnd_4193725 1435597771851139843567277 := by
  unfold tailWord_4193725
  simp only [CollatzResearch.WordTrace]
  refine ⟨152957716731858031053030629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101971811154572020702020419 152957716731858031053030629)
  ·
    refine ⟨28679571887223380822443243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152957716731858031053030629 28679571887223380822443243)
    ·
      refine ⟨43019357830835071233664865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28679571887223380822443243 43019357830835071233664865)
      ·
        refine ⟨32264518373126303425248649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43019357830835071233664865 32264518373126303425248649)
        ·
          refine ⟨24198388779844727568936487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32264518373126303425248649 24198388779844727568936487)
          ·
            refine ⟨36297583169767091353404731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24198388779844727568936487 36297583169767091353404731)
            ·
              refine ⟨54446374754650637030107097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36297583169767091353404731 54446374754650637030107097)
              ·
                refine ⟨40834781065987977772580323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54446374754650637030107097 40834781065987977772580323)
                ·
                  refine ⟨61252171598981966658870485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40834781065987977772580323 61252171598981966658870485)
                  ·
                    refine ⟨1435597771851139843567277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61252171598981966658870485 1435597771851139843567277)
                    ·
                      rfl

theorem cell22_4193725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_4193725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193725 prefixEnd_4193725 := by exact prefixLift 4193725
  have htrace : WordTrace (prefixWord ++ tailWord_4193725) baseStart_4193725 baseEnd_4193725 := by
    simpa [prefixWord, tailWord_4193725, baseEnd_4193725] using wordTrace_append hprefix tailTrace_4193725
  have hstable : (prefixWord ++ tailWord_4193725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193725).length < 2 ^ (prefixWord ++ tailWord_4193725).sum := by decide
  have hdescent : baseEnd_4193725 < baseStart_4193725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193774 : List Nat := [4, 1, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_4193774 : Nat := 118140960795 + 4193774 * 2 ^ 59
def prefixEnd_4193774 : Nat := 4983230072969 + 3 ^ 40 * 4193774 * 2
def baseEnd_4193774 : Nat := 1435614545552520049092127

theorem tailTrace_4193774 : CollatzResearch.WordTrace tailWord_4193774 prefixEnd_4193774 1435614545552520049092127 := by
  unfold tailWord_4193774
  simp only [CollatzResearch.WordTrace]
  refine ⟨19119937988585064052695547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101973002605787008281042917 19119937988585064052695547)
  ·
    refine ⟨28679906982877596079043321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19119937988585064052695547 28679906982877596079043321)
    ·
      refine ⟨21509930237158197059282491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28679906982877596079043321 21509930237158197059282491)
      ·
        refine ⟨32264895355737295588923737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21509930237158197059282491 32264895355737295588923737)
        ·
          refine ⟨24198671516802971691692803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32264895355737295588923737 24198671516802971691692803)
          ·
            refine ⟨36298007275204457537539205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24198671516802971691692803 36298007275204457537539205)
            ·
              refine ⟨6805876364100835788288601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36298007275204457537539205 6805876364100835788288601)
              ·
                refine ⟨5104407273075626841216451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6805876364100835788288601 5104407273075626841216451)
                ·
                  refine ⟨7656610909613440261824677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5104407273075626841216451 7656610909613440261824677)
                  ·
                    refine ⟨1435614545552520049092127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7656610909613440261824677 1435614545552520049092127)
                    ·
                      rfl

theorem cell22_4193774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_4193774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193774 prefixEnd_4193774 := by exact prefixLift 4193774
  have htrace : WordTrace (prefixWord ++ tailWord_4193774) baseStart_4193774 baseEnd_4193774 := by
    simpa [prefixWord, tailWord_4193774, baseEnd_4193774] using wordTrace_append hprefix tailTrace_4193774
  have hstable : (prefixWord ++ tailWord_4193774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193774).length < 2 ^ (prefixWord ++ tailWord_4193774).sum := by decide
  have hdescent : baseEnd_4193774 < baseStart_4193774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193789 : List Nat := [1, 4, 1, 1, 1, 4, 3, 3, 4]
def baseStart_4193789 : Nat := 118140960795 + 4193789 * 2 ^ 59
def prefixEnd_4193789 : Nat := 4983230072969 + 3 ^ 40 * 4193789 * 2
def baseEnd_4193789 : Nat := 478539893453021669989027

theorem tailTrace_4193789 : CollatzResearch.WordTrace tailWord_4193789 prefixEnd_4193789 478539893453021669989027 := by
  unfold tailWord_4193789
  simp only [CollatzResearch.WordTrace]
  refine ⟨152960051003626169983360421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101973367335750779988906947 152960051003626169983360421)
  ·
    refine ⟨28680009563179906871880079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152960051003626169983360421 28680009563179906871880079)
    ·
      refine ⟨43020014344769860307820119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28680009563179906871880079 43020014344769860307820119)
      ·
        refine ⟨64530021517154790461730179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43020014344769860307820119 64530021517154790461730179)
        ·
          refine ⟨96795032275732185692595269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64530021517154790461730179 96795032275732185692595269)
          ·
            refine ⟨18149068551699784817361613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96795032275732185692595269 18149068551699784817361613)
            ·
              refine ⟨6805900706887419306510605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18149068551699784817361613 6805900706887419306510605)
              ·
                refine ⟨2552212765082782239941477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6805900706887419306510605 2552212765082782239941477)
                ·
                  refine ⟨478539893453021669989027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2552212765082782239941477 478539893453021669989027)
                  ·
                    rfl

theorem cell22_4193789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_4193789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193789 prefixEnd_4193789 := by exact prefixLift 4193789
  have htrace : WordTrace (prefixWord ++ tailWord_4193789) baseStart_4193789 baseEnd_4193789 := by
    simpa [prefixWord, tailWord_4193789, baseEnd_4193789] using wordTrace_append hprefix tailTrace_4193789
  have hstable : (prefixWord ++ tailWord_4193789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193789).length < 2 ^ (prefixWord ++ tailWord_4193789).sum := by decide
  have hdescent : baseEnd_4193789 < baseStart_4193789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193800 : List Nat := [2, 1, 3, 2, 1, 1, 12]
def baseStart_4193800 : Nat := 118140960795 + 4193800 * 2 ^ 59
def prefixEnd_4193800 : Nat := 4983230072969 + 3 ^ 40 * 4193800 * 2
def baseEnd_4193800 : Nat := 53171238736439431405261

theorem tailTrace_4193800 : CollatzResearch.WordTrace tailWord_4193800 prefixEnd_4193800 53171238736439431405261 := by
  unfold tailWord_4193800
  simp only [CollatzResearch.WordTrace]
  refine ⟨76480226103293159431005427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101973634804390879241340569 76480226103293159431005427)
  ·
    refine ⟨114720339154939739146508141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76480226103293159431005427 114720339154939739146508141)
    ·
      refine ⟨43020127183102402179940553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114720339154939739146508141 43020127183102402179940553)
      ·
        refine ⟨32265095387326801634955415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43020127183102402179940553 32265095387326801634955415)
        ·
          refine ⟨48397643080990202452433123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32265095387326801634955415 48397643080990202452433123)
          ·
            refine ⟨72596464621485303678649685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48397643080990202452433123 72596464621485303678649685)
            ·
              refine ⟨53171238736439431405261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 72596464621485303678649685 53171238736439431405261)
              ·
                rfl

theorem cell22_4193800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 12].length) (baseStart_4193800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193800 prefixEnd_4193800 := by exact prefixLift 4193800
  have htrace : WordTrace (prefixWord ++ tailWord_4193800) baseStart_4193800 baseEnd_4193800 := by
    simpa [prefixWord, tailWord_4193800, baseEnd_4193800] using wordTrace_append hprefix tailTrace_4193800
  have hstable : (prefixWord ++ tailWord_4193800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193800).length < 2 ^ (prefixWord ++ tailWord_4193800).sum := by decide
  have hdescent : baseEnd_4193800 < baseStart_4193800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193802 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_4193802 : Nat := 118140960795 + 4193802 * 2 ^ 59
def prefixEnd_4193802 : Nat := 4983230072969 + 3 ^ 40 * 4193802 * 2
def baseEnd_4193802 : Nat := 1435624130524737309392041

theorem tailTrace_4193802 : CollatzResearch.WordTrace tailWord_4193802 prefixEnd_4193802 1435624130524737309392041 := by
  unfold tailWord_4193802
  simp only [CollatzResearch.WordTrace]
  refine ⟨38240131288144768300895915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101973683435052715469055773 38240131288144768300895915)
  ·
    refine ⟨57360196932217152451343873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38240131288144768300895915 57360196932217152451343873)
    ·
      refine ⟨43020147699162864338507905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57360196932217152451343873 43020147699162864338507905)
      ·
        refine ⟨32265110774372148253880929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43020147699162864338507905 32265110774372148253880929)
        ·
          refine ⟨24198833080779111190410697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32265110774372148253880929 24198833080779111190410697)
          ·
            refine ⟨18149124810584333392808023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24198833080779111190410697 18149124810584333392808023)
            ·
              refine ⟨27223687215876500089212035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18149124810584333392808023 27223687215876500089212035)
              ·
                refine ⟨40835530823814750133818053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27223687215876500089212035 40835530823814750133818053)
                ·
                  refine ⟨7656662029465265650090885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40835530823814750133818053 7656662029465265650090885)
                  ·
                    refine ⟨1435624130524737309392041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7656662029465265650090885 1435624130524737309392041)
                    ·
                      rfl

theorem cell22_4193802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_4193802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193802 prefixEnd_4193802 := by exact prefixLift 4193802
  have htrace : WordTrace (prefixWord ++ tailWord_4193802) baseStart_4193802 baseEnd_4193802 := by
    simpa [prefixWord, tailWord_4193802, baseEnd_4193802] using wordTrace_append hprefix tailTrace_4193802
  have hstable : (prefixWord ++ tailWord_4193802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193802).length < 2 ^ (prefixWord ++ tailWord_4193802).sum := by decide
  have hdescent : baseEnd_4193802 < baseStart_4193802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193806 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_4193806 : Nat := 118140960795 + 4193806 * 2 ^ 59
def prefixEnd_4193806 : Nat := 4983230072969 + 3 ^ 40 * 4193806 * 2
def baseEnd_4193806 : Nat := 478541833268827544097343

theorem tailTrace_4193806 : CollatzResearch.WordTrace tailWord_4193806 prefixEnd_4193806 478541833268827544097343 := by
  unfold tailWord_4193806
  simp only [CollatzResearch.WordTrace]
  refine ⟨19120083880570572735841159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101973780696376387924486181 19120083880570572735841159)
  ·
    refine ⟨28680125820855859103761739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19120083880570572735841159 28680125820855859103761739)
    ·
      refine ⟨43020188731283788655642609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28680125820855859103761739 43020188731283788655642609)
      ·
        refine ⟨32265141548462841491731957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43020188731283788655642609 32265141548462841491731957)
        ·
          refine ⟨3024857020168391389849871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32265141548462841491731957 3024857020168391389849871)
          ·
            refine ⟨4537285530252587084774807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024857020168391389849871 4537285530252587084774807)
            ·
              refine ⟨6805928295378880627162211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4537285530252587084774807 6805928295378880627162211)
              ·
                refine ⟨10208892443068320940743317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6805928295378880627162211 10208892443068320940743317)
                ·
                  refine ⟨478541833268827544097343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10208892443068320940743317 478541833268827544097343)
                  ·
                    rfl

theorem cell22_4193806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_4193806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193806 prefixEnd_4193806 := by exact prefixLift 4193806
  have htrace : WordTrace (prefixWord ++ tailWord_4193806) baseStart_4193806 baseEnd_4193806 := by
    simpa [prefixWord, tailWord_4193806, baseEnd_4193806] using wordTrace_append hprefix tailTrace_4193806
  have hstable : (prefixWord ++ tailWord_4193806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193806).length < 2 ^ (prefixWord ++ tailWord_4193806).sum := by decide
  have hdescent : baseEnd_4193806 < baseStart_4193806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193866 : List Nat := [3, 1, 2, 1, 1, 3, 3, 4, 1, 3]
def baseStart_4193866 : Nat := 118140960795 + 4193866 * 2 ^ 59
def prefixEnd_4193866 : Nat := 4983230072969 + 3 ^ 40 * 4193866 * 2
def baseEnd_4193866 : Nat := 1435646039032662475791845

theorem tailTrace_4193866 : CollatzResearch.WordTrace tailWord_4193866 prefixEnd_4193866 1435646039032662475791845 := by
  unfold tailWord_4193866
  simp only [CollatzResearch.WordTrace]
  refine ⟨38240714856086803033478363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101975239616231474755942301 38240714856086803033478363)
  ·
    refine ⟨57361072284130204550217545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38240714856086803033478363 57361072284130204550217545)
    ·
      refine ⟨43020804213097653412663159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57361072284130204550217545 43020804213097653412663159)
      ·
        refine ⟨64531206319646480118994739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43020804213097653412663159 64531206319646480118994739)
        ·
          refine ⟨96796809479469720178492109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64531206319646480118994739 96796809479469720178492109)
          ·
            refine ⟨36298803554801145066934541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96796809479469720178492109 36298803554801145066934541)
            ·
              refine ⟨13612051333050429400100453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36298803554801145066934541 13612051333050429400100453)
              ·
                refine ⟨2552259624946955512518835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13612051333050429400100453 2552259624946955512518835)
                ·
                  refine ⟨3828389437420433268778253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552259624946955512518835 3828389437420433268778253)
                  ·
                    refine ⟨1435646039032662475791845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3828389437420433268778253 1435646039032662475791845)
                    ·
                      rfl

theorem cell22_4193866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_4193866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193866 prefixEnd_4193866 := by exact prefixLift 4193866
  have htrace : WordTrace (prefixWord ++ tailWord_4193866) baseStart_4193866 baseEnd_4193866 := by
    simpa [prefixWord, tailWord_4193866, baseEnd_4193866] using wordTrace_append hprefix tailTrace_4193866
  have hstable : (prefixWord ++ tailWord_4193866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193866).length < 2 ^ (prefixWord ++ tailWord_4193866).sum := by decide
  have hdescent : baseEnd_4193866 < baseStart_4193866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193937 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 6, 4]
def baseStart_4193937 : Nat := 118140960795 + 4193937 * 2 ^ 59
def prefixEnd_4193937 : Nat := 4983230072969 + 3 ^ 40 * 4193937 * 2
def baseEnd_4193937 : Nat := 1435670343783641957266627

theorem tailTrace_4193937 : CollatzResearch.WordTrace tailWord_4193937 prefixEnd_4193937 1435670343783641957266627 := by
  unfold tailWord_4193937
  simp only [CollatzResearch.WordTrace]
  refine ⟨152965449007089991259748065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101976966004726660839832043 152965449007089991259748065)
  ·
    refine ⟨114724086755317493444811049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152965449007089991259748065 114724086755317493444811049)
    ·
      refine ⟨86043065066488120083608287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114724086755317493444811049 86043065066488120083608287)
      ·
        refine ⟨129064597599732180125412431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86043065066488120083608287 129064597599732180125412431)
        ·
          refine ⟨193596896399598270188118647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129064597599732180125412431 193596896399598270188118647)
          ·
            refine ⟨290395344599397405282177971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193596896399598270188118647 290395344599397405282177971)
            ·
              refine ⟨435593016899096107923266957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290395344599397405282177971 435593016899096107923266957)
              ·
                refine ⟨163347381337161040471225109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435593016899096107923266957 163347381337161040471225109)
                ·
                  refine ⟨7656908500179423772088677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 163347381337161040471225109 7656908500179423772088677)
                  ·
                    refine ⟨1435670343783641957266627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7656908500179423772088677 1435670343783641957266627)
                    ·
                      rfl

theorem cell22_4193937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_4193937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4193937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4193937 prefixEnd_4193937 := by exact prefixLift 4193937
  have htrace : WordTrace (prefixWord ++ tailWord_4193937) baseStart_4193937 baseEnd_4193937 := by
    simpa [prefixWord, tailWord_4193937, baseEnd_4193937] using wordTrace_append hprefix tailTrace_4193937
  have hstable : (prefixWord ++ tailWord_4193937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193937).length < 2 ^ (prefixWord ++ tailWord_4193937).sum := by decide
  have hdescent : baseEnd_4193937 < baseStart_4193937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194044 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_4194044 : Nat := 118140960795 + 4194044 * 2 ^ 59
def prefixEnd_4194044 : Nat := 4983230072969 + 3 ^ 40 * 4194044 * 2
def baseEnd_4194044 : Nat := 1435706972070329344841299

theorem tailTrace_4194044 : CollatzResearch.WordTrace tailWord_4194044 prefixEnd_4194044 1435706972070329344841299 := by
  unfold tailWord_4194044
  simp only [CollatzResearch.WordTrace]
  refine ⟨76484675808851174266946593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101979567745134899022595457 76484675808851174266946593)
  ·
    refine ⟨57363506856638380700209945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76484675808851174266946593 57363506856638380700209945)
    ·
      refine ⟨43022630142478785525157459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57363506856638380700209945 43022630142478785525157459)
      ·
        refine ⟨64533945213718178287736189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43022630142478785525157459 64533945213718178287736189)
        ·
          refine ⟨24200229455144316857901071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64533945213718178287736189 24200229455144316857901071)
          ·
            refine ⟨36300344182716475286851607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24200229455144316857901071 36300344182716475286851607)
            ·
              refine ⟨54450516274074712930277411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36300344182716475286851607 54450516274074712930277411)
              ·
                refine ⟨81675774411112069395416117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54450516274074712930277411 81675774411112069395416117)
                ·
                  refine ⟨7657103851041756505820261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81675774411112069395416117 7657103851041756505820261)
                  ·
                    refine ⟨1435706972070329344841299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7657103851041756505820261 1435706972070329344841299)
                    ·
                      rfl

theorem cell22_4194044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_4194044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4194044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4194044 prefixEnd_4194044 := by exact prefixLift 4194044
  have htrace : WordTrace (prefixWord ++ tailWord_4194044) baseStart_4194044 baseEnd_4194044 := by
    simpa [prefixWord, tailWord_4194044, baseEnd_4194044] using wordTrace_append hprefix tailTrace_4194044
  have hstable : (prefixWord ++ tailWord_4194044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194044).length < 2 ^ (prefixWord ++ tailWord_4194044).sum := by decide
  have hdescent : baseEnd_4194044 < baseStart_4194044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194054 : List Nat := [6, 2, 2, 1, 1, 1, 3, 6]
def baseStart_4194054 : Nat := 118140960795 + 4194054 * 2 ^ 59
def prefixEnd_4194054 : Nat := 4983230072969 + 3 ^ 40 * 4194054 * 2
def baseEnd_4194054 : Nat := 159523377252743628010141

theorem tailTrace_4194054 : CollatzResearch.WordTrace tailWord_4194054 prefixEnd_4194054 159523377252743628010141 := by
  unfold tailWord_4194054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4780303635864566257554913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101979810898444080161171477 4780303635864566257554913)
  ·
    refine ⟨3585227726898424693166185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4780303635864566257554913 3585227726898424693166185)
    ·
      refine ⟨2688920795173818519874639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3585227726898424693166185 2688920795173818519874639)
      ·
        refine ⟨4033381192760727779811959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2688920795173818519874639 4033381192760727779811959)
        ·
          refine ⟨6050071789141091669717939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4033381192760727779811959 6050071789141091669717939)
          ·
            refine ⟨9075107683711637504576909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6050071789141091669717939 9075107683711637504576909)
            ·
              refine ⟨3403165381391864064216341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9075107683711637504576909 3403165381391864064216341)
              ·
                refine ⟨159523377252743628010141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3403165381391864064216341 159523377252743628010141)
                ·
                  rfl

theorem cell22_4194054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_4194054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4194054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4194054 prefixEnd_4194054 := by exact prefixLift 4194054
  have htrace : WordTrace (prefixWord ++ tailWord_4194054) baseStart_4194054 baseEnd_4194054 := by
    simpa [prefixWord, tailWord_4194054, baseEnd_4194054] using wordTrace_append hprefix tailTrace_4194054
  have hstable : (prefixWord ++ tailWord_4194054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194054).length < 2 ^ (prefixWord ++ tailWord_4194054).sum := by decide
  have hdescent : baseEnd_4194054 < baseStart_4194054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194153 : List Nat := [1, 2, 1, 1, 1, 3, 1, 8, 1, 3]
def baseStart_4194153 : Nat := 118140960795 + 4194153 * 2 ^ 59
def prefixEnd_4194153 : Nat := 4983230072969 + 3 ^ 40 * 4194153 * 2
def baseEnd_4194153 : Nat := 1435744284997889393865965

theorem tailTrace_4194153 : CollatzResearch.WordTrace tailWord_4194153 prefixEnd_4194153 1435744284997889393865965 := by
  unfold tailWord_4194153
  simp only [CollatzResearch.WordTrace]
  refine ⟨152973327174307460149611113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101982218116204973433074075 152973327174307460149611113)
  ·
    refine ⟨114729995380730595112208335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152973327174307460149611113 114729995380730595112208335)
    ·
      refine ⟨172094993071095892668312503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114729995380730595112208335 172094993071095892668312503)
      ·
        refine ⟨258142489606643839002468755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172094993071095892668312503 258142489606643839002468755)
        ·
          refine ⟨387213734409965758503703133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258142489606643839002468755 387213734409965758503703133)
          ·
            refine ⟨145205150403737159438888675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 387213734409965758503703133 145205150403737159438888675)
            ·
              refine ⟨217807725605605739158333013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145205150403737159438888675 217807725605605739158333013)
              ·
                refine ⟨2552434284440692255761715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 217807725605605739158333013 2552434284440692255761715)
                ·
                  refine ⟨3828651426661038383642573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552434284440692255761715 3828651426661038383642573)
                  ·
                    refine ⟨1435744284997889393865965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3828651426661038383642573 1435744284997889393865965)
                    ·
                      rfl

theorem cell22_4194153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 1, 3].length) (baseStart_4194153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4194153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4194153 prefixEnd_4194153 := by exact prefixLift 4194153
  have htrace : WordTrace (prefixWord ++ tailWord_4194153) baseStart_4194153 baseEnd_4194153 := by
    simpa [prefixWord, tailWord_4194153, baseEnd_4194153] using wordTrace_append hprefix tailTrace_4194153
  have hstable : (prefixWord ++ tailWord_4194153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194153).length < 2 ^ (prefixWord ++ tailWord_4194153).sum := by decide
  have hdescent : baseEnd_4194153 < baseStart_4194153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194200 : List Nat := [2, 1, 2, 6, 1, 1, 2, 2, 5]
def baseStart_4194200 : Nat := 118140960795 + 4194200 * 2 ^ 59
def prefixEnd_4194200 : Nat := 4983230072969 + 3 ^ 40 * 4194200 * 2
def baseEnd_4194200 : Nat := 478586791352798979313607

theorem tailTrace_4194200 : CollatzResearch.WordTrace tailWord_4194200 prefixEnd_4194200 478586791352798979313607 := by
  unfold tailWord_4194200
  simp only [CollatzResearch.WordTrace]
  refine ⟨76487520702568593588286027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101983360936758124784381369 76487520702568593588286027)
  ·
    refine ⟨114731281053852890382429041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76487520702568593588286027 114731281053852890382429041)
    ·
      refine ⟨86048460790389667786821781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114731281053852890382429041 86048460790389667786821781)
      ·
        refine ⟨4033521599549515677507271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86048460790389667786821781 4033521599549515677507271)
        ·
          refine ⟨6050282399324273516260907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4033521599549515677507271 6050282399324273516260907)
          ·
            refine ⟨9075423598986410274391361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6050282399324273516260907 9075423598986410274391361)
            ·
              refine ⟨6806567699239807705793521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9075423598986410274391361 6806567699239807705793521)
              ·
                refine ⟨5104925774429855779345141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6806567699239807705793521 5104925774429855779345141)
                ·
                  refine ⟨478586791352798979313607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5104925774429855779345141 478586791352798979313607)
                  ·
                    rfl

theorem cell22_4194200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 5].length) (baseStart_4194200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4194200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4194200 prefixEnd_4194200 := by exact prefixLift 4194200
  have htrace : WordTrace (prefixWord ++ tailWord_4194200) baseStart_4194200 baseEnd_4194200 := by
    simpa [prefixWord, tailWord_4194200, baseEnd_4194200] using wordTrace_append hprefix tailTrace_4194200
  have hstable : (prefixWord ++ tailWord_4194200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194200).length < 2 ^ (prefixWord ++ tailWord_4194200).sum := by decide
  have hdescent : baseEnd_4194200 < baseStart_4194200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194204 : List Nat := [2, 2, 3, 3, 1, 3, 2, 2, 1, 3]
def baseStart_4194204 : Nat := 118140960795 + 4194204 * 2 ^ 59
def prefixEnd_4194204 : Nat := 4983230072969 + 3 ^ 40 * 4194204 * 2
def baseEnd_4194204 : Nat := 1435761743340142260840809

theorem tailTrace_4194204 : CollatzResearch.WordTrace tailWord_4194204 prefixEnd_4194204 1435761743340142260840809 := by
  unfold tailWord_4194204
  simp only [CollatzResearch.WordTrace]
  refine ⟨76487593648561347929858833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101983458198081797239811777 76487593648561347929858833)
  ·
    refine ⟨57365695236421010947394125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76487593648561347929858833 57365695236421010947394125)
    ·
      refine ⟨21512135713657879105272797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57365695236421010947394125 21512135713657879105272797)
      ·
        refine ⟨8067050892621704664477299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21512135713657879105272797 8067050892621704664477299)
        ·
          refine ⟨12100576338932556996715949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8067050892621704664477299 12100576338932556996715949)
          ·
            refine ⟨4537716127099708873768481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12100576338932556996715949 4537716127099708873768481)
            ·
              refine ⟨3403287095324781655326361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4537716127099708873768481 3403287095324781655326361)
              ·
                refine ⟨2552465321493586241494771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3403287095324781655326361 2552465321493586241494771)
                ·
                  refine ⟨3828697982240379362242157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552465321493586241494771 3828697982240379362242157)
                  ·
                    refine ⟨1435761743340142260840809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3828697982240379362242157 1435761743340142260840809)
                    ·
                      rfl

theorem cell22_4194204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_4194204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4194204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4194204 prefixEnd_4194204 := by exact prefixLift 4194204
  have htrace : WordTrace (prefixWord ++ tailWord_4194204) baseStart_4194204 baseEnd_4194204 := by
    simpa [prefixWord, tailWord_4194204, baseEnd_4194204] using wordTrace_append hprefix tailTrace_4194204
  have hstable : (prefixWord ++ tailWord_4194204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194204).length < 2 ^ (prefixWord ++ tailWord_4194204).sum := by decide
  have hdescent : baseEnd_4194204 < baseStart_4194204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194288 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 3, 3]
def baseStart_4194288 : Nat := 118140960795 + 4194288 * 2 ^ 59
def prefixEnd_4194288 : Nat := 4983230072969 + 3 ^ 40 * 4194288 * 2
def baseEnd_4194288 : Nat := 1435790498256794041740551

theorem tailTrace_4194288 : CollatzResearch.WordTrace tailWord_4194288 prefixEnd_4194288 1435790498256794041740551 := by
  unfold tailWord_4194288
  simp only [CollatzResearch.WordTrace]
  refine ⟨76489125514409189102887759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101985500685878918803850345 76489125514409189102887759)
  ·
    refine ⟨114733688271613783654331639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76489125514409189102887759 114733688271613783654331639)
    ·
      refine ⟨172100532407420675481497459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114733688271613783654331639 172100532407420675481497459)
      ·
        refine ⟨258150798611131013222246189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172100532407420675481497459 258150798611131013222246189)
        ·
          refine ⟨96806549479174129958342321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258150798611131013222246189 96806549479174129958342321)
          ·
            refine ⟨72604912109380597468756741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96806549479174129958342321 72604912109380597468756741)
            ·
              refine ⟨13613421020508862025391889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72604912109380597468756741 13613421020508862025391889)
              ·
                refine ⟨10210065765381646519043917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13613421020508862025391889 10210065765381646519043917)
                ·
                  refine ⟨3828774662018117444641469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10210065765381646519043917 3828774662018117444641469)
                  ·
                    refine ⟨1435790498256794041740551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3828774662018117444641469 1435790498256794041740551)
                    ·
                      rfl

theorem cell22_4194288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 3, 3].length) (baseStart_4194288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4194288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4194288 prefixEnd_4194288 := by exact prefixLift 4194288
  have htrace : WordTrace (prefixWord ++ tailWord_4194288) baseStart_4194288 baseEnd_4194288 := by
    simpa [prefixWord, tailWord_4194288, baseEnd_4194288] using wordTrace_append hprefix tailTrace_4194288
  have hstable : (prefixWord ++ tailWord_4194288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194288).length < 2 ^ (prefixWord ++ tailWord_4194288).sum := by decide
  have hdescent : baseEnd_4194288 < baseStart_4194288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194301 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 7]
def baseStart_4194301 : Nat := 118140960795 + 4194301 * 2 ^ 59
def prefixEnd_4194301 : Nat := 4983230072969 + 3 ^ 40 * 4194301 * 2
def baseEnd_4194301 : Nat := 478598316140822113721837

theorem tailTrace_4194301 : CollatzResearch.WordTrace tailWord_4194301 prefixEnd_4194301 478598316140822113721837 := by
  unfold tailWord_4194301
  simp only [CollatzResearch.WordTrace]
  refine ⟨152978725177771281425998757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101985816785180854283999171 152978725177771281425998757)
  ·
    refine ⟨28683510970832115267374767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152978725177771281425998757 28683510970832115267374767)
    ·
      refine ⟨43025266456248172901062151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28683510970832115267374767 43025266456248172901062151)
      ·
        refine ⟨64537899684372259351593227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43025266456248172901062151 64537899684372259351593227)
        ·
          refine ⟨96806849526558389027389841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64537899684372259351593227 96806849526558389027389841)
          ·
            refine ⟨72605137144918791770542381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96806849526558389027389841 72605137144918791770542381)
            ·
              refine ⟨27226926429344546913953393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72605137144918791770542381 27226926429344546913953393)
              ·
                refine ⟨20420194822008410185465045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27226926429344546913953393 20420194822008410185465045)
                ·
                  refine ⟨478598316140822113721837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20420194822008410185465045 478598316140822113721837)
                  ·
                    rfl

theorem cell22_4194301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_4194301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4194301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4194301 prefixEnd_4194301 := by exact prefixLift 4194301
  have htrace : WordTrace (prefixWord ++ tailWord_4194301) baseStart_4194301 baseEnd_4194301 := by
    simpa [prefixWord, tailWord_4194301, baseEnd_4194301] using wordTrace_append hprefix tailTrace_4194301
  have hstable : (prefixWord ++ tailWord_4194301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194301).length < 2 ^ (prefixWord ++ tailWord_4194301).sum := by decide
  have hdescent : baseEnd_4194301 < baseStart_4194301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
